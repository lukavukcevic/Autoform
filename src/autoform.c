/* autoform.c — informal theorem -> Lean 4, verified with `lake env lean`, auto-retried on failure. */
#define _POSIX_C_SOURCE 200809L
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>
#include <curl/curl.h>

static char *vstr(const char *fmt, ...) { // Allocates a string large enough to hold the output, similar to vasprintf from glibc/BSD exts
    va_list ap;
    va_list ap2; // both needed because ap is undefined after vsnprintf call
    va_start(ap, fmt); // Initializes ap to point to the first argument after fmt
    va_copy(ap2, ap);
    int n = vsnprintf(NULL, 0, fmt, ap); // Returns number of bytes written (excluding \0) (0 bytes into buffer NULL)
    va_end(ap); // ap cleanup
    char *s = malloc(n + 1); // Allocates n + 1 bytes for string s (1 for \0)
    vsnprintf(s, n + 1, fmt, ap2);
    va_end(ap2);
    return s;
}

static char *json_body(const char *prompt) {
    char *buf;
    size_t len;
    FILE *m = open_memstream(&buf, &len); // Opens a stream for writing to a growing memory buffer, free buffer after closing stream
    fputs("{\"contents\":[{\"parts\":[{\"text\":\"", m);
    for (const char *s = prompt; *s; ++s) { // Iterates over characters until \0
        unsigned char c = *s; // Avoids sign-extension issues if bytes \ge 0x80 (decimal 128)
        if (c == '"' || c == '\\') fprintf(m, "\\%c", c); // Escapes double quotes and backslashes
        else if (c == '\n') fputs("\\n", m); // Escapes newlines
        else if (c < 0x20) fprintf(m, "\\u%04x", c); // Escape control characters (ASCII 0-31) as Unicode \u00XX (x is hex)
        else fputc(c, m); // All others print normally
    }
    fputs("\"}]}]}", m);
    fclose(m); // Close memstream
    return buf; // Caller must free
}

/* Extract unescaped value string from "key":"value" in a JSON blob */
static char *json_field(const char *json, const char *key) {
    char pat[64];
    snprintf(pat, sizeof(pat), "\"%s\":", key);
    const char *p = strstr(json, pat); // Locate the first occurrence of substring pat in json (NULL if not found)
    if (!p) return NULL;
    p = strchr(p + strlen(pat), '"'); // Look for the opening quote immediately after the pattern
    if (!p) return NULL;
    ++p;
    char *buf;
    size_t len;
    FILE *m = open_memstream(&buf, &len);
    for (; *p && *p != '"'; ++p) {
        if (*p != '\\') { fputc(*p, m); continue; }
        ++p;
        unsigned cp;
        switch (*p) {
            case 'n': fputc('\n', m); break;
            case 't': fputc('\t', m); break;
            case 'r': fputc('\r', m); break;
            case 'u':
                sscanf(p + 1, "%4x", &cp); p += 4; // Grab the two bytes after the \u and store them in cp then advance p to the last of the four digits
                if (cp < 0x80) fputc((int)cp, m); // 0-31 control characters (ASCII is a strict subset of Unicode)
                else if (cp < 0x800) { fputc(0xC0 | (int)(cp >> 6), m); fputc(0x80 | (int)(cp & 0x3F), m); } // 110xxxxx 10xxxxxx (2 bytes), so two fputc calls
                else { fputc(0xE0 | (int)(cp >> 12), m); fputc(0x80 | (int)((cp >> 6) & 0x3F), m); fputc(0x80 | (int)(cp & 0x3F), m); } // 3 bytes (1110xxxx 10xxxxxx 10xxxxxx)
                break;
            default: fputc(*p, m);
        }
    }
    fclose(m);
    return buf; // Caller must free
}

/* Pull the contents of the first ```lean fenced block, or the whole text if none found. */
static char *extract_lean(const char *text) {
    const char *start = strstr(text, "```lean");
    start = start ? start + 7 : strstr(text, "```"); // What if start + 7 is NULL?
    if (!start) return strdup(text); // Should be freeed by the caller
    while (*start == '\n') { ++start; } // Skip any newlines
    const char *end = strstr(start, "```");
    size_t n = end ? (size_t)(end - start) : strlen(start);
    char *out = malloc(n + 1);
    memcpy(out, start, n);
    out[n] = 0; // Null terminator
    return out; // Freed by the caller
}

static char *gemini_generate(CURL *curl, const char *key, const char *model, const char *prompt) {
    char url[256];
    snprintf(url, sizeof(url), "https://generativelanguage.googleapis.com/v1beta/models/%s:generateContent?key=%s", model, key);
    char *body = json_body(prompt);

    char *resp;
    size_t resplen;
    FILE *m = open_memstream(&resp, &resplen);
    struct curl_slist *hdr = curl_slist_append(NULL, "Content-Type: application/json");
    curl_easy_setopt(curl, CURLOPT_URL, url);
    curl_easy_setopt(curl, CURLOPT_HTTPHEADER, hdr);
    curl_easy_setopt(curl, CURLOPT_POSTFIELDS, body);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA, m);
    CURLcode rc = curl_easy_perform(curl);
    curl_slist_free_all(hdr);
    free(body); // Frees the return value of json_body
    fclose(m);

    if (rc != CURLE_OK) { fprintf(stderr, "request failed: %s\n", curl_easy_strerror(rc)); free(resp); return NULL; }
    char *text = json_field(resp, "text");
    if (!text) fprintf(stderr, "gemini error: %s\n", resp); // Got OK but response is empty 
    free(resp);
    return text;
}

/* Write code as Scratch.lean in dir and typecheck it with `lake env lean`. Returns exit status. */
static int run_lake(const char *dir, const char *code, char **out) {
    char path[1024];
    snprintf(path, sizeof(path), "%s/Scratch.lean", dir);
    FILE *f = fopen(path, "w");
    if (!f) { perror("fopen"); return -1; }
    fputs(code, f);
    fclose(f);

    char cwd[1024];
    if (!getcwd(cwd, sizeof(cwd)) || chdir(dir) != 0) { perror("chdir"); return -1; }
    FILE *p = popen("lake env lean Scratch.lean 2>&1", "r");
    char *buf;
    size_t len;
    FILE *m = open_memstream(&buf, &len);
    if (p) { 
      char tmp[4096];
      size_t n;
      while ((n = fread(tmp, 1, sizeof(tmp), p)) > 0) { fwrite(tmp, 1, n, m); }
    }
    fclose(m);
    int status = p ? pclose(p) : -1;
    chdir(cwd);
    *out = buf;
    return (p && WIFEXITED(status)) ? WEXITSTATUS(status) : -1; // If popen() succeeded and the child process exited normally (no signals) return its real exit code, otherwise -1
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "usage: %s \"informal theorem formulation\" [lean_project_dir] [max_retries]\n", argv[0]);
        return 1;
    }
    const char *statement = argv[1];
    const char *dir = argc > 2 ? argv[2] : ".";
    int max_retries = argc > 3 ? atoi(argv[3]) : 1;

    const char *key = getenv("GEMINI_API_KEY");
    if (!key) { fprintf(stderr, "GEMINI_API_KEY not set\n"); return 1; }
    const char *model = getenv("GEMINI_MODEL");
    if (!model) { model = "gemini-3.5-flash-lite"; }

    curl_global_init(CURL_GLOBAL_DEFAULT);
    CURL *curl = curl_easy_init();
    curl_easy_setopt(curl, CURLOPT_TIMEOUT, 120L);

    char *code = NULL;
    char *error = NULL;
    for (int i = 1; i <= max_retries + 1; ++i) {
        char *prompt = !code
            ? vstr("Translate the following informal theorem into a single self-contained Lean 4 theorem "
                   "(mathlib available) that type-checks with `lake env lean`. Reply with ONLY one ```lean "
                   "fenced code block, no other prose.\n\nInformal statement:\n%s\n", statement)
            : vstr("This Lean 4 code failed to type-check with `lake env lean`.\n\nInformal statement:\n%s\n\n"
                   "Lean code:\n%s\n\nCompiler output:\n%s\n\nFix it. Reply with ONLY one corrected ```lean "
                   "fenced code block, no other prose.\n", statement, code, error);

        printf("[%d/%d] generating Lean...\n", i, max_retries + 1);
        char *text = gemini_generate(curl, key, model, prompt);
        free(prompt); // Frees the pointer returned by vstr
        if (!text) { fprintf(stderr, "no response, retrying...\n"); continue; }

        free(code); // noop the first time when code is NULL, frees after potential retry prompt formation
        code = extract_lean(text);
        free(text);

        free(error);
        error = NULL; // To prevent use-after-free in the following call
        int rc = run_lake(dir, code, &error);
        if (rc == 0) {
            printf("verified: %s/Scratch.lean\n", dir);
            curl_easy_cleanup(curl);
            curl_global_cleanup();
            return 0;
        }
        printf("[%d/%d] lake failed:\n%s\n", i, max_retries, error);
    }

    fprintf(stderr, "stopped after %d attempts\n", max_retries + 1);
    curl_easy_cleanup(curl);
    curl_global_cleanup();
    return 1;
}
