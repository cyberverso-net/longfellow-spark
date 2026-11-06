/* Peak heap of a process: counts the usable size of every block from
   malloc, calloc, realloc and the aligned allocators, and prints the
   peak and the size still allocated at exit, with the program's name,
   to the file HEAPSHIM_OUT names (appended), or to standard error.
   Loaded with LD_PRELOAD; single-threaded programs. */
#define _GNU_SOURCE
#include <malloc.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern void *__libc_malloc (size_t);
extern void *__libc_calloc (size_t, size_t);
extern void *__libc_realloc (void *, size_t);
extern void  __libc_free (void *);
extern void *__libc_memalign (size_t, size_t);

static size_t cur, peak;

static void add (void *p) {
   if (p) { cur += malloc_usable_size (p); if (cur > peak) peak = cur; }
}
static void sub (void *p) { if (p) cur -= malloc_usable_size (p); }

void *malloc (size_t n) { void *p = __libc_malloc (n); add (p); return p; }
void *calloc (size_t m, size_t n) { void *p = __libc_calloc (m, n); add (p); return p; }
void free (void *p) { sub (p); __libc_free (p); }
void *realloc (void *q, size_t n) {
   sub (q); void *p = __libc_realloc (q, n);
   if (p) add (p); else if (q && n) add (q);
   return p;
}
void *memalign (size_t a, size_t n) { void *p = __libc_memalign (a, n); add (p); return p; }
void *aligned_alloc (size_t a, size_t n) { return memalign (a, n); }
int posix_memalign (void **r, size_t a, size_t n) {
   void *p = __libc_memalign (a, n); if (!p) return 12; add (p); *r = p; return 0;
}

__attribute__((destructor)) static void report (void) {
   char name[64] = "?"; FILE *f = fopen ("/proc/self/comm", "r");
   if (f) { if (fgets (name, sizeof name, f)) name[strcspn (name, "\n")] = 0; fclose (f); }
   const char *out = getenv ("HEAPSHIM_OUT");
   FILE *o = out ? fopen (out, "a") : NULL;
   fprintf (o ? o : stderr, "heapshim %s peak %zu current %zu\n", name, peak, cur);
   if (o) fclose (o);
}
