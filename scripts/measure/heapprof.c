/* Where the peak heap goes: every block alive at the peak of a process,
   each with the call stack of its allocation.

   Loaded with LD_PRELOAD on Linux (glibc), like heapshim.c, and counting
   the same quantity: the usable size of every block from malloc,
   calloc, realloc and the aligned allocators. Single-threaded programs.

   The peak is known only at exit, so the profile takes two runs of the
   same deterministic command. The first, under heapshim.so, gives the
   peak P. The second, under this object with HEAPPROF_AT=P, records the
   stack of every allocation and, the first time the bytes alive reach
   P, writes to the file HEAPPROF_OUT names:

     at BYTES                  the bytes alive at that moment
     map LINE                  the lines of /proc/self/maps, to place
                               the addresses in their modules
     block SIZE ADDR ADDR ...  one line per block alive, its usable size
                               and the return addresses of its stack,
                               innermost first, in hexadecimal

   A run that never reaches P (not the same command, or not
   deterministic) writes only "at 0" and its own peak at exit. The
   profiler's own allocations (while it records a stack) are kept out of
   the count, so that it counts exactly what heapshim.c counts.
   scripts/measure/attribute-steps.py reads the file. */
#define _GNU_SOURCE
#include <execinfo.h>
#include <fcntl.h>
#include <malloc.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

extern void *__libc_malloc (size_t);
extern void *__libc_calloc (size_t, size_t);
extern void *__libc_realloc (void *, size_t);
extern void  __libc_free (void *);
extern void *__libc_memalign (size_t, size_t);

#define DEPTH 40
#define SLOTS (1u << 21)   /* live blocks at once, at most */

typedef struct { void *p; size_t n; int depth; void *bt[DEPTH]; } slot_t;

static slot_t *table;      /* open addressing, linear probing, in mmap */
static size_t cur, peak, target, lost;
static int busy, dumped, ready;

/* The profiler's own blocks: those allocated while it records a stack
   or writes the dump (the unwinder's, the formatter's). They do not exist
   under heapshim.so, so they are kept out of the count, and their
   addresses here so that their release is kept out too. */
#define OWN 256
static void *own[OWN];
static size_t own_bytes;

static size_t home (void *p) {
   return (size_t) (((uintptr_t) p >> 4) * 0x9E3779B97F4A7C15ull) & (SLOTS - 1);
}

static void insert (void *p, size_t n) {
   size_t i = home (p);
   while (table[i].p) i = (i + 1) & (SLOTS - 1);
   table[i].p = p; table[i].n = n;
   busy = 1; table[i].depth = backtrace (table[i].bt, DEPTH); busy = 0;
}

/* Deletion with backward shift, so that no tombstones accumulate. */
static void erase (void *p) {
   size_t i = home (p), k = 0;
   while (table[i].p && table[i].p != p) {
      i = (i + 1) & (SLOTS - 1);
      if (++k > SLOTS) return;
   }
   if (!table[i].p) return;
   size_t j = i;
   for (;;) {
      table[i].p = NULL;
      for (;;) {
         j = (j + 1) & (SLOTS - 1);
         if (!table[j].p) return;
         size_t h = home (table[j].p);
         if (i <= j ? (i < h && h <= j) : (i < h || h <= j)) continue;
         break;
      }
      table[i] = table[j];
      i = j;
   }
}

static void dump (void) {
   const char *out = getenv ("HEAPPROF_OUT");
   int fd = out ? open (out, O_WRONLY | O_CREAT | O_TRUNC, 0644) : 2;
   if (fd < 0) return;
   busy = 1;
   dprintf (fd, "at %zu\n", cur);
   int m = open ("/proc/self/maps", O_RDONLY);
   if (m >= 0) {
      char buf[4096], line[4096]; ssize_t r; size_t l = 0;
      while ((r = read (m, buf, sizeof buf)) > 0)
         for (ssize_t k = 0; k < r; k++) {
            if (buf[k] == '\n' || l == sizeof line - 1) {
               line[l] = 0; dprintf (fd, "map %s\n", line); l = 0;
            } else line[l++] = buf[k];
         }
      close (m);
   }
   for (size_t i = 0; i < SLOTS; i++)
      if (table[i].p) {
         dprintf (fd, "block %zu", table[i].n);
         for (int k = 0; k < table[i].depth; k++) dprintf (fd, " %p", table[i].bt[k]);
         dprintf (fd, "\n");
      }
   if (lost) dprintf (fd, "unrecorded %zu\n", lost);
   dprintf (fd, "own %zu\n", own_bytes);
   if (fd != 2) close (fd);
   busy = 0;
}

static int own_take (void *p) {
   for (int i = 0; i < OWN; i++)
      if (own[i] == p) { own[i] = NULL; return 1; }
   return 0;
}

static void add (void *p) {
   if (!p) return;
   size_t n = malloc_usable_size (p);
   if (busy) {
      for (int i = 0; i < OWN; i++)
         if (!own[i]) { own[i] = p; own_bytes += n; return; }
      lost += n;           /* not expected: counted, and reported */
   }
   cur += n;
   if (cur > peak) peak = cur;
   if (!ready || busy) return;
   insert (p, n);
   if (target && !dumped && cur >= target) { dumped = 1; dump (); }
}

static void sub (void *p) {
   if (!p) return;
   size_t n = malloc_usable_size (p);
   if (own_take (p)) { own_bytes -= n; return; }
   cur -= n;
   if (ready && !busy) erase (p);
}

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

__attribute__((constructor)) static void init (void) {
   void *bt[2];
   busy = 1; backtrace (bt, 2); busy = 0;   /* loads the unwinder first */
   const char *t = getenv ("HEAPPROF_AT");
   target = t ? strtoull (t, NULL, 10) : 0;
   table = mmap (NULL, sizeof (slot_t) * SLOTS, PROT_READ | PROT_WRITE,
                 MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
   ready = table != MAP_FAILED;
}

__attribute__((destructor)) static void report (void) {
   if (!dumped) {
      const char *out = getenv ("HEAPPROF_OUT");
      int fd = out ? open (out, O_WRONLY | O_CREAT | O_TRUNC, 0644) : 2;
      if (fd >= 0) {
         dprintf (fd, "at 0\npeak %zu\n", peak);
         if (fd != 2) close (fd);
      }
   }
}
