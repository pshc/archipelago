#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

__dead2 void fail(const char *);
__dead2 void oom(void);

#define GC_MARK ((uintptr_t) 1)
#define GC_ARRAY ((uintptr_t) 2)

#ifdef LOGGC
# define GC_PUTS(s) puts(s)
# define GC_PUTCHAR(c) putchar(c)
# define GC_PRINTF(...) printf(__VA_ARGS__)
#else
# define GC_PUTS(s) do {} while (0)
# define GC_PUTCHAR(c) do {} while (0)
# define GC_PRINTF(...) do {} while (0)
#endif

union gc_ptr {
	uintptr_t flags;
	uint8_t *ptr;
};

struct gc_atom {
	union gc_ptr gc;
	/* extrs, discrim, fields etc. */
};

struct vector {
	union gc_ptr gc;
	uintptr_t *ptr;
};

struct frame_map {
	struct frame_map *prev;
	uint32_t num_roots;
	struct gc_atom *roots[1];
};

extern struct frame_map *bluefin_root;

static void *heap[64] = {0};
static size_t heap_count = 0;

static void push_heap_ptr(void *ptr) {
	if (heap_count >= sizeof heap / sizeof *heap)
		fail("Out of GC heap entries"); /* pffft */
	heap[heap_count++] = ptr;
}

static void pop_heap_ptr(size_t i) {
	if (!heap_count)
		fail("Popping empty heap");
	if (i >= heap_count)
		fail("Bad GC heap pop");
	heap_count--;
	/* move last heap entry into this now-vacant slot */
	heap[i] = heap[heap_count];
	heap[heap_count] = NULL;
}

union packed_ptr {
	char bytes[sizeof(uintptr_t)];
	uintptr_t **ptr;
};

static void mark_gc_atom(struct gc_atom *);
static void walk_gc_vector(struct vector *, uintptr_t);

#ifdef LOGGC
static const char *read_gc_spec_name(const uint8_t *spec, size_t n) {
	const uint8_t *name = spec + n * (1 + sizeof(uintptr_t));
	for (size_t i = 0; name[i]; i++) {
		if (name[i] < '0' || name[i] > 'z')
			fail("Suspicious unusual ctor name char");
		if (i > 30)
			fail("Ctor name is suspiciously long");
	}
	return (const char *) name;
}
#endif /* LOGGC */

static void read_atom_spec(struct gc_atom *atom, const uint8_t *spec) {
	GC_PRINTF("    spec at %016lx ", (uintptr_t) spec);
	size_t n = *spec++;
	if (!n)
		return;
	if (n > 20)
		fail("Suspicious field count");

	/* ctor name at end */
	GC_PRINTF("is a %s.\n", read_gc_spec_name(spec, n));

	for (size_t i = 0; i < n; i++) {
		size_t offset = *spec++;

		/* unaligned load */
		union packed_ptr tbl_ptr;
		memcpy(tbl_ptr.bytes, spec, sizeof tbl_ptr.bytes);
		if (tbl_ptr.ptr) {
			/* TODO: use *tbl_ptr.ptr to typecheck */
		}
		spec += sizeof tbl_ptr.bytes;

		/* recurse into atom pointed by field */
		struct gc_atom *ref_atom = *(struct gc_atom **)
				((char *)atom + offset);

		GC_PRINTF("     field at %d points to atom %016lx\n",
				(int) offset, (uintptr_t) ref_atom);

		if (ref_atom)
			mark_gc_atom(ref_atom);
	}
}

static void mark_gc_atom(struct gc_atom *atom) {
	if (atom->gc.flags & GC_MARK) {
		GC_PUTS("(already marked)");
		return;
	}

	GC_PRINTF("   marking %016lx: ", (uintptr_t) atom);
	for (int i = 0; i < 16; i++) {
		GC_PRINTF("%02x ", ((uint8_t *) atom)[i]);
		if (i % 4 == 3)
			GC_PUTCHAR(' ');
	}
	GC_PUTCHAR('\n');

	union gc_ptr orig = atom->gc;
	/* mark before recursing into fields */
	atom->gc.flags |= GC_MARK;

	if (orig.flags & GC_ARRAY)
		walk_gc_vector((struct vector *) atom, orig.flags);
	else if (orig.ptr)
		read_atom_spec(atom, orig.ptr);
}

void gc_collect(void) {
	GC_PUTS("=== marking...");

	struct frame_map *frame = bluefin_root;
	GC_PRINTF("top frame %016lx\n", (uintptr_t) frame);
	for (; frame; frame = frame->prev) {
		uint32_t n = frame->num_roots;
		GC_PRINTF(" stack frame %016lx with %u roots\n",
				(uintptr_t) frame, (unsigned int) n);
		for (uint32_t i = 0; i < n; i++) {
			struct gc_atom *root = frame->roots[i];
			if (root)
				mark_gc_atom(root);
		}
	}

	GC_PUTS("=== sweeping...");
	/* heap_count may decrease due to pop_heap_ptr(); watch out! */
	for (size_t i = 0; i < heap_count; i++) {
		struct gc_atom *atom = heap[i];
		GC_PRINTF(" 0x%016lx is ", (uintptr_t) atom);
		if (atom->gc.flags & GC_MARK) {
			atom->gc.flags &= ~GC_MARK;
			GC_PUTS("live");
		}
		else {
			GC_PRINTF("dead. ");
			/* this heap entry will disappear, so decrement i */
			pop_heap_ptr(i--);
			free(atom);
			GC_PUTS("freed.");
		}
	}

	GC_PUTS("=== done collection.");
}

void *gc_alloc(size_t size) {
	gc_collect();
	void *p = malloc(size);
	if (!p)
		oom();
	push_heap_ptr(p);
	GC_PRINTF("Allocated 0x%016lx.\n", (uintptr_t) p);
	return p;
}

/* GC VECTORS */

static void walk_gc_vector(struct vector *vector, uintptr_t flags) {
	/* there are no array specs, just a len, so check that
	   gc_ptr field == GC_ARRAY | (len<<8) */
	if ((flags & 0xff) != GC_ARRAY)
		fail("GC walk: Suspicious array signature");
	size_t len = flags >> 8;
	if (len > 0xffff)
		fail("GC walk: Array is unrealistically big");
	GC_PRINTF("    array of length %d\n", (int) len);

	uintptr_t *p = vector->ptr;
	for (size_t i = 0; i < len; i++) {
		uintptr_t elem = *p++;
		if (elem)
			mark_gc_atom((struct gc_atom *) elem);
	}
}

struct vector *gc_array(int32_t n) {
	if (n < 0)
		fail("Negative length array?!");
	if (n > 0xffff)
		fail("Array is unrealistically big");

	gc_collect();

	struct vector *vector = malloc(sizeof *vector);
	if (!vector)
		oom();
	if (n > 0) {
		if (!(vector->ptr = calloc(n, sizeof(void *)))) {
			free(vector);
			oom();
		}
	}
	else
		vector->ptr = NULL;

	vector->gc.flags = GC_ARRAY | (n << 8);
	push_heap_ptr(vector);
	GC_PRINTF("Allocated array 0x%016lx of length %u.\n",
			(uintptr_t) vector, n);

	return vector;
}

uintptr_t *gc_array_ptr(struct vector *vec) {
	if (!vec)
		fail("null vector");
	return vec->ptr;
}

int32_t gc_array_len(struct vector *vec) {
	if (!vec)
		fail("null vector");
	uintptr_t flags = vec->gc.flags;
	if ((flags & 0xff) != GC_ARRAY)
		fail(flags & GC_MARK ? "marked array?!" : "bad array sig");

	uintptr_t len = flags >> 8;
	if (len > 0xffff)
		fail("gc_array_len: unrealistic array length");
	return (int32_t) len;
}

uintptr_t gc_array_subscript(struct vector *vec, int32_t index) {
	if (index < 0)
		fail("negative array index");
	int32_t len = gc_array_len(vec);
	if (index >= len)
		fail("out of bounds");
	return vec->ptr[index];
}
