#ifndef ARCHIPELAGO_H
#define ARCHIPELAGO_H

typedef void *tuple_t;
extern tuple_t *tuple(unsigned int, ...);

struct List;
extern struct List *list(unsigned int, ...);

#endif /* ARCHIPELAGO_H */
