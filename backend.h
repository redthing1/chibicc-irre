#ifndef _BACKEND_H_
#define _BACKEND_H_

#include "chibicc.h"

void backend_codegen(Obj *prog, FILE *out);
int backend_align_to(int n, int align);
int backend_ptr_size(void);

extern bool opt_emit_debug;
extern bool opt_default_main;

#endif // _BACKEND_H_