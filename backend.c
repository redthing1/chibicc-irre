#include "chibicc.h"
#include "backend.h"

#define BACKEND_X86_64
#define BACKEND_RISCV64
// #define BACKEND_AARCH64
#define BACKEND_IRRE

#ifdef BACKEND_X86_64
void codegen_x86_64(Obj *prog, FILE *out);
int align_to_x86_64(int n, int align);
extern int ptr_size_x86_64;
#endif
#ifdef BACKEND_AARCH64
void codegen_aarch64(Obj *prog, FILE *out);
int align_to_aarch64(int n, int align);
extern int ptr_size_aarch64;
#endif
#ifdef BACKEND_RISCV64
void codegen_riscv64(Obj *prog, FILE *out);
int align_to_riscv64(int n, int align);
extern int ptr_size_riscv64;
#endif
#ifdef BACKEND_IRRE
void codegen_irre(Obj *prog, FILE *out);
int align_to_irre(int n, int align);
extern int ptr_size_irre;
#endif

/** backend_codegen wrapper that selects backend by arch */
void backend_codegen(Obj *prog, FILE *out) {
  if (!opt_march || strcmp(opt_march, "help") == 0) {
    printf("Specify -march <arch> to select a target architecture.\n");
    exit(2);
  }
#ifdef BACKEND_X86_64
  else if (strcmp(opt_march, "x86_64") == 0)
    codegen_x86_64(prog, out);
#endif
#ifdef BACKEND_AARCH64
  else if (strcmp(opt_march, "aarch64") == 0)
    codegen_aarch64(prog, out);
#endif
#ifdef BACKEND_RISCV64
  else if (strcmp(opt_march, "riscv64") == 0)
    codegen_riscv64(prog, out);
#endif
#ifdef BACKEND_IRRE
  else if (strcmp(opt_march, "irre") == 0)
    codegen_irre(prog, out);
#endif
  else
    error("backend_codegen: unknown arch: %s", opt_march);
}

/** backend_align_to wrapper that selects backend by arch */
int backend_align_to(int n, int align) {
  if (!opt_march || strcmp(opt_march, "help") == 0) {
    printf("Specify -march <arch> to select a target architecture.\n");
    exit(2);
  }
#ifdef BACKEND_X86_64
  else if (strcmp(opt_march, "x86_64") == 0)
    return align_to_x86_64(n, align);
#endif
#ifdef BACKEND_AARCH64
  else if (strcmp(opt_march, "aarch64") == 0)
    return align_to_aarch64(n, align);
#endif
#ifdef BACKEND_RISCV64
  else if (strcmp(opt_march, "riscv64") == 0)
    return align_to_riscv64(n, align);
#endif
#ifdef BACKEND_IRRE
  else if (strcmp(opt_march, "irre") == 0)
    return align_to_irre(n, align);
#endif
  else
    error("backend_align_to: unknown arch: %s", opt_march);
}

/** get the pointer size for the current arch */
int backend_ptr_size(void) {
  if (!opt_march || strcmp(opt_march, "help") == 0) {
    printf("Specify -march <arch> to select a target architecture.\n");
    exit(2);
  }
#ifdef BACKEND_X86_64
  else if (strcmp(opt_march, "x86_64") == 0)
    return ptr_size_x86_64;
#endif
#ifdef BACKEND_AARCH64
  else if (strcmp(opt_march, "aarch64") == 0)
    return ptr_size_aarch64;
#endif
#ifdef BACKEND_RISCV64
  else if (strcmp(opt_march, "riscv64") == 0)
    return ptr_size_riscv64;
#endif
#ifdef BACKEND_IRRE
  else if (strcmp(opt_march, "irre") == 0)
    return ptr_size_irre;
#endif
  else
    error("backend_ptr_size: unknown arch: %s", opt_march);
}
