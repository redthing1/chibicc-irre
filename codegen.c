#include "chibicc.h"
#include "codegen.h"

#define BACKEND_X86_64
#define BACKEND_RISCV64

#ifdef BACKEND_X86_64
void codegen_x86_64(Obj *prog, FILE *out);
int align_to_x86_64(int n, int align);
#endif
#ifdef BACKEND_AARCH64
void codegen_aarch64(Obj *prog, FILE *out);
int align_to_aarch64(int n, int align);
#endif
#ifdef BACKEND_RISCV64
void codegen_riscv64(Obj *prog, FILE *out);
int align_to_riscv64(int n, int align);
#endif

/** codegen wrapper that selects backend by arch */
void codegen(Obj *prog, FILE *out) {
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
  else
    error("codegen: unknown arch: %s", opt_march);
}

/** align_to wrapper that selects backend by arch */
int align_to(int n, int align) {
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
  else
    error("align_to: unknown arch: %s", opt_march);
}
