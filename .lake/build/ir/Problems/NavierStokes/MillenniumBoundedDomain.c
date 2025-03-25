// Lean compiler output
// Module: Problems.NavierStokes.MillenniumBoundedDomain
// Imports: Init Problems.NavierStokes.Imports Problems.NavierStokes.Definitions Problems.NavierStokes.Navierstokes Problems.NavierStokes.MillenniumRDomain Problems.NavierStokes.Torus
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_MillenniumNS__BoundedDomain_SmoothPeriodicSolution_toSmoothSolution(lean_object*);
LEAN_EXPORT lean_object* l_MillenniumNS__BoundedDomain_SmoothPeriodicSolution_toSmoothSolution___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MillenniumNS__BoundedDomain_SmoothPeriodicSolution_toSmoothSolution___rarg(lean_object*);
LEAN_EXPORT lean_object* l_MillenniumNS__BoundedDomain_SmoothPeriodicSolution_toSmoothSolution___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MillenniumNS__BoundedDomain_SmoothPeriodicSolution_toSmoothSolution___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_MillenniumNS__BoundedDomain_SmoothPeriodicSolution_toSmoothSolution(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_MillenniumNS__BoundedDomain_SmoothPeriodicSolution_toSmoothSolution___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MillenniumNS__BoundedDomain_SmoothPeriodicSolution_toSmoothSolution___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MillenniumNS__BoundedDomain_SmoothPeriodicSolution_toSmoothSolution___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MillenniumNS__BoundedDomain_SmoothPeriodicSolution_toSmoothSolution___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MillenniumNS__BoundedDomain_SmoothPeriodicSolution_toSmoothSolution(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Problems_NavierStokes_Imports(uint8_t builtin, lean_object*);
lean_object* initialize_Problems_NavierStokes_Definitions(uint8_t builtin, lean_object*);
lean_object* initialize_Problems_NavierStokes_Navierstokes(uint8_t builtin, lean_object*);
lean_object* initialize_Problems_NavierStokes_MillenniumRDomain(uint8_t builtin, lean_object*);
lean_object* initialize_Problems_NavierStokes_Torus(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Problems_NavierStokes_MillenniumBoundedDomain(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Problems_NavierStokes_Imports(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Problems_NavierStokes_Definitions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Problems_NavierStokes_Navierstokes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Problems_NavierStokes_MillenniumRDomain(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Problems_NavierStokes_Torus(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
