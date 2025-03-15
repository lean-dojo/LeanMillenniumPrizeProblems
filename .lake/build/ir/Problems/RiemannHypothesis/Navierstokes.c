// Lean compiler output
// Module: Problems.RiemannHypothesis.Navierstokes
// Imports: Init Problems.RiemannHypothesis.Imports Problems.RiemannHypothesis.Sobolev Problems.RiemannHypothesis.Definitions
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
LEAN_EXPORT lean_object* l_NavierStokes_getSpace___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NavierStokes_getTime___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NavierStokes_getSpace___boxed(lean_object*);
LEAN_EXPORT lean_object* l_NavierStokes_pairToEuc(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NavierStokes_getSpace___rarg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NavierStokes_getSpace(lean_object*);
LEAN_EXPORT lean_object* l_NavierStokes_getTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NavierStokes_pairToEuc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NavierStokes_pairToEuc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_1, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_mod(x_7, x_6);
lean_dec(x_6);
x_9 = lean_nat_dec_eq(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_nat_sub(x_4, x_5);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_NavierStokes_pairToEuc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_NavierStokes_pairToEuc(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_NavierStokes_getTime(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_1, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_mod(x_5, x_4);
lean_dec(x_4);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_NavierStokes_getTime___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_NavierStokes_getTime(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_NavierStokes_getSpace___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_NavierStokes_getSpace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_NavierStokes_getSpace___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_NavierStokes_getSpace___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_NavierStokes_getSpace___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_NavierStokes_getSpace___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_NavierStokes_getSpace(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Problems_RiemannHypothesis_Imports(uint8_t builtin, lean_object*);
lean_object* initialize_Problems_RiemannHypothesis_Sobolev(uint8_t builtin, lean_object*);
lean_object* initialize_Problems_RiemannHypothesis_Definitions(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Problems_RiemannHypothesis_Navierstokes(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Problems_RiemannHypothesis_Imports(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Problems_RiemannHypothesis_Sobolev(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Problems_RiemannHypothesis_Definitions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
