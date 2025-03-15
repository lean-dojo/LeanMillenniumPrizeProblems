// Lean compiler output
// Module: Problems.RiemannHypothesis.Millennium
// Imports: Init Mathlib.NumberTheory.LSeries.RiemannZeta Mathlib.Data.Complex.Norm Mathlib.Algebra.IsPrimePow Mathlib.Analysis.Calculus.IteratedDeriv.Defs
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
LEAN_EXPORT lean_object* l_Millennium_CriticalStrip;
LEAN_EXPORT lean_object* l_Millennium_CriticalLine;
static lean_object* _init_l_Millennium_CriticalStrip() {
_start:
{
return lean_box(0);
}
}
static lean_object* _init_l_Millennium_CriticalLine() {
_start:
{
return lean_box(0);
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_NumberTheory_LSeries_RiemannZeta(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Complex_Norm(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_IsPrimePow(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Calculus_IteratedDeriv_Defs(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Problems_RiemannHypothesis_Millennium(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_NumberTheory_LSeries_RiemannZeta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Complex_Norm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_IsPrimePow(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Calculus_IteratedDeriv_Defs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Millennium_CriticalStrip = _init_l_Millennium_CriticalStrip();
l_Millennium_CriticalLine = _init_l_Millennium_CriticalLine();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
