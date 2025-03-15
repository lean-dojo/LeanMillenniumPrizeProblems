// Lean compiler output
// Module: Problems.NavierStokes.Definitions
// Imports: Init Problems.NavierStokes.AdjointSpace Problems.NavierStokes.Imports
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
lean_object* l_Ring_toAddGroupWithOne___rarg(lean_object*);
LEAN_EXPORT lean_object* l_ContinuousLinearMap_proj___at_euc__proj___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ContinuousLinearMap_proj___at_euc__proj___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearMap_proj___at_euc__proj___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DerivIndices_order___boxed(lean_object*);
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___rarg(lean_object*);
LEAN_EXPORT lean_object* l_LinearMap_proj___at_euc__proj___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DerivIndices_order___rarg___boxed(lean_object*);
lean_object* l_NonUnitalNonAssocSemiring_toMulZeroClass___rarg(lean_object*);
LEAN_EXPORT lean_object* l_DerivIndices_zero___boxed(lean_object*);
LEAN_EXPORT lean_object* l_euc__proj___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_SeminormedCommRing_toNonUnitalSeminormedCommRing___rarg(lean_object*);
LEAN_EXPORT lean_object* l_RingHom_id___at_euc__proj___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearMap_proj___at_euc__proj___spec__3___rarg(lean_object*);
LEAN_EXPORT lean_object* l_ContinuousLinearMap_proj___at_euc__proj___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_standardBasis___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DerivIndices_order___rarg(lean_object*);
lean_object* l_Function_eval___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ContinuousLinearMap_proj___at_euc__proj___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_standardBasis___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_euc__proj(lean_object*);
static lean_object* l_RingHom_id___at_euc__proj___spec__2___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_euc__proj___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DerivIndices_order(lean_object*);
LEAN_EXPORT lean_object* l_standardBasis(lean_object*);
lean_object* l_NormedCommRing_toSeminormedCommRing___rarg(lean_object*);
LEAN_EXPORT lean_object* l_RingHom_id___at_euc__proj___spec__4(lean_object*, lean_object*);
lean_object* l_NormedField_toNormedCommRing___rarg(lean_object*);
LEAN_EXPORT lean_object* l_RingHom_id___at_euc__proj___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DerivIndices_zero(lean_object*);
LEAN_EXPORT lean_object* l_RingHom_id___at_euc__proj___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_standardBasis___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = l_NormedField_toNormedCommRing___rarg(x_1);
x_7 = l_NormedCommRing_toSeminormedCommRing___rarg(x_6);
x_8 = l_SeminormedCommRing_toNonUnitalSeminormedCommRing___rarg(x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___rarg(x_9);
x_11 = l_NonUnitalNonAssocSemiring_toMulZeroClass___rarg(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = l_NormedField_toNormedCommRing___rarg(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Ring_toAddGroupWithOne___rarg(x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
lean_dec(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_standardBasis(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_standardBasis___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_standardBasis___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_standardBasis___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_RingHom_id___at_euc__proj___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_RingHom_id___at_euc__proj___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RingHom_id___at_euc__proj___spec__2___closed__1;
return x_3;
}
}
LEAN_EXPORT lean_object* l_RingHom_id___at_euc__proj___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RingHom_id___at_euc__proj___spec__2___closed__1;
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearMap_proj___at_euc__proj___spec__3___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Function_eval___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LinearMap_proj___at_euc__proj___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_LinearMap_proj___at_euc__proj___spec__3___rarg), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ContinuousLinearMap_proj___at_euc__proj___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Function_eval___rarg), 2, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ContinuousLinearMap_proj___at_euc__proj___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ContinuousLinearMap_proj___at_euc__proj___spec__1___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_euc__proj___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Function_eval___rarg), 2, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_euc__proj(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_euc__proj___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_RingHom_id___at_euc__proj___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RingHom_id___at_euc__proj___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_RingHom_id___at_euc__proj___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RingHom_id___at_euc__proj___spec__4(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearMap_proj___at_euc__proj___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_LinearMap_proj___at_euc__proj___spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ContinuousLinearMap_proj___at_euc__proj___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ContinuousLinearMap_proj___at_euc__proj___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ContinuousLinearMap_proj___at_euc__proj___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ContinuousLinearMap_proj___at_euc__proj___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_euc__proj___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_euc__proj___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_DerivIndices_zero(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_DerivIndices_zero___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_DerivIndices_zero(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_DerivIndices_order___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_List_lengthTRAux___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_DerivIndices_order(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_DerivIndices_order___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_DerivIndices_order___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_DerivIndices_order___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_DerivIndices_order___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_DerivIndices_order(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Problems_NavierStokes_AdjointSpace(uint8_t builtin, lean_object*);
lean_object* initialize_Problems_NavierStokes_Imports(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Problems_NavierStokes_Definitions(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Problems_NavierStokes_AdjointSpace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Problems_NavierStokes_Imports(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_RingHom_id___at_euc__proj___spec__2___closed__1 = _init_l_RingHom_id___at_euc__proj___spec__2___closed__1();
lean_mark_persistent(l_RingHom_id___at_euc__proj___spec__2___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
