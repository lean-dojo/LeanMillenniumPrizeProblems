// Lean compiler output
// Module: Problems.Poincare.Millennium
// Imports: Init Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected Mathlib.Geometry.Manifold.Instances.Sphere Mathlib.Topology.Homotopy.Equiv Mathlib.Geometry.Manifold.PoincareConjecture Mathlib.Algebra.Homology.Homotopy Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_AlgebraicTopology_FundamentalGroupoid_SimplyConnected(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Geometry_Manifold_Instances_Sphere(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Homotopy_Equiv(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Geometry_Manifold_PoincareConjecture(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Homology_Homotopy(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_AlgebraicTopology_FundamentalGroupoid_FundamentalGroup(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_AlgebraicTopology_FundamentalGroupoid_SimplyConnected(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Problems_Poincare_Millennium(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_AlgebraicTopology_FundamentalGroupoid_SimplyConnected(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Geometry_Manifold_Instances_Sphere(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Homotopy_Equiv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Geometry_Manifold_PoincareConjecture(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Homology_Homotopy(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_AlgebraicTopology_FundamentalGroupoid_FundamentalGroup(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_AlgebraicTopology_FundamentalGroupoid_SimplyConnected(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
