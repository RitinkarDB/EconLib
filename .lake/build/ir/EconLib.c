// Lean compiler output
// Module: EconLib
// Imports: public import Init public import EconLib.Foundations.Basic public import EconLib.Equilibrium.Basic public import EconLib.GameTheory.Basic public import EconLib.Choice.Basic public import EconLib.Examples.PrisonersDilemma public import EconLib.Examples.BattleOfTheSexes public import EconLib.Examples.MatchingPennies public import EconLib.Examples.StagHunt
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_EconLib_EconLib_Foundations_Basic(uint8_t builtin);
lean_object* initialize_EconLib_EconLib_Equilibrium_Basic(uint8_t builtin);
lean_object* initialize_EconLib_EconLib_GameTheory_Basic(uint8_t builtin);
lean_object* initialize_EconLib_EconLib_Choice_Basic(uint8_t builtin);
lean_object* initialize_EconLib_EconLib_Examples_PrisonersDilemma(uint8_t builtin);
lean_object* initialize_EconLib_EconLib_Examples_BattleOfTheSexes(uint8_t builtin);
lean_object* initialize_EconLib_EconLib_Examples_MatchingPennies(uint8_t builtin);
lean_object* initialize_EconLib_EconLib_Examples_StagHunt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_EconLib_EconLib(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_EconLib_EconLib_Foundations_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_EconLib_EconLib_Equilibrium_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_EconLib_EconLib_GameTheory_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_EconLib_EconLib_Choice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_EconLib_EconLib_Examples_PrisonersDilemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_EconLib_EconLib_Examples_BattleOfTheSexes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_EconLib_EconLib_Examples_MatchingPennies(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_EconLib_EconLib_Examples_StagHunt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
