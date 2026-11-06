(* fuzz_preset lib/B, the #102 re-walk of tx_put on image B' (asan-ubsan pin d663f82d7f488d30): THE FUNCTION'S
   THEOREM with the proved rows plugged in. TxPut102B_Top.tx_put_holds_B (the kit's
   ttx_put_specX, lib/A/PRH_FnTx.v (sha256 00de73011bd4; internal record)) at the rows of
   TxPut102B_S0.v (tp_seg_S0_ok), TxPut102B_END.v (tp_seg_END_ok),
   TxPut102B_FIT.v (tp_seg_FIT_ok; its one Section hypothesis AI, __asan_memcpy's text) and
   TxPut102B_GROW.v (tp_seg_GROW_ok): every row by its Qed lemma.
   rule 24: proves function tx_put (reuse search: the internal file REWALK-102-PLAN.md section T3)
   The remaining premises: AREAL / AREALN (the realloc wrapper's two texts), ARX_DEPOT (AR_laws_x's field 25), AI
   (__asan_memcpy's text),
   IMG : tp_img B and HHI : pa_hi <= 2 ^ 40 (the image-B instance: lib/B/PAImg_prog.v's PI_prog_B by vm_compute and
   the image binding of B, TxPut102B_Inst.v).
   PAImg-parametric. Numerals: none. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnTx CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PLB102 TxPut102B_Base TxPut102B_Top.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require TxPut102B_S0 TxPut102B_END TxPut102B_FIT TxPut102B_GROW.
Import ListNotations.
Local Open Scope Z_scope.

Section all. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
Context {PA : PAImg B_prog_listing}.
#[local] Instance TPA_PrhImg : PrhImg := prh_img_B.
#[local] Instance TPA_RL : PrhRoomLive := prh_room_live_a8.
#[local] Notation segs := (@pa_segs _ B_prog_listing PA).
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).
(* the image-B instance's facts *)
Hypothesis HHI : @pa_hi _ B_prog_listing PA <= 2 ^ 40.
Variable IMG : tp_img B.
(* the realloc wrapper's two texts (tp_AREAL: the cf layer's primed row with room and the memnorm keep, tp_AREALN: the
   null row with the keep, TxPut102B_Base.v) *)
Variable AREAL : tp_AREAL B.
Variable AREALN : tp_AREALN B.
(* ARX_DEPOT: AR_laws_x's field 25 at ARcfx (TxPut102B_Base.v's tp_ARX_DEPOT); TxPut102B_Inst.v projects it from the
   cf laws *)
Variable ARX_DEPOT : tp_ARX_DEPOT B.
(* __asan_memcpy's text at the listing's own entry (the FIT row's one Section hypothesis; a callee text of
   YGcallMxmn's intrinsic rules) *)
Variable AI : aintrin_realizes_xm segs B (ARcfx B) OCpy (@pa_sigma _ B_prog_listing PA AS___asan_memcpy).

(* WITNESS of tp_img's CfParams field tpi_head_wide at the preset's CfParams (cf_head = 16), by computation *)
Lemma tp_head_wide_preset : prh_head_wide.
Proof. unfold prh_head_wide. vm_compute. intros H. discriminate H. Qed.

(* the function's theorem at the rows: the kit's text with its run-length premise length rp_os <= 4 (threaded by the twin) *)
Theorem tx_put_holds_B_rows : ttx_put_specX B (ARcfx B) SK CTX0.
Proof.
exact (tx_put_holds_B B SK CTX0
  (fun P HL _ => TxPut102B_S0.tp_seg_S0_ok B SK CTX0 HHI P HL)
  AREAL AREALN ARX_DEPOT (TxPut102B_GROW.tp_seg_GROW_ok B SK CTX0) (TxPut102B_FIT.tp_seg_FIT_ok B SK CTX0 AI)
  (fun P HL _ => TxPut102B_END.tp_seg_END_ok B SK CTX0 P HL)
  IMG).
Qed.

End all.
Print Assumptions tx_put_holds_B_rows.
