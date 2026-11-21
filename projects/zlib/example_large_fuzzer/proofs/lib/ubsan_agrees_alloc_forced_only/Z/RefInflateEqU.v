(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Uncompr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ModelRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateCongr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefZApi.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflate_runA.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateInit1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateInit_run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeS1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeS2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateEqD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateEqA1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateEqA2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateEqT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateEqF.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateEqS.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateEqB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ICALL (s1 s2 : inflate_state) : Prop := IEQ s1 s2 /\ UWS s1 /\ INV s1 /\ INV s2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TwoHooks.
  Context {St : Type}.
  Variable H1 : zhooks St.
Variable H2 : zhooks St.
  Hypothesis HZ : forall a b, srel (fun r1 r2 => option_map fst r1 = option_map fst r2) (zalloc H1 a b) (zalloc H2 a b).
  Hypothesis HF : forall b, srel eq (zfree H1 b) (zfree H2 b).

  Lemma IEQ_init : forall g1 g2 b, IEQ (ireset_s (s_pre g1 b DEF_WBITS)) (ireset_s (s_pre g2 b DEF_WBITS)).
  Proof.
    intros g1 g2 b. unfold ireset_s, s_pre, is_of_oracle. unfold IEQ; cbv zeta; sacc. live_red. cbn [tbl_eq].
    unfold iarr_u16_of, iarr_u32_of. rewrite !arr_len_init.
    repeat match goal with |- _ /\ _ => split end; first [reflexivity | (intros X; discriminate X) | (intros i Hi; exfalso; lia) | idtac].
  Qed.

  Lemma UWS_init : forall g1 b, UWS (ireset_s (s_pre g1 b DEF_WBITS)).
  Proof.
    intros g1 b. unfold UWS, ireset_s, s_pre. sacc. split; [reflexivity|]. split; [reflexivity|]. right. split; [reflexivity|left; reflexivity].
  Qed.

End TwoHooks.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Loop.

  Context {St : Type}.
  Variable H1 : zhooks St.
Variable H2 : zhooks St.
  Hypothesis HZ : forall a b, srel (fun r1 r2 => option_map fst r1 = option_map fst r2) (zalloc H1 a b) (zalloc H2 a b).
  Hypothesis HF : forall b, srel eq (zfree H1 b) (zfree H2 b).
  Variable L0 : Z.
Variable src : list Z.
  Hypothesis HL0 : 0 <= L0 < 2 ^ 64.
  Hypothesis Hsrc : bytes_ok src.

  (* [comment removed for export] *)
  Record U2I (x1 x2 : u2st) : Prop := {
    uq : IEQ (u2_s x1) (u2_s x2);
    uw : UWS (u2_s x1);
    ui1 : INV (u2_s x1);
    ui2 : INV (u2_s x2);
    uz : u2_z x2 = u2_z x1;
    ulen : u2_len x2 = u2_len x1;
    uleft : u2_left x2 = u2_left x1;
    upos : u2_in_pos x2 = u2_in_pos x1;
    uain : u2_avail_in x2 = u2_avail_in x1;
    uaout : u2_avail_out x2 = u2_avail_out x1;
    uout : u2_out_rev x2 = u2_out_rev x1;
    uerr : u2_err x2 = u2_err x1;
    uain0 : 0 <= u2_avail_in x1 < 2 ^ 32;
    uaout0 : 0 <= u2_avail_out x1 < 2 ^ 32;
    uleft0 : 0 <= u2_left x1;
    usum : zlength (u2_out_rev x1) + u2_avail_out x1 + u2_left x1 = L0;
    utot : u2_err x1 = Z_OK \/ u2_err x1 = Z_STREAM_END -> zs_total_out (u2_z x1) = wrap64 (zlength (u2_out_rev x1)) }.

End Loop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ZcHooks.
  Context {MM : MallocModel}.
End ZcHooks.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Final.
End Final.

