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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItProof.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefZApi.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateInit1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateInit_run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflate_runA.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeA1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateSafeS1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateSafeS2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma inf_loop_aty : forall flush w, ATY (w_s w) ->
  let '(stop, w') := inf_loop ivar_ref flush w in ATY (w_s w').
Proof.
  intros flush w HA. unfold inf_loop.
  apply (iterZ_ind2 (fun w0 => ATY (w_s w0)) (fun p : istop * iw => let '(stop, w') := p in ATY (w_s w')));
    [| intros a Ha; exact Ha | exact HA].
  intros a Ha. pose proof (dispatch_aty ivar_ref flush a Ha) as D. unfold ATYr, wof in D.
  destruct (dispatch ivar_ref flush a); exact D.
Qed.

Ltac csplit := lazymatch goal with |- _ /\ _ => split; csplit | _ => idtac end.

Lemma updw_core_arrs : forall s src end_ copy,
  let s' := updw_core s src end_ copy in
  is_lens s' = is_lens s /\ is_work s' = is_work s /\ is_codes s' = is_codes s.
Proof.
  intros s src end_ copy. cbv zeta. unfold updw_core, sA.
  destruct (is_wsize s =? 0); sacc;
  match goal with |- context [if ?c then _ else _] => destruct c end; sacc; try (csplit; reflexivity);
  match goal with |- context [if ?c then _ else _] => destruct c end; sacc; try (csplit; reflexivity);
  match goal with |- context [if ?c then _ else _] => destruct c end; sacc; try (csplit; reflexivity);
  match goal with |- context [if ?c then _ else _] => destruct c end; sacc; try (csplit; reflexivity).
Qed.

Lemma updw_core_aty : forall s src end_ copy, ATY s -> ATY (updw_core s src end_ copy).
Proof.
  intros s src end_ copy HA. destruct (updw_core_arrs s src end_ copy) as (E1 & E2 & E3).
  exact (ATY_same s _ HA E1 E2 E3).
Qed.

Lemma uw_pure_aty : forall s src end_ copy ch s', ATY s -> uw_pure s src end_ copy ch = Some s' -> ATY s'.
Proof.
  intros s src end_ copy ch s' HA E. unfold uw_pure in E.
  destruct (is_window_blk s) as [b|].
  - injection E; intros <-. apply updw_core_aty. exact HA.
  - destruct ch as [[b g]|]; [|discriminate E]. injection E; intros <-. apply updw_core_aty.
    apply (ATY_same s _ HA); reflexivity.
Qed.

Lemma lv_fin_aty : forall flush s c r, ATY s -> ATY (fst (lv_fin flush s c r)).
Proof.
  intros flush s c r HA. unfold lv_fin. cbv zeta.
  destruct (negb _ && negb _); cbn [fst]; apply (ATY_same s _ HA); reflexivity.
Qed.

Lemma inf_leave_aty : forall flush s c r ch s' zr ch',
  ATY s -> inf_leave hooks_pure flush (mkW s c r) ch = MRet ((s', zr), ch') -> ATY s'.
Proof.
  intros flush s c r ch s' zr ch' HA E.
  rewrite (inf_leave_eq hooks_pure) in E. unfold sbind in E.
  assert (HAR : ATY (s_rest s r)) by (apply (ATY_same s _ HA); reflexivity).
  destruct (lv_cond flush (s_rest s r) (c_rest c r) r).
  - rewrite updatewindow_pure in E. cbn [mbind fst snd] in E.
    destruct (uw_pure (s_rest s r) (ic_outbuf (c_rest c r)) (ic_next_out (c_rest c r)) (wrap32 (ir_out r - ic_avail_out (c_rest c r))) ch) as [s2|] eqn:EU.
    + unfold sret in E. apply (f_equal (fun mm => match mm with MRet p => fst (fst p) | _ => s' end)) in E. cbn [fst] in E.
      rewrite <- E. apply lv_fin_aty. exact (uw_pure_aty _ _ _ _ _ _ HAR EU).
    + unfold sret in E. apply (f_equal (fun mm => match mm with MRet p => fst (fst p) | _ => s' end)) in E. cbn [fst] in E.
      rewrite <- E. unfold lv_mem. cbn [fst]. rewrite lv_pre_shape. cbv zeta. cbn [fst].
      destruct (negb _ && negb _); apply (ATY_same s _ HA); reflexivity.
  - unfold sret in E. cbn [mbind fst snd] in E.
    apply (f_equal (fun mm => match mm with MRet p => fst (fst p) | _ => s' end)) in E. cbn [fst] in E.
    rewrite <- E. apply lv_fin_aty. exact HAR.
Qed.

Lemma W0_aty : forall st zc, ATY st -> ATY (w_s (W0 st zc)).
Proof.
  intros st zc HA. unfold W0, s_entry. cbn [w_s]. destruct (is_mode st =? TYPE); [apply (ATY_same st _ HA); reflexivity | exact HA].
Qed.

Theorem inflate_aty : forall s zc flush ch s' zr,
  INV s -> ATY s -> ipure (inflate_m ivar_ref hooks_pure s zc flush) ch = Some (s', zr) -> ATY s'.
Proof.
  intros s zc flush ch s' zr HI HA E.
  unfold ipure in E. rewrite (inflate_m_W0 hooks_pure) in E by (apply INV_check; exact HI).
  pose proof (inf_loop_aty flush (W0 s zc) (W0_aty s zc HA)) as L.
  destruct (inf_loop ivar_ref flush (W0 s zc)) as [stop w'].
  destruct stop as [|rc].
  - destruct w' as [s1 c1 r1]. cbn [w_s] in L.
    destruct (inf_leave hooks_pure flush (mkW s1 c1 r1) ch) as [p| | |] eqn:EL; try discriminate E.
    destruct p as [[s2 zr2] ch']. cbn [fst] in E.
    assert (E2 : s2 = s') by (injection E; intros _ X; exact X). subst s2.
    exact (inf_leave_aty flush s1 c1 r1 ch s' zr2 ch' L EL).
  - unfold sret in E. cbn [fst] in E.
    assert (E2 : w_s w' = s') by (injection E; intros _ X; exact X). rewrite <- E2. exact L.
Qed.

Section Checker2.
  Variable flush : Z.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK : forall w, WINV w -> ATY (w_s w) -> arm_ok flush w = true.

End Checker2.

