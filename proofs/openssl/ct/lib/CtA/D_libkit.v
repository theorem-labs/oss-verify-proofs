(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Canon Stdio.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import SegRw.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_iface D_defs D_kit D_libiface D_clx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma view_c1 : forall (m : mem) a b, seg_rw_ok ctasegs a 1 = true -> mrd ctasegs m (wa a) = Some b -> rw_cells ctasegs m a [C1 b].
Proof.
  intros m a b H E. destruct (seg_rw_ok_sound ctasegs a 1 H m) as [W (S1 & S2 & _)].
  split; [split; [cbn; tauto|]| exact W].
  cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. assert (i = 0%nat) by lia. subst i. rewrite Z.add_0_r. exact E.
Qed.

Lemma in_ranges_intro : forall (W : list (Z * Z)) lo hi x, In (lo, hi) W -> lo <= x < hi -> in_ranges W x.
Proof. intros W lo hi x H1 H2. exists lo, hi. split; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma seg_rw_base_inited : seg_rw_ok ctasegs OSSL_BASE_INITED 1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma seg_rw_do_cleanup : seg_rw_ok ctasegs OSSL_DO_GLOBAL_CLEANUP 1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma rom_do_cleanup : seg_rom ctasegs (wa OSSL_DO_GLOBAL_CLEANUP) = Some (Z_to_bv 8 0). Proof. vm_compute. reflexivity. Qed.

Lemma lib_exit_loc : fp_local LIB_FP lib_exit_cells.
Proof.
  intros m m' (b0 & C1 & C2) AG. exists b0.
  split; [apply (rw_cells_agree_nw ctasegs m m' _ _ C1)| apply (rw_cells_agree_nw ctasegs m m' _ _ C2)];
    intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply AG; apply (in_ranges_intro LIB_FP 0xba46c0 0xba8ae0);
    try (unfold LIB_FP; cbn; tauto); unfold OSSL_BASE_INITED, OSSL_DO_GLOBAL_CLEANUP in Ha; lia.
Qed.

(* [comment removed for export] *)
Lemma lib_startA_exit : forall m, lib_startA m -> lib_exit_cells m.
Proof.
  intros m ((V & _) & _).
  destruct (seg_rw_c1 ctasegs m OSSL_BASE_INITED seg_rw_base_inited) as (b0 & C0). exists b0. split; [exact C0|].
  apply view_c1; [exact seg_rw_do_cleanup|]. rewrite V; [exact rom_do_cleanup|].
  apply (in_ranges_intro LIB_PRISTINE 0xba46c0 0xba4fa0); [unfold LIB_PRISTINE; cbn; tauto| unfold OSSL_DO_GLOBAL_CLEANUP; lia].
Qed.

Lemma lib_startA_loc : fp_local LIB_FP lib_startA.
Proof.
  intros m m' ((V & K) & L) AG.
  assert (SUB : forall x, in_ranges LIB_PRISTINE x -> in_ranges LIB_FP x).
  { intros x (lo & hi & Hin & Hx). unfold LIB_PRISTINE in Hin. unfold LIB_FP.
    destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-.
    - apply (in_ranges_intro _ 0x5aebe0 0x5af400); [cbn; tauto| lia].
    - apply (in_ranges_intro _ 0xba46c0 0xba8ae0); [cbn; tauto| lia].
    - apply (in_ranges_intro _ 0xba9390 0xba9398); [cbn; tauto| lia].
    - apply (in_ranges_intro _ 0xbca358 0xbca798); [cbn; tauto| lia].
    - apply (in_ranges_intro _ 0xbca7a0 0xbcab98); [cbn; tauto| lia]. }
  split; [split|].
  - intros a Ha. unfold mrd. rewrite (AG (wa a)).
    + exact (V a Ha).
    + destruct Ha as (lo & hi & Hin & Hx). rewrite wa_unsigned.
      * apply SUB. exists lo, hi. split; assumption.
      * unfold LIB_PRISTINE in Hin. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia.
  - apply (rw_cells_agree_nw ctasegs m m' _ _ K). intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply AG.
    apply (in_ranges_intro LIB_FP 0xbca358 0xbca798); [unfold LIB_FP; cbn; tauto| lia].
  - apply (rw_cells_agree_nw ctasegs m m' _ _ L). intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply AG.
    apply (in_ranges_intro LIB_FP 0xba4690 0xba4691); [unfold LIB_FP; cbn; tauto| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma seg_rw_errno : seg_rw_ok ctasegs ERRNO_A 4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma errno_exists : forall m : mem, exists v, rw_cells ctasegs m ERRNO_A [C4 v].
Proof. intros m. exact (seg_rw_c4 ctasegs m ERRNO_A seg_rw_errno). Qed.

Lemma rt_pres_fp_weaken : forall live frames sp (W W' : list (Z * Z)) m m',
  (forall x, outside W' x -> outside W x) -> rt_pres_fp live frames sp W m m' -> rt_pres_fp live frames sp W' m m'.
Proof. intros live frames sp W W' m m' HW P a Ha Ho. exact (P a Ha (HW _ Ho)). Qed.

(* [comment removed for export] *)
Lemma LIBW_HXA_sub : forall x, outside LIB_FPE x -> outside LIBW_HXA x.
Proof.
  intros x H. unfold LIB_FPE, LIB_FP in H. cbn [outside] in H. unfold LIBW_HXA. cbn [outside]. repeat split; try exact I; lia.
Qed.

Lemma LIB_FP_sub_E : forall x, outside LIB_FPE x -> outside LIB_FP x.
Proof. intros x H. unfold LIB_FPE in H. cbn [outside] in H. exact (proj2 H). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CLXE.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variables LIB LIB' : mem -> Prop.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

(* [comment removed for export] *)
Lemma CLX_libE : forall so m m' live frames sp, CLX OUT_rep ERR_rep XENV LIB so m -> rt_pres_fp live frames sp LIB_FPE m m' ->
  LIB' m' -> CLX OUT_rep ERR_rep XENV LIB' so m'.
Proof using OUT_loc ERR_loc XENV_loc IO_img XENV_img.
  intros so m m' live frames sp (H1 & H2 & H3 & H4 & (g & SG) & (v & ER) & RS & (l & LT) & CC) PR L'.
  assert (NE : forall x, ERRNO_A <= x < ERRNO_A + 4 -> drv_cell x) by (intros x Hx; left; exact Hx).
  assert (AG : agree_on (fun x => in_ranges IO_FP x \/ in_ranges XENV_FP x \/ (drv_cell x /\ ~ (ERRNO_A <= x < ERRNO_A + 4))) m m').
  { apply (agree_of_pres_fp _ _ _ _ _ _ _ PR). intros x Hx.
    assert (HE : forall y, ~ (ERRNO_A <= y < ERRNO_A + 4) -> outside LIB_FP y -> outside LIB_FPE y).
    { intros y Hy Ho. unfold LIB_FPE. cbn [outside]. split; [unfold ERRNO_A, TP_A in Hy; lia| exact Ho]. }
    destruct Hx as [Hx|[Hx|[Hx Hne]]].
    - split; [right; left; exact (proj1 (IO_img x Hx))|]. apply HE; [| exact (proj2 (proj2 (IO_img x Hx)))].
      intros Hn. exact (proj1 (proj2 (IO_img x Hx)) (NE x Hn)).
    - split; [right; left; exact (proj1 (XENV_img x Hx))|]. apply HE; [| exact (proj2 (proj2 (proj2 (XENV_img x Hx))))].
      intros Hn. exact (proj1 (proj2 (XENV_img x Hx)) (NE x Hn)).
    - split; [right; left; exact (drv_cell_static x Hx)|]. apply HE; [exact Hne| exact (drv_cell_not_lib x Hx)]. }
  split; [apply (OUT_loc so m m' H1); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; left; exact Hx]|].
  split; [apply (ERR_loc m m' H2); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; left; exact Hx]|].
  split; [apply (XENV_loc m m' H3); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; right; left; exact Hx]|].
  split; [exact L'|].
  assert (AGD : forall lo n, (forall x, lo <= x < lo + n -> drv_cell x /\ ~ (ERRNO_A <= x < ERRNO_A + 4)) -> agree_on (fun x => lo <= x < lo + n) m m').
  { intros lo n Hd. eapply agree_sub; [exact AG|]. intros x Hx. right; right. exact (Hd x Hx). }
  unfold drv_cell in AGD. unfold ERRNO_A, TP_A, SSP_GUARD, g_read_stage in AGD.
  split; [exists g; apply (ro_cells_agree ctasegs m m' _ _ SG); apply AGD; cbn; unfold SSP_GUARD; lia|].
  split; [exact (errno_exists m')|].
  split; [apply (stk_agree_nw ctasegs m m' _ _ RS); eapply agree_sub; [apply (AGD g_read_stage 65536); unfold g_read_stage; lia| cbv beta; lia]|].
  split; [exact (latch_exists m')|].
  unfold cancel_cells in *; apply (rw_cells_agree_nw ctasegs m m' _ _ CC); apply AGD; cbn; unfold ERRNO_A, TP_A, SSP_GUARD, g_read_stage; lia.
Qed.

(* [comment removed for export] *)
Lemma CLX_munch_lib : forall so m m' W, CLX OUT_rep ERR_rep XENV LIB so m -> munch W m m' ->
  (forall x, 0x10000 <= x < SEGTOP_A -> outside LIB_FP x -> outside W x) -> LIB' m' -> CLX OUT_rep ERR_rep XENV LIB' so m'.
Proof using OUT_loc ERR_loc XENV_loc IO_img XENV_img.
  intros so m m' W (H1 & H2 & H3 & H4 & (g & SG) & (v & ER) & RS & (l & LT) & CC) MU HW L'.
  assert (AG : agree_on (fun x => in_ranges IO_FP x \/ in_ranges XENV_FP x \/ drv_cell x) m m').
  { apply (agree_of_munch _ _ _ _ MU). intros x [Hx|[Hx|Hx]].
    - apply HW; [exact (client_static_range x (proj1 (IO_img x Hx)))| exact (proj2 (proj2 (IO_img x Hx)))].
    - apply HW; [exact (client_static_range x (proj1 (XENV_img x Hx)))| exact (proj2 (proj2 (proj2 (XENV_img x Hx))))].
    - apply HW; [exact (client_static_range x (drv_cell_static x Hx))| exact (drv_cell_not_lib x Hx)]. }
  split; [apply (OUT_loc so m m' H1); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; left; exact Hx]|].
  split; [apply (ERR_loc m m' H2); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; left; exact Hx]|].
  split; [apply (XENV_loc m m' H3); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; right; left; exact Hx]|].
  split; [exact L'|].
  assert (AGD : forall lo n, (forall x, lo <= x < lo + n -> drv_cell x) -> agree_on (fun x => lo <= x < lo + n) m m').
  { intros lo n Hd. eapply agree_sub; [exact AG|]. intros x Hx. right; right. exact (Hd x Hx). }
  unfold drv_cell in AGD.
  split; [exists g; apply (ro_cells_agree ctasegs m m' _ _ SG); apply AGD; cbn; lia|].
  split; [exact (errno_exists m')|].
  split; [apply (stk_agree_nw ctasegs m m' _ _ RS); eapply agree_sub; [apply (AGD g_read_stage 65536); lia| cbv beta; lia]|].
  split; [exact (latch_exists m')|].
  unfold cancel_cells in *; apply (rw_cells_agree_nw ctasegs m m' _ _ CC); apply AGD; cbn; unfold ERRNO_A, TP_A, SSP_GUARD, g_read_stage; lia.
Qed.

End CLXE.

(* [comment removed for export] *)
Lemma lib_pristineA_loc : fp_local LIB_FP lib_pristineA.
Proof.
  intros m m' P AG.
  assert (L0 : exists l, rw_cells ctasegs m 0xba4690 [C1 l]) by exact (latch_exists m).
  (* [comment removed for export] *)
  destruct P as (V & K). split.
  - intros a Ha. unfold mrd. rewrite (AG (wa a)); [exact (V a Ha)|].
    destruct Ha as (lo & hi & Hin & Hx).
    assert (R : 0 <= a < 2 ^ 64) by (unfold LIB_PRISTINE in Hin; destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia).
    rewrite wa_unsigned by exact R. unfold LIB_PRISTINE in Hin. unfold LIB_FP.
    destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-.
    + apply (in_ranges_intro _ 0x5aebe0 0x5af400); [cbn; tauto| lia].
    + apply (in_ranges_intro _ 0xba46c0 0xba8ae0); [cbn; tauto| lia].
    + apply (in_ranges_intro _ 0xba9390 0xba9398); [cbn; tauto| lia].
    + apply (in_ranges_intro _ 0xbca358 0xbca798); [cbn; tauto| lia].
    + apply (in_ranges_intro _ 0xbca7a0 0xbcab98); [cbn; tauto| lia].
  - apply (rw_cells_agree_nw ctasegs m m' _ _ K). intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply AG.
    apply (in_ranges_intro LIB_FP 0xbca358 0xbca798); [unfold LIB_FP; cbn; tauto| lia].
Qed.

(* [comment removed for export] *)
Lemma lib_pristineA_munch : forall (m m' : mem) W, lib_pristineA m -> munch W m m' ->
  (forall x, in_ranges LIB_FP x -> x <> TR_INIT -> outside W x) -> lib_pristineA m'.
Proof.
  intros m m' W P MU HW. destruct P as (V & K). split.
  - intros a Ha. unfold mrd. rewrite (MU (wa a)); [exact (V a Ha)|].
    destruct Ha as (lo & hi & Hin & Hx).
    assert (R : 0 <= a < 2 ^ 64 /\ a <> TR_INIT /\ in_ranges LIB_FP a).
    { unfold LIB_PRISTINE in Hin. unfold TR_INIT, LIB_FP.
      destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; (split; [lia|]; split; [lia|]).
      + apply (in_ranges_intro _ 0x5aebe0 0x5af400); [cbn; tauto| lia].
      + apply (in_ranges_intro _ 0xba46c0 0xba8ae0); [cbn; tauto| lia].
      + apply (in_ranges_intro _ 0xba9390 0xba9398); [cbn; tauto| lia].
      + apply (in_ranges_intro _ 0xbca358 0xbca798); [cbn; tauto| lia].
      + apply (in_ranges_intro _ 0xbca7a0 0xbcab98); [cbn; tauto| lia]. }
    destruct R as (R1 & R2 & R3). rewrite wa_unsigned by exact R1. exact (HW a R3 R2).
  - apply (rw_cells_agree_nw ctasegs m m' _ _ K). intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply MU.
    apply HW; [apply (in_ranges_intro LIB_FP 0xbca358 0xbca798); [unfold LIB_FP; cbn; tauto| lia]| unfold TR_INIT; lia].
Qed.
