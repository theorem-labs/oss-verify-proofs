(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzContracts BzContracts0 DecCut DecTac DecTac2 DecTacM DecAux DecAuxM S0_dec_U13.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_hbCreate.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_dec_U7B.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAuxM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_dec_U13 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_hbCreate.S0_hbCreateB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_dec_U7B.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU6 BzDUM BzDU7. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR DecTacFR2 S0F_decRet S0F_decCuts7.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU6 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU7 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts7.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecFast DecFastT.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacFR BzImg0Tac.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Lemma Forall2_of_nth : forall {A B} (P : A -> B -> Prop) (l1 : list A) (l2 : list B),
  length l1 = length l2 ->
  (forall i x y, nth_error l1 i = Some x -> nth_error l2 i = Some y -> P x y) ->
  Forall2 P l1 l2.
Proof.
  intros A B P l1. induction l1 as [|x l1 IH]; intros [|y l2] HL H; cbn in HL; try discriminate; [constructor|].
  constructor.
  - apply (H 0%nat); reflexivity.
  - apply IH; [lia|]. intros i a b Ha Hb. apply (H (S i)); assumption.
Qed.

Lemma nth_error_app3 : forall {A} (pre mid suf : list A) i,
  nth_error (pre ++ mid ++ suf) i =
  if (i <? length pre)%nat then nth_error pre i
  else if (i <? length pre + length mid)%nat then nth_error mid (i - length pre)
  else nth_error suf (i - length pre - length mid).
Proof.
  intros A pre mid suf i.
  destruct (Nat.ltb_spec i (length pre)).
  - rewrite nth_error_app1 by lia. reflexivity.
  - rewrite nth_error_app2 by lia. destruct (Nat.ltb_spec i (length pre + length mid)).
    + rewrite nth_error_app1 by lia. reflexivity.
    + rewrite nth_error_app2 by lia. f_equal; lia.
Qed.

Lemma sv32_mod32 : forall ws i, (bv_unsigned (wnth ws i) mod 4294967296 = sv32 ws i mod 4294967296)%Z.
Proof. intros ws i. unfold sv32. symmetry. change 4294967296%Z with (2^32)%Z. apply swrap32_mod32. Qed.

Lemma wnth_of_nth_error : forall ws i x, nth_error ws i = Some x -> wnth ws (Z.of_nat i) = x.
Proof. intros ws i x H. unfold wnth. rewrite Nat2Z.id. apply nth_error_nth. exact H. Qed.

Lemma splice_zw32 : forall (a a' : zarr) (n : Z) (k : nat) (row : list word) (f : Z -> Z),
  (Z.of_nat k + 258 <= n)%Z -> length row = 258%nat ->
  ag32s row f 258 ->
  (forall i, (0 <= i < 258)%Z -> (zget a' (Z.of_nat k + i) mod 4294967296 = f i mod 4294967296)%Z) ->
  (forall j, (0 <= j < n)%Z -> (j < Z.of_nat k \/ Z.of_nat k + 258 <= j)%Z -> zget a' j = zget a j) ->
  Forall2 (fun x y => le4 x = le4 y) (firstn k (zw32 a n) ++ row ++ skipn (k + 258) (zw32 a n)) (zw32 a' n).
Proof.
  intros a a' n k row f Hk Hrow AG ROW FR.
  assert (LF : length (firstn k (zw32 a n)) = k) by (rewrite firstn_length_le; [reflexivity| rewrite zw32_length_nat; lia]).
  assert (LS : length (skipn (k + 258) (zw32 a n)) = (Z.to_nat n - (k + 258))%nat) by (rewrite length_skipn, zw32_length_nat; reflexivity).
  apply Forall2_of_nth.
  { rewrite !length_app, LF, Hrow, LS, zw32_length_nat. lia. }
  intros i x y Hx Hy.
  assert (Hi : (i < Z.to_nat n)%nat).
  { rewrite <- (zw32_length_nat a' n). apply (proj1 (nth_error_Some _ _)). rewrite Hy. discriminate. }
  replace i with (Z.to_nat (Z.of_nat i)) in Hy by lia. rewrite zw32_nth in Hy by lia. injection Hy as <-.
  rewrite nth_error_app3 in Hx. rewrite LF, Hrow in Hx.
  destruct (Nat.ltb_spec i k).
  - rewrite nth_error_firstn' in Hx by lia. replace i with (Z.to_nat (Z.of_nat i)) in Hx by lia.
    rewrite zw32_nth in Hx by lia. injection Hx as <-. rewrite FR by lia. reflexivity.
  - destruct (Nat.ltb_spec i (k + 258)).
    + apply le4_lit_mod32. change (2^32)%Z with 4294967296%Z.
      replace (Z.of_nat i) with (Z.of_nat k + (Z.of_nat i - Z.of_nat k))%Z by lia.
      rewrite ROW by lia. rewrite <- (AG (Z.of_nat i - Z.of_nat k)%Z) by lia.
      rewrite <- sv32_mod32. rewrite <- (wnth_of_nth_error row (i - k) x Hx). f_equal. f_equal. f_equal. lia.
    + replace (i - k - 258)%nat with (i - (k + 258))%nat in Hx by lia.
      rewrite <- (nth_error_skipn _ (k + 258) (i - (k + 258))) in Hx || rewrite nth_error_skipn in Hx.
      replace (k + 258 + (i - (k + 258)))%nat with i in Hx by lia.
      replace i with (Z.to_nat (Z.of_nat i)) in Hx by lia.
      rewrite zw32_nth in Hx by lia. injection Hx as <-. rewrite FR by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma uv8_zb8 : forall a n i, (0 <= i < n)%Z -> (0 <= zget a i < 256)%Z -> uv8 (zb8 a n) i = zget a i.
Proof.
  intros a n i Hi Hv. unfold uv8. rewrite (nth_error_nth _ _ _ (zb8_nth a n i Hi)). apply unsigned_lit8. exact Hv.
Qed.
(* [comment removed for export] *)
Lemma sv32_zw32_window : forall a n (k : nat) i, (0 <= i < 258)%Z -> (Z.of_nat k + 258 <= n)%Z ->
  (sv32 (firstn 258 (skipn k (zw32 a n))) i mod 4294967296 = zget a (Z.of_nat k + i) mod 4294967296)%Z.
Proof.
  intros a n k i Hi Hk. rewrite <- sv32_mod32.
  assert (NE : nth_error (firstn 258 (skipn k (zw32 a n))) (Z.to_nat i) = Some (Z_to_bv 64 (zget a (Z.of_nat k + i)))).
  { rewrite nth_error_firstn' by lia. rewrite nth_error_skipn.
    replace (k + Z.to_nat i)%nat with (Z.to_nat (Z.of_nat k + i)) by lia. apply zw32_nth. lia. }
  replace (wnth (firstn 258 (skipn k (zw32 a n))) i) with (Z_to_bv 64 (zget a (Z.of_nat k + i)))
    by (symmetry; rewrite <- (Z2Nat.id i) at 1 by lia; apply wnth_of_nth_error; exact NE).
  rewrite unsigned_lit_wrap. change (2 ^ 64)%Z with (4294967296 * 4294967296)%Z.
  rewrite Zaux.Zmod_mod_mult by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac zw32_store_done ARR i v :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?mm ?ga (le4 ?x)) _) =>
      lazymatch type of ARR with u32arr _ _ ?A (zw32 ?a ?n) =>
        let H := fresh "ARR" in
        pose proof (zw32_write segs mm A a n i x v ARR ltac:(lia)
                      ltac:(first [ reflexivity | rewrite unsigned_lit by lia; reflexivity | rewrite unsigned_lit_wrap, <- Znumtheory.Zmod_div_mod by lia; reflexivity ])) as H;
        let ga' := lazymatch ga with wa _ => ga | Z_to_bv 64 ?X => constr:(wa X) | _ => ga end in
        replace (wa (A + 4 * i)%Z) with ga' in H by (cbv delta [wa]; first [reflexivity | f_equal; lia | apply f_equal; lia]);
        clear ARR; store_done; rename H into ARR
      end
  end.

Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac prep DM MU :=
    unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU; open_dmemF DM; s2img.

  Lemma S0F_U7_C : forall t mn mx, S0F_cut_L7D A F t -> S0F_cut_L7C A F t mn mx.
  Proof.
    intros t mn mx HL7D. unfold S0F_cut_L7C. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof DI as DI'. cps_destruct DI' as (COM & Ht & Hmm & SCAN & TU).
    pose proof COM as COM'. destruct COM' as [SEL LALL]. pose proof SEL as SEL'. cps_destruct SEL' as ((AL & NBL) & NG & NSC & SOK).
    assert (Ha : (1 <= sv_alphaSize L <= 258)%Z) by (unfold alpha_ok in AL; lia).
    prep DM MU. kq_intro. rewrite K_L7C_D in KQ. (* [comment removed for export] *)
    pose proof (mt_rows_bridge d t (sv_alphaSize L) mn mx Ha ltac:(lia) Hmm SCAN) as BRG. cbv zeta in BRG.
    pose proof (mt_rows_fields t (sv_alphaSize L) d mn mx) as FL. cbv zeta in FL.
    set (d' := mt_rows t (sv_alphaSize L) d mn mx) in *.
    destruct (hbCreateDecodeTables (d_limit d) (d_base d) (d_perm d) (d_len d) (258 * t) mn mx (sv_alphaSize L)) as [[li ba] pe] eqn:HBD.
    cps_destruct FL as (El & Eb & Ep & Elen & Eml & Esel & Eniu & Ebs & Est & Era & Esb & Eop & Ebl).
    unfold r_of in DR. dr_open.
    (* [comment removed for export] *)
    set (i0 := Z.to_nat (258 * t)).
    assert (Hi0 : Z.of_nat i0 = (258 * t)%Z) by (subst i0; lia).
    lazymatch goal with H : u32arr _ _ (S + 45436)%Z ?l |- _ =>
      cps_destruct (u32arr_split3 s0segs m (S + 45436) l i0 258 ltac:(rewrite zw32_length_nat; lia) H) as (LIMa & LIMb & LIMc & LNLa & LNLb & LNLc & _); clear H end.
    lazymatch goal with H : u32arr _ _ (S + 51628)%Z ?l |- _ =>
      cps_destruct (u32arr_split3 s0segs m (S + 51628) l i0 258 ltac:(rewrite zw32_length_nat; lia) H) as (BASa & BASb & BASc & LNBa & LNBb & LNBc & _); clear H end.
    lazymatch goal with H : u32arr _ _ (S + 57820)%Z ?l |- _ =>
      cps_destruct (u32arr_split3 s0segs m (S + 57820) l i0 258 ltac:(rewrite zw32_length_nat; lia) H) as (PRMa & PRMb & PRMc & LNPa & LNPb & LNPc & _); clear H end.
    lazymatch goal with H : u8arr _ _ (S + 43888)%Z ?l |- _ =>
      destruct (u8arr_split3 s0segs m (S + 43888) l i0 258 ltac:(rewrite zb8_length_nat; lia) H) as (_ & LENb & _ & _ & LN8b & _ & _) end.
    remember (firstn 258 (skipn i0 (zw32 (d_limit d) 1548))) as lws eqn:Elws.
    remember (firstn 258 (skipn i0 (zw32 (d_base d) 1548))) as bws eqn:Ebws.
    remember (firstn 258 (skipn i0 (zw32 (d_perm d) 1548))) as pws eqn:Epws.
    remember (firstn 258 (skipn i0 (zb8 (d_len d) 1548))) as lbs eqn:Elbs.
    rewrite zw32_length_nat in LNLc, LNBc, LNPc.
    remember (firstn i0 (zw32 (d_limit d) 1548)) as preL eqn:EpreL. remember (skipn (i0 + 258) (zw32 (d_limit d) 1548)) as sufL eqn:EsufL.
    remember (firstn i0 (zw32 (d_base d) 1548)) as preB eqn:EpreB. remember (skipn (i0 + 258) (zw32 (d_base d) 1548)) as sufB eqn:EsufB.
    remember (firstn i0 (zw32 (d_perm d) 1548)) as preP eqn:EpreP. remember (skipn (i0 + 258) (zw32 (d_perm d) 1548)) as sufP eqn:EsufP.
    assert (ZLa : Z.of_nat (length preL) = (258 * t)%Z) by lia. assert (ZLc : Z.of_nat (length sufL) = (1548 - 258 - 258 * t)%Z) by lia.
    assert (ZBa : Z.of_nat (length preB) = (258 * t)%Z) by lia. assert (ZBc : Z.of_nat (length sufB) = (1548 - 258 - 258 * t)%Z) by lia.
    assert (ZPa : Z.of_nat (length preP) = (258 * t)%Z) by lia. assert (ZPc : Z.of_nat (length sufP) = (1548 - 258 - 258 * t)%Z) by lia.
    replace (S + 45436 + 4 * Z.of_nat i0)%Z with (S + 45436 + 1032 * t)%Z in LIMb by lia.
    replace (S + 51628 + 4 * Z.of_nat i0)%Z with (S + 51628 + 1032 * t)%Z in BASb by lia.
    replace (S + 57820 + 4 * Z.of_nat i0)%Z with (S + 57820 + 1032 * t)%Z in PRMb by lia.
    replace (S + 43888 + Z.of_nat i0)%Z with (S + 43888 + 258 * t)%Z in LENb by lia.
    replace (S + 45436 + 4 * Z.of_nat (i0 + 258))%Z with (S + 45436 + 1032 * t + 1032)%Z in LIMc by lia.
    replace (S + 51628 + 4 * Z.of_nat (i0 + 258))%Z with (S + 51628 + 1032 * t + 1032)%Z in BASc by lia.
    replace (S + 57820 + 4 * Z.of_nat (i0 + 258))%Z with (S + 57820 + 1032 * t + 1032)%Z in PRMc by lia.
    (* [comment removed for export] *)
    assert (Hlen : forall j, (0 <= j < sv_alphaSize L)%Z -> (mn <= uv8 lbs j <= mx)%Z).
    { intros j Hj. rewrite Elbs. rewrite uv8_window by lia. rewrite Hi0.
      rewrite uv8_zb8 by (first [lia | pose proof (LALL t j ltac:(lia) Hj); lia]). apply SCAN. exact Hj. }
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof (act_ok_al _ _ AOK) as ALG; unfold ctx_al in ALG.
    cps_destruct ALG as (ALG1 & ALG2 & ALG3 & ALG4 & _). apply Z.mod_divide in ALG1; [|lia]. apply Z.mod_divide in ALG2; [|lia]. apply Z.mod_divide in ALG3; [|lia]. apply Z.mod_divide in ALG4; [|lia].
    destruct ALG1 as [qa1 ALG1]. destruct ALG2 as [qa2 ALG2]. destruct ALG3 as [qa3 ALG3]. destruct ALG4 as [qa4 ALG4].
    hide_all_but_at [S + 45436 + 1032 * t; S + 51628 + 1032 * t; S + 57820 + 1032 * t; S + 43888 + 258 * t; S + 64012; usp + -336]%Z.
    pose proof (munch_refl ([(S + 45436 + 1032 * t, S + 45436 + 1032 * t + 1032); (S + 51628 + 1032 * t, S + 51628 + 1032 * t + 1032);
                             (S + 57820 + 1032 * t, S + 57820 + 1032 * t + 1032); (usp + -336 + -64, usp + -336)]
                            ++ [(S + 64012, S + 64036); (usp + -336, usp)])%Z m) as MUL.
    pose proof (wmono_refl s0segs m) as WML.
    (* [comment removed for export] *)
    wstepl. wstepl. notrap. wstepl. wstepl. wstepl. wstepl. notrap. wstepl. wstepl. notrap. wstepl. wstepl. notrap.
    wstepl. wstepl. notrap. do 16 wstepl.
    eapply evt_cut.
    { eapply (S0_hbCreate_specZ S t lws bws pws lbs mn mx (sv_alphaSize L) (a_lo A) (usp + -336)%Z);
        [ exact LIMb | exact LNLb | exact BASb | exact LNBb | exact PRMb | exact LNPb | exact LENb | exact LN8b
        | lia | lia | lia | exact ST | exact MI | lia | lia | exact Hlen
        | first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia]
        | first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia]
        | first [reflexivity | f_equal; lia] ]. }
    intros ms' PO. unfold S0_hbCreateZ_post in PO.
    cps_destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & lws' & bws' & pws'
                    & Ems & MUc & WMc & MIc & ARL' & LNl' & ARB' & LNb' & ARP' & LNp' & AR8' & ST' & AG).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 158332)) with (Z_to_bv 64 158332) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    lazymatch type of MUL with munch ?Wq _ _ =>
      pose proof (munch_weaken _ Wq m m' (sub_fp_app_l _ _) MUc) as MULn end.
    clear MUL. rename MULn into MUL. cbn [app] in MUL.
    lazymatch type of MU with munch ?W14 ?m0 _ =>
    lazymatch type of MUc with munch ?Wc _ _ =>
      assert (SUB14 : sub_fp Wc W14) by (lin_unbox LIN; clear - LIN Ht NG; sub_fp_solve);
      apply (munch_trans W14 m0 m m') in MU; [ | exact (munch_weaken Wc W14 m m' SUB14 MUc) ]; clear SUB14 end end.
    apply (wmono_trans s0segs _ m m') in WM; [ | exact WMc ].
    clear WML. pose proof WMc as WML.
    lazymatch type of MUc with munch ?Wc _ _ =>
      apply (rw_cells_transport s0segs Wc m m') in FR; [ | exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; lia ];
      lazymatch goal with H : u32arr s0segs m (S + 64012)%Z ?ws |- _ =>
        apply (u32arr_transport s0segs Wc m m') in H; [ | exact MUc | exact WMc | cbn [disjoint_from]; rewrite ?zw32_length_nat; lia ] end end.
    clear LIMb BASb PRMb LENb ST MI MUc WMc.
    (* [comment removed for export] *)
    do 8 wstepl. notrap. do 5 wstepl.
    lazymatch goal with H : u32arr _ ?mm (S + 64012)%Z ?ws |- _ =>
      pose proof (u32arr_store_ok s0segs mm (S + 64012) ws t _ H ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO;
      wstepl; zw32_store_done H t mn end.
    try clear SO.
    (* [comment removed for export] *)
    pose proof (hb_create_cong (zrow (d_limit d) (258 * t)) (sv32 lws) (zrow (d_base d) (258 * t)) (sv32 bws)
                  (zrow (d_perm d) (258 * t)) (sv32 pws) (zrow (d_len d) (258 * t)) (uv8 lbs) mn mx (sv_alphaSize L)) as CG.
    assert (CGl : cong32 (zrow (d_limit d) (258 * t)) (sv32 lws)).
    { intros i Hi. unfold zrow. rewrite Elws, sv32_zw32_window, Hi0 by lia. reflexivity. }
    assert (CGb : cong32 (zrow (d_base d) (258 * t)) (sv32 bws)).
    { intros i Hi. unfold zrow. rewrite Ebws, sv32_zw32_window, Hi0 by lia. reflexivity. }
    assert (CGp : cong32 (zrow (d_perm d) (258 * t)) (sv32 pws)).
    { intros i Hi. unfold zrow. rewrite Epws, sv32_zw32_window, Hi0 by lia. reflexivity. }
    assert (CGn : forall j, (0 <= j < sv_alphaSize L)%Z -> zrow (d_len d) (258 * t) j = uv8 lbs j).
    { intros j Hj. unfold zrow. rewrite Elbs, uv8_window, Hi0 by lia. symmetry. apply uv8_zb8; [lia|].
      pose proof (LALL t j ltac:(lia) Hj). lia. }
    specialize (CG CGl CGb CGp CGn ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros j Hj; unfold zrow; pose proof (LALL t j ltac:(lia) Hj); lia)).
    destruct (hb_create (zrow (d_limit d) (258 * t)) (zrow (d_base d) (258 * t)) (zrow (d_perm d) (258 * t))
                        (zrow (d_len d) (258 * t)) mn mx (sv_alphaSize L)) as [[lim bas] per] eqn:HCz.
    destruct (hb_create (sv32 lws) (sv32 bws) (sv32 pws) (uv8 lbs) mn mx (sv_alphaSize L)) as [[lim' bas'] per'] eqn:HCm.
    cps_destruct CG as (CG1 & CG2 & CG3). cps_destruct AG as (AG1 & AG2 & AG3). destruct BRG as [BROW BFRM].
    (* [comment removed for export] *)
    revive_all_fs MUL WML AOK ltac:(clear - AOK LIN Ht NG RNL ZLa ZLc ZBa ZBc ZPa ZPc).
    (* [comment removed for export] *)
    replace (S + 45436 + 1032 * t)%Z with (S + 45436 + 4 * Z.of_nat i0)%Z in ARL' by lia.
    replace (S + 45436 + 1032 * t + 1032)%Z with (S + 45436 + 4 * Z.of_nat (i0 + 258))%Z in LIMc by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mg _) => assert (DRlimN : u32arr s0segs mg (S + 45436) (zw32 (d_limit d') 1548)) end.
    { lazymatch type of ARL' with u32arr _ ?mm _ _ =>
      eapply (u32arr_ext4 s0segs mm (S + 45436) (preL ++ lws' ++ sufL));
        [ apply u32arr_join3; [ exact LIMa | rewrite LNLa; exact ARL' | rewrite LNLa, LNl'; exact LIMc ]
        | rewrite EpreL, EsufL; apply (splice_zw32 (d_limit d) (d_limit d') 1548 i0 lws' lim' ltac:(lia) LNl' AG1);
          [ intros i Hi; rewrite <- (CG1 i Hi), Hi0; cps_destruct (BROW i Hi) as (Q1 & _ & _); rewrite Q1; reflexivity
          | intros j Hj Hjk; cps_destruct (BFRM j ltac:(lia)) as (Q1 & _ & _); exact Q1 ] ] end. }
    clear LIMa ARL' LIMc.
    (* [comment removed for export] *)
    replace (S + 51628 + 1032 * t)%Z with (S + 51628 + 4 * Z.of_nat i0)%Z in ARB' by lia.
    replace (S + 51628 + 1032 * t + 1032)%Z with (S + 51628 + 4 * Z.of_nat (i0 + 258))%Z in BASc by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mg _) => assert (DRbasN : u32arr s0segs mg (S + 51628) (zw32 (d_base d') 1548)) end.
    { lazymatch type of ARB' with u32arr _ ?mm _ _ =>
      eapply (u32arr_ext4 s0segs mm (S + 51628) (preB ++ bws' ++ sufB));
        [ apply u32arr_join3; [ exact BASa | rewrite LNBa; exact ARB' | rewrite LNBa, LNb'; exact BASc ]
        | rewrite EpreB, EsufB; apply (splice_zw32 (d_base d) (d_base d') 1548 i0 bws' bas' ltac:(lia) LNb' AG2);
          [ intros i Hi; rewrite <- (CG2 i Hi), Hi0; cps_destruct (BROW i Hi) as (_ & Q2 & _); rewrite Q2; reflexivity
          | intros j Hj Hjk; cps_destruct (BFRM j ltac:(lia)) as (_ & Q2 & _); exact Q2 ] ] end. }
    clear BASa ARB' BASc.
    (* [comment removed for export] *)
    replace (S + 57820 + 1032 * t)%Z with (S + 57820 + 4 * Z.of_nat i0)%Z in ARP' by lia.
    replace (S + 57820 + 1032 * t + 1032)%Z with (S + 57820 + 4 * Z.of_nat (i0 + 258))%Z in PRMc by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mg _) => assert (DRprmN : u32arr s0segs mg (S + 57820) (zw32 (d_perm d') 1548)) end.
    { lazymatch type of ARP' with u32arr _ ?mm _ _ =>
      eapply (u32arr_ext4 s0segs mm (S + 57820) (preP ++ pws' ++ sufP));
        [ apply u32arr_join3; [ exact PRMa | rewrite LNPa; exact ARP' | rewrite LNPa, LNp'; exact PRMc ]
        | rewrite EpreP, EsufP; apply (splice_zw32 (d_perm d) (d_perm d') 1548 i0 pws' per' ltac:(lia) LNp' AG3);
          [ intros i Hi; rewrite <- (CG3 i Hi), Hi0; cps_destruct (BROW i Hi) as (_ & _ & Q3); rewrite Q3; reflexivity
          | intros j Hj Hjk; cps_destruct (BFRM j ltac:(lia)) as (_ & _ & Q3); exact Q3 ] ] end. }
    clear PRMa ARP' PRMc AR8'.
    (* [comment removed for export] *)
    clear Elws Ebws Epws Elbs EpreL EsufL EpreB EsufB EpreP EsufP.
    (* [comment removed for export] *)
    rewrite El in DRlimN. rewrite Eb in DRbasN. rewrite Ep in DRprmN.
    match goal with KQ : kq _ _ |- _ =>
      replace (d_set_minLens d' (zset (d_minLens d) t mn))
        with (d_set_minLens (d_set_perm (d_set_base (d_set_limit d li) ba) pe) (zset (d_minLens d) t mn)) in KQ
        by (cbv delta [d']; unfold mt_rows; rewrite HBD; reflexivity) end.
    assert (BROW' : forall i, (0 <= i < 258)%Z ->
              zget li (258 * t + i) = lim i /\ zget ba (258 * t + i) = bas i /\ zget pe (258 * t + i) = per i).
    { rewrite <- El, <- Eb, <- Ep. exact BROW. }
    assert (BFRM' : forall k, (k < 258 * t \/ 258 * t + 258 <= k)%Z ->
              zget li k = zget (d_limit d) k /\ zget ba k = zget (d_base d) k /\ zget pe k = zget (d_perm d) k).
    { rewrite <- El, <- Eb, <- Ep. exact BFRM. }
    clear BROW BFRM. clearbody d'. clear dependent d'.
    kq_fold. enter_cutF (HL7D _ _ _ JK_) DP.
    (* [comment removed for export] *)
    split; [| lia]. unfold dinv_L7T, u7com. dmodel_cbn.
    split; [split; [exact SEL| exact LALL]|]. split; [lia|].
    intros t' Ht'. destruct (Z.eq_dec t' t) as [->|NE].
    - exists mn. apply (tab_okF_of_rows _ _ _ mn mx); [| dmodel_cbn; rewrite zget_zset, Z.eqb_refl; reflexivity].
      exists (zrow (d_len d) (258 * t)), (zrow (d_limit d) (258 * t)), (zrow (d_base d) (258 * t)), (zrow (d_perm d) (258 * t)).
      split; [exact Hmm|]. split; [intros j Hj; unfold zrow; apply SCAN; exact Hj|]. rewrite HCz. dmodel_cbn.
      split; [| split]; intros i Hi; cps_destruct (BROW' i Hi) as (Q1 & Q2 & Q3); [exact Q1 | exact Q2 | exact Q3].
    - destruct (TU t' ltac:(lia)) as [mn' G]. exists mn'.
      assert (RNG : forall i, (0 <= i < 258)%Z -> (258 * t' + i < 258 * t \/ 258 * t + 258 <= 258 * t' + i)%Z) by (intros; lia).
      apply (tab_okF_frame_pt d); [exact G | | | | dmodel_cbn; rewrite zget_zset; destruct (Z.eqb_spec t' t); [lia| reflexivity]];
        dmodel_cbn; intros i Hi; cps_destruct (BFRM' (258 * t' + i)%Z (RNG i Hi)) as (Q1 & Q2 & Q3); [exact Q1 | exact Q2 | exact Q3].
  Qed.
End R.
End ACeilS1.
