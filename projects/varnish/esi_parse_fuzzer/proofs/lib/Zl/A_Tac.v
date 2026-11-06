(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpnnp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpya4 AIcp3q7 AIcpii0 AIcpinq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Img A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.

Module A_Frame.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge ZBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpnnp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Img A_Cocsh.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ro_C4_of_bytes : forall (m : mem) a (w : word), bytes_at rsegs m a (le4 w) -> ro_cells rsegs m a [C4 w].
Proof. intros m a w B. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B. Qed.

(* [comment removed for export] *)
Definition zcells (n : nat) : list cell := repeat (C1 (Z_to_bv 8 0)) n.

Lemma zcells_size : forall n, cells_size (zcells n) = n.
Proof. unfold zcells. induction n as [|n IH]; [reflexivity|]. cbn [repeat cells_size csize Nat.add]. rewrite IH. reflexivity. Qed.
Lemma zcells_wf : forall n, cells_wf (zcells n).
Proof. unfold zcells. induction n as [|n IH]; [exact I|]. cbn [repeat cells_wf cell_wf]. split; [exact I| exact IH]. Qed.
Lemma zcells_bytes : forall n, cells_bytes (zcells n) = repeat (Z_to_bv 8 0) n.
Proof. unfold zcells. induction n as [|n IH]; [reflexivity|]. cbn [repeat cells_bytes cbytes app]. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_align32 : forall x, 0 <= x -> x mod 16 = 0 ->
  exists d, (d = 0 \/ d = 16) /\ Z.land x (Z.lnot 31) = x - d /\ (x - d) mod 32 = 0.
Proof.
  intros x Hx H16.
  assert (E : Z.land x (Z.lnot 31) = x - x mod 32).
  { rewrite <- Z.ldiff_land. change 31 with (Z.ones 5). rewrite Z.ldiff_ones_r by lia.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
    pose proof (Z.div_mod x 32 ltac:(lia)). lia. }
  rewrite E. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as B.
  assert (C : x mod 32 = 0 \/ x mod 32 = 16).
  { pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
    rewrite H16, Z.add_0_r in D16.
    assert (M : (x mod 32) mod 16 = 0).
    { replace (x mod 32) with (x - 32 * (x / 32)) by lia. rewrite D16 at 1.
      replace (16 * (x / 16) - 32 * (x / 32)) with ((x / 16 - 2 * (x / 32)) * 16) by lia. apply Z_mod_mult. }
    pose proof (Z.div_mod (x mod 32) 16 ltac:(lia)) as D2. rewrite M, Z.add_0_r in D2.
    assert (Q : (x mod 32) / 16 = 0 \/ (x mod 32) / 16 = 1).
    { pose proof (Z.div_pos (x mod 32) 16 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (x mod 32) 16 2 ltac:(lia) ltac:(lia)). lia. }
    destruct Q as [Q|Q]; rewrite Q in D2; lia. }
  destruct C as [C|C]; rewrite C.
  - exists 0. split; [left; reflexivity|]. split; [reflexivity|].
    rewrite Z.sub_0_r. exact C.
  - exists 16. split; [right; reflexivity|]. split; [reflexivity|].
    pose proof (Z.div_mod x 32 ltac:(lia)) as D. rewrite C in D.
    replace (x - 16) with ((x / 32) * 32) by lia. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Lemma land_align32_w : forall x, 0 <= x < 2^64 -> x mod 16 = 0 ->
  exists d, (d = 0 \/ d = 16) /\ Z.land x 18446744073709551584 = x - d /\ (x - d) mod 32 = 0.
Proof.
  intros x Hx H16. destruct (land_align32 x ltac:(lia) H16) as (d & Hd & E & M).
  exists d. split; [exact Hd|]. split; [|exact M]. rewrite <- E.
  (* [comment removed for export] *)
  apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
  destruct (Z.ltb_spec n 64).
  - f_equal. change 18446744073709551584 with (Z.lor (Z.shiftl (Z.ones 59) 5) 0).
    rewrite Z.lor_0_r. rewrite Z.lnot_spec by lia. change 31 with (Z.ones 5).
    destruct (Z.ltb_spec n 5).
    + rewrite Z.shiftl_spec_low by lia. rewrite Z.ones_spec_low by lia. reflexivity.
    + rewrite Z.shiftl_spec_high by lia. rewrite Z.ones_spec_low by lia. rewrite Z.ones_spec_high by lia. reflexivity.
  - assert (TX : Z.testbit x n = false).
    { apply Z.testbit_false; [lia|]. rewrite Z.div_small; [reflexivity|]. split; [lia|].
      eapply Z.lt_le_trans; [apply (proj2 Hx)|]. apply Z.pow_le_mono_r; lia. }
    rewrite TX. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac fix_neg :=
  repeat match goal with
  | |- context [Z_to_bv 64 (Zneg ?p)] =>
      rewrite <- (ZBridge.Z_to_bv_mod64 (Zneg p));
      let e := eval vm_compute in ((Zneg p) mod 2^64)%Z in
      change (((Zneg p) mod 2^64)%Z) with e
  end.

(* [comment removed for export] *)
Lemma le1_byte : forall x : word, le1 x = [Z_to_bv 8 (bv_unsigned x mod 256)].
Proof. intros x. cbn. f_equal. apply Mem.Z_to_bv8_mod. rewrite Z.mod_mod by lia. reflexivity. Qed.
Ltac sb1 := zstep; rewrite le1_byte, ?unsigned_lit by lia; mem_after_store_opt.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition uar_cells (v : mem) : Prop :=
  ro_cells rsegs v 0xa8bc8 [C8 (Z_to_bv 64 0xb4bc0)] /\ ro_cells rsegs v 0xb4bc0 [C4 (Z_to_bv 64 1)].

Section Consts.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variable v : mem.
  Hypothesis CH : consts_hold LPA v.
  #[using="CH"] Lemma uar_cells_of_consts : uar_cells v.
  Proof.
    split.
    - apply ro_C8_of_bytes. apply (consts_lookup v _ _ CH). vm_compute. reflexivity.
    - apply ro_C4_of_bytes. apply (consts_lookup v _ _ CH). vm_compute. reflexivity.
  Qed.
End Consts.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma rw_cells_of_mapped : forall (v : mem) a n,
    0 <= n -> wr_at rsegs v a n -> mapped v a n -> off_image LPA a n ->
    exists junk, length junk = Z.to_nat n /\ rw_cells rsegs v a [CB (Z.to_nat n) junk].
  Proof.
    intros v a n N0 WR MP OFF. pose proof WR as (W0 & W1 & W).
    assert (G : forall i, 0 <= i < n -> exists b, v (Z_to_bv 64 (a + i)) = Some b).
    { intros i Hi. specialize (MP i Hi). destruct (v (Z_to_bv 64 (a + i))) as [b|]; [exists b; reflexivity| exfalso; apply MP; reflexivity]. }
    assert (REC : forall k, (k <= Z.to_nat n)%nat -> exists bs, length bs = k /\
              forall i, (i < k)%nat -> v (Z_to_bv 64 (a + (n - Z.of_nat k) + Z.of_nat i)) = nth_error bs i).
    { induction k as [|k IH]; intros Hk.
      - exists []. split; [reflexivity|]. intros i Hi. cbn in Hi. lia.
      - destruct (IH ltac:(lia)) as (bs & Lb & Hbs). destruct (G (n - Z.of_nat (S k)) ltac:(lia)) as (b & Hb).
        exists (b :: bs). split; [cbn; lia|]. intros [|i] Hi.
        + cbn. rewrite <- Hb. f_equal. f_equal. lia.
        + cbn. rewrite <- (Hbs i ltac:(lia)). f_equal. f_equal. lia. }
    destruct (REC (Z.to_nat n) ltac:(lia)) as (junk & LJ & HJ).
    exists junk. split; [exact LJ|]. split.
    - split; [cbn; split; [exact LJ| exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
      split; [lia|]. split; [rewrite LJ; lia|]. intros i Hi. unfold mrd, wa.
      specialize (HJ i ltac:(rewrite LJ in Hi; exact Hi)).
      replace (a + (n - Z.of_nat (Z.to_nat n)) + Z.of_nat i) with (a + Z.of_nat i) in HJ by lia.
      rewrite HJ. destruct (nth_error junk i) eqn:E; [reflexivity|]. apply nth_error_None in E. rewrite LJ in Hi. lia.
    - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact WR.
  Qed.

  (* [comment removed for export] *)
  Lemma fframe_cells : forall A m md ff k age,
    ainv A m md -> a_frame A ff = Some (k, age) ->
    exists junk, length junk = Z.to_nat (fsize k - 8) /\ rw_cells rsegs (aview A m) ff [CB (Z.to_nat (fsize k - 8)) junk].
  Proof.
    intros A m md ff k age AI0 HF.
    destruct (fframe_geom LPA A m md ff k age AI0 HF) as (K0 & FS & LO & HI & OFF & _ & MP & _ & WR & _).
    apply rw_cells_of_mapped; [lia| exact WR| | eapply off_image_sub; [exact OFF| lia| lia]].
    eapply mapped_sub; [exact MP| lia| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma fshadow_cells : forall A m md ff k age,
    ainv A m md -> a_frame A ff = Some (k, age) ->
    exists junk, length junk = Z.to_nat (fsize k / 8) /\ rw_cells rsegs (aview A m) (sh ff) [CB (Z.to_nat (fsize k / 8)) junk].
  Proof.
    intros A m md ff k age AI0 HF.
    destruct (fframe_geom LPA A m md ff k age AI0 HF) as (K0 & FS & LO & HI & _ & OFF & _ & MP & _ & WR).
    apply rw_cells_of_mapped; [apply Z.div_pos; lia| exact WR| exact MP| exact OFF].
  Qed.

  (* [comment removed for export] *)
  Lemma fshadow_zcells : forall A m md ff k age n,
    ainv A m md -> a_frame A ff = Some (k, age) -> all_zero (aview A m) (sh ff) n -> n = fsize k / 8 ->
    rw_cells rsegs (aview A m) (sh ff) (zcells (Z.to_nat n)).
  Proof.
    intros A m md ff k age n AI0 HF AZ En.
    destruct (fframe_geom LPA A m md ff k age AI0 HF) as (K0 & FS & LO & HI & _ & OFF & _ & MP & _ & WR).
    assert (N0 : 0 <= n) by (subst n; apply Z.div_pos; lia).
    subst n. pose proof WR as (W0 & W1 & _).
    split.
    - split; [exact (zcells_wf _)|]. rewrite zcells_bytes. split; [exact W0|].
      rewrite repeat_length, Z2Nat.id by lia. split; [exact W1|].
      intros i Hi. unfold mrd, wa. rewrite (AZ (Z.of_nat i) ltac:(lia)).
      symmetry. apply nth_error_repeat. exact Hi.
    - rewrite zcells_size, Z2Nat.id by lia. exact WR.
  Qed.

  (* [comment removed for export] *)
  Lemma owned_outside_live : forall A m md p n a,
    ainv A m md -> a_live A p = Some n -> owned A a -> a + 1 <= p \/ p + n <= a.
  Proof.
    intros A m md p n a AI0 HL HO.
    destruct (as_live_ok LPA A m md p n AI0 HL) as (_ & _ & _ & _ & _ & _ & NO & _).
    destruct (Z_lt_le_dec a p) as [X|X]; [left; lia|]. destruct (Z_lt_le_dec a (p + n)) as [Y|Y]; [|right; lia].
    exfalso. apply (NO (a - p) ltac:(lia)). replace (p + (a - p)) with a by lia. exact HO.
  Qed.
  Lemma owned_outside_fframe : forall A m md ff k age a,
    ainv A m md -> a_frame A ff = Some (k, age) -> owned A a ->
    (a + 1 <= ff \/ ff + fsize k - 8 <= a) /\ (a + 1 <= sh ff \/ sh ff + fsize k / 8 <= a).
  Proof.
    intros A m md ff k age a AI0 HF HO.
    destruct (as_frame_ok LPA A m md ff k age AI0 HF) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & NO & NOS).
    split.
    - destruct (Z_lt_le_dec a ff) as [X|X]; [left; lia|]. destruct (Z_lt_le_dec a (ff + fsize k - 8)) as [Y|Y]; [|right; lia].
      exfalso. apply (NO (a - ff) ltac:(lia)). replace (ff + (a - ff)) with a by lia. exact HO.
    - destruct (Z_lt_le_dec a (sh ff)) as [X|X]; [left; lia|]. destruct (Z_lt_le_dec a (sh ff + fsize k / 8)) as [Y|Y]; [|right; lia].
      exfalso. apply (NOS (a - sh ff) ltac:(lia)). replace (sh ff + (a - sh ff)) with a by lia. exact HO.
  Qed.
  Lemma owned_below_ceiling : forall A m md a,
    ainv A m md -> owned A a -> ~ in_image LPA a -> 0 <= a < alloc_ceiling.
  Proof.
    intros A m md a AI0 HO NI. destruct (as_owned_where LPA A m md a AI0 HO) as [ST|[HZ _]]; [|exact HZ].
    exfalso. apply NI. pose proof (as_static_where LPA a ST). pose proof (layout_facts (L:=LPA)). unfold in_image. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fframe_flag : forall A m md ff k age,
    ainv A m md -> a_frame A ff = Some (k, age) ->
    exists (fa : Z) (b : byte),
      0 <= fa < alloc_ceiling /\
      bytes_at rsegs (aview A m) (ff + fsize k - 8) (le8 (Z_to_bv 64 fa)) /\
      ro_cells rsegs (aview A m) (ff + fsize k - 8) [C8 (Z_to_bv 64 fa)] /\
      rw_cells rsegs (aview A m) fa [C1 b] /\
      owned A fa /\ ~ in_image LPA fa.
  Proof.
    intros A m md ff k age AI0 HF.
    destruct (as_sframe_flag LPA A m md ff k age AI0 HF) as (fa & FB & OW & NI & (W0 & W1 & _) & _).
    change (aview_of (ahull A) m) with (aview A m) in FB.
    pose proof (owned_below_ceiling A m md fa AI0 OW NI) as R. pose proof alloc_ceiling_num as ACV.
    destruct (flag_cell_rw LPA A m md ff k age (Z_to_bv 64 fa) AI0 HF FB) as [b RW].
    rewrite unsigned_lit in RW by lia.
    exists fa, b. split; [exact R|]. split; [exact FB|]. split; [apply ro_C8_of_bytes; exact FB|].
    split; [exact RW|]. split; [exact OW| exact NI].
  Qed.

  (* [comment removed for export] *)
  #[using="AI Clg"] Lemma flag_cleared : forall (v : mem) (fa : Z),
    rw_cells rsegs v fa [C1 (Z_to_bv 8 0)] -> ~ in_image LPA fa -> 0 <= fa < 2^64 ->
    v (Z_to_bv 64 fa) = Some (Z_to_bv 8 0).
  Proof.
    intros v fa [[_ (B0 & B1 & B)] _] NI R.
    specialize (B 0%nat ltac:(cbn; lia)). cbn [cells_bytes cbytes app nth_error] in B.
    unfold mrd, wa in B. rewrite Z.add_0_r in B.
    destruct (v (Z_to_bv 64 fa)) as [b|] eqn:E; [congruence|].
    rewrite (as_seg_rom_outside LPA) in B; [discriminate B|]. rewrite unsigned_lit by lia. exact NI.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma smalloc_acall :
    forall (k : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (sz : Z) (T : TSet),
      ainv A m md -> mem_inv rsegs (aview A m) ->
      (k = 0 \/ k = 1) -> a0 = Z_to_bv 64 sz -> 0 < sz <= fsize k ->
      (forall ff age, a_frame A ff = Some (k, age) -> Z.of_nat age + 2 < fslots k) ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      alloc_ceiling <= bv_unsigned sp - ASTK ->
      mapped (aview A m) (bv_unsigned sp - ASTK) ASTK ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (ff : Z) (A' : AS) (m' : mem) (md' : Model)
              (junk : list byte) (fa : Z) (fb : byte),
          ainv A' m' md' -> mem_inv rsegs (aview A' m') -> amd_frame md md' ->
          (forall q, a_live A' q = a_live A q) -> a_livebytes A' = a_livebytes A -> a_tinycred A' = a_tinycred A -> a_nlive A' = a_nlive A ->
          a_seccred A' = a_seccred A -> a_primcred A' = a_primcred A (* [comment removed for export] *) ->
          ff <> 0 -> a_frame A ff = None -> a_frame A' ff = Some (k, 0%nat) ->
          (forall g k' age', g <> ff -> a_frame A g = Some (k', age') ->
              a_frame A' g = Some (k', if Z.eqb k' k then S age' else age')) ->
          (forall g, g <> ff -> a_frame A g = None -> a_frame A' g = None) ->
          (* [comment removed for export] *)
          ff mod 32 = 0 /\ app_range LPA ff (fsize k) (* [comment removed for export] *) /\ ff + fsize k <= alloc_ceiling /\
          0 <= sh ff /\ sh ff + fsize k / 8 <= SHMAX ->
          (* [comment removed for export] *)
          length junk = Z.to_nat (fsize k - 8) ->
          rw_cells rsegs (aview A' m') ff [CB (Z.to_nat (fsize k - 8)) junk] ->
          rw_cells rsegs (aview A' m') (sh ff) (zcells (Z.to_nat (fsize k / 8))) ->
          ro_cells rsegs (aview A' m') (ff + fsize k - 8) [C8 (Z_to_bv 64 fa)] ->
          cframe LPA (owned A) (owned A') (bv_unsigned sp) ASTK nowhere (frm ff k) (aview A m) (aview A' m') ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 ff) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_smalloc_pc LPA k) fc None m (seg_rom rsegs)) md) T.
  Proof.
    intros until T. intros AI0 MI K01 Ha0 Hsz YOUNG TP SP16 RA2 CEIL MP KK.
    eapply (as_smalloc_cps LPA k); [exact AI0| exact MI| destruct K01 as [-> | ->]; [left|right;left]; reflexivity
      | exact Ha0| exact Hsz| intros K7; exfalso; lia| exact YOUNG| exact TP| exact SP16| exact RA2| exact CEIL| exact MP|].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ff A' m' md'. cbv zeta.
    intros AI' MI' MDF HH HE LV LB TC NL SC PC NZ FN FF AGE NONE AZ FR.   (* [comment removed for export] *)
    change (aview_of (ahull A') m') with (aview A' m') in MI', AZ, FR.
    change (aview_of (ahull A) m) with (aview A m) in FR.
    destruct (fframe_cells A' m' md' ff k 0%nat AI' FF) as (junk & LJ & FC).
    destruct (fframe_flag A' m' md' ff k 0%nat AI' FF) as (fa & fb & _ & _ & FRO & _ & _ & _).
    destruct (fframe_geom LPA A' m' md' ff k 0%nat AI' FF) as (K0 & FS & LO & HI & _).
    destruct (as_frame_ok LPA A' m' md' ff k 0%nat AI' FF) as (_ & AL & _).
    pose proof (app_facts LPA ff (fsize k) LO) as (FB & _).   (* [comment removed for export] *)
    pose proof (sh_bound ff (fsize k) ltac:(lia) ltac:(lia) HI) as (S0 & S1 & _).
    replace ((fsize k + 7) / 8) with (fsize k / 8) in S1
      by (destruct K01 as [-> | ->]; reflexivity).
    eapply (KK t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ff A' m' md' junk fa fb);
      [ exact AI' | exact MI' | exact MDF | exact LV | exact LB | exact TC | exact NL | exact SC | exact PC | exact NZ | exact FN | exact FF | exact AGE | exact NONE
      | | exact LJ | exact FC | | exact FRO | apply cframe_of_frame_ok; exact FR ].
    - split; [| split; [exact LO| split; [exact HI| split; [exact S0| exact S1]]]].
      (* [comment removed for export] *)
      destruct K01 as [-> | ->]; [change (Z.min (fsize 0) 4096) with 64 in AL| change (Z.min (fsize 1) 4096) with 128 in AL].
      + pose proof (Z.div_mod ff 64 ltac:(lia)) as D. rewrite AL, Z.add_0_r in D. rewrite D.
        replace (64 * (ff / 64)) with ((2 * (ff / 64)) * 32) by lia. apply Z_mod_mult.
      + pose proof (Z.div_mod ff 128 ltac:(lia)) as D. rewrite AL, Z.add_0_r in D. rewrite D.
        replace (128 * (ff / 128)) with ((4 * (ff / 128)) * 32) by lia. apply Z_mod_mult.
    - eapply fshadow_zcells; [exact AI'| exact FF| | reflexivity].
      replace (Z.leb k 6) with true in AZ by (destruct K01 as [-> | ->]; reflexivity). exact AZ.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma frames_aged_alloc_release : forall (A A1 A2 : AS) m2 md2 ff k,
    (k = 0 \/ k = 1) ->
    a_frame A ff = None -> a_frame A1 ff = Some (k, 0%nat) ->
    (forall g k' age', g <> ff -> a_frame A g = Some (k', age') ->
        a_frame A1 g = Some (k', if Z.eqb k' k then S age' else age')) ->
    (forall g, g <> ff -> a_frame A g = None -> a_frame A1 g = None) ->
    frames_same A1 A2 -> ainv A2 m2 md2 ->
    (exists age, a_frame A2 ff = Some (k, age)) ->
    frames_aged A (a_release A2 ff) (if Z.eqb k 0 then 1 else 0)%nat (if Z.eqb k 1 then 1 else 0)%nat.
  Proof.
    intros A A1 A2 m2 md2 ff k K01 FN FF AGE NONE FS AI2 [age2 HF2].
    destruct (as_release_spec LPA A2 m2 md2 ff k age2 AI2 HF2) as (RN & RO & _).
    split.
    - intros g k' age' HG.
      assert (NE : g <> ff) by (intros ->; rewrite FN in HG; discriminate HG).
      rewrite (RO g NE), (FS g), (AGE g k' age' NE HG).
      destruct (Z.eqb_spec k' k) as [->|NK].
      + exists 1%nat. split; [rewrite Nat.add_1_r; reflexivity|].
        unfold fbound. destruct K01 as [-> | ->]; cbn; lia.
      + exists 0%nat. split; [rewrite Nat.add_0_r; reflexivity| lia].
    - intros g HG. destruct (Z.eq_dec g ff) as [->|NE]; [exact RN|].
      rewrite (RO g NE), (FS g). exact (NONE g NE HG).
  Qed.

  (* [comment removed for export] *)
  Lemma cframe_release : forall (o o2 o3 : Z -> Prop) sp W (V N N' : Z -> Prop) (v v2 v3 : mem) W3,
    cframe LPA o o2 sp W V N v v2 ->
    munch W3 v2 v3 ->
    (forall a, 0 <= a < 2^64 -> ~ outside W3 a -> N a \/ o2 a) ->
    0 <= sp - W -> sp <= 2^64 -> (forall i, 0 <= i < W -> outside W3 (sp - W + i)) ->
    (forall a, o3 a -> o2 a \/ N a) ->
    (forall a, N' a -> N a) ->
    cframe LPA o o3 sp W V N' v v3.
  Proof.
    intros o o2 o3 sp W V N N' v v2 v3 W3 (C1 & C2 & C3) MU IN W0 W1 NW REL SUB.
    assert (NEWDEAD : forall a, 0 <= a < 2^64 -> ~ o a -> ~ (sp - W <= a < sp) -> ~ (cl_errno LPA <= a < cl_errno LPA + 4) ->
              ~ V a -> N a -> (v (Z_to_bv 64 a) <> None \/ in_image LPA a) -> False).
    { intros a Ha NO NWa NE NV HN VIS. destruct (C3 a Ha NWa NE HN) as [X|[X|[X Y]]]; [exact (NO X)| exact (NV X)|].
      destruct VIS as [Z1|Z1]; [exact (Z1 X)| exact (Y Z1)]. }
    split; [| split].
    - intros a Ha NO VIS NWa NE NV. destruct (C1 a Ha NO VIS NWa NE NV) as [E NO2].
      assert (OUT : outside W3 a).
      { destruct (Classical_Prop.classic (outside W3 a)) as [X|X]; [exact X|]. exfalso.
        destruct (IN a Ha X) as [HN|HO]; [exact (NEWDEAD a Ha NO NWa NE NV HN VIS)| exact (NO2 HO)]. }
      split.
      + rewrite <- E. unfold munch in MU. rewrite (MU (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit by lia. exact OUT.
      + intros O3. destruct (REL a O3) as [X|X]; [exact (NO2 X)| exact (NEWDEAD a Ha NO NWa NE NV X VIS)].
    - eapply mapped_munch; [exact MU| exact W0| lia| exact NW| exact C2].
    - intros a Ha NWa NE HN. apply C3; [exact Ha| exact NWa| exact NE| exact (SUB a HN)].
  Qed.

  (* [comment removed for export] *)
  Lemma stk_ccall_any : forall A A' m md (v v' : mem) (sp win : Z) V N lo hi,
    ainv A m md -> cframe LPA (owned A) (owned A') sp win V N v v' ->
    stk rsegs v lo hi -> alloc_ceiling <= lo -> (forall a, lo <= a < hi -> ~ V a) ->
    stk rsegs v' lo hi.
  Proof.
    intros A A' m md v v' sp win V N lo hi AI0 (C1 & C2 & C3) ST Hlo HV.
    destruct ST as (S0 & S1 & SS). split; [exact S0|]. split; [exact S1|].
    pose proof (layout_facts (L:=LPA)) as LO.
    intros a Ha.
    assert (NO : ~ owned A a).
    { intros O. destruct (as_owned_where LPA A m md a AI0 O) as [Hs|[[_ Hlt] _]]; [apply (as_static_where LPA) in Hs; lia| lia]. }
    destruct (Classical_Prop.classic (sp - win <= a < sp)) as [Hin|Hout].
    - assert (Hm : v' (wa a) <> None).
      { unfold wa. replace a with (sp - win + (a - (sp - win))) by lia. apply C2. lia. }
      split.
      + unfold wview. destruct (v' (wa a)); [discriminate| exfalso; apply Hm; reflexivity].
      + unfold mrd. destruct (v' (wa a)) as [b|]; [exists b; reflexivity| exfalso; apply Hm; reflexivity].
    - destruct (SS a Ha) as [W [b Hb']].
      assert (VISm : v (Z_to_bv 64 a) <> None).
      { intros E. unfold mrd, wa in Hb'. rewrite E in Hb'.
        rewrite (as_seg_rom_outside LPA) in Hb'; [discriminate|]. unfold in_image. rewrite unsigned_lit by lia. lia. }
      destruct (C1 a ltac:(lia) NO (or_introl VISm) Hout ltac:(lia) (HV a Ha)) as [E _].
      split.
      + unfold wview, wa in *. rewrite E. exact W.
      + exists b. unfold mrd, wa in *. rewrite E. exact Hb'.
  Qed.

  (* [comment removed for export] *)
  Lemma frames_young_smalloc : forall A k n0 n1,
    frames_young A n0 n1 -> (k = 0 /\ (1 <= n0)%nat \/ k = 1 /\ (1 <= n1)%nat) ->
    forall ff age, a_frame A ff = Some (k, age) -> Z.of_nat age + 2 < fslots k.
  Proof.
    intros A k n0 n1 FY K ff age HF.
    destruct K as [[-> N]|[-> N]]; pose proof (FY ff _ age HF ltac:(lia)) as Y; unfold fbound in Y; cbn in Y; lia.
  Qed.
End S.
End A_Frame.

   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac lit32 K :=
  repeat match type of K with
  | context [bv_unsigned (zx32 (Z_to_bv 64 ?z))] =>
      let v := eval vm_compute in (bv_unsigned (zx32 (Z_to_bv 64 z))) in
      change (bv_unsigned (zx32 (Z_to_bv 64 z))) with v in K
  | context [bv_unsigned (sx32 (Z_to_bv 64 ?z))] =>
      let v := eval vm_compute in (bv_unsigned (sx32 (Z_to_bv 64 z))) in
      change (bv_unsigned (sx32 (Z_to_bv 64 z))) with v in K
  | context [bv_signed (zx32 (Z_to_bv 64 ?z))] =>
      let v := eval vm_compute in (bv_signed (zx32 (Z_to_bv 64 z))) in
      change (bv_signed (zx32 (Z_to_bv 64 z))) with v in K
  | context [bv_signed (sx32 (Z_to_bv 64 ?z))] =>
      let v := eval vm_compute in (bv_signed (sx32 (Z_to_bv 64 z))) in
      change (bv_signed (sx32 (Z_to_bv 64 z))) with v in K
  end.
(* [comment removed for export] *)
Ltac is_zlit v := lazymatch v with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac fold_bits K :=
  repeat match type of K with
  | context [Z.land ?a ?b] => let v := eval vm_compute in (Z.land a b) in is_zlit v; change (Z.land a b) with v in K
  | context [Z.lor ?a ?b] => let v := eval vm_compute in (Z.lor a b) in is_zlit v; change (Z.lor a b) with v in K
  | context [Z.shiftl ?a ?b] => let v := eval vm_compute in (Z.shiftl a b) in is_zlit v; change (Z.shiftl a b) with v in K
  | context [Z.shiftr ?a ?b] => let v := eval vm_compute in (Z.shiftr a b) in is_zlit v; change (Z.shiftr a b) with v in K
  end.
Ltac kill K := exfalso; lit32 K; fold_bits K; first [ klia K | unsign K; klia K | dead K ].

(* [comment removed for export] *)
Ltac kdead := let K := fresh "K" in if_cases K; zify_cond K; [ kill K | clear K ].
(* [comment removed for export] *)
Ltac kdead2 := let K := fresh "K" in if_cases K; zify_cond K; [ clear K | kill K ].

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma hff_al8 : forall H k,
  henv_geom LPA H -> k mod 8 = 0 -> (h_ff H + k) mod 8 = 0.
Proof.
  intros H k (G1 & _ & _) Hk.
  pose proof (Z.div_mod (h_ff H) 4096 ltac:(lia)) as D. rewrite G1, Z.add_0_r in D.
  rewrite D. rewrite Z.add_mod, Hk by lia.
  replace (4096 * (h_ff H / 4096)) with ((512 * (h_ff H / 4096)) * 8) by lia.
  rewrite Z_mod_mult. reflexivity.
Qed.

End CEIL.

(* [comment removed for export] *)
Ltac rebundle :=
  cbv beta delta [AIcpya4.asan_memset_cells AIcp3q7.asan_memcpy_cells AIcpii0.strlen_icpt_cells
             AIcpinq.strcpy_icpt_cells OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp.AIcpwd0.set_shadow_cells AIcp0e6.asan_inited_cell
             OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj.map_cells];
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption.

(* [comment removed for export] *)
Ltac paok K HG := exfalso; apply K; apply land7_of_mod8; [lia| apply (hff_al8 _ _ HG); reflexivity].

(* [comment removed for export] *)
Ltac shadow_chk0z SRC k :=
  zstep; zstep; shadow_addr SRC k; zstep;
  let K := fresh "KS" in
  zstep; if_cases K; zify_cond K;
  [ first [ shadow_fast K; clear K; shadow_cleanup | shadow_dead | (exfalso; lia) ]
  | first [ shadow_fast K; clear K; shadow_cleanup | shadow_dead | (exfalso; lia) ] ].

(* [comment removed for export] *)
Ltac henv_side GLOB HSH HG CE MU WM ST :=
  rewrite ?unsigned_lit by lia;
  first [ reflexivity
        | exact HG | exact ST | assumption
        | (eapply glob_ok_munch; [exact GLOB| exact MU| exact WM|
             intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_cp, h_vsc in Ha__; cbn; lia])
        | (eapply hshadow_munch; [exact HSH| exact MU| exact HG| intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn; lia])
        | (eapply cenv_munch; [exact CE| exact MU| repeat constructor; unfold const_free_ivl, CONSTS_TOP; cbn; lia])
        | (unfold WSASSERT_STACK, WSEMU_STACK, WSMARK_STACK; lia) ].

(* [comment removed for export] *)
Ltac ws_cranges H AINVx HFR' FR :=
  lazymatch type of AINVx with ainv ?Ax ?mx ?mdx =>
    let CW := fresh "CRW" in let CEm := fresh "CRE" in let CSW := fresh "CRSW" in let CSB := fresh "CRSB" in let CF := fresh "CRF" in
    pose proof (crange_fframe (L:=LPA) Ax mx mdx _ _ _ (h_ff H + 2976) 40 AINVx HFR'
                  ltac:(lia) ltac:(change (fsize HCLASS) with 8192; lia) ltac:(lia)) as CW;
    pose proof (crange_fframe (L:=LPA) Ax mx mdx _ _ _ (h_ff H + 3152) 32 AINVx HFR'
                  ltac:(lia) ltac:(change (fsize HCLASS) with 8192; lia) ltac:(lia)) as CEm;
    pose proof (crange_fshadow (L:=LPA) Ax mx mdx _ _ _ (sh (h_ff H + 2976)) (Z.of_nat (length (shpat 40))) AINVx HFR'
                  ltac:(lia) ltac:(change (fsize HCLASS / 8) with 1024; lia) ltac:(lia)) as CSW;
    pose proof (crange_fshadow (L:=LPA) Ax mx mdx _ _ _ (sh (h_ff H + 3152)) (Z.of_nat (length (shpat 1024))) AINVx HFR'
                  ltac:(lia) ltac:(change (fsize HCLASS / 8) with 1024; lia) ltac:(lia)) as CSB;
    lazymatch type of FR with rw_cells _ _ ?fa ?cs =>
      pose proof (crange_stack (L:=LPA) Ax mx mdx (aview Ax mx) fa (Z.of_nat (cells_size cs)) AINVx ltac:(lia)
                    ltac:(cbn [cells_size csize Nat.add length]; lia)
                    (rw_cells_mapped LPA _ _ _ FR ltac:(off_image_solve LPA))) as CF end
  end.

(* [comment removed for export] *)
Tactic Notation "shadow_chk_gen" constr(SRC) constr(k) constr(U) integer(n) :=
  zstep; zstep; shadow_addr SRC k;
  lazymatch goal with |- evt ?segs ?Q _ =>
    eapply (evt_cut segs _ Q);
    [ zstep; do n zstep;
      let K := fresh "KS" in
      zstep; if_cases K; zify_cond K;
      [ first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slow U ]
      | first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slow U ] ]
    | let ms := fresh "ms" in let x := fresh "junk" in
      intros ms [x ->]; simp_regs ]
  end;
  shadow_cleanup.

Tactic Notation "shadow_rechk_gen" constr(SRC) constr(X) constr(k) constr(U) integer(n) :=
  shadow_addr_at SRC X k;
  lazymatch goal with |- evt ?segs ?Q _ =>
    eapply (evt_cut segs _ Q);
    [ zstep; do n zstep;
      let K := fresh "KS" in
      zstep; if_cases K; zify_cond K;
      [ first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slow U ]
      | first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slow U ] ]
    | let ms := fresh "ms" in let x := fresh "junk" in
      intros ms [x ->]; simp_regs ]
  end;
  shadow_cleanup.
