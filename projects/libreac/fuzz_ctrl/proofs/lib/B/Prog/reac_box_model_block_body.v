(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 687 of its 711 lines of code are new or changed and 224 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcParseLib RcKindLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c dt1_head_c name_field_c reac_box_model_block_c
  reac_box_model_block.
Import ListNotations.
Open Scope Z_scope.

(* Local copy of reac_box_model_block.v:215's store hook: that file made it Local (a Theorem Labs lane, approved by a Theorem Labs lane, 2026-10-30). *)
Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | RMo : rd_mono ?mq m |- _ => apply (rd_mono_write mq m (wa a) bs) in RMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* Body walk (0x866d4 -> 0x86e14), frame release (0x86e14 -> Q0) and the final theorem for reac_box_model_block,
   image B (asan-ubsan). The scaffolding (entry/fwords/td_tail, epi0, rel_flags, the Section Main exports) lives in
   reac_box_model_block.v; this file imports it so rel_flags is not recompiled each iteration. *)

Lemma out_app_l : forall (W1 W2 : list ivl) x, outside (W1 ++ W2) x -> outside W1 x.
Proof.
  induction W1 as [|[lo hi] W1 IH]; intros W2 x H; cbn [app outside] in *; [exact I|].
  destruct H as [H1 H2]. split; [exact H1 | exact (IH W2 x H2)].
Qed.

Lemma out_app_r : forall (W1 W2 : list ivl) x, outside (W1 ++ W2) x -> outside W2 x.
Proof.
  induction W1 as [|[lo hi] W1 IH]; intros W2 x H; cbn [app outside] in *; [exact H|].
  destruct H as [_ H2]. exact (IH W2 x H2).
Qed.

(* Generic helpers of the release (outside the section: they must not depend on its hypotheses, which the walk
   clears before the stores). *)

(* Eight readable and writable shadow bytes as one 8-byte cell. *)
Lemma sh_cells : forall mc S, shadow_rw mc -> (forall i, 0 <= i < 8 -> in_shadow (S + i)) ->
  exists w, rw_cells rsegs mc S [CB 8 (le8 w)].
Proof.
  intros mc S Hsr Hin.
  pose proof (rt_shadow_bound _ (Hin 0 ltac:(lia))) as B0. pose proof (rt_shadow_bound _ (Hin 7 ltac:(lia))) as B7.
  destruct (rd8_le8 mc S ltac:(lia) ltac:(lia) (fun i Hi => proj2 (Hsr _ (Hin i Hi)))) as (w & Hb).
  exists w. split; [split|].
  - cbn [cells_wf cell_wf]. split; [apply length_le8 | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - change (Z.of_nat (cells_size [CB 8 (le8 w)])) with 8.
    split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (Hsr _ (Hin i Hi))).
Qed.

(* One readable and writable byte as a one-byte cell. *)
Lemma rw1 : forall mc a v, 0 <= a -> a + 1 <= 2^64 ->
  wview rsegs mc (wa a) <> None -> mrd rsegs mc (wa a) = Some v -> rw_cells rsegs mc a [CB 1 [v]].
Proof.
  intros mc a v Ha Hb Hw Hr. split; [split|].
  - cbn [cells_wf cell_wf length]. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [exact Ha|]. split; [cbn [length]; lia|].
    intros i Hi. cbn [length] in Hi. replace i with 0%nat by lia. cbn [nth_error Z.of_nat].
    rewrite Z.add_0_r. exact Hr.
  - change (Z.of_nat (cells_size [CB 1 [v]])) with 1.
    split; [exact Ha|]. split; [lia|]. intros i Hi. replace (a + i) with a by lia. exact Hw.
Qed.

Lemma nth_rep0 : forall (n i : nat), (i < n)%nat -> nth_error (repeat (Z_to_bv 8 0) n) i = Some (Z_to_bv 8 0).
Proof.
  induction n as [|n IH]; intros i H; [exfalso; lia|].
  destruct i as [|i]; cbn [repeat nth_error]; [reflexivity | apply IH; lia].
Qed.

Section Body.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte).
  Hypothesis HSM : asan_stack_malloc_0_contract.
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  Hypothesis SR0 : shadow_rw m.
  Hypothesis HHM : HIGHMEM_BEG <= bv_unsigned sp - 4272.
  Hypothesis HAE : bv_unsigned sp <= APPMEM_END.
  Hypothesis AW0 : addressable m (bv_unsigned sp - 4272) 4272.
  Hypothesis FP0 : fp [0%nat] m (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
    (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o).
  Hypothesis TLS0 : reac_box_model_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp).
  Hypothesis Rp : 0 <= p < 2^64.
  Hypothesis Rb : 0 <= b < 2^64.
  Hypothesis Ro : 0 <= o < 2^64.
  Hypothesis HP : p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs m p row /\
    (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) /\ (o = 0 \/ o + 32 <= p \/ p + 296 <= o).
  Hypothesis HN : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    name_ok nb /\ bytes_at rsegs m (rname row) nb /\
    (bv_unsigned sp <= rname row \/ rname row + Z.of_nat (length nb) <= bv_unsigned sp - 4272) /\
    (o = 0 \/ o + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= o).
  Hypothesis HO : o <> 0 -> rw_cells rsegs m o [CB 32 ob] /\
    (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) /\ (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o).
  Hypothesis AP : p <> 0 -> addressable m p 296.
  Hypothesis ANB : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    addressable m (rname row) (Z.of_nat (length nb)).
  Hypothesis AO : o <> 0 -> addressable m o 32 /\ app_mem (o + 32) /\ (o + 32 <= RT_LO \/ RT_HI <= o).
  Hypothesis AJ1 : b = 1 -> addressable m JOIN_0014 32.
  Hypothesis AJ2 : b = 2 -> addressable m JOIN_0013 32.
  Hypothesis NDJ : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    fp_dj [(rname row, rname row + Z.of_nat (length nb))] (fp_w [0%nat] FS).

  Hypothesis HMS : asan_memset_contract.
  Hypothesis HMC : asan_memcpy_contract.
  Hypothesis HBD : build_dt1_single_contract.
  Hypothesis HDH : dt1_head_contract.
  Hypothesis HNF : name_field_contract.

  (* The window is addressable whenever every window shadow byte reads 0 (the dual of win_shadow0): used to rebuild
     addressable at the frame release, after the frame's shadow is reset to 0. *)
  Lemma addr_rebuild : forall mc,
    (forall i, 0 <= i < 4272 ->
       mrd rsegs mc (wa (shadow_addr (bv_unsigned sp - 4272 + i))) = Some (Z_to_bv 8 0)) ->
    addressable mc (bv_unsigned sp - 4272) 4272.
  Proof.
    intros mc Hsh. pose proof AW0 as (A0 & An & Ae & HAd). unfold REAC_BOX_MODEL_BLOCK_K in *.
    split; [exact A0|]. split; [exact An|]. split; [exact Ae|].
    intros i Hi. destruct (HAd i Hi) as (Hap & _). split; [exact Hap|].
    exists (Z_to_bv 8 0). split; [exact (Hsh i Hi)|]. left. reflexivity.
  Qed.
  (* The body's fine footprint (window, hint word, flag j, the frame and its shadow, and o) lies inside the post's
     write set reac_box_model_block_W ++ reac_box_model_block_X: the sub_fp that br_fp/br_ac need at the release.
     PERF: every unfold/cbn/rewrite targets one hypothesis, never `in *` over the section. *)
  Lemma sub_post : forall fr f spc j n w56, FK FS A fr f spc j n w56 ->
    sub_fp (Wf sp FS fr j n ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)]))
           (reac_box_model_block_W o (bv_unsigned sp) ++ reac_box_model_block_X (bv_unsigned sp) FS).
  Proof.
    intros fr f spc j n w56 HK x Hout.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    assert (outapp : forall (W1 W2 : list ivl) y, outside (W1 ++ W2) y -> outside W1 y /\ outside W2 y).
    { induction W1 as [|[lo hi] W1 IH]; intros W2 y H; cbn [app outside] in *; [split; [exact I | exact H]|].
      destruct H as [H1 H2]. destruct (IH W2 y H2) as [H3 H4]. split; [split; [exact H1 | exact H3]|exact H4]. }
    assert (HAb : A mod 32 = 0 /\ bv_unsigned sp - 176 <= A <= bv_unsigned sp - 160)
      by (rewrite HA; Z.div_mod_to_equations; lia).
    assert (EH0 : fs_hint FS 0 = FS) by (unfold fs_hint; cbn [Z.of_nat]; lia).
    assert (EF0 : fs_flag FS 0 0 = FS + 4096) by (unfold fs_flag; cbn [Z.of_nat]; lia).
    assert (EFj : fs_flag FS 0 j = FS + 4096 + j) by (unfold fs_flag; cbn [Z.of_nat]; lia).
    assert (EM0 : fs_M 0 = 16384) by reflexivity.
    assert (EFR0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (EFMf : fs_frame FS 0 (fs_M 0) = FS + 1085440).
    { unfold fs_frame, fs_B, fs_M.
      replace (2 ^ (14 - Z.of_nat 0) * (64 * 2 ^ Z.of_nat 0)) with 1048576 by reflexivity.
      replace (Z.of_nat 0 * 2 ^ 20) with 0 by reflexivity. lia. }
    pose proof Rsp as _Rsp.
    destruct (outapp _ _ _ Hout) as (HoutW & HoutX).
    unfold reac_box_model_block_W, REAC_BOX_MODEL_BLOCK_K in HoutW. cbn [outside fst snd] in HoutW.
    destruct HoutW as (Hwin & HoutO).
    unfold reac_box_model_block_X, REAC_BOX_MODEL_BLOCK_K in HoutX.
    destruct (outapp _ _ _ HoutX) as (HoutFP & HoutWS).
    cbn [fp_w fp_w1 flat_map app outside fst snd] in HoutFP.
    rewrite EFR0, EFMf, EH0, EF0, EM0 in HoutFP.
    destruct HoutFP as (Hhint & Hflag & Hframe & HfrSh & _).
    cbn [outside fst snd] in HoutWS. destruct HoutWS as (HwinSh & _).
    clear Hout outapp Rsp _Rsp HSM Hoff HA HS16 ST0 MI0 AC0 SR0 HHM HAE AW0 FP0 TLS0
      Rp Rb Ro HP HN HO AP ANB AO AJ1 AJ2 NDJ HMS HMC HBD HDH HNF.
    apply fl_out_app.
    - (* outside (Wf sp FS fr j n) x *)
      unfold Wf. cbn [outside fst snd].
      destruct HK as [(Ef & Efr & Espc & Ej & En) | (Hj & Efr & Ef & Espc & Ew & En)].
      + (* real-stack frame: fr = A - 64, j = 0, n = 0 *)
        subst fr j n.
        assert (Esh : shadow_addr (A - 64) + 8 = shadow_addr A)
          by (unfold shadow_addr; Z.div_mod_to_equations; lia).
        assert (G1 : shadow_addr (bv_unsigned sp - 4272) <= shadow_addr (A - 64))
          by (apply acl_sh_ge; lia).
        assert (G2 : shadow_addr A <= shadow_addr (bv_unsigned sp)) by (apply acl_sh_ge; lia).
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|exact I].
      + (* side-stack frame: fr = fs_frame FS 0 j, n = 1 *)
        subst fr n.
        change (fs_M 0) with 16384 in Hj.
        assert (Efrv : fs_frame FS 0 j = FS + 36864 + j * 64)
          by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
        assert (Esh : shadow_addr (fs_frame FS 0 j) + 8 = shadow_addr (fs_frame FS 0 j + 64))
          by (unfold shadow_addr; Z.div_mod_to_equations; lia).
        assert (G1 : shadow_addr (FS + 36864) <= shadow_addr (fs_frame FS 0 j))
          by (apply acl_sh_ge; lia).
        assert (G2 : shadow_addr (fs_frame FS 0 j + 64) <= shadow_addr (FS + 1085440))
          by (apply acl_sh_ge; lia).
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|exact I].
    - (* outside the o-tail x *)
      destruct ((p =? 0) || (o =? 0)) eqn:Epo; cbn [outside fst snd]; [exact I|].
      apply orb_false_iff in Epo. destruct Epo as (Ep & Eo).
      split; [|exact I]. rewrite Eo in HoutO. cbn [outside fst snd] in HoutO.
      destruct HoutO as (HoW & _). exact HoW.
  Qed.

  (* PERF: the heavy section hypotheses, cleared before lia / Z.div_mod_to_equations. *)
  Ltac clr := try clear HSM; try clear HA; try clear ST0; try clear MI0; try clear AC0; try clear SR0;
    try clear AW0; try clear FP0; try clear TLS0; try clear HP; try clear HN; try clear HO; try clear AP;
    try clear ANB; try clear AO; try clear AJ1; try clear AJ2; try clear NDJ; try clear HMS; try clear HMC;
    try clear HBD; try clear HDH; try clear HNF.

  Lemma app_rng : forall X n, 0 < n -> (forall i, 0 <= i < n -> app_mem (X + i)) ->
    X + n <= 2147450880 \/ 17594333495296 <= X.
  Proof.
    intros X n Hn H. pose proof (H 0 ltac:(lia)) as H0. pose proof (H (n - 1) ltac:(lia)) as H1.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H0, H1.
    destruct (Z.le_gt_cases (X + n) 2147450880) as [L|L]; [left; exact L|].
    destruct (Z.le_gt_cases 17594333495296 X) as [G|G]; [right; exact G|].
    exfalso. pose proof (H (2147450880 - X) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H2. clr. lia.
  Qed.

  (* The fine footprint without o lies inside the window and reac_box_model_block_X: the post's munch of the early
     return (p = 0 or o = 0). *)
  Lemma sub_wf : forall fr f spc j n w56, FK FS A fr f spc j n w56 ->
    sub_fp (Wf sp FS fr j n)
      ([(bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K, bv_unsigned sp)] ++ reac_box_model_block_X (bv_unsigned sp) FS).
  Proof.
    intros fr f spc j n w56 HK x Hout.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    assert (outapp : forall (W1 W2 : list ivl) y, outside (W1 ++ W2) y -> outside W1 y /\ outside W2 y).
    { induction W1 as [|[lo hi] W1 IH]; intros W2 y H; cbn [app outside] in *; [split; [exact I | exact H]|].
      destruct H as [H1 H2]. destruct (IH W2 y H2) as [H3 H4]. split; [split; [exact H1 | exact H3]|exact H4]. }
    pose proof (HA1 sp A HA HS16) as HAb.
    assert (EH0 : fs_hint FS 0 = FS) by (unfold fs_hint; cbn [Z.of_nat]; lia).
    assert (EF0 : fs_flag FS 0 0 = FS + 4096) by (unfold fs_flag; cbn [Z.of_nat]; lia).
    assert (EM0 : fs_M 0 = 16384) by reflexivity.
    assert (EFR0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (EFMf : fs_frame FS 0 (fs_M 0) = FS + 1085440).
    { unfold fs_frame, fs_B, fs_M.
      replace (2 ^ (14 - Z.of_nat 0) * (64 * 2 ^ Z.of_nat 0)) with 1048576 by reflexivity.
      replace (Z.of_nat 0 * 2 ^ 20) with 0 by reflexivity. lia. }
    destruct (outapp _ _ _ Hout) as (HoutW & HoutX).
    unfold REAC_BOX_MODEL_BLOCK_K in HoutW. cbn [outside fst snd] in HoutW. destruct HoutW as (Hwin & _).
    unfold reac_box_model_block_X, REAC_BOX_MODEL_BLOCK_K in HoutX.
    destruct (outapp _ _ _ HoutX) as (HoutFP & HoutWS).
    cbn [fp_w fp_w1 flat_map app outside fst snd] in HoutFP.
    rewrite EFR0, EFMf, EH0, EF0, EM0 in HoutFP.
    destruct HoutFP as (Hhint & Hflag & Hframe & HfrSh & _).
    cbn [outside fst snd] in HoutWS. destruct HoutWS as (HwinSh & _).
    clear Hout outapp. clr.
    unfold Wf. cbn [outside fst snd].
    destruct HK as [(Ef & Efr & Espc & Ej & En) | (Hj & Efr & Ef & Espc & Ew & En)].
    - subst fr j n.
      assert (Esh : shadow_addr (A - 64) + 8 = shadow_addr A)
        by (unfold shadow_addr; Z.div_mod_to_equations; lia).
      assert (G1 : shadow_addr (bv_unsigned sp - 4272) <= shadow_addr (A - 64)) by (apply acl_sh_ge; lia).
      assert (G2 : shadow_addr A <= shadow_addr (bv_unsigned sp)) by (apply acl_sh_ge; lia).
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|exact I].
    - subst fr n.
      change (fs_M 0) with 16384 in Hj.
      assert (Efrv : fs_frame FS 0 j = FS + 36864 + j * 64) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
      assert (EFj : fs_flag FS 0 j = FS + 4096 + j) by (unfold fs_flag; cbn [Z.of_nat]; lia).
      assert (Esh : shadow_addr (fs_frame FS 0 j) + 8 = shadow_addr (fs_frame FS 0 j + 64))
        by (unfold shadow_addr; Z.div_mod_to_equations; lia).
      assert (G1 : shadow_addr (FS + 36864) <= shadow_addr (fs_frame FS 0 j)) by (apply acl_sh_ge; lia).
      assert (G2 : shadow_addr (fs_frame FS 0 j + 64) <= shadow_addr (FS + 1085440)) by (apply acl_sh_ge; lia).
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|exact I].
  Qed.

  (* A shadow byte outside the frame's own shadow is outside the run's fine footprint (every other range of it is
     application memory). *)
  Lemma wf_shadow_out : forall fr f spc j n w56 x,
    FK FS A fr f spc j n w56 -> in_shadow x ->
    ~ (shadow_addr fr <= x < shadow_addr fr + 8) ->
    outside (Wf sp FS fr j n ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)])) x.
  Proof.
    intros fr f spc j n w56 x HK Hx Hnf.
    assert (OA : forall lo hi, (forall a, lo <= a < hi -> app_mem a) -> ~ (lo <= x < hi)).
    { intros lo hi Ha Hin. exact (app_not_shadow x x (Ha x Hin) Hx eq_refl). }
    destruct (fk_facts sp tp m p o FS off A Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 fr f spc j n w56 HK)
      as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HPl & _ & _ & _ & HFSl & HApp & _ & _).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in P4.
    apply fl_out_app.
    - unfold Wf. cbn [outside fst snd].
      split; [apply OA; exact HApp|].
      split; [apply OA; intros a Ha; apply P4; clear -Ha; lia|].
      split.
      { destruct HK as [(Ef & Efr & Espc & Ej & En) | (Hj & Efr & Ef & Espc & Ew & En)].
        - subst n. clear -Hx. lia.
        - subst n. apply OA. intros a Ha. apply P4. change (fs_M 0) with 16384 in Hj.
          unfold fs_flag in Ha. cbn [Z.of_nat] in Ha. clear -Ha Hj. lia. }
      split; [apply OA; intros a Ha; replace a with (fr + (a - fr)) by (clear; lia); apply FAP; clear -Ha; lia|].
      split; [exact Hnf | exact I].
    - destruct ((p =? 0) || (o =? 0)) eqn:Epo; cbn [outside fst snd]; [exact I|].
      split; [|exact I]. apply orb_false_iff in Epo. destruct Epo as (_ & Eo). apply Z.eqb_neq in Eo.
      destruct (AO Eo) as (AOa & _ & _). apply OA. intros a Ha. replace a with (o + (a - o)) by (clear; lia).
      exact (acl_app_in m o 32 (a - o) AOa ltac:(clear -Ha; lia)).
  Qed.

  (* o is apart from every range the class-0 side stack writes. *)
  Lemma o_dj_fs : o <> 0 -> forall lo hi, In (lo, hi) (fp_w [0%nat] FS) -> o + 32 <= lo \/ hi <= o.
  Proof.
    intros Eo lo hi Hin.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDd).
    assert (Hin_o : In (o, o + 32) (reac_box_model_block_D p o)).
    { unfold reac_box_model_block_D. apply in_or_app. right.
      replace (o =? 0) with false by (symmetry; apply Z.eqb_neq; exact Eo). left; reflexivity. }
    unfold fp_dj in HDd. rewrite Forall_forall in HDd. pose proof (HDd _ Hin_o) as H1.
    rewrite Forall_forall in H1. pose proof (H1 _ Hin) as H2. unfold ly_dj in H2. cbn [fst snd] in H2. exact H2.
  Qed.

  (* The window shadow reads 0 at the release: inside the frame's shadow by the stores (real stack), elsewhere by
     munch from m (win_shadow0). *)
  Lemma rel_wsh : forall fr f spc j n w56 (m' : word -> option byte),
    FK FS A fr f spc j n w56 ->
    munch (Wf sp FS fr j n ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)])) m m' ->
    (forall x, shadow_addr fr <= x < shadow_addr fr + 8 ->
       shadow_addr (bv_unsigned sp - 4272) <= x < shadow_addr (bv_unsigned sp) ->
       mrd rsegs m' (wa x) = Some (Z_to_bv 8 0)) ->
    forall i, 0 <= i < 4272 -> mrd rsegs m' (wa (shadow_addr (bv_unsigned sp - 4272 + i))) = Some (Z_to_bv 8 0).
  Proof.
    intros fr f spc j n w56 m' HK MU HZ i Hi.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof (acl_app_in m _ _ i AW0 Hi) as Hap.
    pose proof (rt_app_shadow _ Hap) as Hsx. pose proof (rt_shadow_bound _ Hsx) as Hbd.
    assert (Hm8 : (bv_unsigned sp - 4272) mod 8 = 0) by (clear -HS16 Rsp; Z.div_mod_to_equations; lia).
    assert (Hs8 : bv_unsigned sp mod 8 = 0) by (clear -HS16 Rsp; Z.div_mod_to_equations; lia).
    destruct (Z.le_gt_cases (shadow_addr fr) (shadow_addr (bv_unsigned sp - 4272 + i))) as [L1|L1];
      [destruct (Z.lt_ge_cases (shadow_addr (bv_unsigned sp - 4272 + i)) (shadow_addr fr + 8)) as [L2|L2]|].
    - apply HZ; [lia|].
      apply (proj2 (sh_range (bv_unsigned sp - 4272) (bv_unsigned sp) (bv_unsigned sp - 4272 + i) Hm8 Hs8)). lia.
    - unfold mrd.
      rewrite MU by (rewrite wa_unsigned by lia;
        exact (wf_shadow_out fr f spc j n w56 _ HK Hsx ltac:(lia))).
      exact (win_shadow0 sp m p b o row nb ob HS16 AW0 Rp Rb Ro HP HO i Hi).
    - unfold mrd.
      rewrite MU by (rewrite wa_unsigned by lia;
        exact (wf_shadow_out fr f spc j n w56 _ HK Hsx ltac:(lia))).
      exact (win_shadow0 sp m p b o row nb ob HS16 AW0 Rp Rb Ro HP HO i Hi).
  Qed.

  (* 0x86e74 after the release stores: the post from the fine footprint, the flag readback, the window shadow at 0
     and the output block. *)
  Lemma rel_fin : forall (fr f spc j n : Z) (w56 : word) (m' : word -> option byte) (ret : Z) (h' : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    FK FS A fr f spc j n w56 ->
    ret = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
    munch (Wf sp FS fr j n ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)])) m m' ->
    wmono rsegs m m' -> rd_mono m m' -> mem_inv rsegs m' ->
    rw_cells rsegs m' (bv_unsigned sp + -88) (SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) ->
    bytes_at rsegs m' FS (le8 h') ->
    (n = 1 -> mrd rsegs m' (wa (fs_flag FS 0 j)) = Some (Z_to_bv 8 0)) ->
    (forall i, 0 <= i < 4272 ->
       mrd rsegs m' (wa (shadow_addr (bv_unsigned sp - 4272 + i))) = Some (Z_to_bv 8 0)) ->
    (if (p =? 0) || (o =? 0) then True else bytes_at rsegs m' o (synth row b nb)) ->
    evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 ret) x22 (Z_to_bv 64 fr)
              (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x86e74) fc None m' (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 m' ret h' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31
      HK Er MU WM RM MI SV HH Hfj Hsh HX.
    pose proof (sub_post fr f spc j n w56 HK) as SP.
    destruct (rel_flags sp tp m p b o FS off A row nb ob Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro HP HO
                fr f spc j n w56 m' HK MU Hfj) as (flags' & HF & HL & H01).
    assert (HH0 : bytes_at rsegs m' (fs_hint FS 0) (le8 h'))
      by (replace (fs_hint FS 0) with FS by (unfold fs_hint; cbn [Z.of_nat]; lia); exact HH).
    apply (epi0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A row nb Rp Rb Ro HP
             ret m' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 spc fr f Er SV WM MI).
    - exact (stk_mono m m' _ _ ST0 WM RM).
    - exact (br_ac sp tp m p b o FS row nb ob AC0 HHM HAE FP0 Rp Rb Ro HP HO AO _ m' MU SP).
    - exact (shadow_rw_mono m m' SR0 WM RM).
    - exact (addr_rebuild m' Hsh).
    - exact (br_fp sp tp m p o FS HHM HAE FP0 TLS0 _ m' h' flags' MU WM RM SP HH0 HF HL H01).
    - unfold reac_box_model_block_X in SP.
      exact (acl_tls_ret [0%nat] m m' (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
               (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o)
               [(shadow_addr (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K), shadow_addr (bv_unsigned sp))] _
               FP0 TLS0 MU SP).
    - revert MU HX SP. destruct ((p =? 0) || (o =? 0)) eqn:Epo; intros MU HX SP.
      + rewrite app_nil_r in MU. exact (munch_weaken _ _ m m' (sub_wf fr f spc j n w56 HK) MU).
      + split; [exact HX|].
        apply orb_false_iff in Epo. destruct Epo as (_ & Eo).
        unfold reac_box_model_block_W in SP. rewrite Eo in SP.
        exact (munch_weaken _ _ m m' SP MU).
  Qed.

  Ltac cell_of_bytes bs ::=
    lazymatch bs with
    | le8 ?v => constr:(C8 v)
    | le4 ?v => constr:(C4 v)
    | le2 ?v => constr:(C2 v)
    | [?b] => constr:(C1 b)
    | le1 (zxb ?b) => constr:(C1 b)
    | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
    end.

  (* 0x86e14 -> 0x86e74: the magic word at the frame, the frame's shadow (0 on the real stack, 0xf5 on the side
     stack) and, on the side stack, the flag byte back to 0. Every store is inside Wf, so the tail C of the
     footprint is untouched and the caller carries its own facts about it over the local munch. *)
  Lemma rel_run : forall (C : list ivl) (fr f spc j n : Z) (w56 : word) (mc : word -> option byte) (ret : Z)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ C) fr w56 mc ->
    (forall (m' : word -> option byte) (h' x10' : word),
       munch (Wf sp FS fr j n ++ C) m m' -> munch (Wf sp FS fr j n) mc m' ->
       wmono rsegs m m' -> rd_mono m m' -> mem_inv rsegs m' ->
       rw_cells rsegs m' (bv_unsigned sp + -88) (SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) ->
       bytes_at rsegs m' FS (le8 h') ->
       (n = 1 -> mrd rsegs m' (wa (fs_flag FS 0 j)) = Some (Z_to_bv 8 0)) ->
       (forall x, shadow_addr fr <= x < shadow_addr fr + 8 ->
          shadow_addr (bv_unsigned sp - 4272) <= x < shadow_addr (bv_unsigned sp) ->
          mrd rsegs m' (wa x) = Some (Z_to_bv 8 0)) ->
       evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
         (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10' x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 ret) x22 (Z_to_bv 64 fr)
                 (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
               F (Z_to_bv 64 0x86e74) fc None m' (seg_rom rsegs))) ->
    evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 ret) x22 (Z_to_bv 64 fr)
              (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x86e14) fc None mc (seg_rom rsegs)).
  Proof.
    intros C fr f spc j n w56 mc ret x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 HK HB K.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof (HA1 sp A HA HS16) as HAb.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (fk_facts sp tp m p o FS off A Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 fr f spc j n w56 HK)
      as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    rewrite Hoff in SH1, SH2. unfold ASAN_K in SH1, SH2.
    pose proof FP0 as (DT & TS & Cw & T & DB & k & _ & _ & HPl & _ & _ & _ & HFSl & _ & _ & HDd).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFSl, P4, P5. unfold ASAN_GT in P3.
    pose proof (app_rng FS 11571200 ltac:(lia) ltac:(intros i Hi; apply P4; lia)) as FSA.
    destruct HB as (MU & WM & RM & MI & SV & (h & HH) & F56).
    pose proof (shadow_rw_mono m mc SR0 WM RM) as SRc.
    assert (SHin : forall i, 0 <= i < 8 -> in_shadow (fr / 8 + 2147450880 + i)).
    { intros i Hi. replace (fr / 8 + 2147450880 + i) with (shadow_addr (fr + 8 * i))
        by (rewrite sh_add8 by exact FR8; unfold shadow_addr, ASAN_K; lia).
      apply rt_app_shadow. apply FAP. lia. }
    rewrite Hoff. unfold ASAN_K.
    destruct HK as [(Ef & Efr & Espc & Ej & En) | (Hj & Efr & Ef & Espc & Ew & En)].
    - (* the real-stack frame [A - 64, A) *)
      subst f fr spc j n.
      unfold Wf, shadow_addr, ASAN_K in MU. cbn [app] in MU.
      pose proof (munch_refl (Wf sp FS (A - 64) 0 0) mc) as MU2.
      unfold Wf, shadow_addr, ASAN_K in MU2.
      destruct (sh_cells mc ((A - 64) / 8 + 2147450880) SRc SHin) as (w & CS).
      assert (HS : store_ok rsegs mc (wa (A - 64)) 8 = true)
        by (eapply wv_store_ok; [intros i Hi; apply (stk_wv m _ _ _ ST0); lia | exact WM | lia | lia]).
      clear HSM HA ST0 MI0 AC0 SR0 AW0 FP0 TLS0 HP HN HO AP ANB AO AJ1 AJ2 NDJ HMS HMC HBD HDH HNF
        SRc SHin FW FAP SW Fsp FRA HPl P4 P5 HDd Rp Rb Ro.
      do 3 step. store_done. step. nt. do 8 step.
      pose proof (proj2 (proj1 CS)) as CB0.
      lazymatch type of CB0 with
      | bytes_at _ _ _ ?L =>
          assert (ECB : L = repeat (Z_to_bv 8 0) 8) by (vm_compute; reflexivity); rewrite ECB in CB0
      end.
      first [fold ASAN_K | change 2147450880 with ASAN_K]. rewrite <- Hoff.
      apply (K _ h _ MU MU2 WM RM MI SV HH ltac:(intros Hn1; exfalso; lia)).
      intros xx Hx1 Hx2. unfold shadow_addr, ASAN_K in Hx1.
      destruct CB0 as (B1 & B2 & B3).
      pose proof (B3 (Z.to_nat (xx - ((A - 64) / 8 + 2147450880)))
                    ltac:(rewrite repeat_length; lia)) as B4.
      replace ((A - 64) / 8 + 2147450880 + Z.of_nat (Z.to_nat (xx - ((A - 64) / 8 + 2147450880))))
        with xx in B4 by lia.
      rewrite B4. apply nth_rep0. lia.
    - (* a class-0 side-stack frame *)
      subst fr f spc n w56.
      change (fs_M 0) with 16384 in Hj.
      assert (EFRj : fs_frame FS 0 j = FS + 36864 + j * 64) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
      assert (EFJj : fs_flag FS 0 j = FS + 4096 + j) by (unfold fs_flag; cbn [Z.of_nat]; lia).
      assert (GSH : shadow_addr (fs_frame FS 0 j) + 8 <= shadow_addr (bv_unsigned sp - 4272)).
      { replace (shadow_addr (fs_frame FS 0 j) + 8) with (shadow_addr (fs_frame FS 0 j + 64))
          by (unfold shadow_addr; clr; Z.div_mod_to_equations; lia).
        apply acl_sh_ge. lia. }
      unfold Wf, shadow_addr, ASAN_K in MU. cbn [app] in MU.
      pose proof (munch_refl (Wf sp FS (fs_frame FS 0 j) j 1) mc) as MU2.
      unfold Wf, shadow_addr, ASAN_K in MU2.
      destruct (sh_cells mc (fs_frame FS 0 j / 8 + 2147450880) SRc SHin) as (w & CS).
      pose proof (stk_mono m mc _ _ P5 WM RM) as STF.
      destruct (proj2 (proj2 STF) (fs_flag FS 0 j) ltac:(lia)) as (FLw & vfl & FLr). clear STF.
      pose proof (rw1 mc (fs_flag FS 0 j) vfl ltac:(lia) ltac:(lia) FLw FLr) as FL.
      apply bytes_ro8 in F56.
      assert (HS : store_ok rsegs mc (wa (fs_frame FS 0 j)) 8 = true)
        by (eapply wv_store_ok; [intros i Hi; apply FW; lia | exact WM | lia | lia]).
      clear HSM HA ST0 MI0 AC0 SR0 AW0 FP0 TLS0 HP HN HO AP ANB AO AJ1 AJ2 NDJ HMS HMC HBD HDH HNF
        SRc SHin FW FAP SW Fsp FRA HPl P4 P5 HDd Rp Rb Ro FLw FLr.
      do 3 step. store_done. step. nf. do 12 step.
      pose proof (proj2 (proj1 FL)) as FB.
      lazymatch type of FB with
      | bytes_at _ _ _ ?L =>
          assert (EFB : L = [Z_to_bv 8 0]) by (vm_compute; reflexivity); rewrite EFB in FB
      end.
      destruct FB as (B1 & B2 & B3).
      pose proof (B3 0%nat ltac:(cbn [length]; lia)) as B4. cbn [nth_error Z.of_nat] in B4.
      rewrite Z.add_0_r in B4.
      first [fold ASAN_K | change 2147450880 with ASAN_K]. rewrite <- Hoff.
      apply (K _ h _ MU MU2 WM RM MI SV HH ltac:(intros _; exact B4)).
      intros xx Hx1 Hx2. exfalso. lia.
  Qed.

  (* 0x86e14 -> Q0: the interface pin's rel_stmt. *)
  Lemma rel : forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte) (ret : Z)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    FK FS A fr f spc j n w56 ->
    ret = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS
       (Wf sp FS fr j n ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)])) fr w56 mc ->
    (if (p =? 0) || (o =? 0) then True else bytes_at rsegs mc o (synth row b nb)) ->
    evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 ret) x22 (Z_to_bv 64 fr)
              (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x86e14) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc ret x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 HK Er HB HX.
    apply (rel_run _ fr f spc j n w56 mc ret x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31
             HK HB).
    intros m' h' x10' MU MU2 WM RM MI SV HH Hfj WSH.
    apply (rel_fin fr f spc j n w56 m' ret h' x1 x5 x6 x7 x10' x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31
             HK Er MU WM RM MI SV HH Hfj (rel_wsh fr f spc j n w56 m' HK MU WSH)).
    (* the output block, carried from mc past the release stores *)
    revert HX. destruct ((p =? 0) || (o =? 0)) eqn:Epo; intros HX; [exact HX|].
    assert (Eo : o <> 0)
      by (apply orb_false_iff in Epo; destruct Epo as (_ & E); apply Z.eqb_neq in E; exact E).
    assert (Ep : p <> 0)
      by (apply orb_false_iff in Epo; destruct Epo as (E & _); apply Z.eqb_neq in E; exact E).
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof (HA1 sp A HA HS16) as HAb.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (fk_facts sp tp m p o FS off A Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 fr f spc j n w56 HK)
      as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    rewrite Hoff in SH1, SH2. unfold ASAN_K in SH1, SH2.
    pose proof FP0 as (DT & TS & Cw & T & DB & k & _ & _ & HPl & _ & _ & _ & HFSl & _ & _ & HDd).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFSl, P4, P5. unfold ASAN_GT in P3.
    destruct (HP Ep) as (_ & Hlen & _ & _ & _).
    destruct (HO Eo) as (HOC & HOS & HOJ). destruct (AO Eo) as (AOa & AOe & AOr).
    pose proof (app_rng o 32 ltac:(lia) ltac:(intros i Hi; exact (acl_app_in m o 32 i AOa Hi))) as OAR.
    assert (EH0 : fs_hint FS 0 = FS) by (unfold fs_hint; cbn [Z.of_nat]; lia).
    assert (EF0 : fs_flag FS 0 0 = FS + 4096) by (unfold fs_flag; cbn [Z.of_nat]; lia).
    assert (EM0 : fs_M 0 = 16384) by reflexivity.
    assert (EFR0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (EFMf : fs_frame FS 0 (fs_M 0) = FS + 1085440).
    { unfold fs_frame, fs_B, fs_M.
      replace (2 ^ (14 - Z.of_nat 0) * (64 * 2 ^ Z.of_nat 0)) with 1048576 by reflexivity.
      replace (Z.of_nat 0 * 2 ^ 20) with 0 by reflexivity. lia. }
    assert (ODJ0 : o + 32 <= fs_hint FS 0 \/ fs_hint FS 0 + 8 <= o)
      by (apply (o_dj_fs Eo); unfold fp_w, fp_w1; cbn [flat_map app]; left; reflexivity).
    assert (ODJ1 : o + 32 <= fs_flag FS 0 0 \/ fs_flag FS 0 0 + fs_M 0 <= o)
      by (apply (o_dj_fs Eo); unfold fp_w, fp_w1; cbn [flat_map app]; right; left; reflexivity).
    assert (ODJ2 : o + 32 <= fs_frame FS 0 0 \/ fs_frame FS 0 (fs_M 0) <= o)
      by (apply (o_dj_fs Eo); unfold fp_w, fp_w1; cbn [flat_map app]; right; right; left; reflexivity).
    rewrite EH0 in ODJ0. rewrite EF0, EM0 in ODJ1. rewrite EFR0, EFMf in ODJ2.
    apply (fl_bytes _ mc m' _ _ HX MU2).
    intros xx Hxx. rewrite (rs_synth_len row b nb Hlen) in Hxx.
    unfold Wf. cbn [outside fst snd].
    destruct HK as [(Ef & Efr & Espc & Ej & En) | (Hj & Efr & Ef & Espc & Ew & En)].
    - subst j n.
      split; [clr; lia|]. split; [clr; lia|]. split; [clr; lia|]. split; [clr; lia|].
      split; [clr; unfold shadow_addr, ASAN_K; lia | exact I].
    - subst n. change (fs_M 0) with 16384 in Hj.
      assert (EFRj : fs_frame FS 0 j = FS + 36864 + j * 64) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
      assert (EFJj : fs_flag FS 0 j = FS + 4096 + j) by (unfold fs_flag; cbn [Z.of_nat]; lia).
      split; [clr; lia|]. split; [clr; lia|]. split; [clr; lia|]. split; [clr; lia|].
      split; [clr; unfold shadow_addr, ASAN_K; lia | exact I].
  Qed.

  (* The output block is apart from everything the frame release writes. *)
  Lemma o_out_wf : o <> 0 -> forall fr f spc j n w56, FK FS A fr f spc j n w56 ->
    disjoint_from (Wf sp FS fr j n) o 32.
  Proof.
    intros Eo fr f spc j n w56 HK.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof (HA1 sp A HA HS16) as HAb.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (fk_facts sp tp m p o FS off A Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 fr f spc j n w56 HK)
      as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    rewrite Hoff in SH1, SH2. unfold ASAN_K in SH1, SH2.
    pose proof FP0 as (DT & TS & Cw & T & DB & k & _ & _ & HPl & _ & _ & _ & HFSl & _ & _ & HDd).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFSl, P4, P5. unfold ASAN_GT in P3.
    destruct (HO Eo) as (HOC & HOS & HOJ). destruct (AO Eo) as (AOa & AOe & AOr).
    pose proof (app_rng o 32 ltac:(lia) ltac:(intros i Hi; exact (acl_app_in m o 32 i AOa Hi))) as OAR.
    assert (EH0 : fs_hint FS 0 = FS) by (unfold fs_hint; cbn [Z.of_nat]; lia).
    assert (EF0 : fs_flag FS 0 0 = FS + 4096) by (unfold fs_flag; cbn [Z.of_nat]; lia).
    assert (EM0 : fs_M 0 = 16384) by reflexivity.
    assert (EFR0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (EFMf : fs_frame FS 0 (fs_M 0) = FS + 1085440).
    { unfold fs_frame, fs_B, fs_M.
      replace (2 ^ (14 - Z.of_nat 0) * (64 * 2 ^ Z.of_nat 0)) with 1048576 by reflexivity.
      replace (Z.of_nat 0 * 2 ^ 20) with 0 by reflexivity. lia. }
    assert (ODJ0 : o + 32 <= fs_hint FS 0 \/ fs_hint FS 0 + 8 <= o)
      by (apply (o_dj_fs Eo); unfold fp_w, fp_w1; cbn [flat_map app]; left; reflexivity).
    assert (ODJ1 : o + 32 <= fs_flag FS 0 0 \/ fs_flag FS 0 0 + fs_M 0 <= o)
      by (apply (o_dj_fs Eo); unfold fp_w, fp_w1; cbn [flat_map app]; right; left; reflexivity).
    assert (ODJ2 : o + 32 <= fs_frame FS 0 0 \/ fs_frame FS 0 (fs_M 0) <= o)
      by (apply (o_dj_fs Eo); unfold fp_w, fp_w1; cbn [flat_map app]; right; right; left; reflexivity).
    rewrite EH0 in ODJ0. rewrite EF0, EM0 in ODJ1. rewrite EFR0, EFMf in ODJ2.
    unfold Wf. cbn [disjoint_from fst snd].
    destruct HK as [(Ef & Efr & Espc & Ej & En) | (Hj & Efr & Ef & Espc & Ew & En)].
    - subst j n.
      split; [clr; lia|]. split; [clr; lia|]. split; [clr; lia|]. split; [clr; lia|].
      split; [clr; unfold shadow_addr, ASAN_K; lia | exact I].
    - subst n. change (fs_M 0) with 16384 in Hj.
      assert (EFRj : fs_frame FS 0 j = FS + 36864 + j * 64) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
      assert (EFJj : fs_flag FS 0 j = FS + 4096 + j) by (unfold fs_flag; cbn [Z.of_nat]; lia).
      split; [clr; lia|]. split; [clr; lia|]. split; [clr; lia|]. split; [clr; lia|].
      split; [clr; unfold shadow_addr, ASAN_K; lia | exact I].
  Qed.

  (* ... and so are its shadow bytes. *)
  Lemma o_sh_out_wf : o <> 0 -> forall fr f spc j n w56, FK FS A fr f spc j n w56 ->
    forall i, 0 <= i < 32 -> outside (Wf sp FS fr j n) (shadow_addr (o + i)).
  Proof.
    intros Eo fr f spc j n w56 HK i Hi.
    destruct (AO Eo) as (AOa & _ & _).
    pose proof (acl_app_in m o 32 i AOa Hi) as Hap.
    pose proof (rt_app_shadow _ Hap) as Hsh.
    pose proof (disjoint_outside _ _ _ (o + i) (o_out_wf Eo fr f spc j n w56 HK) ltac:(lia)) as OW.
    unfold Wf in OW. cbn [outside fst snd] in OW. destruct OW as (_ & _ & _ & OW4 & _).
    destruct (fk_facts sp tp m p o FS off A Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 fr f spc j n w56 HK)
      as (FR8 & _ & _ & _ & _ & _ & _ & _ & _ & _).
    assert (Hnf : ~ (shadow_addr fr <= shadow_addr (o + i) < shadow_addr fr + 8))
      by (intros Hin; exact (OW4 (proj1 (sh_range8 fr (o + i) FR8) Hin))).
    exact (out_app_l _ _ _ (wf_shadow_out fr f spc j n w56 _ HK Hsh Hnf)).
  Qed.

  (* The shape of the seven case lemmas: the case PC the jump table selects, with the output block memset to 0. *)
  Definition case_stmt (K pc : Z) : Prop :=
    forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
      b = K -> p <> 0 -> o <> 0 ->
      FK FS A fr f spc j n w56 ->
      BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 mc ->
      rw_cells rsegs mc o [CB 32 (zeros 32)] ->
      evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
        (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
                (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr)
                (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 pc) fc None mc (seg_rom rsegs)).

  (* 0x866d4 -> the case lemmas: the early returns (p = 0, o = 0, 6 < b), the checked memset of the output block
     and the jump table at 0x219f4. *)
  Lemma disp :
    case_stmt 0 0x86714 -> case_stmt 1 0x86a44 -> case_stmt 2 0x869fc -> case_stmt 3 0x86a08 ->
    case_stmt 4 0x8691c -> case_stmt 5 0x86a5c -> case_stmt 6 0x86b24 ->
    KB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A
      (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb).
  Proof.
    intros Hc0 Hc1 Hc2 Hc3 Hc4 Hc5 Hc6.
    intros fr f spc j n w56 mc t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HK HB.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof (HA1 sp A HA HS16) as HAb.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (fk_facts sp tp m p o FS off A Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 fr f spc j n w56 HK)
      as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof FP0 as (DT & TS & Cw & T & DB & k & _ & _ & HPl & _ & _ & _ & HFSl & _ & _ & HDd).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFSl, P4, P5. unfold ASAN_GT in P3.
    pose proof HB as HB1. destruct HB1 as (MU & WM & RM & MI & SV & (h & HH) & F56).
    assert (Fspc : bv_unsigned sp - 240 <= spc /\ spc <= bv_unsigned sp - 160)
      by (destruct HK as [(Ef & Efr & Espc & Ej & En) | (Hj & Efr & Ef & Espc & Ew & En)];
          rewrite Espc; clr; lia).
    step.
    try (match goal with
         | |- context [Z_to_bv 64 18446744073709551615] =>
             replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (-1))
               by (apply bv_eq; vm_compute; reflexivity)
         end).
    step.
    (* p = 0: the early return *)
    destruct (Z.eq_dec p 0) as [Ep0|Ep0].
    { assert (Ecnd : (p =? 0) || (o =? 0) = true)
        by (apply orb_true_iff; left; apply Z.eqb_eq; exact Ep0).
      nt. eapply rel; [exact HK | rewrite Ecnd; reflexivity | rewrite Ecnd; exact HB | rewrite Ecnd; exact I]. }
    nf. step.
    (* o = 0: the early return *)
    destruct (Z.eq_dec o 0) as [Eo0|Eo0].
    { assert (Ecnd : (p =? 0) || (o =? 0) = true)
        by (apply orb_true_iff; right; apply Z.eqb_eq; exact Eo0).
      nt. eapply rel; [exact HK | rewrite Ecnd; reflexivity | rewrite Ecnd; exact HB | rewrite Ecnd; exact I]. }
    nf.
    assert (Ecnd : (p =? 0) || (o =? 0) = false)
      by (apply orb_false_iff; split; apply Z.eqb_neq; assumption).
    destruct (HO Eo0) as (HOC & HOS & HOJ). destruct (AO Eo0) as (AOa & AOe & AOr).
    (* the output block and the runtime state at mc *)
    pose proof (o_out_wf Eo0 fr f spc j n w56 HK) as ODJ.
    pose proof (o_sh_out_wf Eo0 fr f spc j n w56 HK) as OUTS.
    assert (OC : rw_cells rsegs mc o [CB 32 ob])
      by (eapply rw_cells_transport; [exact HOC | exact MU | exact WM | exact ODJ]).
    assert (OADD : addressable mc o 32)
      by (eapply addr_munch; [exact AOa | exact MU | exact OUTS]).
    pose proof (stk_mono m mc _ _ ST0 WM RM) as STc0.
    destruct (stk_split rsegs mc (bv_unsigned sp - 4272) spc (bv_unsigned sp) STc0 ltac:(lia)) as (STc & _).
    pose proof (shadow_rw_mono m mc SR0 WM RM) as SRc.
    pose proof (sub_post fr f spc j n w56 HK) as SP. rewrite Ecnd in SP.
    assert (ACc : asan_cells mc)
      by (exact (br_ac sp tp m p b o FS row nb ob AC0 HHM HAE FP0 Rp Rb Ro HP HO AO _ mc MU
                   (fun x Hx => out_app_l _ _ _ (SP x Hx)))).
    assert (Uo : bv_unsigned (Z_to_bv 64 o) = o) by (apply unsigned_lit; lia).
    assert (Uspc : bv_unsigned (Z_to_bv 64 spc) = spc) by (apply unsigned_lit; clr; lia).
    do 4 step.
    eapply evt_cut.
    { eapply HMS with (junk := ob) (lo := bv_unsigned sp - 4272);
        change (bv_unsigned (Z_to_bv 64 32)) with 32; rewrite ?Uo, ?Uspc;
        unfold ASAN_MEMSET_K.
      - exact OC.
      - lia.
      - exact OADD.
      - right. exact AOe.
      - right. exact (acl_app_in m o 32 7 AOa ltac:(lia)).
      - exact AOr.
      - clr; lia.
      - exact STc.
      - clr; lia.
      - exact HHM.
      - clr; lia.
      - exact ACc.
      - exact SRc.
      - exact MI. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & m2 & E & MU2 & WM2
                    & MI2 & ST2 & RW2 & AC2 & SR2).
    subst ms'.
    change (bv_unsigned (Z_to_bv 64 32)) with 32 in MU2, RW2.
    rewrite Uo, Uspc in MU2. rewrite Uspc in ST2. rewrite Uo in RW2. unfold ASAN_MEMSET_K in MU2.
    change (Z.to_nat 32) with 32%nat in RW2.
    change (repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) 32) with (zeros 32) in RW2.
    replace (ret_pc (Z_to_bv 64 0x866f0)) with (Z_to_bv 64 0x866f0)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    (* the body invariant at m2 *)
    assert (RM2 : rd_mono mc m2).
    { apply (rd_mono_list _ _ _ MU2). repeat constructor; cbn [fst snd]; intros y Hy.
      - apply (rd_of_bytes _ _ _ (mb_rw1 _ _ _ _ _ RW2)). unfold zeros. rewrite repeat_length. lia.
      - apply (rd_of_stk _ _ _ ST2). clr; lia. }
    assert (MU3 : munch (Wf sp FS fr j n ++ [(o, o + 32)]) m m2).
    { apply (munch_trans _ m mc m2).
      - eapply munch_weaken; [|exact MU]. intros x Hx. exact (out_app_l _ _ _ Hx).
      - eapply munch_weaken; [|exact MU2]. intros x Hx.
        pose proof (out_app_l _ _ _ Hx) as HxW. pose proof (out_app_r _ _ _ Hx) as HxO.
        unfold Wf in HxW. cbn [outside fst snd] in HxW. destruct HxW as (Hw & _).
        cbn [outside fst snd] in HxO. destruct HxO as (Ho & _).
        cbn [outside fst snd]. split; [exact Ho|]. split; [clr; lia | exact I]. }
    pose proof ODJ as ODJ'. unfold Wf in ODJ'. cbn [disjoint_from fst snd] in ODJ'.
    assert (Ffr : spc = fr \/ fr + 64 <= bv_unsigned sp - 4272)
      by (destruct HK as [(Ef & Efr & Espc & Ej & En) | (Hj & Efr & Ef & Espc & Ew & En)];
          [left; lia | right; rewrite Efr; change (fs_M 0) with 16384 in Hj;
           unfold fs_frame, fs_B; cbn [Z.of_nat]; clr; lia]).
    assert (BI2 : BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 m2).
    { split; [exact MU3|]. split; [exact (wmono_trans rsegs _ _ _ WM WM2)|].
      split; [exact (rd_mono_trans _ _ _ RM RM2)|]. split; [exact MI2|].
      split.
      { eapply rw_cells_transport; [exact SV | exact MU2 | exact WM2 |].
        cbn [disjoint_from fst snd cells_size csize SAVES Nat.add]. repeat split; try exact I; clr; lia. }
      split.
      { exists h. eapply bytes_at_transport; [exact HH | exact MU2 |].
        rewrite length_le8. cbn [disjoint_from fst snd]. repeat split; try exact I; clr; lia. }
      eapply bytes_at_transport; [exact F56 | exact MU2 |].
      rewrite length_le8. cbn [disjoint_from fst snd]. repeat split; try exact I; clr; lia. }
    do 2 step.
    (* 6 < b: the unknown kind returns -1 with the block left at zero *)
    destruct (Z.lt_ge_cases 6 b) as [Bgt|Ble].
    { nt.
      assert (Erc : rc row b = -1)
        by (unfold rc; replace (6 <? b) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
      assert (Esy : synth row b nb = zeros 32)
        by (unfold synth; replace (6 <? b) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
      eapply rel; [exact HK | rewrite Ecnd, Erc; reflexivity | rewrite Ecnd; exact BI2 |].
      rewrite Ecnd, Esy. exact (mb_rw1 _ _ _ _ _ RW2). }
    nf.
    assert (Bk : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6) by (clr; lia).
    destruct Bk as [Bk|[Bk|[Bk|[Bk|[Bk|[Bk|Bk]]]]]];
      rewrite (mb_word (Z_to_bv 64 b) _ ltac:(rewrite unsigned_lit by lia; exact Bk));
      do 7 step;
      [ eapply Hc0 | eapply Hc1 | eapply Hc2 | eapply Hc3 | eapply Hc4 | eapply Hc5 | eapply Hc6 ];
      first [exact Bk | exact Ep0 | exact Eo0 | exact HK | exact BI2 | exact RW2].
  Qed.
End Body.
