(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 687 of its 711 lines of code are new or changed and 224 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block_body.v, with its addresses changed; 228 of its 373 lines of code are new or changed and 566 lines of the source are left out. *)
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

(* Cases b = 1 and b = 2 of the body of reac_box_model_block, image B (asan-ubsan): the 32 image bytes at JOIN_0014
   (b = 1, case PC 0x86a44) or JOIN_0013 (b = 2, case PC 0x869fc) are copied into o by checked_memcpy (0x52164), s5 = 1,
   then the frame release at 0x86e14. The release is the hypothesis Hrel (its type is rel_stmt of the interface pin);
   reac_box_model_block_body.v proves it and applies these lemmas. *)

(* A shadow address is apart from an interval of application memory. *)
Lemma c12_sh_app : forall lo hi z, (forall y, lo <= y < hi -> app_mem y) -> in_shadow z -> ~ (lo <= z < hi).
Proof. intros lo hi z H Hz Hr. exact (acl_app_not_shadow z (H z Hr) Hz). Qed.

(* The shadow byte of an application byte x outside the window [S - 4272, S) and outside the class-0 frames is outside
   the post's write set reac_box_model_block_W ++ reac_box_model_block_X. *)
Lemma c12_sh_out : forall S FS o x,
  (forall a, S - 4272 <= a < S -> app_mem a) -> (forall a, FS <= a < FS + FS_SIZE -> app_mem a) ->
  FS mod 4096 = 0 -> S mod 16 = 0 -> (o <> 0 -> forall y, o <= y < o + 32 -> app_mem y) ->
  app_mem x -> ~ (S - 4272 <= x < S) -> ~ (FS + 36864 <= x < FS + 1085440) ->
  outside (reac_box_model_block_W o S ++ reac_box_model_block_X S FS) (shadow_addr x).
Proof.
  intros S FS o x HW HF HF8 HS8 HO Hx Hw Hf.
  pose proof (rt_app_shadow x Hx) as Hsx.
  assert (EH0 : fs_hint FS 0 = FS) by (unfold fs_hint; cbn [Z.of_nat]; lia).
  assert (EF0 : fs_flag FS 0 0 = FS + 4096) by (unfold fs_flag; cbn [Z.of_nat]; lia).
  assert (EFR0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
  assert (EFMf : fs_frame FS 0 (fs_M 0) = FS + 1085440).
  { unfold fs_frame, fs_B, fs_M.
    replace (2 ^ (14 - Z.of_nat 0) * (64 * 2 ^ Z.of_nat 0)) with 1048576 by reflexivity.
    replace (Z.of_nat 0 * 2 ^ 20) with 0 by reflexivity. lia. }
  assert (EM0 : fs_M 0 = 16384) by reflexivity.
  unfold FS_SIZE in HF.
  apply fl_out_app.
  - unfold reac_box_model_block_W, REAC_BOX_MODEL_BLOCK_K. cbn [outside]. split.
    + exact (c12_sh_app _ _ _ HW Hsx).
    + destruct (Z.eqb_spec o 0) as [Eo|Eo]; cbn [outside]; [exact I|].
      split; [exact (c12_sh_app _ _ _ (HO Eo) Hsx) | exact I].
  - unfold reac_box_model_block_X, REAC_BOX_MODEL_BLOCK_K, fp_w, fp_w1. cbn [flat_map app outside].
    rewrite EH0, EF0, EFMf, EFR0, EM0.
    split; [apply c12_sh_app; [intros y Hy; apply HF; lia | exact Hsx]|].
    split; [apply c12_sh_app; [intros y Hy; apply HF; lia | exact Hsx]|].
    split; [apply c12_sh_app; [intros y Hy; apply HF; lia | exact Hsx]|].
    split; [exact (acl_win_sh x (FS + 36864) (FS + 1085440) ltac:(Z.div_mod_to_equations; lia) Hf)|].
    split; [exact (acl_win_sh x (S - 4272) S ltac:(Z.div_mod_to_equations; lia) Hw) | exact I].
Qed.

(* The two source blocks lie in low application memory, below the side stack. *)
Lemma c12_j14 : 0 <= JOIN_0014 /\ JOIN_0014 + 32 <= ASAN_GT.
Proof. unfold JOIN_0014, ASAN_GT. lia. Qed.
Lemma c12_j13 : 0 <= JOIN_0013 /\ JOIN_0013 + 32 <= ASAN_GT.
Proof. unfold JOIN_0013, ASAN_GT. lia. Qed.

Section Case12.
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

  (* The frame release at 0x86e14 (rel_stmt of the interface pin), proved in reac_box_model_block_body.v. *)
  Hypothesis Hrel :
    forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte) (ret : Z)
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

  (* The body's fine footprint lies inside the post's write set (the proof of sub_post in
     reac_box_model_block_body.v; this file cannot import that file, which imports this one). *)
  Lemma c12_sub_post : forall fr f spc j n w56, FK FS A fr f spc j n w56 ->
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
      Rp Rb Ro HP HN HO AP ANB AO AJ1 AJ2 NDJ HMS HMC HBD HDH HNF Hrel.
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

  (* o is apart from the class-0 hint word and from the class-0 frames (fp's D apart from fp_w). *)
  Lemma c12_o_fs : o <> 0 -> (o + 32 <= FS \/ FS + 8 <= o) /\ (o + 32 <= FS + 36864 \/ FS + 1085440 <= o).
  Proof.
    intros Eo.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDd).
    assert (Hin_o : In (o, o + 32) (reac_box_model_block_D p o)).
    { unfold reac_box_model_block_D. apply in_or_app. right. apply Z.eqb_neq in Eo. rewrite Eo. left; reflexivity. }
    assert (Hin_h : In (fs_hint FS 0, fs_hint FS 0 + 8) (fp_w [0%nat] FS)).
    { unfold fp_w, fp_w1. cbn [flat_map app]. left; reflexivity. }
    assert (Hin_f : In (fs_frame FS 0 0, fs_frame FS 0 (fs_M 0)) (fp_w [0%nat] FS)).
    { unfold fp_w, fp_w1. cbn [flat_map app]. right; right; left; reflexivity. }
    unfold fp_dj in HDd. rewrite Forall_forall in HDd. pose proof (HDd _ Hin_o) as HD1.
    rewrite Forall_forall in HD1. pose proof (HD1 _ Hin_h) as HD2. pose proof (HD1 _ Hin_f) as HD3.
    unfold ly_dj in HD2, HD3. cbn [fst snd] in HD2, HD3.
    assert (EH0 : fs_hint FS 0 = FS) by (unfold fs_hint; cbn [Z.of_nat]; lia).
    assert (EFR0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (EFMf : fs_frame FS 0 (fs_M 0) = FS + 1085440).
    { unfold fs_frame, fs_B, fs_M.
      replace (2 ^ (14 - Z.of_nat 0) * (64 * 2 ^ Z.of_nat 0)) with 1048576 by reflexivity.
      replace (Z.of_nat 0 * 2 ^ 20) with 0 by reflexivity. lia. }
    rewrite EH0 in HD2. rewrite EFR0, EFMf in HD3.
    clear - HD2 HD3. split; lia.
  Qed.

  (* The frame of FK: the real one (fr = spc = A - 64) or a class-0 side-stack frame (spc = A). *)
  Lemma c12_fk : forall fr f spc j n w56, FK FS A fr f spc j n w56 ->
    (spc = A - 64 /\ fr = A - 64) \/ (spc = A /\ FS + 36864 <= fr /\ fr + 64 <= FS + 1085440).
  Proof.
    intros fr f spc j n w56 HK.
    destruct HK as [(Ef & Efr & Espc & Ej & En) | (Hj & Efr & Ef & Espc & Ew & En)].
    - left. split; assumption.
    - right. subst fr. change (fs_M 0) with 16384 in Hj.
      assert (Efrv : fs_frame FS 0 j = FS + 36864 + j * 64)
        by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
      rewrite Efrv. clear - Hj Espc. split; [exact Espc | lia].
  Qed.

  (* 0x86a4c: a2 = 32, a0 = o, checked_memcpy (o, S, 32); then 0x86a58: j 0x86e10; s5 = 1; the release at 0x86e14. *)
  Lemma c12_join : forall (S : Z) (JJ : list byte) (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
    p <> 0 -> o <> 0 -> FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 (zeros 32)] ->
    addressable m S 32 -> bytes_at rsegs mc S JJ -> length JJ = 32%nat ->
    0 <= S -> S + 32 <= ASAN_GT -> (o + 32 <= S \/ S + 32 <= o) ->
    JJ = synth row b nb -> rc row b = 1 ->
    evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 (Z_to_bv 64 S) x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr)
              (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86a4c) fc None mc (seg_rom rsegs)).
  Proof.
    intros S JJ fr f spc j n w56 mc x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31
      Hp Ho HK HB HOc AS HJ LJ S0 SG DJ EJ Er.
    destruct HB as (MU & WM & RM & MI & SV & (hh & HH) & F56).
    assert (Epo : (p =? 0) || (o =? 0) = false)
      by (apply orb_false_iff; split; apply Z.eqb_neq; assumption).
    pose proof (c12_sub_post fr f spc j n w56 HK) as SP. rewrite Epo in SP. cbv iota in SP.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & _ & HFSb & HApp & _ & _).
    destruct (HO Ho) as (_ & HOsp & _).
    destruct (AO Ho) as (AOa & AOe & AOr).
    destruct (c12_o_fs Ho) as (Dh & Df).
    pose proof (c12_fk fr f spc j n w56 HK) as HF.
    assert (HAb : A mod 32 = 0 /\ bv_unsigned sp - 176 <= A <= bv_unsigned sp - 160)
      by (rewrite HA; clear - Rsp HS16; Z.div_mod_to_equations; lia).
    assert (Hoapp : o <> 0 -> forall y, o <= y < o + 32 -> app_mem y).
    { intros _ y Hy. replace y with (o + (y - o)) by (clear - Hy; lia).
      exact (acl_app_in m o 32 (y - o) AOa ltac:(clear - Hy; lia)). }
    unfold ASAN_GT in P3, SG. unfold FS_SIZE in HFSb.
    (* the source and the destination are addressable at mc: their shadow bytes are outside the run's writes *)
    assert (ADS : addressable mc S 32).
    { apply (addr_munch _ m mc S 32 AS MU). intros i Hi. apply SP.
      apply (c12_sh_out (bv_unsigned sp) FS o (S + i) HApp P4 P2 HS16 Hoapp (acl_app_in m S 32 i AS Hi)).
      - clear - Hi SG P3 HFSb. lia.
      - clear - Hi SG P3. lia. }
    assert (ADD : addressable mc o 32).
    { apply (addr_munch _ m mc o 32 AOa MU). intros i Hi. apply SP.
      apply (c12_sh_out (bv_unsigned sp) FS o (o + i) HApp P4 P2 HS16 Hoapp (acl_app_in m o 32 i AOa Hi)).
      - clear - Hi HOsp. lia.
      - clear - Hi Df. lia. }
    assert (Hspc : bv_unsigned sp - 4272 <= spc - 2224 /\ spc <= bv_unsigned sp - 160)
      by (clear - HF HAb; lia).
    pose proof (stk_mono m mc _ _ ST0 WM RM) as STm.
    destruct (stk_split rsegs mc _ spc _ STm ltac:(clear - Hspc; lia)) as [STc _].
    pose proof (br_ac sp tp m p b o FS row nb ob AC0 HHM HAE FP0 Rp Rb Ro HP HO AO _ mc MU SP) as ACc.
    pose proof (shadow_rw_mono m mc SR0 WM RM) as SRc.
    assert (US : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; clear - S0 SG; lia).
    assert (UO : bv_unsigned (Z_to_bv 64 o) = o) by (apply unsigned_lit; exact Ro).
    assert (U32 : bv_unsigned (Z_to_bv 64 32) = 32) by (apply unsigned_lit; lia).
    assert (USP : bv_unsigned (Z_to_bv 64 spc) = spc) by (apply unsigned_lit; clear - Hspc HHM Rsp; unfold HIGHMEM_BEG in HHM; lia).
    assert (Hsv : forall x, bv_unsigned sp + -88 <= x < bv_unsigned sp -> ~ (o <= x < o + 32) /\ ~ (spc - 2224 <= x < spc))
      by (intros x Hx; clear - Hx HOsp Hspc; lia).
    assert (Hfh : forall x, FS <= x < FS + 8 -> ~ (o <= x < o + 32) /\ ~ (spc - 2224 <= x < spc))
      by (intros x Hx; clear - Hx Dh Hspc HFSb; lia).
    assert (Hf56 : forall x, fr + 56 <= x < fr + 64 -> ~ (o <= x < o + 32) /\ ~ (spc - 2224 <= x < spc))
      by (intros x Hx; clear - Hx HF HOsp Df HAb HFSb; lia).
    assert (HSlo : S + 32 <= spc - 2224) by (clear - SG P3 HFSb Hspc; lia).
    pose proof HMC as HM. unfold asan_memcpy_contract in HM. cbv zeta in HM.
    clear SP HApp HSM Hoff HA HS16 ST0 MI0 AC0 SR0 AW0 FP0 TLS0 HP HN HO AP ANB AO AJ1 AJ2 NDJ HMS HMC HBD HDH HNF.
    step. step. step.
    eapply evt_cut.
    { eapply HM with (src := JJ) (junk := zeros 32) (lo := bv_unsigned sp - 4272).
      all: rewrite ?US, ?UO, ?U32, ?USP; try unfold ASAN_MEMCPY_K.
      - exact HJ.
      - rewrite LJ. reflexivity.
      - exact HOc.
      - clear - DJ. lia.
      - clear - U32. lia.
      - exact ADS.
      - exact ADD.
      - right. unfold app_mem, LOWMEM_END. left. clear - S0 SG. lia.
      - right. exact AOe.
      - right. split; [unfold app_mem, LOWMEM_END; left; clear - S0 SG; lia|].
        exact (acl_app_in mc o 32 7 ADD ltac:(clear - U32; lia)).
      - exact AOr.
      - clear - HOsp Hspc. lia.
      - clear - HSlo. lia.
      - exact STc.
      - clear - Hspc. lia.
      - exact HHM.
      - clear - Hspc HAE. lia.
      - exact ACc.
      - exact SRc.
      - exact MI. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & a1' & a2' & a3' & a4' & a5' & a6' & a7' & u3 & u4 & u5 & u6 & m2
                    & E & MU2 & WM2 & MI2 & ST2 & RW2 & SB2 & AC2 & SR2).
    subst ms'.
    rewrite UO, U32, USP in MU2. rewrite USP in ST2. rewrite UO, U32 in RW2. unfold ASAN_MEMCPY_K in MU2.
    replace (ret_pc (Z_to_bv 64 0x86a58)) with (Z_to_bv 64 0x86a58)
      by (symmetry; apply ret_pc_even; [clear - U32; lia | reflexivity]).
    (* the run's state at m2 *)
    assert (BI2 : BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 m2).
    { assert (Hsub : sub_fp [(o, o + 32); (spc - 2224, spc)] (Wf sp FS fr j n ++ [(o, o + 32)])).
      { unfold sub_fp, Wf. intros x Hx. cbn [app outside] in Hx |- *.
        destruct Hx as (H1 & _ & _ & _ & _ & H6 & _).
        split; [exact H6|]. split; [|exact I]. clear - H1 Hspc. lia. }
      split; [exact (munch_trans _ m mc m2 MU (munch_weaken _ _ mc m2 Hsub MU2))|].
      split; [exact (wmono_trans rsegs m mc m2 WM WM2)|].
      split.
      { apply (rd_mono_trans m mc m2 RM). apply (rd_mono_list _ mc m2 MU2).
        constructor; [cbn [fst snd]; intros y Hy; apply (rd_of_bytes m2 o JJ (mb_rw1 _ _ _ _ _ RW2));
                      rewrite LJ; exact Hy|].
        constructor; [cbn [fst snd]; intros y Hy; exact (rd_of_stk m2 _ _ ST2 y ltac:(clear - Hy Hspc; lia))|].
        constructor. }
      split; [exact MI2|].
      split.
      { apply (acl_rw _ mc m2 _ _ SV MU2 WM2). intros x Hx.
        assert (Hx' : bv_unsigned sp + -88 <= x < bv_unsigned sp)
          by (unfold SAVES in Hx; cbn [cells_size csize Nat.add] in Hx; clear - Hx; lia).
        destruct (Hsv x Hx') as (Ha & Hb'). cbn [outside]. split; [exact Ha|]. split; [exact Hb' | exact I]. }
      split.
      { exists hh. apply (rc_bytes_at_munch rsegs _ mc m2 FS _ HH MU2). intros x Hx.
        rewrite length_le8 in Hx.
        destruct (Hfh x Hx) as (Ha & Hb'). cbn [outside]. split; [exact Ha|]. split; [exact Hb' | exact I]. }
      apply (rc_bytes_at_munch rsegs _ mc m2 (fr + 56) _ F56 MU2). intros x Hx.
      rewrite length_le8 in Hx.
      destruct (Hf56 x ltac:(clear - Hx; lia)) as (Ha & Hb'). cbn [outside].
      split; [exact Ha|]. split; [exact Hb' | exact I]. }
    step. step.
    eapply (Hrel fr f spc j n w56 m2 1).
    - exact HK.
    - rewrite Epo. symmetry. exact Er.
    - rewrite Epo. exact BI2.
    - rewrite Epo. rewrite <- EJ. exact (mb_rw1 _ _ _ _ _ RW2).
  Qed.

  (* b = 1 (0x86a44): a1 = JOIN_0014, then the copy at 0x86a4c. *)
  Lemma c12_case1 : forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    b = 1 -> p <> 0 -> o <> 0 -> FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 (zeros 32)] ->
    evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr)
              (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86a44) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 Hb Hp Ho HK HB HOc.
    pose proof HB as (_ & _ & _ & MI & _).
    pose proof (AJ1 Hb) as AS.
    destruct (HO Ho) as (_ & _ & HOj).
    pose proof c12_j14 as (J0 & JG).
    assert (DJ : o + 32 <= JOIN_0014 \/ JOIN_0014 + 32 <= o)
      by (clear - HOj; unfold JOIN_0013, JOIN_0014 in HOj |- *; lia).
    step. step.
    eapply (c12_join JOIN_0014 J14 fr f spc j n w56 mc);
      [exact Hp | exact Ho | exact HK | exact HB | exact HOc | exact AS | | reflexivity | exact J0 | exact JG
      | exact DJ | rewrite Hb; reflexivity | rewrite Hb; reflexivity].
    apply rc_ro_in_image; [exact MI | vm_compute; reflexivity].
  Qed.

  (* b = 2 (0x869fc): a1 = JOIN_0013, j 0x86a4c, then the copy. *)
  Lemma c12_case2 : forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    b = 2 -> p <> 0 -> o <> 0 -> FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 (zeros 32)] ->
    evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr)
              (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x869fc) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 Hb Hp Ho HK HB HOc.
    pose proof HB as (_ & _ & _ & MI & _).
    pose proof (AJ2 Hb) as AS.
    destruct (HO Ho) as (_ & _ & HOj).
    pose proof c12_j13 as (J0 & JG).
    assert (DJ : o + 32 <= JOIN_0013 \/ JOIN_0013 + 32 <= o)
      by (clear - HOj; unfold JOIN_0013, JOIN_0014 in HOj |- *; lia).
    step. step. step.
    eapply (c12_join JOIN_0013 J13 fr f spc j n w56 mc);
      [exact Hp | exact Ho | exact HK | exact HB | exact HOc | exact AS | | reflexivity | exact J0 | exact JG
      | exact DJ | rewrite Hb; reflexivity | rewrite Hb; reflexivity].
    apply rc_ro_in_image; [exact MI | vm_compute; reflexivity].
  Qed.
End Case12.
