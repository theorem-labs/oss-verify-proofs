(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 687 of its 711 lines of code are new or changed and 224 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block_body.v, with its module names changed; 82 of its 202 lines of code are new or changed and 591 lines of the source are left out. *)
(* GENERATED - do not edit.  C_reac_box_model_blockRB_case12.v is the re-based copy of lib/B/Prog/reac_box_model_block_case12.v at 20372bbcc3a
   (source sha256 d468658ab5e4dded42f624b2c5261883a0149909b051cb209c3a110203bb8ac5) by gen_rb_modelblock.py
   (its sha256 is cited in the commit that adds this file); the substitutions are listed there.  Dropped here: c12_join, c12_case1, c12_case2. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcParseLib RcKindLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c dt1_head_c name_field_c reac_box_model_block_c
  C_reac_box_model_blockRB.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_box_model_block_c_on reac_box_model_block_cF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c_on asan_memset_c_on asan_memcpy_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import name_field_c_on.
Import ListNotations.
Open Scope Z_scope.

(* Cases b = 1 and b = 2 of the body of reac_box_model_block, image B (asan-ubsan): the 32 image bytes at JOIN_0014
   (b = 1, case PC 0x86a44) or JOIN_0013 (b = 2, case PC 0x869fc) are copied into o by checked_memcpy (0x52164), s5 = 1,
   then the frame release at 0x86e14. The release is the hypothesis Hrel (its type is rel_stmt of the interface pin);
   C_reac_box_model_blockRB_body.v proves it and applies these lemmas. *)

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
  Hypothesis HSM : asan_stack_malloc_0_contract_on.
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  Hypothesis SR0 : shadow_rw_on (reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) m.
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

  Hypothesis HMS : asan_memset_contract_on.
  Hypothesis HMC : asan_memcpy_contract_on.
  Hypothesis HBD : build_dt1_single_contract_on.
  Hypothesis HDH : dt1_head_contract_on.
  Hypothesis HNF : name_field_contract_on.

  (* The frame release at 0x86e14 (rel_stmt of the interface pin), proved in C_reac_box_model_blockRB_body.v. *)
  Hypothesis Hrel :
    forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte) (ret : Z)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
      FK FS A fr f spc j n w56 ->
      ret = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
      BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS
         (Wf sp FS fr j n ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)])) fr w56 mc ->
      (if (p =? 0) || (o =? 0) then True else bytes_at rsegs mc o (synth row b nb)) ->
      evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
        (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
                (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 ret) x22 (Z_to_bv 64 fr)
                (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x86e14) fc None mc (seg_rom rsegs)).

  (* The body's fine footprint lies inside the post's write set (the proof of sub_post in
     C_reac_box_model_blockRB_body.v; this file cannot import that file, which imports this one). *)
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

  (* b = 1 (0x86a44): a1 = JOIN_0014, then the copy at 0x86a4c. *)

  (* b = 2 (0x869fc): a1 = JOIN_0013, j 0x86a4c, then the copy. *)
End Case12.
