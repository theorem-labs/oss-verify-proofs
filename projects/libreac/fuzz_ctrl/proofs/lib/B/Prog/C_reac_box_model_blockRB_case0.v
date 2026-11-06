(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 388 of its 406 lines of code are new or changed and 126 lines of the source are left out. *)
(* GENERATED - do not edit.  C_reac_box_model_blockRB_case0.v is the re-based copy of lib/B/Prog/reac_box_model_block_case0.v at 20372bbcc3a
   (source sha256 6ceeab617d6146d8be754411bf491cebccd719d1cbb6434e5c76ded6b8c5b10e) by gen_rb_modelblock.py
   (its sha256 is cited in the commit that adds this file); the substitutions are listed there.  Dropped here: c0_fin, c0_ex0, c0_st31, c0_sumtail, c0_sum, c0_tailc, c0_case0. *)
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

(* The case b = 0 of reac_box_model_block's body walk, image B (asan-ubsan): build_config inlined, from the target of
   the jump-table dispatch at 0x86714 to the frame release at 0x86e14. The release is the hypothesis Hrel (proved in
   C_reac_box_model_blockRB_body.v) and the two slot-filling branches are Hlay1 / Hlay2 (proved in
   C_reac_box_model_blockRB_case0s.v); this file repeats that file's `Section Body` preamble byte for byte, so the three
   compose. Every lemma and Ltac of this file carries the prefix c0_. *)

(* A one-byte store of a register value is a C1 cell (as in the ubsan twin). *)
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

(* --- image-independent arithmetic (outside the Section, so lia never sees the Section's hypotheses) --- *)
Lemma c0_m8 : forall x k, x mod 8 = 0 -> (x + k) mod 8 = k mod 8.
Proof. intros x k H. rewrite Zplus_mod, H, Z.add_0_l, Zmod_mod. reflexivity. Qed.

Lemma c0_mb : forall x, 0 <= x mod 8 <= 7.
Proof. intros x. pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. Qed.

(* The check byte that the 64-bit neg of the running sum stores. *)
Lemma c0_neg8 : forall s, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (0 - s))) = bz ((- s) mod 256).
Proof.
  intros s. unfold bz. apply Z_to_bv8_mod. rewrite unsigned_lit_wrap.
  replace (0 - s) with (- s) by lia.
  rewrite (mod_mod8_of_modw (- s) 64 ltac:(lia)).
  change (2 ^ 8) with 256. symmetry. apply Z.mod_mod. lia.
Qed.

Section c0_S.
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

  (* The frame release at 0x86e14 (C_reac_box_model_blockRB_body.v's rel). *)
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

  (* 0x868c4: lay = 1, the slot chain (C_reac_box_model_blockRB_case0s.v's c0s_lay1). *)
  Hypothesis Hlay1 :
    forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
           (x1 x5 x6 x7 a0 a1 a6 a7 x22 x28 x29 x30 x31 : word),
      lay row = 1 ->
      b = 0 -> synok row = true ->
      0 < p -> p mod 8 = 0 -> length row = 296%nat -> p + 296 <= APPMEM_END ->
      0 < o -> o + 32 <= APPMEM_END ->
      (p + 296 <= o \/ o + 32 <= p) ->
      (FS + 8 <= o \/ o + 32 <= FS) ->
      (fr + 64 <= o \/ o + 32 <= fr) ->
      (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) ->
      (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) ->
      (forall i, 0 <= i <= 32 -> app_mem (o + i)) ->
      FS + 8 <= bv_unsigned sp - 4272 ->
      bv_unsigned sp - 240 <= spc -> spc <= bv_unsigned sp - 160 ->
      (fr + 64 <= spc - 2224 \/ spc <= fr + 56) ->
      (o + 32 <= RT_LO \/ RT_HI <= o) ->
      addressable m p 296 -> addressable m o 32 -> bytes_at rsegs m p row ->
      (forall x, p <= x < p + 296 -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) x) ->
      (forall i, 0 <= i < 296 -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) (shadow_addr (p + i))) ->
      (forall i, 0 <= i < 32 -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) (shadow_addr (o + i))) ->
      (forall x, RT_LO <= x < RT_HI -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) x) ->
      FK FS A fr f spc j n w56 ->
      BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 mc ->
      rw_cells rsegs mc o [CB 32 ([bz 1; bz 3; bz 0; bz 16; sel row; bz 0; bz 0; strap row] ++ zeros 24)] ->
      evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
        (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) a0 a1
                 (Z_to_bv 64 (ic row)) (Z_to_bv 64 (oc row)) (Z_to_bv 64 (oc row / 4)) (Z_to_bv 64 (ic row / 4)) a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr)
                 (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x868c4) fc None mc (seg_rom rsegs)).

  (* 0x86f78: lay <> 1, the slot chain (C_reac_box_model_blockRB_case0s.v's c0s_lay2). *)
  Hypothesis Hlay2 :
    forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
           (x1 x5 x6 x7 a0 a1 a6 a7 x22 x28 x29 x30 x31 : word),
      lay row <> 1 ->
      b = 0 -> synok row = true ->
      0 < p -> p mod 8 = 0 -> length row = 296%nat -> p + 296 <= APPMEM_END ->
      0 < o -> o + 32 <= APPMEM_END ->
      (p + 296 <= o \/ o + 32 <= p) ->
      (FS + 8 <= o \/ o + 32 <= FS) ->
      (fr + 64 <= o \/ o + 32 <= fr) ->
      (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) ->
      (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) ->
      (forall i, 0 <= i <= 32 -> app_mem (o + i)) ->
      FS + 8 <= bv_unsigned sp - 4272 ->
      bv_unsigned sp - 240 <= spc -> spc <= bv_unsigned sp - 160 ->
      (fr + 64 <= spc - 2224 \/ spc <= fr + 56) ->
      (o + 32 <= RT_LO \/ RT_HI <= o) ->
      addressable m p 296 -> addressable m o 32 -> bytes_at rsegs m p row ->
      (forall x, p <= x < p + 296 -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) x) ->
      (forall i, 0 <= i < 296 -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) (shadow_addr (p + i))) ->
      (forall i, 0 <= i < 32 -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) (shadow_addr (o + i))) ->
      (forall x, RT_LO <= x < RT_HI -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) x) ->
      FK FS A fr f spc j n w56 ->
      BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 mc ->
      rw_cells rsegs mc o [CB 32 ([bz 1; bz 3; bz 0; bz 16; sel row; bz 0; bz 0; strap row] ++ zeros 24)] ->
      evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
        (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) a0 a1
                 (Z_to_bv 64 (ic row)) (Z_to_bv 64 (oc row)) (Z_to_bv 64 (oc row / 4)) (Z_to_bv 64 (ic row / 4)) a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr)
                 (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x86f78) fc None mc (seg_rom rsegs)).

  (* --- the state of the case-0 walk --- *)

  Definition c0_R (fr spc f r : Z)
      (x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 x22 x28 x29 x30 x31 : word) : bvmap 5 word :=
    mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
        (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 r) x22 (Z_to_bv 64 fr)
        (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31.

  Definition c0_at (pc : Z) (R : bvmap 5 word) (mc : word -> option byte) : machine_state :=
    MS R F (Z_to_bv 64 pc) fc None mc (seg_rom rsegs).

  Definition c0_Q (frq jq nq : Z) : machine_state -> Prop :=
    Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb frq jq nq.

  Definition c0_K (fr j n : Z) (w56 : word) (mc : word -> option byte) : Prop :=
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 mc.

  (* The geometry of the row p, the output block o and the frame fr, and the state at m: what the walk needs of the
     Section's hypotheses, as one package, so that the heavy hypotheses are never in scope of a lia. *)
  Definition c0_G (fr spc j n : Z) : Prop :=
    0 < p /\ p mod 8 = 0 /\ length row = 296%nat /\ p + 296 <= APPMEM_END /\
    0 < o /\ o + 32 <= APPMEM_END /\
    (p + 296 <= o \/ o + 32 <= p) /\
    (FS + 8 <= o \/ o + 32 <= FS) /\
    (fr + 64 <= o \/ o + 32 <= fr) /\
    (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) /\
    (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) /\
    (forall i, 0 <= i <= 32 -> app_mem (o + i)) /\
    FS + 8 <= bv_unsigned sp - 4272 /\
    bv_unsigned sp - 240 <= spc /\ spc <= bv_unsigned sp - 160 /\
    (fr + 64 <= spc - 2224 \/ spc <= fr + 56) /\
    (o + 32 <= RT_LO \/ RT_HI <= o) /\
    addressable m p 296 /\ addressable m o 32 /\ bytes_at rsegs m p row /\
    (forall x, p <= x < p + 296 -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) x) /\
    (forall i, 0 <= i < 296 -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) (shadow_addr (p + i))) /\
    (forall i, 0 <= i < 32 -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) (shadow_addr (o + i))) /\
    (forall x, RT_LO <= x < RT_HI -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) x).

  Ltac c0_gd G :=
    destruct G as (Gp0 & Gp8 & Grow & Gpe & Go0 & Goe & Gop & Gof & Gofr & Gow & Gpw & Goapp & Gfsw & Gsc1 & Gsc2
                   & Gfr56 & Gort & GAP & GAO & GRow & GOUTP & GSHP & GSHO & GRTO);
    unfold APPMEM_END in Gpe, Goe.

  Ltac c0_bd H := destruct H as (MU & WM & RM & MI & SV & (hh & HH) & F56);
    unfold Wf in MU; cbn [app] in MU; unfold SAVES in SV.

  Ltac c0_bi := split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
                split; [eassumption|]; split; [eexists; eassumption | eassumption].

  (* An arithmetic side condition of a callee's contract: unfold the named bounds, then lia. *)
  Ltac c0_num :=
    repeat (first [ unfold ASAN_MEMCPY_K | unfold RT_LO | unfold RT_HI | unfold HIGHMEM_BEG
                  | unfold APPMEM_END ]); lia.

  (* The Section hypotheses that zify would blow up on, and that no lemma of this file needs after it has
     taken what it must from them.  Every lemma clears the same set, so the lemmas compose. *)
  Ltac c0_clr := clear HP HN HO AP ANB AO AJ1 AJ2 NDJ HSM HMS HMC HBD HDH HNF
                       ST0 MI0 AC0 SR0 AW0 TLS0 FP0 HA HS16.

  (* The shadow byte of an access of w bytes at X, read at X / 8 + off as the code reads it. *)
  Lemma c0_chk : forall mc q nn j w X, addressable mc q nn -> 0 <= j -> 1 <= w -> j + w <= nn ->
    X mod 8 + w <= 8 -> X = q + j ->
    exists k : byte, ov_read_bytes rsegs mc (wa (X / 8 + off)) 1 = Some [k]
                     /\ (bv_signed k = 0 \/ X mod 8 + (w - 1) < bv_signed k) /\ -128 <= bv_signed k < 128.
  Proof.
    intros mc q nn j w X H1 H2 H3 H4 H5 H6. rewrite Hoff.
    exact (acl_shadow mc q nn j w X H1 H2 H3 H4 H5 H6).
  Qed.

  (* The release: every exit of the walk ends here. *)

  (* build_config refuses the row: the block stays zero and the case returns -1. *)

  (* 0x86e08: the check byte of the gram, then the release. *)

  (* 0x87178: the shadow check of the last byte of the block, then the check byte. *)

  (* 0x87140: the outer byte sum of build_config. *)


  (* 0x8710c: the tail bytes of the row by checked_memcpy, then the outer sum. *)


  (* The geometry of the case, from the Section's hypotheses. *)
  Lemma c0_geom : forall (fr f spc j n : Z) (w56 : word),
    p <> 0 -> o <> 0 -> FK FS A fr f spc j n w56 -> c0_G fr spc j n.
  Proof.
    intros fr f spc j n w56 Pnz Onz HK.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    assert (HAfacts : A mod 32 = 0 /\ bv_unsigned sp - 176 <= A <= bv_unsigned sp - 160)
      by (clear -HA HS16; rewrite HA; Z.div_mod_to_equations; lia).
    destruct HAfacts as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'.
    pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
    destruct (HP Pnz) as (P8 & Lrow & HRow0 & DPW & DPO0).
    destruct (HO Onz) as (HOb0 & DOW & DOJ).
    pose proof (AP Pnz) as APm.
    destruct (AO Onz) as (AOm & AO32 & AORT).
    pose proof FP0 as (DT & TS & C & T & DB & kk0 & HT & HTP & HPl & H88 & H96 & HCL & HFSb & HAPP & HWd & HDd).
    pose proof HPl as (Q1 & Q2 & Q3 & Q4 & Q5). unfold ASAN_GT in Q3. unfold FS_SIZE in HFSb, Q4, Q5.
    pose proof APm as APm2. destruct APm2 as (_ & _ & APend & APd).
    pose proof AOm as AOm2. destruct AOm2 as (_ & _ & AOend & AOd).
    assert (APap : forall i, 0 <= i < 296 -> app_mem (p + i))
      by (intros i Hi; destruct (APd i Hi) as (Hap & _); exact Hap).
    assert (AOap : forall i, 0 <= i <= 32 -> app_mem (o + i)).
    { intros i Hi. destruct (Z.eq_dec i 32) as [Ei|Ei]; [rewrite Ei; exact AO32|].
      destruct (AOd i ltac:(lia)) as (Hap & _). exact Hap. }
    assert (DPO : p + 296 <= o \/ o + 32 <= p)
      by (destruct DPO0 as [H|[H|H]]; [lia | right; exact H | left; exact H]).
    assert (Epz : (p =? 0) = false) by (apply Z.eqb_neq; lia).
    assert (Eoz : (o =? 0) = false) by (apply Z.eqb_neq; lia).
    unfold reac_box_model_block_D in HDd. rewrite Epz, Eoz in HDd. cbn [app] in HDd.
    unfold fp_dj, fp_w, fp_w1 in HDd. cbn [flat_map app] in HDd.
    apply Forall_cons_iff in HDd. destruct HDd as [HDp HDd].
    apply Forall_cons_iff in HDd. destruct HDd as [HDo _].
    cbn [fst snd] in HDp, HDo.
    apply Forall_cons_iff in HDp. destruct HDp as [DpH HDp].
    apply Forall_cons_iff in HDp. destruct HDp as [DpF HDp].
    apply Forall_cons_iff in HDp. destruct HDp as [DpR _].
    apply Forall_cons_iff in HDo. destruct HDo as [DoH HDo].
    apply Forall_cons_iff in HDo. destruct HDo as [DoF HDo].
    apply Forall_cons_iff in HDo. destruct HDo as [DoR _].
    cbn [fst snd] in DpH, DpF, DpR, DoH, DoF, DoR.
    unfold ly_dj in DpH, DpF, DpR, DoH, DoF, DoR.
    c0_clr. clear Hoff HT HTP HCL HWd HPl DOJ DPO0 Q5.
    assert (EH0 : fs_hint FS 0 = FS) by (unfold fs_hint; cbn [Z.of_nat]; lia).
    assert (EF0 : fs_flag FS 0 0 = FS + 4096) by (unfold fs_flag; cbn [Z.of_nat]; lia).
    assert (EFj : fs_flag FS 0 j = FS + 4096 + j) by (unfold fs_flag; cbn [Z.of_nat]; lia).
    assert (EM0 : fs_M 0 = 16384) by reflexivity.
    assert (EFR0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (EFMf : fs_frame FS 0 (fs_M 0) = FS + 1085440).
    { unfold fs_frame, fs_B, fs_M.
      replace (2 ^ (14 - Z.of_nat 0) * (64 * 2 ^ Z.of_nat 0)) with 1048576 by reflexivity.
      replace (Z.of_nat 0 * 2 ^ 20) with 0 by reflexivity. lia. }
    rewrite EH0 in DpH, DoH. rewrite EF0, EM0 in DpF, DoF. rewrite EFR0, EFMf in DpR, DoR.
    assert (HKf : 0 <= j < 16384 /\ 0 <= n <= 1 /\ A - 64 <= spc <= A /\
                  fr mod 8 = 0 /\ FS + 36864 <= fr /\ fr + 64 <= A /\
                  (forall i, 0 <= i < 64 -> app_mem (fr + i)) /\
                  (fr + 64 <= FS + 1085440 \/ (fr = A - 64 /\ spc = fr))).
    { assert (FS8 : FS mod 8 = 0) by (clear -Q2; Z.div_mod_to_equations; lia).
      destruct HK as [(Ef & Efr & Espc & Ej & En) | (Hj & Efr & Ef & Espc & Ew & En)].
      - subst j n fr spc.
        split; [lia|]. split; [lia|]. split; [lia|].
        split; [clear -HA32; Z.div_mod_to_equations; lia|].
        split; [lia|]. split; [lia|].
        split; [intros i Hi; apply HAPP; lia|].
        right. split; reflexivity.
      - change (fs_M 0) with 16384 in Hj.
        assert (Efrv : fs_frame FS 0 j = FS + 36864 + j * 64)
          by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
        rewrite Efrv in Efr. subst n spc.
        split; [lia|]. split; [lia|]. split; [lia|].
        split; [clear -Efr FS8 Hj; rewrite Efr; Z.div_mod_to_equations; lia|].
        split; [lia|]. split; [lia|].
        split; [intros i Hi; apply Q4; lia|].
        left. lia. }
    destruct HKf as (Hj16 & Hn01 & Hspc & FR8 & FRlo & FRhi & FAP & HKfr).
    assert (FR0 : 0 <= fr) by lia.
    assert (FRend : fr + 64 <= APPMEM_END).
    { pose proof (FAP 63 ltac:(lia)) as H63.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H63. unfold APPMEM_END. lia. }
    assert (DOFR : fr + 64 <= o \/ o + 32 <= fr).
    { destruct HKfr as [Hside | (Ef1 & Ef2)].
      - destruct DoR as [H|H]; [right; lia | left; lia].
      - destruct DOW as [H|H]; [left; lia | right; lia]. }
    assert (DPFR : p + 296 <= fr \/ fr + 64 <= p).
    { destruct HKfr as [Hside | (Ef1 & Ef2)].
      - destruct DpR as [H|H]; [left; lia | right; lia].
      - destruct DPW as [H|H]; [right; lia | left; lia]. }
    assert (SHfr : forall x, shadow_addr fr <= shadow_addr x < shadow_addr fr + 8 <-> fr <= x < fr + 64)
      by (intros x; apply sh_range8; exact FR8).
    assert (SH64 : shadow_addr (fr + 64) = shadow_addr fr + 8)
      by (replace (fr + 64) with (fr + 8 * 8) by lia; apply (sh_add8 fr 8 FR8)).
    assert (OUTP : forall x, p <= x < p + 296 -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) x).
    { intros x Hx. unfold Wf. cbn [app outside].
      assert (Hap : app_mem x).
      { pose proof (APap (x - p) ltac:(lia)) as H. replace (p + (x - p)) with x in H by lia. exact H. }
      split; [lia|]. split; [lia|]. split; [rewrite EFj; lia|]. split; [lia|].
      split; [|split; [lia|exact I]].
      rewrite <- SH64. exact (acl_sh_out x fr (fr + 64) Hap FR0 FRend). }
    assert (OUTSP : forall i, 0 <= i < 296 ->
              outside (Wf sp FS fr j n ++ [(o, o + 32)]) (shadow_addr (p + i))).
    { intros i Hi. unfold Wf. cbn [app outside].
      pose proof (APap i Hi) as Hap. pose proof (rt_app_shadow _ Hap) as Hsh0.
      pose proof Hsh0 as Hsh.
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh.
      split; [lia|].
      split; [intros Hc;
              assert (Hq : app_mem (shadow_addr (p + i))) by (apply Q4; lia);
              exact (app_not_shadow _ _ Hq Hsh0 eq_refl)|].
      split; [rewrite EFj; intros Hc;
              assert (Hq : app_mem (shadow_addr (p + i))) by (apply Q4; lia);
              exact (app_not_shadow _ _ Hq Hsh0 eq_refl)|].
      split; [intros Hc;
              assert (Hq : app_mem (shadow_addr (p + i)))
                by (pose proof (FAP (shadow_addr (p + i) - fr) ltac:(lia)) as Hf;
                    replace (fr + (shadow_addr (p + i) - fr)) with (shadow_addr (p + i)) in Hf by lia; exact Hf);
              exact (app_not_shadow _ _ Hq Hsh0 eq_refl)|].
      split; [intros Hc; apply (proj1 (SHfr (p + i))) in Hc; lia|].
      split; [|exact I].
      intros Hc.
      assert (Hq : app_mem (shadow_addr (p + i)))
        by (pose proof (AOap (shadow_addr (p + i) - o) ltac:(lia)) as Hf;
            replace (o + (shadow_addr (p + i) - o)) with (shadow_addr (p + i)) in Hf by lia; exact Hf).
      exact (app_not_shadow _ _ Hq Hsh0 eq_refl). }
    assert (OUTSO : forall i, 0 <= i < 32 ->
              outside (Wf sp FS fr j n ++ [(o, o + 32)]) (shadow_addr (o + i))).
    { intros i Hi. unfold Wf. cbn [app outside].
      pose proof (AOap i ltac:(lia)) as Hap. pose proof (rt_app_shadow _ Hap) as Hsh0.
      pose proof Hsh0 as Hsh.
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh.
      split; [lia|].
      split; [intros Hc;
              assert (Hq : app_mem (shadow_addr (o + i))) by (apply Q4; lia);
              exact (app_not_shadow _ _ Hq Hsh0 eq_refl)|].
      split; [rewrite EFj; intros Hc;
              assert (Hq : app_mem (shadow_addr (o + i))) by (apply Q4; lia);
              exact (app_not_shadow _ _ Hq Hsh0 eq_refl)|].
      split; [intros Hc;
              assert (Hq : app_mem (shadow_addr (o + i)))
                by (pose proof (FAP (shadow_addr (o + i) - fr) ltac:(lia)) as Hf;
                    replace (fr + (shadow_addr (o + i) - fr)) with (shadow_addr (o + i)) in Hf by lia; exact Hf);
              exact (app_not_shadow _ _ Hq Hsh0 eq_refl)|].
      split; [intros Hc; apply (proj1 (SHfr (o + i))) in Hc; lia|].
      split; [|exact I].
      intros Hc.
      assert (Hq : app_mem (shadow_addr (o + i)))
        by (pose proof (AOap (shadow_addr (o + i) - o) ltac:(lia)) as Hf;
            replace (o + (shadow_addr (o + i) - o)) with (shadow_addr (o + i)) in Hf by lia; exact Hf).
      exact (app_not_shadow _ _ Hq Hsh0 eq_refl). }
    assert (OUTRT : forall x, RT_LO <= x < RT_HI -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) x).
    { intros x Hx. unfold RT_LO, RT_HI in Hx. unfold Wf. cbn [app outside].
      assert (SHlo : 2147450880 <= shadow_addr fr)
        by (clear -FR0; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
      split; [lia|]. split; [lia|]. split; [rewrite EFj; lia|]. split; [lia|]. split; [lia|].
      split; [|exact I]. unfold RT_LO, RT_HI in AORT. lia. }
    unfold c0_G.
    assert (Gp0 : 0 < p) by lia.
    assert (Go0 : 0 < o) by lia.
    assert (Gfsw : FS + 8 <= bv_unsigned sp - 4272) by lia.
    assert (Gsc1 : bv_unsigned sp - 240 <= spc) by lia.
    assert (Gsc2 : spc <= bv_unsigned sp - 160) by lia.
    assert (Gof : FS + 8 <= o \/ o + 32 <= FS) by (destruct DoH as [H|H]; [right|left]; lia).
    assert (Gfr56 : fr + 64 <= spc - 2224 \/ spc <= fr + 56)
      by (destruct HKfr as [Hs|(E1 & E2)]; [left; lia | right; lia]).
    exact (conj Gp0 (conj P8 (conj Lrow (conj APend (conj Go0 (conj AOend (conj DPO (conj Gof (conj DOFR
      (conj DOW (conj DPW (conj AOap (conj Gfsw (conj Gsc1 (conj Gsc2 (conj Gfr56 (conj AORT (conj APm
      (conj AOm (conj HRow0 (conj OUTP (conj OUTSP (conj OUTSO OUTRT))))))))))))))))))))))).
  Qed.

  (* The shadow check of one access of a byte of the output block. *)
  Ltac c0_so X r GA GS :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?mk _) =>
        lazymatch goal with
        | MUx : munch _ m mk |- _ =>
            let HA := fresh "HAok" in let SH := fresh "SHok" in let RX := fresh "RXok" in
            assert (HA : addressable mk o 32) by (apply (addr_munch _ m mk o 32 GA MUx GS));
            assert (RX : 0 <= X < 2^64) by lia;
            pose proof (c0_chk mk o 32 (X - o) 1 X HA ltac:(lia) ltac:(lia) ltac:(lia)
                          ltac:(pose proof (c0_mb X); lia) ltac:(lia)) as SH;
            chk_core X RX r SH pre_sr no_extra
        end
    end.

  (* The shadow check of one access of a byte of the row. *)
  Ltac c0_lp X r GA GS :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?mk _) =>
        lazymatch goal with
        | MUx : munch _ m mk |- _ =>
            let HA := fresh "HApk" in let SH := fresh "SHpk" in let RX := fresh "RXpk" in
            assert (HA : addressable mk p 296) by (apply (addr_munch _ m mk p 296 GA MUx GS));
            assert (RX : 0 <= X < 2^64) by lia;
            pose proof (c0_chk mk p 296 (X - p) 1 X HA ltac:(lia) ltac:(lia) ltac:(lia)
                          ltac:(pose proof (c0_mb X); lia) ltac:(lia)) as SH;
            chk_core X RX r SH pre_sr no_extra
        end
    end.

  (* The current memory's copy of the row, and its byte k. *)
  Ltac c0_rdp k kz GR GO :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?mk _) =>
        lazymatch goal with
        | MUx : munch _ m mk |- _ =>
            let HR := fresh "HRk" in let RD := fresh "RDk" in
            assert (HR : bytes_at rsegs mk p row)
              by (apply (fl_bytes _ m mk p row GR MUx); intros xx Hxx; apply GO; lia);
            pose proof (rd_byte rsegs mk p row k HR ltac:(lia)) as RD;
            change (Z.of_nat k) with kz in RD
        end
    end.

  (* 0x86714: the case b = 0, build_config inlined. *)

End c0_S.
