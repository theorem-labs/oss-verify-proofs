(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 388 of its 406 lines of code are new or changed and 126 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/C_reac_box_model_blockRB_case0.v; 98 of its 205 lines of code are new or changed and 299 lines of the source are left out. *)
(* GENERATED - do not edit.  C_reac_box_model_blockRB_case0s.v is the re-based copy of lib/B/Prog/reac_box_model_block_case0s.v at 20372bbcc3a
   (source sha256 ff669d259814d1994aa93421692b4e3be0ec6d8e1338160202f21e4872eed91c) by gen_rb_modelblock.py
   (its sha256 is cited in the commit that adds this file); the substitutions are listed there.  Dropped here: c0s_tail, c0s_fill, c0s_dd8, c0s_l2a, c0s_l2b, c0s_ec4, c0s_f34, c0s_l1a, c0s_l1b, c0s_s1, c0s_s2, c0s_lay1, c0s_lay2. *)
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

(* The case b = 0 of reac_box_model_block, image B (asan-ubsan): the slot chain of the inlined build_config, from the
   two sides of the lay test at 0x868c0 (0x868c4: lay = 1; 0x86f78: lay <> 1) to the tail at 0x8710c. The tail is the
   Section hypothesis Htail (c0_tailc of C_reac_box_model_blockRB_case0.v). The Section preamble repeats the one of
   C_reac_box_model_blockRB_body.v byte for byte, so the lemmas compose. Every lemma and Ltac carries the prefix c0s_.
   PERF: every proof clears the heavy Section hypotheses (c0s_clr) before its first lia. *)

(* --- image-independent facts (outside the Section, so lia never sees the Section's hypotheses) --- *)
Lemma c0s_in_r : forall (W1 W2 : list ivl) a k, inside W2 a k -> inside (W1 ++ W2) a k.
Proof.
  induction W1 as [|[lo hi] W1 IH]; intros W2 a k H; cbn [app inside]; [exact H | right; exact (IH W2 a k H)].
Qed.

(* The value `not o` that the fill loop compares with. *)
Lemma c0s_not : forall x, 0 <= x < 2^64 ->
  bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 x)) 18446744073709551615)) = 18446744073709551615 - x.
Proof. intros x Hx. rewrite (unsigned_lit x Hx), (zb_lxor_ones x Hx). apply unsigned_lit. lia. Qed.

Section Body.
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

  (* The tail at 0x8710c (c0_tailc, proved in C_reac_box_model_blockRB_case0.v). *)
  Hypothesis Htail :
  forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
         (x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 x22 x28 x29 x30 x31 : word),
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
    rw_cells rsegs mc o [CB 32 ([bz 1; bz 3; bz 0; bz 16; sel row; bz 0; bz 0; strap row] ++ slots row ++ zeros 12)] ->
    evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x8710c) fc None mc (seg_rom rsegs)).

  Ltac c0s_clr := clear HSM HA HS16 ST0 MI0 AC0 SR0 HHM HAE AW0 FP0 TLS0 Rp Rb Ro HP HN HO AP ANB AO AJ1 AJ2 NDJ
    HMS HMC HBD HDH HNF.

  (* --- the state of the chain --- *)
  Definition c0s_H8 : list byte := [bz 1; bz 3; bz 0; bz 16; sel row; bz 0; bz 0; strap row].

  Definition c0s_R (fr spc f : Z) (x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 x22 x28 x29 x30 x31 : word) : bvmap 5 word :=
    mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
        (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr)
        (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31.

  Definition c0s_at (pc : Z) (R : bvmap 5 word) (mc : word -> option byte) : machine_state :=
    MS R F (Z_to_bv 64 pc) fc None mc (seg_rom rsegs).

  Definition c0s_Q (frq jq nq : Z) : machine_state -> Prop :=
    Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb frq jq nq.

  Definition c0s_K (fr j n : Z) (w56 : word) (mc : word -> option byte) : Prop :=
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 mc.

  (* The premises of the pinned statements that do not mention the current memory, as one package. *)
  Definition c0s_G (fr f spc j n : Z) (w56 : word) : Prop :=
    b = 0 /\ synok row = true /\
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
    (forall x, RT_LO <= x < RT_HI -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) x) /\
    FK FS A fr f spc j n w56.

  Lemma c0s_go : forall fr f spc j n w56, c0s_G fr f spc j n w56 -> 0 < o /\ o + 32 <= APPMEM_END /\ synok row = true.
  Proof.
    intros fr f spc j n w56 G. destruct G as (_ & G2 & _ & _ & _ & _ & G7 & G8 & _). exact (conj G7 (conj G8 G2)).
  Qed.

  (* o stays addressable in the current memory: its shadow bytes are outside the run's write set. *)
  Lemma c0s_ac : forall fr f spc j n w56 mc, c0s_G fr f spc j n w56 -> c0s_K fr j n w56 mc -> addressable mc o 32.
  Proof.
    intros fr f spc j n w56 mc G HB.
    destruct G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G21 & _ & _ & _
                   & G25 & _).
    destruct HB as (MU & _). exact (addr_munch _ m mc o 32 G21 MU G25).
  Qed.

  (* The shadow byte that the instrumented check of w bytes at X reads, with this build's offset register. *)
  Lemma c0s_chk : forall mc q L jj w X, addressable mc q L -> 0 <= jj -> 1 <= w -> jj + w <= L ->
    X mod 8 + w <= 8 -> X = q + jj ->
    exists k : byte, ov_read_bytes rsegs mc (wa (X / 8 + off)) 1 = Some [k]
      /\ (bv_signed k = 0 \/ X mod 8 + (w - 1) < bv_signed k) /\ -128 <= bv_signed k < 128.
  Proof.
    intros mc q L jj w X H1 H2 H3 H4 H5 H6. rewrite Hoff.
    exact (acl_shadow mc q L jj w X H1 H2 H3 H4 H5 H6).
  Qed.

  Lemma c0s_ok : forall mc X k, (k < 32)%nat -> rw_cells rsegs mc o [CB 32 X] ->
    store_ok rsegs mc (Z_to_bv 64 (o + Z.of_nat k)) 1 = true.
  Proof.
    intros mc X k Hk [_ HW]. c0s_clr. cbn [cells_size csize Nat.add] in HW.
    exact (wr_at_store_ok rsegs mc _ _ (Z.of_nat k) 1 HW ltac:(lia) ltac:(lia)).
  Qed.

  (* A byte store at a variable offset k of the output block keeps the carried state. *)
  Lemma c0s_ost : forall fr f spc j n w56 mc X k v, (k < 32)%nat -> c0s_G fr f spc j n w56 ->
    c0s_K fr j n w56 mc -> rw_cells rsegs mc o [CB 32 X] ->
    c0s_K fr j n w56 (write_to_mem mc (Z_to_bv 64 (o + Z.of_nat k)) (le1 v)) /\
    rw_cells rsegs (write_to_mem mc (Z_to_bv 64 (o + Z.of_nat k)) (le1 v)) o
      [CB 32 (upd_bytes X k [Z_to_bv 8 (bv_unsigned v)])].
  Proof.
    intros fr f spc j n w56 mc X k v Hk G HB HV.
    c0s_clr.
    destruct G as (_ & _ & _ & _ & _ & _ & Go0 & Goe & _ & GoF & Gofr & Gow & _).
    unfold APPMEM_END in Goe.
    pose proof (c0s_ok mc X k Hk HV) as HS1.
    pose proof HV as [[[LX _] HBo] HW]. cbn [cell_wf] in LX. cbn [cells_bytes cbytes] in HBo. rewrite app_nil_r in HBo.
    cbn [cells_size csize Nat.add] in HW.
    change (le1 v) with [Z_to_bv 8 (bv_unsigned v)].
    change (Z_to_bv 64 (o + Z.of_nat k)) with (wa (o + Z.of_nat k)) in HS1 |- *.
    unfold c0s_K, BI in HB |- *.
    destruct HB as (MU & WM & RM & MI & SV & (h & HH) & F56).
    split.
    - split.
      { apply munch_write; [exact MU | lia | cbn [length]; lia |].
        apply c0s_in_r. cbn [inside length Z.of_nat Pos.of_succ_nat]. left. lia. }
      split; [apply wmono_write; exact WM|].
      split; [apply rd_mono_write; exact RM|].
      split; [apply mem_inv_store; [exact MI | exact HS1]|].
      split.
      { apply rw_cells_frame; [exact SV | lia | cbn [length]; lia |].
        unfold SAVES. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
      split.
      { exists h. apply bytes_at_write_other; [exact HH | lia | cbn [length]; lia |].
        rewrite length_le8. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
      apply bytes_at_write_other; [exact F56 | lia | cbn [length]; lia |].
      rewrite length_le8. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - split; [split|].
      + cbn [cells_wf cell_wf]. split; [rewrite upd_bytes_length by (cbn [length]; lia); exact LX | exact I].
      + cbn [cells_bytes cbytes]. rewrite app_nil_r.
        pose proof (bytes_at_write_inside rsegs mc o X (Z.of_nat k) [Z_to_bv 8 (bv_unsigned v)] HBo ltac:(lia)
                      ltac:(rewrite Nat2Z.id; cbn [length]; lia)) as H. rewrite Nat2Z.id in H. exact H.
      + cbn [cells_size csize Nat.add]. apply wr_at_write. exact HW.
  Qed.

  (* One step that stores a byte at offset kk of the output block, then the carried state at the new memory. *)
  Ltac c0s_vst kk :=
    lazymatch goal with
    | G : c0s_G ?fr ?f ?spc ?j ?n ?w56, HB : c0s_K ?fr ?j ?n ?w56 ?mm, HV : rw_cells rsegs ?mm o [CB 32 ?X] |- _ =>
        let HSo := fresh "HSo" in
        pose proof (c0s_ok mm X kk ltac:(lia) HV) as HSo;
        step; clear HSo;
        lazymatch goal with |- context [write_to_mem mm (Z_to_bv 64 (o + Z.of_nat kk)) (le1 ?v)] =>
          let HB' := fresh "HB" in let HV' := fresh "HV" in
          destruct (c0s_ost fr f spc j n w56 mm X kk v ltac:(lia) G HB HV) as (HB' & HV'); clear HB HV;
          let m2 := fresh "mc" in
          set (m2 := write_to_mem mm (Z_to_bv 64 (o + Z.of_nat kk)) (le1 v)) in HB', HV' |- *; clearbody m2;
          rename HB' into HB; rename HV' into HV
        end
    end.

  (* 0x8710c: the tail. *)

  (* The fill loop of the empty slots (3), at 0x870d8. *)

  (* 0x870b4: both sides join; 12 slots done goes to the tail, else the fill loop. *)

  (* lay = 1: the input slots (0), at 0x86fe8 (with the 32-bit overflow test of the slot index). *)

  (* lay <> 1: the output slots (1), at 0x8705c (with the 32-bit overflow test of the slot index). *)

  (* lay = 1, after the output slots: 0x86fd4 (0x86fd0 sets a1 = 0 when there is none). *)

  (* lay <> 1, after the input slots: 0x87044 (0x87040 sets a1 = 0 when there is none). *)

  (* lay = 1: the output slots (1), at 0x868e0. *)

  (* lay <> 1: the input slots (2), at 0x86f94. *)

  (* 0x868c4, lay = 1. *)

  (* 0x86f78, lay <> 1. *)

  (* Statement (2b) of the pin, verbatim. *)

  (* Statement (2c) of the pin, verbatim. *)
End Body.
