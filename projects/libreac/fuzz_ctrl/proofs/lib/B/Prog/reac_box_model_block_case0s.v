(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 1475 of its 1496 lines of code are new or changed and 124 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/U/Prog/reac_box_model_block.v; 506 of its 622 lines of code are new or changed and 1380 lines of the source are left out. *)
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

(* The case b = 0 of reac_box_model_block, image B (asan-ubsan): the slot chain of the inlined build_config, from the
   two sides of the lay test at 0x868c0 (0x868c4: lay = 1; 0x86f78: lay <> 1) to the tail at 0x8710c. The tail is the
   Section hypothesis Htail (c0_tailc of reac_box_model_block_case0.v). The Section preamble repeats the one of
   reac_box_model_block_body.v byte for byte, so the lemmas compose. Every lemma and Ltac carries the prefix c0s_.
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

  (* The tail at 0x8710c (c0_tailc, proved in reac_box_model_block_case0.v). *)
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
    evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
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

  Definition c0s_Q : machine_state -> Prop :=
    Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb.

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
  Lemma c0s_tail : forall fr f spc j n w56 mc (x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 x22 x28 x29 x30 x31 : word),
    c0s_G fr f spc j n w56 -> c0s_K fr j n w56 mc ->
    rw_cells rsegs mc o [CB 32 (c0s_H8 ++ slots row ++ zeros 12)] ->
    evt rsegs c0s_Q (c0s_at 0x8710c (c0s_R fr spc f x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 x22 x28 x29 x30 x31) mc).
  Proof.
    intros fr f spc j n w56 mc x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 x22 x28 x29 x30 x31 G HB HV.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18
                   & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
    exact (Htail fr f spc j n w56 mc x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 x22 x28 x29 x30 x31 G1 G2 G3 G4 G5 G6 G7 G8 G9
             G10 G11 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 HB HV).
  Qed.

  (* The fill loop of the empty slots (3), at 0x870d8. *)
  Lemma c0s_fill : forall k P (a1w : word) (z2 z3 z4 : Z) fr f spc j n w56 mc
      (x1 x5 x6 x7 a0 a5 a6 a7 x22 x28 x29 x30 x31 : word),
    (length P + k = 12)%nat -> (0 < k)%nat -> P ++ repeat (bz 3) k = slots row ->
    bv_unsigned a1w = 18446744073709551615 - o -> z2 = 3 -> z3 = Z.of_nat (8 + length P) -> z4 = 20 ->
    c0s_G fr f spc j n w56 -> c0s_K fr j n w56 mc ->
    rw_cells rsegs mc o [CB 32 (c0s_H8 ++ P ++ zeros (24 - length P))] ->
    evt rsegs c0s_Q (c0s_at 0x870d8 (c0s_R fr spc f x1 x5 x6 x7 a0 a1w (Z_to_bv 64 z2) (Z_to_bv 64 z3) (Z_to_bv 64 z4)
                                       a5 a6 a7 x22 x28 x29 x30 x31) mc).
  Proof.
    c0s_clr.
    induction k as [|k IH]; intros P a1w z2 z3 z4 fr f spc j n w56 mc x1 x5 x6 x7 a0 a5 a6 a7 x22 x28 x29 x30 x31
      Hk Hk0 EP H1w E2 E3 E4 G HB HV; [lia|].
    subst z2 z4.
    destruct (c0s_go fr f spc j n w56 G) as (Go0 & Goe & Hsy). unfold APPMEM_END in Goe.
    pose proof (c0s_ac fr f spc j n w56 mc G HB) as HAc.
    assert (RX : 0 <= o + z3 < 2^64) by lia.
    pose proof (c0s_chk mc o 32 z3 1 (o + z3) HAc ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + z3) 8 ltac:(lia)); lia) ltac:(lia)) as SH.
    unfold c0s_at, c0s_R.
    bstep. step.
    chk_core (o + z3) RX (Z_to_bv 5 16) SH pre_sr no_extra.
    step.
    c0s_vst (8 + length P)%nat.
    step.
    rewrite (rc_eqb_lit (z3 + 1) 20) by lia.
    rewrite mb_fill_step in HV by first [reflexivity | lia].
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 3))) with (bz 3) in HV.
    destruct k as [|k].
    - replace (z3 + 1 =? 20) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
      step.
      replace (P ++ [bz 3]) with (slots row) in HV by (rewrite <- EP; reflexivity).
      rewrite (rs_slots_len row Hsy) in HV. change (24 - 12)%nat with 12%nat in HV.
      eapply c0s_tail; [exact G | exact HB | exact HV].
    - replace (z3 + 1 =? 20) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
      eapply (IH (P ++ [bz 3]) a1w 3 (z3 + 1) 20); [rewrite length_app; cbn [length]; lia | lia
        | rewrite <- EP, <- app_assoc; reflexivity | exact H1w | reflexivity | rewrite length_app; cbn [length]; lia
        | reflexivity | exact G | exact HB | exact HV].
  Qed.

  (* 0x870b4: both sides join; 12 slots done goes to the tail, else the fill loop. *)
  Lemma c0s_dd8 : forall P (z1 : Z) fr f spc j n w56 mc (x1 x5 x6 x7 a0 a2 a3 a4 a5 a6 a7 x22 x28 x29 x30 x31 : word),
    (length P <= 12)%nat -> P ++ repeat (bz 3) (12 - length P) = slots row -> z1 = Z.of_nat (length P) ->
    c0s_G fr f spc j n w56 -> c0s_K fr j n w56 mc ->
    rw_cells rsegs mc o [CB 32 (c0s_H8 ++ P ++ zeros (24 - length P))] ->
    evt rsegs c0s_Q (c0s_at 0x870b4 (c0s_R fr spc f x1 x5 x6 x7 a0 (Z_to_bv 64 z1) a2 a3 a4 a5 a6 a7
                                       x22 x28 x29 x30 x31) mc).
  Proof.
    intros P z1 fr f spc j n w56 mc x1 x5 x6 x7 a0 a2 a3 a4 a5 a6 a7 x22 x28 x29 x30 x31 LP EP E1 G HB HV.
    c0s_clr.
    destruct (c0s_go fr f spc j n w56 G) as (Go0 & Goe & Hsy). unfold APPMEM_END in Goe.
    unfold c0s_at, c0s_R.
    step. first [rewrite mb_addiw by lia | rewrite mb_swrap_lit by lia]. rewrite ?Z.add_0_r.
    step. step. rewrite mb_lts_lit by lia.
    destruct (Z.ltb_spec 11 z1) as [C|C]; cbv iota.
    - assert (L12 : length P = 12%nat) by lia. rewrite L12 in EP, HV.
      change (12 - 12)%nat with 0%nat in EP. cbn [repeat] in EP. rewrite app_nil_r in EP.
      rewrite EP in HV. change (24 - 12)%nat with 12%nat in HV.
      eapply c0s_tail; [exact G | exact HB | exact HV].
    - step. step. step. step. step. step.
      rewrite mb_zext32 by lia.
      eapply (c0s_fill (12 - length P) P); [lia | lia | exact EP | apply c0s_not; lia
        | first [reflexivity | lia] | lia | first [reflexivity | lia] | exact G | exact HB | exact HV].
  Qed.

  (* lay = 1: the input slots (0), at 0x86fe8 (with the 32-bit overflow test of the slot index). *)
  Lemma c0s_l2a : forall k P (z1 z2 z5 : Z) fr f spc j n w56 mc
      (x1 x5 x6 x7 a0 a3 a4 a6 a7 x22 x28 x29 x30 x31 : word),
    (length P + k <= 12)%nat -> (0 < k)%nat ->
    P ++ repeat (bz 0) k ++ repeat (bz 3) (12 - (length P + k)) = slots row ->
    z1 = Z.of_nat (length P) -> z2 = 2147483640 -> z5 = Z.of_nat k ->
    c0s_G fr f spc j n w56 -> c0s_K fr j n w56 mc ->
    rw_cells rsegs mc o [CB 32 (c0s_H8 ++ P ++ zeros (24 - length P))] ->
    evt rsegs c0s_Q (c0s_at 0x86fe8 (c0s_R fr spc f x1 x5 x6 x7 a0 (Z_to_bv 64 z1) (Z_to_bv 64 z2) a3 a4
                                       (Z_to_bv 64 z5) a6 a7 x22 x28 x29 x30 x31) mc).
  Proof.
    c0s_clr.
    induction k as [|k IH]; intros P z1 z2 z5 fr f spc j n w56 mc x1 x5 x6 x7 a0 a3 a4 a6 a7 x22 x28 x29 x30 x31
      Hk Hk0 EP E1 E2 E5 G HB HV; [lia|].
    subst z2.
    destruct (c0s_go fr f spc j n w56 G) as (Go0 & Goe & Hsy). unfold APPMEM_END in Goe.
    pose proof (c0s_ac fr f spc j n w56 mc G HB) as HAc.
    assert (RX : 0 <= z1 + 8 + o < 2^64) by lia.
    pose proof (c0s_chk mc o 32 (z1 + 8) 1 (z1 + 8 + o) HAc ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (z1 + 8 + o) 8 ltac:(lia)); lia) ltac:(lia)) as SH.
    unfold c0s_at, c0s_R.
    step. first [rewrite mb_addiw by lia | rewrite mb_swrap_lit by lia]. rewrite ?Z.add_0_r.
    bstep.
    step. rewrite mb_addiw by lia.
    step. bstep.
    step. rewrite mb_sltu0 by (rewrite ?unsigned_lit by lia; lia).
    step. rewrite mb_slti0 by lia.
    step. step. bst.
    chk_core (z1 + 8 + o) RX (Z_to_bv 5 14) SH pre_sr no_extra.
    c0s_vst (8 + length P)%nat.
    step. rewrite mb_addiw by lia.
    step. step.
    rewrite (rc_eqb_lit (z5 + -1) 0) by lia.
    rewrite mb_fill_step in HV by first [reflexivity | lia].
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0))) with (bz 0) in HV.
    destruct k as [|k].
    - replace (z5 + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
      step.
      eapply (c0s_dd8 (P ++ [bz 0]) (z1 + 1)); [rewrite length_app; cbn [length]; lia |
        | rewrite length_app; cbn [length]; lia | exact G | exact HB | exact HV].
      rewrite <- EP, <- app_assoc, length_app. reflexivity.
    - replace (z5 + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
      eapply (IH (P ++ [bz 0]) (z1 + 1) 2147483640 (z5 + -1)); [rewrite length_app; cbn [length]; lia | lia |
        | rewrite length_app; cbn [length]; lia | reflexivity | lia | exact G | exact HB | exact HV].
      rewrite <- EP, <- app_assoc, length_app. cbn [length app repeat].
      replace (length P + 1 + S k)%nat with (length P + S (S k))%nat by lia. reflexivity.
  Qed.

  (* lay <> 1: the output slots (1), at 0x8705c (with the 32-bit overflow test of the slot index). *)
  Lemma c0s_l2b : forall k P (z1 z2 z3 z4 : Z) fr f spc j n w56 mc
      (x1 x5 x6 x7 a0 a5 a6 a7 x22 x28 x29 x30 x31 : word),
    (length P + k <= 12)%nat -> (0 < k)%nat ->
    P ++ repeat (bz 1) k ++ repeat (bz 3) (12 - (length P + k)) = slots row ->
    z1 = Z.of_nat (length P) -> z2 = 2147483640 -> z3 = 1 -> z4 = Z.of_nat k ->
    c0s_G fr f spc j n w56 -> c0s_K fr j n w56 mc ->
    rw_cells rsegs mc o [CB 32 (c0s_H8 ++ P ++ zeros (24 - length P))] ->
    evt rsegs c0s_Q (c0s_at 0x8705c (c0s_R fr spc f x1 x5 x6 x7 a0 (Z_to_bv 64 z1) (Z_to_bv 64 z2) (Z_to_bv 64 z3)
                                       (Z_to_bv 64 z4) a5 a6 a7 x22 x28 x29 x30 x31) mc).
  Proof.
    c0s_clr.
    induction k as [|k IH]; intros P z1 z2 z3 z4 fr f spc j n w56 mc x1 x5 x6 x7 a0 a5 a6 a7 x22 x28 x29 x30 x31
      Hk Hk0 EP E1 E2 E3 E4 G HB HV; [lia|].
    subst z2 z3.
    destruct (c0s_go fr f spc j n w56 G) as (Go0 & Goe & Hsy). unfold APPMEM_END in Goe.
    pose proof (c0s_ac fr f spc j n w56 mc G HB) as HAc.
    assert (RX : 0 <= z1 + 8 + o < 2^64) by lia.
    pose proof (c0s_chk mc o 32 (z1 + 8) 1 (z1 + 8 + o) HAc ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (z1 + 8 + o) 8 ltac:(lia)); lia) ltac:(lia)) as SH.
    unfold c0s_at, c0s_R.
    step. first [rewrite mb_addiw by lia | rewrite mb_swrap_lit by lia]. rewrite ?Z.add_0_r.
    bstep.
    step. rewrite mb_addiw by lia.
    step. bstep.
    step. rewrite mb_sltu0 by (rewrite ?unsigned_lit by lia; lia).
    step. rewrite mb_slti0 by lia.
    step. step. bst.
    chk_core (z1 + 8 + o) RX (Z_to_bv 5 16) SH pre_sr no_extra.
    c0s_vst (8 + length P)%nat.
    step. rewrite mb_addiw by lia.
    step. step.
    rewrite (rc_eqb_lit (z4 + -1) 0) by lia.
    rewrite mb_fill_step in HV by first [reflexivity | lia].
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (bz 1) in HV.
    destruct k as [|k].
    - replace (z4 + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
      step.
      eapply (c0s_dd8 (P ++ [bz 1]) (z1 + 1)); [rewrite length_app; cbn [length]; lia |
        | rewrite length_app; cbn [length]; lia | exact G | exact HB | exact HV].
      rewrite <- EP, <- app_assoc, length_app. reflexivity.
    - replace (z4 + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
      eapply (IH (P ++ [bz 1]) (z1 + 1) 2147483640 1 (z4 + -1)); [rewrite length_app; cbn [length]; lia | lia |
        | rewrite length_app; cbn [length]; lia | reflexivity | reflexivity | lia | exact G | exact HB | exact HV].
      rewrite <- EP, <- app_assoc, length_app. cbn [length app repeat].
      replace (length P + 1 + S k)%nat with (length P + S (S k))%nat by lia. reflexivity.
  Qed.

  (* lay = 1, after the output slots: 0x86fd4 (0x86fd0 sets a1 = 0 when there is none). *)
  Lemma c0s_ec4 : forall P (z1 : Z) fr f spc j n w56 mc (x1 x5 x6 x7 a0 a3 a4 a6 a7 x22 x28 x29 x30 x31 : word),
    lay row = 1 -> P = repeat (bz 1) (Z.to_nat (oc row / 4)) -> z1 = Z.of_nat (length P) ->
    c0s_G fr f spc j n w56 -> c0s_K fr j n w56 mc ->
    rw_cells rsegs mc o [CB 32 (c0s_H8 ++ P ++ zeros (24 - length P))] ->
    evt rsegs c0s_Q (c0s_at 0x86fd4 (c0s_R fr spc f x1 x5 x6 x7 a0 (Z_to_bv 64 z1) (Z_to_bv 64 (ic row)) a3 a4
                                       (Z_to_bv 64 (ic row / 4)) a6 a7 x22 x28 x29 x30 x31) mc).
  Proof.
    intros P z1 fr f spc j n w56 mc x1 x5 x6 x7 a0 a3 a4 a6 a7 x22 x28 x29 x30 x31 L1 EP E1 G HB HV.
    c0s_clr.
    destruct (c0s_go fr f spc j n w56 G) as (Go0 & Goe & Hsy). unfold APPMEM_END in Goe.
    pose proof (proj1 (mb_synok_iff row) Hsy) as (Ri & Ro0 & Mi & Mo & Sum).
    pose proof (rs_ic_range row) as RI.
    assert (LP : length P = Z.to_nat (oc row / 4)) by (rewrite EP, repeat_length; reflexivity).
    assert (ES : slots row = P ++ repeat (bz 0) (Z.to_nat (ic row / 4)) ++
                             repeat (bz 3) (12 - (length P + Z.to_nat (ic row / 4)))).
    { rewrite (rs_slots_1 row L1), LP, <- EP.
      replace (12 - Z.to_nat (ic row / 4) - Z.to_nat (oc row / 4))%nat
        with (12 - (Z.to_nat (oc row / 4) + Z.to_nat (ic row / 4)))%nat by lia. reflexivity. }
    unfold c0s_at, c0s_R.
    step. rewrite rc_eqb_lit by lia.
    destruct (Z.eqb_spec (ic row) 0) as [I0|I0]; cbv iota.
    - eapply (c0s_dd8 P z1); [rewrite LP; lia | | exact E1 | exact G | exact HB | exact HV].
      rewrite ES, I0. change (Z.to_nat (0 / 4)) with 0%nat. rewrite Nat.add_0_r. reflexivity.
    - step. step. rewrite rs_seqz by lia. step. step.
      eapply (c0s_l2a (Z.to_nat (ic row / 4)) P); [lia | lia | symmetry; exact ES | exact E1
        | first [reflexivity | vm_compute; reflexivity | lia] | lia | exact G | exact HB | exact HV].
  Qed.

  (* lay <> 1, after the input slots: 0x87044 (0x87040 sets a1 = 0 when there is none). *)
  Lemma c0s_f34 : forall P (z1 : Z) fr f spc j n w56 mc (x1 x5 x6 x7 a0 a2 a5 a6 a7 x22 x28 x29 x30 x31 : word),
    lay row <> 1 -> P = repeat (bz 2) (Z.to_nat (ic row / 4)) -> z1 = Z.of_nat (length P) ->
    c0s_G fr f spc j n w56 -> c0s_K fr j n w56 mc ->
    rw_cells rsegs mc o [CB 32 (c0s_H8 ++ P ++ zeros (24 - length P))] ->
    evt rsegs c0s_Q (c0s_at 0x87044 (c0s_R fr spc f x1 x5 x6 x7 a0 (Z_to_bv 64 z1) a2 (Z_to_bv 64 (oc row))
                                       (Z_to_bv 64 (oc row / 4)) a5 a6 a7 x22 x28 x29 x30 x31) mc).
  Proof.
    intros P z1 fr f spc j n w56 mc x1 x5 x6 x7 a0 a2 a5 a6 a7 x22 x28 x29 x30 x31 L1 EP E1 G HB HV.
    c0s_clr.
    destruct (c0s_go fr f spc j n w56 G) as (Go0 & Goe & Hsy). unfold APPMEM_END in Goe.
    pose proof (proj1 (mb_synok_iff row) Hsy) as (Ri & Ro0 & Mi & Mo & Sum).
    pose proof (rs_oc_range row) as RO.
    assert (LP : length P = Z.to_nat (ic row / 4)) by (rewrite EP, repeat_length; reflexivity).
    assert (ES : slots row = P ++ repeat (bz 1) (Z.to_nat (oc row / 4)) ++
                             repeat (bz 3) (12 - (length P + Z.to_nat (oc row / 4)))).
    { rewrite (rs_slots_2 row L1), LP, <- EP.
      replace (12 - Z.to_nat (ic row / 4) - Z.to_nat (oc row / 4))%nat
        with (12 - (Z.to_nat (ic row / 4) + Z.to_nat (oc row / 4)))%nat by lia. reflexivity. }
    unfold c0s_at, c0s_R.
    step. rewrite rc_eqb_lit by lia.
    destruct (Z.eqb_spec (oc row) 0) as [O0|O0]; cbv iota.
    - eapply (c0s_dd8 P z1); [rewrite LP; lia | | exact E1 | exact G | exact HB | exact HV].
      rewrite ES, O0. change (Z.to_nat (0 / 4)) with 0%nat. rewrite Nat.add_0_r. reflexivity.
    - step. step. step. rewrite rs_seqz by lia. step. step.
      eapply (c0s_l2b (Z.to_nat (oc row / 4)) P); [lia | lia | symmetry; exact ES | exact E1
        | first [reflexivity | vm_compute; reflexivity | lia] | first [reflexivity | lia] | lia
        | exact G | exact HB | exact HV].
  Qed.

  (* lay = 1: the output slots (1), at 0x868e0. *)
  Lemma c0s_l1a : forall k P nn (z0 z1 z3 z4 z6 : Z) fr f spc j n w56 mc (x1 x5 x6 x7 a7 x22 x28 x29 x30 x31 : word),
    lay row = 1 -> (length P + k = nn)%nat -> nn = Z.to_nat (oc row / 4) -> (0 < k)%nat -> P = repeat (bz 1) (length P) ->
    z0 = o + Z.of_nat (8 + length P) -> z3 = o + Z.of_nat (8 + length P) -> z1 = Z.of_nat nn -> z4 = 1 ->
    z6 = Z.of_nat k ->
    c0s_G fr f spc j n w56 -> c0s_K fr j n w56 mc ->
    rw_cells rsegs mc o [CB 32 (c0s_H8 ++ P ++ zeros (24 - length P))] ->
    evt rsegs c0s_Q (c0s_at 0x868e0 (c0s_R fr spc f x1 x5 x6 x7 (Z_to_bv 64 z0) (Z_to_bv 64 z1) (Z_to_bv 64 (ic row))
                                       (Z_to_bv 64 z3) (Z_to_bv 64 z4) (Z_to_bv 64 (ic row / 4)) (Z_to_bv 64 z6) a7
                                       x22 x28 x29 x30 x31) mc).
  Proof.
    c0s_clr.
    induction k as [|k IH]; intros P nn z0 z1 z3 z4 z6 fr f spc j n w56 mc x1 x5 x6 x7 a7 x22 x28 x29 x30 x31
      L1 Hn En Hk EP E0 E3 E1 E4 E6 G HB HV; [lia|].
    subst z4.
    destruct (c0s_go fr f spc j n w56 G) as (Go0 & Goe & Hsy). unfold APPMEM_END in Goe.
    pose proof (proj1 (mb_synok_iff row) Hsy) as (Ri & Ro0 & Mi & Mo & Sum).
    assert (LP : (length P < 12)%nat) by lia.
    pose proof (c0s_ac fr f spc j n w56 mc G HB) as HAc.
    assert (RX : 0 <= z0 < 2^64) by lia.
    pose proof (c0s_chk mc o 32 (Z.of_nat (8 + length P)) 1 z0 HAc ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound z0 8 ltac:(lia)); lia) ltac:(lia)) as SH.
    unfold c0s_at, c0s_R.
    bstep. bstep.
    chk_core z0 RX (Z_to_bv 5 5) SH pre_sr no_extra.
    c0s_vst (8 + length P)%nat.
    step. step. step. step.
    rewrite (rc_eqb_lit (z6 + -1) 0) by lia.
    rewrite mb_fill_step in HV by first [reflexivity | lia].
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (bz 1) in HV.
    assert (EP' : P ++ [bz 1] = repeat (bz 1) (length (P ++ [bz 1])))
      by (rewrite length_app; cbn [length]; rewrite Nat.add_1_r, <- mb_rep_snoc, <- EP; reflexivity).
    destruct k as [|k].
    - replace (z6 + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
      eapply (c0s_ec4 (P ++ [bz 1])); [exact L1 | rewrite EP'; f_equal; rewrite length_app; cbn [length]; lia
        | rewrite length_app; cbn [length]; lia | exact G | exact HB | exact HV].
    - replace (z6 + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
      step.
      eapply (IH (P ++ [bz 1]) nn (z0 + 1) z1 (z3 + 1) 1 (z6 + -1)); [exact L1 | rewrite length_app; cbn [length]; lia
        | exact En | lia | exact EP' | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
        | exact E1 | reflexivity | lia | exact G | exact HB | exact HV].
  Qed.

  (* lay <> 1: the input slots (2), at 0x86f94. *)
  Lemma c0s_l1b : forall k P nn (z0 z1 z2 z5 z6 : Z) fr f spc j n w56 mc (x1 x5 x6 x7 a7 x22 x28 x29 x30 x31 : word),
    lay row <> 1 -> (length P + k = nn)%nat -> nn = Z.to_nat (ic row / 4) -> (0 < k)%nat -> P = repeat (bz 2) (length P) ->
    z0 = o + Z.of_nat (8 + length P) -> z2 = o + Z.of_nat (8 + length P) -> z1 = Z.of_nat nn -> z5 = 2 ->
    z6 = Z.of_nat k ->
    c0s_G fr f spc j n w56 -> c0s_K fr j n w56 mc ->
    rw_cells rsegs mc o [CB 32 (c0s_H8 ++ P ++ zeros (24 - length P))] ->
    evt rsegs c0s_Q (c0s_at 0x86f94 (c0s_R fr spc f x1 x5 x6 x7 (Z_to_bv 64 z0) (Z_to_bv 64 z1) (Z_to_bv 64 z2)
                                       (Z_to_bv 64 (oc row)) (Z_to_bv 64 (oc row / 4)) (Z_to_bv 64 z5) (Z_to_bv 64 z6) a7
                                       x22 x28 x29 x30 x31) mc).
  Proof.
    c0s_clr.
    induction k as [|k IH]; intros P nn z0 z1 z2 z5 z6 fr f spc j n w56 mc x1 x5 x6 x7 a7 x22 x28 x29 x30 x31
      L1 Hn En Hk EP E0 E2 E1 E5 E6 G HB HV; [lia|].
    subst z5.
    destruct (c0s_go fr f spc j n w56 G) as (Go0 & Goe & Hsy). unfold APPMEM_END in Goe.
    pose proof (proj1 (mb_synok_iff row) Hsy) as (Ri & Ro0 & Mi & Mo & Sum).
    assert (LP : (length P < 12)%nat) by lia.
    pose proof (c0s_ac fr f spc j n w56 mc G HB) as HAc.
    assert (RX : 0 <= z0 < 2^64) by lia.
    pose proof (c0s_chk mc o 32 (Z.of_nat (8 + length P)) 1 z0 HAc ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound z0 8 ltac:(lia)); lia) ltac:(lia)) as SH.
    unfold c0s_at, c0s_R.
    bstep. bstep.
    chk_core z0 RX (Z_to_bv 5 5) SH pre_sr no_extra.
    c0s_vst (8 + length P)%nat.
    step. step. step. step.
    rewrite (rc_eqb_lit (z6 + -1) 0) by lia.
    rewrite mb_fill_step in HV by first [reflexivity | lia].
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 2))) with (bz 2) in HV.
    assert (EP' : P ++ [bz 2] = repeat (bz 2) (length (P ++ [bz 2])))
      by (rewrite length_app; cbn [length]; rewrite Nat.add_1_r, <- mb_rep_snoc, <- EP; reflexivity).
    destruct k as [|k].
    - replace (z6 + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
      eapply (c0s_f34 (P ++ [bz 2])); [exact L1 | rewrite EP'; f_equal; rewrite length_app; cbn [length]; lia
        | rewrite length_app; cbn [length]; lia | exact G | exact HB | exact HV].
    - replace (z6 + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
      step.
      eapply (IH (P ++ [bz 2]) nn (z0 + 1) z1 (z2 + 1) 2 (z6 + -1)); [exact L1 | rewrite length_app; cbn [length]; lia
        | exact En | lia | exact EP' | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
        | exact E1 | reflexivity | lia | exact G | exact HB | exact HV].
  Qed.

  (* 0x868c4, lay = 1. *)
  Lemma c0s_s1 : forall fr f spc j n w56 mc (x1 x5 x6 x7 a0 a1 a6 a7 x22 x28 x29 x30 x31 : word),
    lay row = 1 -> c0s_G fr f spc j n w56 -> c0s_K fr j n w56 mc ->
    rw_cells rsegs mc o [CB 32 (c0s_H8 ++ zeros 24)] ->
    evt rsegs c0s_Q (c0s_at 0x868c4 (c0s_R fr spc f x1 x5 x6 x7 a0 a1 (Z_to_bv 64 (ic row)) (Z_to_bv 64 (oc row))
                                       (Z_to_bv 64 (oc row / 4)) (Z_to_bv 64 (ic row / 4)) a6 a7 x22 x28 x29 x30 x31) mc).
  Proof.
    intros fr f spc j n w56 mc x1 x5 x6 x7 a0 a1 a6 a7 x22 x28 x29 x30 x31 L1 G HB HV.
    c0s_clr.
    destruct (c0s_go fr f spc j n w56 G) as (Go0 & Goe & Hsy). unfold APPMEM_END in Goe.
    pose proof (proj1 (mb_synok_iff row) Hsy) as (Ri & Ro0 & Mi & Mo & Sum).
    pose proof (rs_oc_range row) as RO.
    unfold c0s_at, c0s_R.
    step. rewrite rc_eqb_lit by lia.
    destruct (Z.eqb_spec (oc row) 0) as [O0|O0]; cbv iota.
    - step.
      eapply (c0s_ec4 []); [exact L1 | rewrite O0; reflexivity | first [reflexivity | lia] | exact G | exact HB
        | exact HV].
    - step. step. rewrite rs_seqz by lia. step. step. step. step.
      eapply (c0s_l1a (Z.to_nat (oc row / 4)) [] (Z.to_nat (oc row / 4))); [exact L1 | cbn [length]; lia | reflexivity
        | lia | reflexivity | cbn [length]; lia | cbn [length]; lia | lia | first [reflexivity | lia] | lia
        | exact G | exact HB | exact HV].
  Qed.

  (* 0x86f78, lay <> 1. *)
  Lemma c0s_s2 : forall fr f spc j n w56 mc (x1 x5 x6 x7 a0 a1 a6 a7 x22 x28 x29 x30 x31 : word),
    lay row <> 1 -> c0s_G fr f spc j n w56 -> c0s_K fr j n w56 mc ->
    rw_cells rsegs mc o [CB 32 (c0s_H8 ++ zeros 24)] ->
    evt rsegs c0s_Q (c0s_at 0x86f78 (c0s_R fr spc f x1 x5 x6 x7 a0 a1 (Z_to_bv 64 (ic row)) (Z_to_bv 64 (oc row))
                                       (Z_to_bv 64 (oc row / 4)) (Z_to_bv 64 (ic row / 4)) a6 a7 x22 x28 x29 x30 x31) mc).
  Proof.
    intros fr f spc j n w56 mc x1 x5 x6 x7 a0 a1 a6 a7 x22 x28 x29 x30 x31 L1 G HB HV.
    c0s_clr.
    destruct (c0s_go fr f spc j n w56 G) as (Go0 & Goe & Hsy). unfold APPMEM_END in Goe.
    pose proof (proj1 (mb_synok_iff row) Hsy) as (Ri & Ro0 & Mi & Mo & Sum).
    pose proof (rs_ic_range row) as RI.
    unfold c0s_at, c0s_R.
    step. rewrite rc_eqb_lit by lia.
    destruct (Z.eqb_spec (ic row) 0) as [I0|I0]; cbv iota.
    - step.
      eapply (c0s_f34 []); [exact L1 | rewrite I0; reflexivity | first [reflexivity | lia] | exact G | exact HB
        | exact HV].
    - step. step. rewrite rs_seqz by lia. step. step. step. step.
      eapply (c0s_l1b (Z.to_nat (ic row / 4)) [] (Z.to_nat (ic row / 4))); [exact L1 | cbn [length]; lia | reflexivity
        | lia | reflexivity | cbn [length]; lia | cbn [length]; lia | lia | first [reflexivity | lia] | lia
        | exact G | exact HB | exact HV].
  Qed.

  (* Statement (2b) of the pin, verbatim. *)
  Lemma c0s_lay1 :
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
    evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) a0 a1
               (Z_to_bv 64 (ic row)) (Z_to_bv 64 (oc row)) (Z_to_bv 64 (oc row / 4)) (Z_to_bv 64 (ic row / 4)) a6 a7
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x868c4) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc x1 x5 x6 x7 a0 a1 a6 a7 x22 x28 x29 x30 x31 L1 G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12
      G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 HB HV.
    exact (c0s_s1 fr f spc j n w56 mc x1 x5 x6 x7 a0 a1 a6 a7 x22 x28 x29 x30 x31 L1
             (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 (conj G7 (conj G8 (conj G9 (conj G10 (conj G11 (conj G12 (conj G13 (conj G14 (conj G15 (conj G16 (conj G17 (conj G18 (conj G19 (conj G20 (conj G21 (conj G22 (conj G23 (conj G24 (conj G25 (conj G26 G27))))))))))))))))))))))))))
             HB HV).
  Qed.

  (* Statement (2c) of the pin, verbatim. *)
  Lemma c0s_lay2 :
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
    evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) a0 a1
               (Z_to_bv 64 (ic row)) (Z_to_bv 64 (oc row)) (Z_to_bv 64 (oc row / 4)) (Z_to_bv 64 (ic row / 4)) a6 a7
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x86f78) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc x1 x5 x6 x7 a0 a1 a6 a7 x22 x28 x29 x30 x31 L1 G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12
      G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 HB HV.
    exact (c0s_s2 fr f spc j n w56 mc x1 x5 x6 x7 a0 a1 a6 a7 x22 x28 x29 x30 x31 L1
             (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 (conj G7 (conj G8 (conj G9 (conj G10 (conj G11 (conj G12 (conj G13 (conj G14 (conj G15 (conj G16 (conj G17 (conj G18 (conj G19 (conj G20 (conj G21 (conj G22 (conj G23 (conj G24 (conj G25 (conj G26 G27))))))))))))))))))))))))))
             HB HV).
  Qed.
End Body.
