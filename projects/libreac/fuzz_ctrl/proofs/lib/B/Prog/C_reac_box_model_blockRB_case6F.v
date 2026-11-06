(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 550 of its 565 lines of code are new or changed and 233 lines of the source are left out. *)
(* GENERATED - do not edit.  C_reac_box_model_blockRB_case6F.v is the re-based copy of lib/B/Prog/reac_box_model_block_case6F.v at 20372bbcc3a
   (source sha256 5bd6f5ed6f1b9adb721b1707e7ad6c441630aa89c7180b74bc2b474df777c8e2) by gen_rb_modelblock.py
   (its sha256 is cited in the commit that adds this file); the substitutions are listed there.  Dropped here: nothing. *)
(* This delivery then edited comment text only: the code is unchanged from release c5e779efe8c, the comments are not. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcParseLib RcKindLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c dt1_head_c name_field_c reac_box_model_block_c
  C_reac_box_model_blockRB C_reac_box_model_blockRBF C_reac_box_model_blockRB_case56 C_reac_box_model_blockRB_case6
  C_reac_box_model_blockRB_case56F.
(* Last: StepF's step / if_false / mem_after_store (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_box_model_block_c_on reac_box_model_block_cF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c_on asan_stack_malloc_cF_on asan_memset_c_on asan_memset_cF_on
  asan_memcpy_c_on asan_memcpy_cF_on sh_word_on C_reac_box_model_blockOnHB.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import name_field_c_on.
Import ListNotations.
Open Scope Z_scope.

(* Local copy of C_reac_box_model_blockRB.v:228's store hook: that file made it Local (a Theorem Labs lane; generator owner a Theorem Labs lane stopped, a Theorem Labs lane audits). *)
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

(* The footprint twin of C_reac_box_model_blockRB_case6.v (image B, asan-ubsan; RECIPE.md step 1, route 2 (a working note, not in this delivery)):
   the case b = 6 of reac_box_model_block (0x86b24 to the release at 0x86e14) as an ExecF.evtF run under the
   footprint RNG, by the plain file's scripts over StepF's step.  Every lemma of C_reac_box_model_blockRB_case6.v that
   does not mention `evt` is used from there with its Section arguments; this file restates the seven that do
   (c6_call_nf, c6_call_mco, c6_call_mcf, c6_loop6, c6_tail6, c6_loopr, c6_case6, each with suffix F).
   The four evt lemmas of C_reac_box_model_blockRB_case56.v that the plain file wraps (c56_call_nf, c56_call_mco,
   c56_call_mcf, c56_loop6) come from their twins in C_reac_box_model_blockRB_case56F.v. *)

(* The byte stores of this case write a register value, so the cell of a 1-byte store is read off le1 (as in
   the ubsan twin lib/U/Prog/C_reac_box_model_blockRB.v). *)
Local Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?bb] => constr:(C1 bb)
  | le1 (zxb ?bb) => constr:(C1 bb)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The store hook of this file: Tac.v's mem_after_store_opt (the hook the plain files run under) on evtF goals.  It
   folds Z_to_le_bytes of a literal into le8 / le4 / le2 / le1 as Tac's fix_lit_store does, and it does not run
   StepF's norm_lit_store_bytes, whose le1 (Z_to_bv 64 z) -> [Z_to_bv 8 z] folding would leave nothing for the
   scripts' own `rewrite rc_le1_*`. *)
Ltac mbF_fix_lit_store :=
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => rewrite (le2_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_zlit z) by lia
  | _ => idtac
  end.

Ltac mbF_store_opt :=
  try mbF_fix_lit_store;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::= mbF_store_opt.

Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= mbF_acc_hint.

Section c6_SF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte) (RNG : footprint).
  Hypothesis HSM : asan_stack_malloc_0_contract_F_on.
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

  Hypothesis HMS : asan_memset_contract_F_on.
  Hypothesis HMC : asan_memcpy_contract_F_on.
  Hypothesis HBD : build_dt1_single_contract_F_on.
  Hypothesis HDH : dt1_head_contract_F_on.
  Hypothesis HNF : name_field_contract_F_on.

  (* The release continuation at 0x86e14 (rel_stmt of mbb-interface-pin.md, verbatim). *)
  Hypothesis Hrel : forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte) (ret : Z)
       (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
  FK FS A fr f spc j n w56 ->
  ret = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
  BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS
     (Wf sp FS fr j n ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)])) fr w56 mc ->
  (if (p =? 0) || (o =? 0) then True else bytes_at rsegs mc o (synth row b nb)) ->
  evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
    (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 ret) x22 (Z_to_bv 64 fr)
            (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86e14) fc None mc (seg_rom rsegs)).

  Hypothesis HRNG : mbF_rng RNG m sp tp p b o FS row nb.

  (* PERF (mbb-lanes-common.md): lia and Z.div_mod_to_equations never run with the Section's hypotheses in scope;
     every arithmetic step below drops them first, and takes what it needs from a named hypothesis.  Hoff stays:
     the prelude's shadow-access hook (mbF_rng1) rewrites `X / 8 + off` to `X / 8 + ASAN_K` with it. *)
  Ltac c6_sc :=
    try clear HRNG;
    try clear Hrel; try clear HNF; try clear HDH; try clear HBD; try clear HMC; try clear HMS;
    try clear NDJ; try clear AJ2; try clear AJ1; try clear AO; try clear ANB; try clear AP;
    try clear HO; try clear HN; try clear HP; try clear TLS0; try clear FP0; try clear AW0;
    try clear SR0; try clear AC0; try clear MI0; try clear ST0; try clear HS16; try clear HA;
    try clear HSM.
  (* The arithmetic context for lia: the Section's hypotheses and every memory fact dropped, the linear facts
     kept. *)
  Ltac c6_ar :=
    c6_sc;
    repeat match goal with
    | H : forall _ : word -> option byte, _ |- _ => clear H
    | H : forall _ : word, _ |- _ => clear H
    | H : forall _ : Z, _ |- _ => clear H
    | H : forall _ : nat, _ |- _ => clear H
    | H : forall _ : list byte, _ |- _ => clear H
    | H : BI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => clear H
    | H : rw_cells _ _ _ _ |- _ => clear H
    | H : ro_cells _ _ _ _ |- _ => clear H
    | H : bytes_at _ _ _ _ |- _ => clear H
    | H : stk _ _ _ _ |- _ => clear H
    | H : munch _ _ _ |- _ => clear H
    | H : wmono _ _ _ |- _ => clear H
    | H : rd_mono _ _ |- _ => clear H
    | H : addressable _ _ _ |- _ => clear H
    | H : asan_cells _ |- _ => clear H
    | H : shadow_rw _ |- _ => clear H
    | H : mem_inv _ _ |- _ => clear H
    | H : fp_dj _ _ |- _ => clear H
    | H : name_ok _ |- _ => clear H
    | H : ov_read_bytes _ _ _ _ = _ |- _ => clear H
    | H : store_ok _ _ _ _ = _ |- _ => clear H
    end.
  Ltac c6_lia := c6_ar; lia.
  Ltac c6_hide H := let T := type of H in change (c6_box T) in H.
  Ltac c6_show H := unfold c6_box in H.

  (* ---- the case56 lemmas with this Section's variables and hypotheses supplied once ---- *)

  Lemma c6_call_nfF : forall (k ret fr f spc j n : Z) (w56 : word) (mc : word -> option byte) (WB OB : list byte)
      (x5 x6 x7 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
    p <> 0 -> o <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 ->
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> 35 <= k -> k + 16 <= 72 ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c6_W sp o FS fr j n) fr w56 mc ->
    rw_cells rsegs mc (A + 35) [CB 37 WB] -> rw_cells rsegs mc o [CB 32 OB] ->
    (forall (mc' : word -> option byte) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c6_W sp o FS fr j n) fr w56 mc' ->
       rw_cells rsegs mc' (A + 35) [CB 37 (upd_bytes WB (Z.to_nat (k - 35)) (nmr row nb))] ->
       rw_cells rsegs mc' o [CB 32 OB] ->
       bytes_at rsegs mc' (A + k) (nmr row nb) -> length (nmr row nb) = 16%nat ->
       evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
         (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spc) gp tp y5 y6 y7 sp (Z_to_bv 64 A)
                  y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) x21 x22
                  (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 y28 y29 y30 y31)
             F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
      (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A)
               (Z_to_bv 64 p) (Z_to_bv 64 (A + k)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 f) (Z_to_bv 64 o)
               (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 NAME_FIELD) fc None mc (seg_rom rsegs)).
  Proof. intros. eapply c56_call_nfF; eassumption. Qed.

  Lemma c6_call_mcoF : forall (kd ks N ret fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (WB OB : list byte) (x5 x6 x7 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
    p <> 0 -> o <> 0 -> ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret ->
    0 <= kd -> kd + 8 <= 32 -> kd + N <= 32 -> 35 <= ks -> ks + N <= 72 -> 0 <= N ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c6_W sp o FS fr j n) fr w56 mc ->
    rw_cells rsegs mc (A + 35) [CB 37 WB] -> rw_cells rsegs mc o [CB 32 OB] ->
    (forall (mc' : word -> option byte) (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c6_W sp o FS fr j n) fr w56 mc' ->
       rw_cells rsegs mc' (A + 35) [CB 37 WB] ->
       rw_cells rsegs mc' o
         [CB 32 (upd_bytes OB (Z.to_nat kd) (firstn (Z.to_nat N) (skipn (Z.to_nat (ks - 35)) WB)))] ->
       evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
         (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spc) gp tp y5 y6 y7 sp (Z_to_bv 64 A)
                  (Z_to_bv 64 (o + kd)) y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 f) (Z_to_bv 64 o)
                  (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11
                  y28 y29 y30 y31)
             F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
      (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A)
               (Z_to_bv 64 (o + kd)) (Z_to_bv 64 (A + ks)) (Z_to_bv 64 N) x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 ASAN_MEMCPY) fc None mc (seg_rom rsegs)).
  Proof. intros. eapply c56_call_mcoF; eassumption. Qed.

  Lemma c6_call_mcfF : forall (kd ks N ret fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (WB OB : list byte) (x5 x6 x7 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
    p <> 0 -> o <> 0 -> ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret ->
    35 <= kd -> kd + N <= ks -> ks + N <= 72 -> 0 <= N ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c6_W sp o FS fr j n) fr w56 mc ->
    rw_cells rsegs mc (A + 35) [CB 37 WB] -> rw_cells rsegs mc o [CB 32 OB] ->
    (forall (mc' : word -> option byte) (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c6_W sp o FS fr j n) fr w56 mc' ->
       rw_cells rsegs mc' (A + 35)
         [CB 37 (upd_bytes WB (Z.to_nat (kd - 35)) (firstn (Z.to_nat N) (skipn (Z.to_nat (ks - 35)) WB)))] ->
       rw_cells rsegs mc' o [CB 32 OB] ->
       evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
         (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spc) gp tp y5 y6 y7 sp (Z_to_bv 64 A)
                  (Z_to_bv 64 (A + kd)) y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 f) (Z_to_bv 64 o)
                  (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11
                  y28 y29 y30 y31)
             F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
      (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A)
               (Z_to_bv 64 (A + kd)) (Z_to_bv 64 (A + ks)) (Z_to_bv 64 N) x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 ASAN_MEMCPY) fc None mc (seg_rom rsegs)).
  Proof. intros. eapply c56_call_mcfF; eassumption. Qed.

  Lemma c6_loop6F : forall (kk i : nat) (X : list byte) (a3w : word) (fr f spc j n : Z) (w56 : word)
      (mc : word -> option byte) (x1 x5 x6 x7 x10 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
    p <> 0 -> o <> 0 -> (i + kk = 31)%nat -> (0 < kk)%nat -> length X = 32%nat ->
    bv_unsigned a3w = 18446744073709551615 - o ->
    withchk (firstn 31 X) = synth row b nb -> rc row b = 1 ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c6_W sp o FS fr j n) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 X] ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A)
               x10 (Z_to_bv 64 (psum X i)) (Z_to_bv 64 (Z.of_nat i)) a3w (Z_to_bv 64 31) x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86d84) fc None mc (seg_rom rsegs)).
  Proof. intros. eapply c56_loop6F; eassumption. Qed.

  (* ---- b = 6: the pre-tail, the record sum and the case ---- *)

  (* 0x86d28: the shadow checks of o + 15 and o + 16, the stamp byte (- sum) mod 128 at o + 15 and the 247 at
     o + 16, then the outer sum loop at 0x86d84 (port of the ubsan twin's tail6, U line 707). *)
  Lemma c6_tail6F : forall (X REC : list byte) (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
    p <> 0 -> o <> 0 -> length X = 32%nat ->
    0 <= psum REC 21 < 2^31 ->
    withchk (firstn 31 (upd_bytes X 15 [Z_to_bv 8 ((- psum REC 21) mod 128); bz 247])) = synth row b nb ->
    rc row b = 1 ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c6_W sp o FS fr j n) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 X] ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A)
               x10 (Z_to_bv 64 (psum REC 21)) x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86d28) fc None mc (seg_rom rsegs)).
  Proof.
    mbF_open HRNG.
    intros X REC fr f spc j n w56 mc x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31
      Hp0 Ho0 LX PR ES Er HK HB HOc.
    destruct (ROUT Hp0 Ho0) as (ROUTr & ROUTc & ROUTs & ROUTk).
    pose proof c6_loop6F as L6. pose proof (c6_chk off Hoff) as CHK.
    pose proof (c6_addr_o sp tp m p b o FS off A ob Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro HO AO
                  Ho0 fr f spc j n w56) as AOw.
    destruct (c6_geoA sp tp m p b o FS off A Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro fr f spc j n w56 HK)
      as (Rsp & HA32 & HAlo & HAhi & FR8 & FRlo & FRhi & Fsp & FSpos & FSsz & HM1 & HM2).
    destruct (c6_geoO sp tp m p b o FS ob FP0 Rp Rb Ro HO AO Ho0)
      as (HoA & Dos & Drt & Hoapp & Oapp & Dofs & DofsF).
    pose proof (c6_o_fr_iv sp tp m p b o FS off A ob Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro HO AO
                  Ho0 fr f spc j n w56 HK) as Dofr.
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI & SV & (hh & HH) & F56).
    assert (RX15 : 0 <= o + 15 < 2^64) by c6_lia.
    assert (RX16 : 0 <= o + 16 < 2^64) by c6_lia.
    unfold c6_W, Wf in MU. cbn [app] in MU. unfold SAVES in SV.
    clear HB Fsp Drt DofsF Oapp Hoapp.
    c6_sc.
    (* 0x86d28: the store at o + 15 does not wrap, then its shadow check *)
    pose proof (CHK _ o 32 15 1 (o + 15) (AOw _ HK MU) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 15) 8 eq_refl); lia) eq_refl) as SH15.
    step. bstep.
    step.
    chk_core (o + 15) RX15 (Z_to_bv 5 13) SH15 pre_sr no_extra.
    (* 0x86d44: negw / andi 127, the stamp byte at o + 15, then the check of o + 16 (on the memory after
       that store) *)
    step. step. step. step. bstep.
    pose proof (CHK _ o 32 16 1 (o + 16) (AOw _ HK MU) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 16) 8 eq_refl); lia) eq_refl) as SH16.
    step.
    chk_core (o + 16) RX16 (Z_to_bv 5 12) SH16 pre_sr no_extra.
    (* 0x86d6c: the 247 at o + 16 and the registers of the outer sum *)
    step. step. step. step. step. step.
    apply (rs_rw_take _ _ _ _ 4) in HOc.
    cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in HOc.
    rewrite mb_stamp8 in HOc.
    match type of HOc with rw_cells _ _ _ [CB 32 ?X6] =>
      replace X6 with (upd_bytes X 15 [Z_to_bv 8 ((- psum REC 21) mod 128); bz 247]) in HOc end.
    2:{ unfold upd_bytes. rewrite (c6_skk X 1 16). cbn [length Nat.add app]. rewrite ?app_nil_r.
        f_equal. apply mb_cons; [reflexivity|].
        apply mb_cons; [apply Z_to_bv8_mod; vm_compute; reflexivity|]. reflexivity. }
    eapply (L6 31%nat 0%nat (upd_bytes X 15 [Z_to_bv 8 ((- psum REC 21) mod 128); bz 247]) _
              fr f spc j n w56 _);
      [exact Hp0 | exact Ho0 | lia | lia
      | rewrite upd_bytes_length by (cbn [length]; lia); exact LX
      | | exact ES | exact Er | exact HK | | exact HOc].
    - pose proof (zr_word (Z_to_bv 64 o)) as Ruo. unfold inr64 in Ruo.
      rewrite zb_lxor_ones by exact Ruo. rewrite (unsigned_lit o) by lia.
      rewrite unsigned_lit by lia. reflexivity.
    - split; [unfold c6_W, Wf; exact MU|]. split; [assumption|]. split; [assumption|].
      split; [assumption|]. split; [assumption|]. split; [eexists; eassumption | assumption].
  Qed.

  (* 0x86d18: the inner byte sum over the window record [A + 35, A + 56) of build_ident_last.  The record is
     in the function's own window, so its loads carry no shadow check (port of the ubsan twin's loopr,
     U line 735). *)
  Lemma c6_looprF : forall (kk i : nat) (REC X : list byte) (fr f spc j n : Z) (w56 : word)
      (mc : word -> option byte) (x1 x5 x6 x7 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
    p <> 0 -> o <> 0 -> (i + kk = 21)%nat -> (0 < kk)%nat ->
    length REC = 21%nat -> length X = 32%nat ->
    bytes_at rsegs mc (A + 35) REC ->
    withchk (firstn 31 (upd_bytes X 15 [Z_to_bv 8 ((- psum REC 21) mod 128); bz 247])) = synth row b nb ->
    rc row b = 1 ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c6_W sp o FS fr j n) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 X] ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A)
               (Z_to_bv 64 (A + 35 + Z.of_nat i)) (Z_to_bv 64 (psum REC i)) (Z_to_bv 64 (A + 56))
               x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86d18) fc None mc (seg_rom rsegs)).
  Proof.
    mbF_open HRNG.
    induction kk as [|kk IH]; intros i REC X fr f spc j n w56 mc x1 x5 x6 x7 x13 x14 x15 x16 x17 x21 x22
      x28 x29 x30 x31 Hp0 Ho0 Hik Hk LR LX HREC ES Er HK HB HOc; [c6_lia|].
    pose proof c6_tail6F as T6.
    destruct (c6_geoA sp tp m p b o FS off A Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro fr f spc j n w56 HK)
      as (Rsp & HA32 & HAlo & HAhi & FR8 & FRlo & FRhi & Fsp & FSpos & FSsz & HM1 & HM2).
    pose proof (rd_byte rsegs mc (A + 35) REC i HREC ltac:(c6_lia)) as RD.
    pose proof (psum_range REC i) as PR.
    pose proof (psum_range REC 21) as PR21.
    clear Fsp.
    c6_sc.
    step. step. step.
    rewrite psum_S_zxb.
    step.
    rewrite (rc_eqb_lit (A + 35 + Z.of_nat i + 1) (A + 56)) by lia.
    destruct kk as [|kk].
    - replace (A + 35 + Z.of_nat i + 1 =? A + 56) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota. replace (S i) with 21%nat by lia.
      eapply T6; first [lia | eassumption].
    - replace (A + 35 + Z.of_nat i + 1 =? A + 56) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      replace (A + 35 + Z.of_nat i + 1) with (A + 35 + Z.of_nat (S i)) by lia.
      eapply (IH (S i)); first [lia | eassumption].
  Qed.

  (* 0x86b24: name_field into the window's buffer at A + 56, the five header bytes of the record at A + 35,
     the record's copy of the name at A + 40, nine checked header bytes into the output block, the six name
     bytes at o + 9, then the record sum, the pre-tail, the outer sum and the release. *)
  Lemma c6_case6F : forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    b = 6 -> p <> 0 -> o <> 0 ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 (zeros 32)] ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p)
               (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x86b24) fc None mc (seg_rom rsegs)).
  Proof.
    mbF_open HRNG.
    intros fr f spc j n w56 mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31
      Hb Hp0 Ho0 HK HB HOc.
    pose proof c6_call_nfF as CNF. pose proof c6_call_mcoF as CMC. pose proof c6_call_mcfF as CMF.
    pose proof c6_looprF as LR. pose proof Hrel as REL. pose proof (c6_Wu sp p o FS Hp0 Ho0 fr j n) as EW.
    destruct (RROW Hp0) as (RROWr & RROWc & RROWs & RROWk).
    destruct (ROUT Hp0 Ho0) as (ROUTr & ROUTc & ROUTs & ROUTk).
    pose proof (c6_chk off Hoff) as CHK.
    pose proof (c6_rt ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m p b o FS A row nb ob HA HS16 ST0 AC0 SR0 HHM HAE
                  FP0 Rp Rb Ro HP HO AO) as RT.
    pose proof (c6_addr_o sp tp m p b o FS off A ob Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro HO AO
                  Ho0 fr f spc j n w56) as AOw.
    pose proof (c6_rowb sp tp m p b o FS off A row Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro HP AP) as ROWB.
    pose proof (c6_app_win sp tp m p o FS FP0) as APW. pose proof c6_p64 as P64.
    destruct (c6_geoA sp tp m p b o FS off A Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro fr f spc j n w56 HK)
      as (Rsp & HA32 & HAlo & HAhi & FR8 & FRlo & FRhi & Fsp & FSpos & FSsz & HM1 & HM2).
    destruct (c6_geoP sp m p o row HP AP Hp0) as (Hp8 & Hrow & HpA & Dps & Dpo & Papp).
    destruct (c6_geoO sp tp m p b o FS ob FP0 Rp Rb Ro HO AO Ho0)
      as (HoA & Dos & Drt & Hoapp & Oapp & Dofs & DofsF).
    pose proof (c6_frpos sp tp m p b o FS off A Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro fr f spc j n w56 HK)
      as FKp.
    pose proof (c6_o_fr_iv sp tp m p b o FS off A ob Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro HO AO
                  Ho0 fr f spc j n w56 HK) as Dofr.
    assert (SPC1 : A - 64 <= spc <= A) by (clear -FKp; destruct FKp as [(E & _) | (E & _)]; lia).
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI & SV & (hh & HH) & F56).
    destruct (RT fr f spc j n w56 mc HK Hp0 Ho0 HB) as (AC & SW & ST).
    pose proof (ROWB Hp0 Ho0 fr f spc j n w56 mc HK MU) as HRB.
    pose proof (rs_rd4 rsegs mc p row 56 HRB ltac:(clear -Hrow; lia)) as RD56.
    change (Z.of_nat 56) with 56 in RD56.
    pose proof (rs_rw32_range row 56) as Rh.
    pose proof (c6_addr_p sp tp m p b o FS off A row Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro HP AP AO
                  Hp0 Ho0 fr f spc j n w56 mc HK MU) as APm.
    (* the window's scratch buffer [A + 35, A + 72) *)
    destruct (stk_split rsegs mc _ (A + 72) _ ST ltac:(clear -HAlo HAhi; lia)) as [STb _].
    destruct (stk_carve rsegs mc _ (A + 72) 37%nat STb ltac:(clear -HAlo HAhi HM1; cbn [Z.of_nat]; lia))
      as [_ [WB HWB]].
    replace (A + 72 - Z.of_nat 37) with (A + 35) in HWB by (cbn [Z.of_nat]; lia).
    unfold Wf in MU. cbn [app] in MU. unfold SAVES in SV.
    clear Fsp HB ST STb ROWB RT FKp.
    c6_hide Dps. c6_hide Dpo. c6_hide DofsF. c6_hide Drt.
    c6_sc.
    (* 0x86b24: p is 8-aligned, so the alignment branch is not taken *)
    step. step.
    replace (Z.land (bv_unsigned (Z_to_bv 64 p)) 7) with 0
      by (rewrite unsigned_lit by lia; rewrite rc_land7; rewrite Hp8; reflexivity).
    nf.
    (* the instrumented check of the 4 bytes at p + 56 *)
    step.
    assert (RX56 : 0 <= p + 56 < 2^64) by lia.
    pose proof (CHK mc p 296 56 4 (p + 56) APm ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound p 8 eq_refl); Z.div_mod_to_equations; lia) eq_refl)
      as SH56.
    chk_core (p + 56) RX56 (Z_to_bv 5 12) SH56 pre_sr add1.
    step. step.
    rewrite mb_sx32_eq0 by lia.
    destruct (Z.eqb_spec (rw32 row 56) 0) as [H0|H0]; cbv iota.
    { (* has row = 0: the block stays zero and the return value is 0 *)
      step. step.
      assert (Epo : (p =? 0) || (o =? 0) = false)
        by (apply orb_false_iff; split; apply Z.eqb_neq; assumption).
      eapply (REL fr f spc j n w56 _ 0); [exact HK | | | ].
      - rewrite Epo, Hb, mb_rc6. unfold has. rewrite H0. reflexivity.
      - rewrite EW. split; [unfold c6_W, Wf; exact MU|].
        split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
        split; [eexists; eassumption | assumption].
      - rewrite Epo, Hb, mb_synth6. unfold has. rewrite H0.
        exact (mb_rw1 _ _ _ _ _ HOc). }
    (* name_field (p, A + 56) *)
    step. step. step.
    eapply (CNF 56 0x86b54 fr f spc j n w56 mc WB (zeros 32));
      [exact Hp0 | exact Ho0 | right; exact Hb | unfold has; exact H0
      | apply ret_pc_even; [lia | reflexivity] | lia | lia | exact HK | | exact HWB | exact HOc |].
    { split; [unfold c6_W, Wf; exact MU|]. split; [assumption|]. split; [assumption|].
      split; [assumption|]. split; [assumption|]. split; [eexists; eassumption | assumption]. }
    intros mc2 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 HB2 HWB2 HOB2 HNM LN.
    pose proof HB2 as HB2'. destruct HB2' as (MU2 & WM2 & RM2 & MI2 & SV2 & (hh2 & HH2) & F562).
    unfold c6_W, Wf in MU2. cbn [app] in MU2. unfold SAVES in SV2.
    clear MU WM RM MI SV HH F56 HWB HOc HRB RD56 APm AC SW.
    (* 0x86b54: the five header bytes of the record at A + 35 *)
    step. step. step. step. bstep.
    step. step. bstep.
    step. step. step. step. bstep.
    step. step. bstep.
    step. step. step. step. bstep.
    apply (rs_rw_take _ _ _ _ 6) in HWB2.
    cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in HWB2.
    match type of HWB2 with rw_cells _ _ _ [CB 37 ?Wv] => remember Wv as W5 eqn:EW5 end.
    pose proof HWB2 as HWB2c. destruct HWB2c as [[Hwf5 _] _].
    cbn [cells_wf cell_wf] in Hwf5. destruct Hwf5 as [LW5 _].
    assert (EH5 : firstn 5 W5 = [bz 5; bz 0; bz 16; bz 0; bz 1]).
    { rewrite EW5. cbn [firstn]. mb_bytes. }
    assert (ENM : firstn 16 (skipn 21 W5) = nmr row nb).
    { pose proof (rs_rw_sub rsegs _ (A + 35) 37 W5 21 16 HWB2 ltac:(lia)) as HS.
      replace (A + 35 + Z.of_nat 21) with (A + 56) in HS by (cbn [Z.of_nat]; lia).
      eapply c6_bat_det;
        [exact (mb_rw1 _ _ _ _ _ HS) | exact HNM
        | rewrite length_firstn, length_skipn, LW5, LN; reflexivity]. }
    assert (ENM2 : skipn 21 W5 = nmr row nb).
    { rewrite <- ENM. symmetry. apply c6_fall. rewrite length_skipn, LW5. reflexivity. }
    clear EW5 HNM.
    (* asan_memcpy (A + 40, A + 56, 16): the record's copy of the name *)
    step. step. step. step.
    eapply (CMF 40 56 16 0x86bb8 fr f spc j n w56 _ W5 _);
      [exact Hp0 | exact Ho0 | apply ret_pc_even; [lia | reflexivity]
      | lia | lia | lia | lia | exact HK | | exact HWB2 | exact HOB2 |].
    { split; [unfold c6_W, Wf; exact MU2|]. split; [assumption|]. split; [assumption|].
      split; [assumption|]. split; [assumption|]. split; [eexists; eassumption | assumption]. }
    intros mc3 u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 HB3 HWB3 HOB3.
    replace (Z.to_nat (40 - 35)) with 5%nat in HWB3 by reflexivity.
    replace (Z.to_nat 16) with 16%nat in HWB3 by reflexivity.
    replace (Z.to_nat (56 - 35)) with 21%nat in HWB3 by reflexivity.
    rewrite ENM in HWB3.
    pose proof HB3 as HB3'. destruct HB3' as (MU3 & WM3 & RM3 & MI3 & SV3 & (hh3 & HH3) & F563).
    unfold c6_W, Wf in MU3. cbn [app] in MU3. unfold SAVES in SV3.
    clear MU2 WM2 RM2 MI2 SV2 HH2 F562 HB2 HWB2 HOB2.
    (* 0x86bb8: the nine checked header bytes of the output block *)
    assert (RXo : 0 <= o < 2^64) by lia.
    pose proof (CHK _ o 32 0 1 o (AOw _ HK MU3) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound o 8 eq_refl); lia) ltac:(lia)) as SHo.
    chk_core o RXo (Z_to_bv 5 11) SHo pre_sr no_extra.
    step. step. step. bstep.
    assert (RX1 : 0 <= o + 1 < 2^64) by lia.
    pose proof (CHK _ o 32 1 1 (o + 1) (AOw _ HK MU3) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 1) 8 eq_refl); lia) eq_refl) as SH1.
    step. chk_core (o + 1) RX1 (Z_to_bv 5 12) SH1 pre_sr no_extra.
    step. step. step. bstep.
    assert (RX2 : 0 <= o + 2 < 2^64) by lia.
    pose proof (CHK _ o 32 2 1 (o + 2) (AOw _ HK MU3) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 2) 8 eq_refl); lia) eq_refl) as SH2.
    step. chk_core (o + 2) RX2 (Z_to_bv 5 12) SH2 pre_sr no_extra.
    step. step. bstep.
    assert (RX3 : 0 <= o + 3 < 2^64) by lia.
    pose proof (CHK _ o 32 3 1 (o + 3) (AOw _ HK MU3) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 3) 8 eq_refl); lia) eq_refl) as SH3.
    step. chk_core (o + 3) RX3 (Z_to_bv 5 12) SH3 pre_sr no_extra.
    step. step. step. bstep.
    assert (RX4 : 0 <= o + 4 < 2^64) by lia.
    pose proof (CHK _ o 32 4 1 (o + 4) (AOw _ HK MU3) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 4) 8 eq_refl); lia) eq_refl) as SH4.
    step. chk_core (o + 4) RX4 (Z_to_bv 5 12) SH4 pre_sr no_extra.
    step. step. bstep.
    assert (RX5 : 0 <= o + 5 < 2^64) by lia.
    pose proof (CHK _ o 32 5 1 (o + 5) (AOw _ HK MU3) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 5) 8 eq_refl); lia) eq_refl) as SH5.
    step. chk_core (o + 5) RX5 (Z_to_bv 5 12) SH5 pre_sr no_extra.
    step. step. step. bstep.
    assert (RX6 : 0 <= o + 6 < 2^64) by lia.
    pose proof (CHK _ o 32 6 1 (o + 6) (AOw _ HK MU3) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 6) 8 eq_refl); lia) eq_refl) as SH6.
    step. chk_core (o + 6) RX6 (Z_to_bv 5 12) SH6 pre_sr no_extra.
    step. step. bstep.
    assert (RX7 : 0 <= o + 7 < 2^64) by lia.
    pose proof (CHK _ o 32 7 1 (o + 7) (AOw _ HK MU3) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 7) 8 eq_refl); lia) eq_refl) as SH7.
    step. chk_core (o + 7) RX7 (Z_to_bv 5 12) SH7 pre_sr no_extra.
    step. step. step. bstep.
    assert (RX8 : 0 <= o + 8 < 2^64) by lia.
    pose proof (CHK _ o 32 8 1 (o + 8) (AOw _ HK MU3) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 8) 8 eq_refl); lia) eq_refl) as SH8.
    step. chk_core (o + 8) RX8 (Z_to_bv 5 12) SH8 pre_sr no_extra.
    step. step. step. bstep.
    (* 0x86cec: the window pointer A + 56 does not wrap *)
    step. step. rewrite mb_sltiu1 by lia. step. step. nfc.
    apply (rs_rw_take _ _ _ _ 10) in HOB3.
    cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in HOB3.
    match type of HOB3 with rw_cells _ _ _ [CB 32 ?X0] =>
      replace X0 with (map bz [4; 2; 0; 13; 0; 2; 0; 254; 8] ++ zeros 23) in HOB3
        by (unfold zeros, bz; cbn [map repeat app skipn]; mb_bytes) end.
    (* asan_memcpy (o + 9, A + 66, 6): the six name bytes of build_ident_last *)
    step. step. step. step.
    eapply (CMC 9 66 6 0x86d0c fr f spc j n w56 _ (upd_bytes W5 5 (nmr row nb)) _);
      [exact Hp0 | exact Ho0 | apply ret_pc_even; [lia | reflexivity]
      | lia | lia | lia | lia | lia | lia | exact HK | | exact HWB3 | exact HOB3 |].
    { split; [unfold c6_W, Wf; exact MU3|]. split; [assumption|]. split; [assumption|].
      split; [assumption|]. split; [assumption|]. split; [eexists; eassumption | assumption]. }
    intros mc4 v5 v6 v7 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 HB4 HWB4 HOB4.
    replace (Z.to_nat 9) with 9%nat in HOB4 by reflexivity.
    replace (Z.to_nat 6) with 6%nat in HOB4 by reflexivity.
    replace (Z.to_nat (66 - 35)) with (5 + 16 + 10)%nat in HOB4 by reflexivity.
    rewrite (c6_sk W5 (nmr row nb) 5 16 10 ltac:(lia) LN) in HOB4.
    cbn [Nat.add] in HOB4. rewrite ENM2 in HOB4.
    (* the record at A + 35: the five header bytes and the sixteen name bytes *)
    assert (EREC : firstn (5 + 16) (upd_bytes W5 5 (nmr row nb))
                   = [bz 5; bz 0; bz 16; bz 0; bz 1] ++ nmr row nb).
    { rewrite (c6_fu W5 (nmr row nb) 5 16 ltac:(lia) LN). rewrite EH5. reflexivity. }
    assert (HREC : bytes_at rsegs mc4 (A + 35) ([bz 5; bz 0; bz 16; bz 0; bz 1] ++ nmr row nb)).
    { rewrite <- EREC.
      pose proof (rs_rw_sub rsegs mc4 (A + 35) 37 (upd_bytes W5 5 (nmr row nb)) 0 (5 + 16)%nat HWB4
                    ltac:(lia)) as HS.
      replace (A + 35 + Z.of_nat 0) with (A + 35) in HS by (cbn [Z.of_nat]; lia).
      exact (mb_rw1 _ _ _ _ _ HS). }
    (* 0x86d0c: the inner sum over the record *)
    step. step. step.
    replace (Z_to_bv 64 (A + 35)) with (Z_to_bv 64 (A + 35 + Z.of_nat 0))
      by (f_equal; cbn [Z.of_nat]; lia).
    match type of HOB4 with rw_cells _ _ _ [CB 32 ?X6] =>
      eapply (LR 21%nat 0%nat ([bz 5; bz 0; bz 16; bz 0; bz 1] ++ nmr row nb) X6 fr f spc j n w56 _) end;
      [exact Hp0 | exact Ho0 | lia | lia
      | rewrite length_app, LN; reflexivity
      | | exact HREC | | | exact HK | exact HB4 | exact HOB4].
    - rewrite upd_bytes_length
        by (rewrite length_firstn, length_skipn, LN;
            cbn [length map zeros repeat app Nat.min Nat.sub Nat.add]; lia).
      cbn [length map zeros repeat app]. reflexivity.
    - rewrite Hb, mb_synth6. unfold has.
      replace (rw32 row 56 =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
      unfold idl. f_equal.
      rewrite mb_idl_eq by first [reflexivity | rewrite length_firstn, length_skipn, LN; reflexivity].
      assert (EPS : psum ([bz 5; bz 0; bz 16; bz 0; bz 1] ++ nmr row nb) 21
                    = 22 + psum (nmr row nb) 16).
      { change (psum ([bz 5; bz 0; bz 16; bz 0; bz 1] ++ nmr row nb) 21)
          with (psum ([bz 5; bz 0; bz 16; bz 0; bz 1] ++ nmr row nb)
                     (length [bz 5; bz 0; bz 16; bz 0; bz 1] + 16)).
        rewrite mb_psum_app; f_equal; vm_compute; reflexivity. }
      rewrite EPS. unfold idl31, idlc. reflexivity.
    - rewrite Hb, mb_rc6. unfold has.
      replace (rw32 row 56 =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0). reflexivity.
  Qed.
End c6_SF.
