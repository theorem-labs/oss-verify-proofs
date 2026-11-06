(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 628 of its 642 lines of code are new or changed and 234 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block_case0F.v, with its addresses changed; 309 of its 352 lines of code are new or changed and 599 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcParseLib RcKindLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c dt1_head_c name_field_c reac_box_model_block_c
  reac_box_model_block reac_box_model_block_body reac_box_model_block_case12 reac_box_model_block_case0s
  reac_box_model_block_case0 reac_box_model_block_case56 reac_box_model_block_case6 reac_box_model_block_case34
  reac_box_model_blockF reac_box_model_block_bodyF reac_box_model_block_case12F reac_box_model_block_case0sF
  reac_box_model_block_case0F reac_box_model_block_case56F reac_box_model_block_case6F
  reac_box_model_block_case34F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.
Import ListNotations.
Open Scope Z_scope.

(* The footprint twin of reac_box_model_block_holds.v (image B, asan-ubsan): the same assembly over evtF.  The
   contract from the entry (entryF, reac_box_model_blockF.v), the dispatch and the frame release (bodyF), the cases
   b = 1, 2 (case12F), the case-0 slot chain (case0sF), the case b = 0 with its tail (case0F), b = 5 (case56F),
   b = 6 (case6F) and b = 3, 4 (case34F).  hbF_ctx is the plain hb_ctx with the callees' footprint forms and the
   run's footprint mbF_rng; reac_box_model_block_holds_F builds mbF_rng from the region premises of
   reac_box_model_block_contract_F once, then applies entryF and hbF_body. *)

(* The 30 hypotheses of the `Section Body` preamble of reac_box_model_block_body.v, in its order, as premises of P. *)
Definition hbF_ctx (sp tp : word) (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte)
    (RNG : footprint) (P : Prop) : Prop :=
  asan_stack_malloc_0_contract_F ->
  off = ASAN_K ->
  A = (bv_unsigned sp - 160) / 32 * 32 ->
  bv_unsigned sp mod 16 = 0 ->
  stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp) ->
  mem_inv rsegs m ->
  asan_cells m ->
  shadow_rw m ->
  HIGHMEM_BEG <= bv_unsigned sp - 4272 ->
  bv_unsigned sp <= APPMEM_END ->
  addressable m (bv_unsigned sp - 4272) 4272 ->
  fp [0%nat] m (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
    (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o) ->
  reac_box_model_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp) ->
  0 <= p < 2^64 ->
  0 <= b < 2^64 ->
  0 <= o < 2^64 ->
  (p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs m p row /\
     (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) /\ (o = 0 \/ o + 32 <= p \/ p + 296 <= o)) ->
  (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
     name_ok nb /\ bytes_at rsegs m (rname row) nb /\
     (bv_unsigned sp <= rname row \/ rname row + Z.of_nat (length nb) <= bv_unsigned sp - 4272) /\
     (o = 0 \/ o + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= o)) ->
  (o <> 0 -> rw_cells rsegs m o [CB 32 ob] /\
     (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) /\ (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o)) ->
  (p <> 0 -> addressable m p 296) ->
  (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
     addressable m (rname row) (Z.of_nat (length nb))) ->
  (o <> 0 -> addressable m o 32 /\ app_mem (o + 32) /\ (o + 32 <= RT_LO \/ RT_HI <= o)) ->
  (b = 1 -> addressable m JOIN_0014 32) ->
  (b = 2 -> addressable m JOIN_0013 32) ->
  (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
     fp_dj [(rname row, rname row + Z.of_nat (length nb))] (fp_w [0%nat] FS)) ->
  asan_memset_contract_F ->
  asan_memcpy_contract_F ->
  build_dt1_single_contract_F ->
  dt1_head_contract_F ->
  name_field_contract_F ->
  mbF_rng RNG m sp tp p b o FS row nb ->
  P.

(* The frame release at 0x86e14: the statement of reac_box_model_block_body.v's rel (the case files' Hrel). *)
Definition hbF_rel (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb : list byte) (RNG : footprint) : Prop :=
  forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte) (ret : Z)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    FK FS A fr f spc j n w56 ->
    ret = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS
       (Wf sp FS fr j n ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)])) fr w56 mc ->
    (if (p =? 0) || (o =? 0) then True else bytes_at rsegs mc o (synth row b nb)) ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 ret) x22 (Z_to_bv 64 fr)
              (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x86e14) fc None mc (seg_rom rsegs)).

(* The case-0 tail at 0x8710c: the statement of c0_tailc (reac_box_model_block_case0.v), which is the hypothesis
   Htail of reac_box_model_block_case0s.v. *)
Definition hbF_tail (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb : list byte) (RNG : footprint) : Prop :=
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
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x8710c) fc None mc (seg_rom rsegs)).

(* The slot chain at 0x868c4 (lay = 1): the statement of c0s_lay1, the hypothesis Hlay1 of c0_case0. *)
Definition hbF_lay1 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb : list byte) (RNG : footprint) : Prop :=
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
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) a0 a1
               (Z_to_bv 64 (ic row)) (Z_to_bv 64 (oc row)) (Z_to_bv 64 (oc row / 4)) (Z_to_bv 64 (ic row / 4)) a6 a7
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x868c4) fc None mc (seg_rom rsegs)).

(* The slot chain at 0x86f78 (lay <> 1): the statement of c0s_lay2, the hypothesis Hlay2 of c0_case0. *)
Definition hbF_lay2 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb : list byte) (RNG : footprint) : Prop :=
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
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) a0 a1
               (Z_to_bv 64 (ic row)) (Z_to_bv 64 (oc row)) (Z_to_bv 64 (oc row / 4)) (Z_to_bv 64 (ic row / 4)) a6 a7
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x86f78) fc None mc (seg_rom rsegs)).

(* --- the premise shapes of holdsF_of_cases --- *)

(* c0_tailc: given the preamble and the release, the case-0 tail. *)
Definition hbF_tail_hyp : Prop :=
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte) (RNG : footprint),
    hbF_ctx sp tp m p b o FS off A row nb ob RNG
      (hbF_rel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A row nb RNG ->
       hbF_tail ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A row nb RNG).

(* c0_case0: given the preamble, the release and the two slot chains, the case b = 0. *)
Definition hbF_case0_hyp : Prop :=
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte) (RNG : footprint),
    hbF_ctx sp tp m p b o FS off A row nb ob RNG
      (hbF_rel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A row nb RNG ->
       hbF_lay1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A row nb RNG ->
       hbF_lay2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A row nb RNG ->
       case_stmtF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A row nb RNG 0 0x86714).

(* The case b = K at its case PC pc, given the preamble and the release. *)
Definition hbF_case (K pc : Z) : Prop :=
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte) (RNG : footprint),
    hbF_ctx sp tp m p b o FS off A row nb ob RNG
      (hbF_rel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A row nb RNG ->
       case_stmtF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A row nb RNG K pc).

(* --- the proved pieces in those shapes --- *)

Lemma hbF_rel_ok : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte) (RNG : footprint),
  hbF_ctx sp tp m p b o FS off A row nb ob RNG
    (hbF_rel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A row nb RNG).
Proof. repeat intro. eapply relF; eassumption. Qed.

Lemma hbF_lay1_ok : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte) (RNG : footprint),
  hbF_ctx sp tp m p b o FS off A row nb ob RNG
    (hbF_tail ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A row nb RNG ->
     hbF_lay1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A row nb RNG).
Proof. repeat intro. eapply c0s_lay1F; eassumption. Qed.

Lemma hbF_lay2_ok : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte) (RNG : footprint),
  hbF_ctx sp tp m p b o FS off A row nb ob RNG
    (hbF_tail ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A row nb RNG ->
     hbF_lay2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A row nb RNG).
Proof. repeat intro. eapply c0s_lay2F; eassumption. Qed.

Lemma hbF_c1 : hbF_case 1 0x86a44.
Proof. repeat intro. eapply c12_case1F; eassumption. Qed.

Lemma hbF_c2 : hbF_case 2 0x869fc.
Proof. repeat intro. eapply c12_case2F; eassumption. Qed.

(* c0_tailc (reac_box_model_block_case0.v): the case-0 tail at 0x8710c, which case0s.v takes as Htail. *)
Lemma hbF_tail_ok : hbF_tail_hyp.
Proof. repeat intro. eapply c0_tailcF; eassumption. Qed.

(* c0_case0 (reac_box_model_block_case0.v): the case b = 0 at 0x86714, from the release and the two slot chains. *)
Lemma hbF_case0_ok : hbF_case0_hyp.
Proof. repeat intro. eapply c0_case0F; eassumption. Qed.

Lemma hbF_c5 : hbF_case 5 0x86a5c.
Proof. repeat intro. eapply c56_case5F; eassumption. Qed.

Lemma hbF_c6 : hbF_case 6 0x86b24.
Proof. repeat intro. eapply c6_case6F; eassumption. Qed.

Lemma hbF_c3 : hbF_case 3 0x86a08.
Proof. repeat intro. eapply c34_case3F; eassumption. Qed.

Lemma hbF_c4 : hbF_case 4 0x8691c.
Proof. repeat intro. eapply c34_case4F; eassumption. Qed.

(* The body walk 0x866d4 -> Q0 (KB Q0) from the cases. *)
Lemma hbF_body : hbF_tail_hyp -> hbF_case0_hyp -> hbF_case 3 0x86a08 -> hbF_case 4 0x8691c -> hbF_case 5 0x86a5c ->
  hbF_case 6 0x86b24 ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte) (RNG : footprint),
    hbF_ctx sp tp m p b o FS off A row nb ob RNG
      (KBF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A RNG
          (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)).
Proof.
  intros Ht H0 H3 H4 H5 H6 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A row nb ob
    RNG HSM Hoff HA HS16 ST0 MI0 AC0 SR0 HHM HAE AW0 FP0 TLS0 Rp Rb Ro HP HN HO AP ANB AO AJ1 AJ2 NDJ
    HMS HMC HBD HDH HNF HRNG.
  assert (Hrel : hbF_rel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A row nb RNG)
    by (eapply hbF_rel_ok; eassumption).
  assert (Htl : hbF_tail ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A row nb RNG)
    by (eapply Ht; eassumption).
  assert (L1 : hbF_lay1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A row nb RNG)
    by (eapply hbF_lay1_ok; eassumption).
  assert (L2 : hbF_lay2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A row nb RNG)
    by (eapply hbF_lay2_ok; eassumption).
  eapply dispF; try eassumption;
    first [ eapply H0; eassumption | eapply hbF_c1; eassumption | eapply hbF_c2; eassumption
          | eapply H3; eassumption | eapply H4; eassumption | eapply H5; eassumption | eapply H6; eassumption ].
Qed.

(* The contract of reac_box_model_block, image B, from the six callee contracts and the cases 0, 3, 4, 5, 6 (with
   c0_tailc for the case-0 slot chain). *)
Theorem holdsF_of_cases :
  asan_stack_malloc_0_contract_F -> asan_memset_contract_F -> asan_memcpy_contract_F ->
  build_dt1_single_contract_F -> dt1_head_contract_F -> name_field_contract_F ->
  hbF_tail_hyp -> hbF_case0_hyp ->
  hbF_case 3 0x86a08 -> hbF_case 4 0x8691c -> hbF_case 5 0x86a5c -> hbF_case 6 0x86b24 ->
  reac_box_model_block_contract_F.
Proof.
  intros HSM HMS HMC HBD HDH HNF Ht H0 H3 H4 H5 H6.
  unfold reac_box_model_block_contract_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p b o FS row nb ob Ea0 Ea1 Ea2 Rp Rb Ro HS16 ST0 HP HN HO MI0 AC0 SR0 HHM HAE AW0 AP ANB AO AJ1 AJ2
    FP0 NDJ TLS0 RBY RIMG RWIN SWIN RHDR RFW RTLS RROW ROUT RJ4 RJ3 RNM.
  subst a0 a1 a2.
  (* the run's footprint, out of the statement's region premises *)
  assert (HRNG : mbF_rng RNG m sp tp p b o FS row nb).
  { pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & HPl & _ & _ & _ & _ & _ & _ & _).
    pose proof HPl as (PL1 & PL2 & PL3 & PL4 & PL5).
    assert (E0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (E1 : fs_frame FS 0 (fs_M 0) = FS + 1085440)
      by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat]; lia).
    unfold fp_w, fp_w1 in RFW. cbn [flat_map app] in RFW.
    apply Forall_cons_iff in RFW. destruct RFW as [W1 RFW]. cbv beta in W1. cbn [fst snd] in W1.
    apply Forall_cons_iff in RFW. destruct RFW as [W2 RFW]. cbv beta in W2. cbn [fst snd] in W2.
    apply Forall_cons_iff in RFW. destruct RFW as [W3 RFW]. cbv beta in W3. cbn [fst snd] in W3.
    apply Forall_cons_iff in RFW. destruct RFW as [W4 RFW]. cbv beta in W4. cbn [fst snd] in W4.
    rewrite E0, E1 in W3, W4. rewrite E0 in RHDR.
    unfold REAC_BOX_MODEL_BLOCK_K in RWIN, SWIN.
    assert (M8a : (FS + 36864) mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (M8b : (FS + 1085440) mod 8 = 0) by (Z.div_mod_to_equations; lia).
    pose proof W4 as W4'.
    assert (K0 : shadow_addr (FS + 36864) = 8 * ((FS + 36864) / 64) + ASAN_K)
      by (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
    assert (K1 : shadow_addr (FS + 1085440) = 8 * ((FS + 1085440) / 64) + ASAN_K)
      by (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
    rewrite K0, K1 in W4'.
    pose proof (mbF_span_kov RNG ((FS + 36864) / 64) ((FS + 1085440) / 64) W4') as KK.
    split; [exact RIMG|].
    split; [exact RWIN|].
    split; [exact (mbF_cov0 RNG _ _ SWIN)|].
    split; [exact (mbF_span0 RNG _ _ SWIN)|].
    split; [exact (mbF_kov0 RNG _ _ SWIN)|].
    split; [eapply rng_sub; [exact RHDR | lia | lia]|].
    split; [eapply rng_sub; [exact W3 | lia | lia]|].
    split; [eapply shcov_sub; [exact (mbF_span_cov RNG (FS + 36864) (FS + 1085440) M8a M8b W4) | lia | lia]|].
    split; [eapply shspan_sub; [exact (mbF_span_span RNG (FS + 36864) (FS + 1085440) M8a M8b W4) | lia | lia]|].
    split; [eapply shkov_sub; [exact KK | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia]|].
    split; [exact RTLS|].
    split.
    { intros Hp. destruct (RROW Hp) as (RRr & RRs).
      split; [exact RRr|]. split; [exact (mbF_cov0 RNG _ _ RRs)|].
      split; [exact (mbF_span0 RNG _ _ RRs) | exact (mbF_kov0 RNG _ _ RRs)]. }
    split.
    { intros Hp Ho. destruct (ROUT Hp Ho) as (ROr & ROs).
      split; [exact ROr|]. split; [exact (mbF_cov0 RNG _ _ ROs)|].
      split; [exact (mbF_span0 RNG _ _ ROs) | exact (mbF_kov0 RNG _ _ ROs)]. }
    split.
    { intros Hb. pose proof (RJ4 Hb) as Hs.
      split; [exact (mbF_cov0 RNG _ _ Hs)|].
      split; [exact (mbF_span0 RNG _ _ Hs) | exact (mbF_kov0 RNG _ _ Hs)]. }
    split.
    { intros Hb. pose proof (RJ3 Hb) as Hs.
      split; [exact (mbF_cov0 RNG _ _ Hs)|].
      split; [exact (mbF_span0 RNG _ _ Hs) | exact (mbF_kov0 RNG _ _ Hs)]. }
    split.
    { intros Hp Hb Hh Hr. destruct (RNM Hp Hb Hh Hr) as (RNr & RNs).
      split; [exact RNr|]. split; [exact (mbF_cov0 RNG _ _ RNs)|].
      split; [exact (mbF_span0 RNG _ _ RNs) | exact (mbF_kov0 RNG _ _ RNs)]. }
    exact RBY. }
  eapply (entryF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS ASAN_K
            ((bv_unsigned sp - 160) / 32 * 32) row nb RNG HSM eq_refl eq_refl HS16 ST0 MI0 AC0 SR0 HHM HAE AW0 FP0
            HRNG t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 _ m eq_refl).
  exact (hbF_body Ht H0 H3 H4 H5 H6 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS ASAN_K
           ((bv_unsigned sp - 160) / 32 * 32) row nb ob RNG HSM eq_refl eq_refl HS16 ST0 MI0 AC0 SR0 HHM HAE AW0
           FP0 TLS0 Rp Rb Ro HP HN HO AP ANB AO AJ1 AJ2 NDJ HMS HMC HBD HDH HNF HRNG).
Qed.

(* The contract from the six callee contracts and the cases 3, 4, 5, 6: the case-0 chain (its tail, its two slot
   chains and the case itself) is closed. *)
Theorem holdsF_of_cases34 :
  asan_stack_malloc_0_contract_F -> asan_memset_contract_F -> asan_memcpy_contract_F ->
  build_dt1_single_contract_F -> dt1_head_contract_F -> name_field_contract_F ->
  hbF_case 3 0x86a08 -> hbF_case 4 0x8691c -> hbF_case 5 0x86a5c -> hbF_case 6 0x86b24 ->
  reac_box_model_block_contract_F.
Proof.
  intros HSM HMS HMC HBD HDH HNF H3 H4 H5 H6.
  exact (holdsF_of_cases HSM HMS HMC HBD HDH HNF hbF_tail_ok hbF_case0_ok H3 H4 H5 H6).
Qed.

(* The same with the case b = 5 closed by c56_case5: only the cases 3, 4 and 6 are left open. *)
Theorem holdsF_of_cases5 :
  asan_stack_malloc_0_contract_F -> asan_memset_contract_F -> asan_memcpy_contract_F ->
  build_dt1_single_contract_F -> dt1_head_contract_F -> name_field_contract_F ->
  hbF_case 3 0x86a08 -> hbF_case 4 0x8691c -> hbF_case 6 0x86b24 ->
  reac_box_model_block_contract_F.
Proof.
  intros HSM HMS HMC HBD HDH HNF H3 H4 H6.
  exact (holdsF_of_cases34 HSM HMS HMC HBD HDH HNF H3 H4 hbF_c5 H6).
Qed.

(* The same with the case b = 6 closed by c6_case6: only the cases 3 and 4 are left open. *)
Theorem holdsF_of_cases34_only :
  asan_stack_malloc_0_contract_F -> asan_memset_contract_F -> asan_memcpy_contract_F ->
  build_dt1_single_contract_F -> dt1_head_contract_F -> name_field_contract_F ->
  hbF_case 3 0x86a08 -> hbF_case 4 0x8691c ->
  reac_box_model_block_contract_F.
Proof.
  intros HSM HMS HMC HBD HDH HNF H3 H4.
  exact (holdsF_of_cases5 HSM HMS HMC HBD HDH HNF H3 H4 hbF_c6).
Qed.

(* Every case is proved: the contract of reac_box_model_block in image B follows from the six callee contracts
   alone. *)
Theorem reac_box_model_block_holds_F :
  asan_stack_malloc_0_contract_F -> asan_memset_contract_F -> asan_memcpy_contract_F ->
  build_dt1_single_contract_F -> dt1_head_contract_F -> name_field_contract_F ->
  reac_box_model_block_contract_F.
Proof.
  intros HSM HMS HMC HBD HDH HNF.
  exact (holdsF_of_cases34_only HSM HMS HMC HBD HDH HNF hbF_c3 hbF_c4).
Qed.
