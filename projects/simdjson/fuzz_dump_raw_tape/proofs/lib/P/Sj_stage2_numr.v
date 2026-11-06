(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Sj_stage2_defs Sj_stage2_tapek Sj_num_iface Sj_stage2_numkit Sj_stage2_numkit3 Sj_stage2_numr_defs
  Sj_stage2_numr1 Sj_stage2_numr2 Sj_stage2_numr3 Sj_stage2_numr4 Sj_stage2_numr5 Sj_stage2_numr6 Sj_stage2_numr7 Sj_stage2_numr8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section NumR.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Variables (CP : Z) (t : list Z).
  Hypothesis TOK : bytes_ok t.
  Hypothesis CP0 : (0 <= CP)%Z.
  Hypothesis CPHI : (CP + blen t + 64 <= e_lo E)%Z.
  Hypothesis CPSEP : cp_sep E CP t.
  Hypothesis RLMAX : (blen t <= 1048512)%Z.
  Notation rl := (blen t).
  Hypothesis HSLOWF : slowf_stmt_g psegs 0x5028c 0x101000.
  Hypothesis HPFF : pff_stmt_g psegs 0x50314 0x101000.
  Hypothesis HROOM : (e_lo E + 368 + NUM_STACK <= bv_unsigned (e_sp E))%Z.

  Theorem rootnum_walk : forall (Q : machine_state -> Prop),
    Z.of_nat (length (e_tws E)) = 1%Z ->
    rdel_err_k E CP Q -> (forall v r, num_word v -> rdel_int_k (gapp E [v; r] []) CP Q) -> (forall v r, num_word v -> rdel_flt0_k (gapp E [v; r] []) CP Q) -> rdel_flt9_k E CP Q ->
    rootnum_k E CP t Q.
  Proof using OK TOK CP0 CPHI CPSEP RLMAX HSLOWF HPFF HROOM.
    intros Q GLT KX KI KF0 KF9.
    pose proof (seg_numr_wr E OK CP t TOK CP0 CPHI CPSEP Q GLT KX KF0 KF9) as KWR.
    pose proof (seg_numr_fb E OK CP t TOK CP0 CPHI CPSEP RLMAX HPFF HROOM Q KF9 KWR) as KFB.
    pose proof (seg_numr_slow E OK CP t TOK CP0 CPHI CPSEP RLMAX HSLOWF HROOM Q KWR) as KSLOW.
    pose proof (seg_numr_wr0 E OK CP t Q KWR) as KWR0.
    pose proof (seg_numr_t6d4 E OK CP t TOK CP0 CPHI CPSEP Q GLT KX KI KWR0
                  (fun e He => seg_numr_cmp E OK CP t TOK CP0 CPHI CPSEP Q e He KWR0 KFB)) as K6d4.
    assert (TAIL : forall neg, (0 <= neg <= 1)%Z -> (neg < rl)%Z ->
              (forall p, (0 <= p <= rl)%Z -> numr_scan_k E CP t Q neg p)).
    { intros neg HNEG HS p HP.
      assert (KFLT : forall c, (0 <= c < 256)%Z -> numr_flt_k E CP t Q neg c)
        by (intros c Hc; exact (seg_numr_flt E OK CP t TOK CP0 CPHI CPSEP Q neg c Hc HNEG HS K6d4 KSLOW)).
      apply (seg_numr_exp E OK CP t TOK CP0 CPHI CPSEP Q neg p HP KFLT).
      - exact (seg_numr_int E OK CP t TOK CP0 CPHI CPSEP Q p HP GLT KX KI).
      - intros q0 HQ0. apply (seg_numr_e48 E OK CP t TOK CP0 CPHI CPSEP Q neg q0 HQ0 KX).
        intros c Hc. exact (seg_numr_e78 E OK CP t TOK CP0 CPHI CPSEP Q neg c (KFLT c Hc)). }
    apply (seg_numr_entry E OK CP t TOK CP0 CPHI CPSEP Q KX).
    - intros neg p HNEG HS HP HDOT.
      assert (HPL : (p < rl)%Z) by (apply Bc_lt; rewrite ?HDOT; lia).
      apply (seg_numr_frac E OK CP t TOK CP0 CPHI CPSEP Q neg p HNEG ltac:(lia)).
      intros d r HD HR HRL.
      apply (seg_numr_ftail E OK CP t TOK CP0 CPHI CPSEP Q neg p d r ltac:(lia) HD HR HRL).
      intros d' HD' HPD'.
      apply (seg_numr_fdig E OK CP t TOK CP0 CPHI CPSEP Q neg p d' ltac:(lia) ltac:(lia) HPD' KX).
      intros p' HP'. apply (TAIL neg HNEG HS p'). lia.
    - intros neg p HNEG HS HP. apply (TAIL neg HNEG HS p). lia.
  Qed.
End NumR.
