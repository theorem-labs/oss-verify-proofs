(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Sj_stage2_defs Sj_stage2_tapek Sj_stage2_objf Sj_num_iface Sj_stage2_numkit Sj_stage2_numo_defs
  Sj_stage2_numo1 Sj_stage2_numo2 Sj_stage2_numo3 Sj_stage2_numo4 Sj_stage2_numo5 Sj_stage2_numo6 Sj_stage2_numo7.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section NumO.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).
  Hypothesis HSLOWF : slowf_stmt_g psegs 0x5028c 0x101000.
  Hypothesis HPFF : pff_stmt_g psegs 0x50314 0x101000.
  Hypothesis HROOM : (e_lo E + 368 + NUM_STACK <= bv_unsigned (e_sp E))%Z.

  Theorem seg_numo : forall (Q : machine_state -> Prop) (s : st),
    (0 <= k s <= e_n E)%Z -> (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> exit_k E Q ->
    (forall v r, num_word v -> is_numstart (e_tok E (k s)) = true -> lab_k (gapp E [v; r] []) Q 0x4434c (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) ->
    objval_k E Q 0x43890 s.
  Proof using OK HSLOWF HPFF HROOM.
    intros Q s HK HW0 HW GLT KX KC.
    pose proof (off_range _ _ (ok_s1 _ OK) (k s) HK) as HOR.
    assert (TAIL : forall neg, is_numstart (e_tok E (k s)) = true -> (0 <= neg <= 1)%Z -> (e_off E (k s) + neg < e_len E)%Z ->
              (forall p, (0 <= p <= e_len E)%Z -> numo_scan_k E Q s neg (W s) 0x43d34 p)).
    { intros neg HNUM HNEG HS p HP.
      assert (KJ : forall v r, num_word v -> numo_join_k (gapp E [v; r] []) Q s neg (W s + 2))
        by (intros v r Hv; exact (seg_numo_join (gapp E [v; r] []) (env_ok_gapp _ _ _ OK) Q s neg (KC v r Hv HNUM))).
      pose proof (seg_numo_wr E OK Q s neg HW0 HW GLT KX KJ) as KWR.
      pose proof (seg_numo_fb E OK HPFF HROOM Q s neg HK KX KWR) as KFB.
      pose proof (seg_numo_slow E OK HSLOWF HROOM Q s neg HK KWR) as KSLOW.
      pose proof (seg_numo_wr0 E OK Q s neg KWR) as KWR0.
      pose proof (seg_numo_t114 E OK Q s neg HW0 HW GLT KX KJ KWR0 (fun e He => seg_numo_cmp E OK Q s neg e He KWR0 KFB)) as K114.
      assert (KFLT : forall c, (0 <= c < 256)%Z -> numo_flt_k E Q s neg (W s) c)
        by (intros c Hc; exact (seg_numo_flt E OK Q s neg c Hc HNEG HK HS K114 KSLOW)).
      apply (seg_numo_exp E OK Q s neg p HP KFLT).
      - exact (seg_numo_int E OK Q s neg p HP HW0 HW GLT KX KJ).
      - intros q0 HQ0. apply (seg_numo_e48 E OK Q s neg q0 HQ0 KX). intros c Hc. exact (seg_numo_e98 E OK Q s neg c (KFLT c Hc)). }
    apply (seg_numo_entry E OK Q s HK KX).
    - intros neg p HNUM HNEG HS HP HDOT.
      assert (HPL : (p < e_len E)%Z) by (apply B_nz_lt; rewrite HDOT; lia).
      apply (seg_numo_frac E OK Q s neg p HK HNEG ltac:(lia) KX).
      intros d r HD HR HRL.
      apply (seg_numo_ftail E OK Q s neg p d r ltac:(lia) HD HR HRL).
      intros d' HD' HPD'.
      apply (seg_numo_fdig E OK Q s neg p d' ltac:(lia) ltac:(lia) HPD' KX).
      intros p' HP'. apply (TAIL neg HNUM HNEG HS p'). lia.
    - intros neg p HNUM HNEG HS HP. apply (TAIL neg HNUM HNEG HS p). lia.
  Qed.
End NumO.
