(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes Z10q FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf Zpi Zpa SjTape Zpj Zpk Zpe.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zwd Z103 Zw6 Zsl Zxc Zx7
  Zwv Zww Zwy Zx0 Zx2 Zx3 Zx4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section NumA.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).
  Hypothesis HSLOWF : slowf_stmt_g psegs 0x3cb88 0xab000.
  Hypothesis HPFF : pff_stmt_g psegs 0x3cc10 0xab000.
  Hypothesis HROOM : (e_lo E + 368 + NUM_STACK <= bv_unsigned (e_sp E))%Z.

  Theorem seg_numa : forall (Q : machine_state -> Prop) (s : st),
    (0 <= k s <= e_n E)%Z -> (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> exit_k E Q ->
    (forall v r, exit_k (gapp E [v; r] []) Q) ->
    (forall v r, num_word v -> is_numstart (e_tok E (k s)) = true -> lab_k (gapp E [v; r] []) Q 0x30fb0 (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) ->
    arrprim_k E Q 0x31350 s.
  Proof using OK HSLOWF HPFF HROOM.
    intros Q s HK HW0 HW GLT KX KXg KC.
    pose proof (off_range _ _ (ok_s1 _ OK) (k s) HK) as HOR.
    assert (TAIL : forall neg, is_numstart (e_tok E (k s)) = true -> (0 <= neg <= 1)%Z -> (e_off E (k s) + neg < e_len E)%Z ->
              (forall p, (0 <= p <= e_len E)%Z -> numa_scan_k E Q s neg 0x31804 p)).
    { intros neg HNUM HNEG HS p HP.
      assert (KJ : forall v r, num_word v -> numa_join_k (gapp E [v; r] []) Q s neg)
        by (intros v r Hv; exact (seg_numa_join (gapp E [v; r] []) (env_ok_gapp _ _ _ OK) Q s neg (KC v r Hv HNUM))).
      pose proof (seg_numa_wr E OK Q s neg HW0 HW GLT KX KJ) as KWR.
      pose proof (seg_numa_fb E OK HPFF HROOM Q s neg HK KX KWR) as KFB.
      pose proof (seg_numa_slow E OK HSLOWF HROOM Q s neg HK KWR) as KSLOW.
      pose proof (seg_numa_wr0 E OK Q s neg KWR) as KWR0.
      pose proof (seg_numa_t114 E OK Q s neg HW0 HW GLT KX KJ KWR0 (fun e He => seg_numa_cmp E OK Q s neg e He KWR0 KFB)) as K114.
      assert (KFLT : forall c, (0 <= c < 256)%Z -> numa_flt_k E Q s neg c)
        by (intros c Hc; exact (seg_numa_flt E OK Q s neg c Hc HNEG HK HS K114 KSLOW)).
      apply (seg_numa_exp E OK Q s neg p HP KFLT).
      - apply (seg_numa_int E OK Q s neg p HP HW0 HW GLT KX). intros c Hc v r Hv.
        exact (seg_numa_i3f4 (gapp E [v; r] []) (env_ok_gapp _ _ _ OK) Q s neg c Hc (KXg v r) (KJ v r Hv)).
      - intros q0 HQ0. apply (seg_numa_e48 E OK Q s neg q0 HQ0 KX). intros c Hc. exact (seg_numa_e98 E OK Q s neg c (KFLT c Hc)). }
    apply (seg_numa_entry E OK Q s HK KX).
    - intros neg p HNUM HNEG HS HP HDOT.
      assert (HPL : (p < e_len E)%Z) by (apply B_nz_lt; rewrite HDOT; lia).
      apply (seg_numa_frac E OK Q s neg p HK HNEG ltac:(lia) KX).
      intros d r HD HR HRL.
      apply (seg_numa_ftail E OK Q s neg p d r ltac:(lia) HD HR HRL).
      intros d' HD' HPD'.
      apply (seg_numa_fdig E OK Q s neg p d' ltac:(lia) ltac:(lia) HPD' KX).
      intros p' HP'. apply (TAIL neg HNUM HNEG HS p'). lia.
    - intros neg p HNUM HNEG HS HP. apply (TAIL neg HNUM HNEG HS p). lia.
  Qed.
End NumA.
