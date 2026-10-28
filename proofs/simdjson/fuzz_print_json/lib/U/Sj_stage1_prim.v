(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage1_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section PRIM.
  Variable E : s1env.
  Hypothesis OK : env_ok_u E.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Lemma u1_prim_loop : forall (Q : machine_state -> Prop) (f : nat) (j : Z) (out : list Z) (idxc err : Z) xa0 xa5 xt3 xt5 (m1 : mem),
    U1INV E m1 out idxc err -> (0 <= j)%Z -> (j + 1 < len)%Z -> (len - j <= Z.of_nat f)%Z ->
    (forall idxc' xra' xa3' xa5' xt5' xt6' m1', U1INV E m1' out idxc' err ->
       evt usegs Q (U1ST E 0x4195c xra' xa0 xa3' xa5' (Z_to_bv 64 (prim_run bs f j)) (Z_to_bv 64 len) xt3 xt5' xt6' m1')) ->
    evt usegs Q (U1ST E 0x41cb4 (Z_to_bv 64 (e_BUF E + (j + 1))) xa0 (Z_to_bv 64 (j + 1)) xa5 (Z_to_bv 64 j) (Z_to_bv 64 len) xt3 xt5
                      (Z_to_bv 64 (e_BUF E + (j + 1))) m1).
  Proof using OK.
    intros Q f. induction f as [|f IH]; intros j out idxc err xa0 xa5 xt3 xt5 m1 INV Hj Hj1 Hf HBOT; [exfalso; lia|].
    destruct OK as [OKB BUFP IDXP ALIGN].
    destruct OKB as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, U1_STACK, U1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    rewrite prim_run_S in HBOT. rewrite (proj2 (Z.ltb_lt _ _) Hj1) in HBOT. cbn [andb] in HBOT.
    pose proof (B_range bs (j + 1) BOK) as CR. set (c := B bs (j + 1)) in *.
    pose proof (tbl_range c) as TR.
    pose proof INV as INV'. u1_open_inv INV'.
    pose proof (rw_cells_CB_bytes_at _ _ _ _ _ FRtb) as TBL.
    pose proof (ubuf_read m1 (e_BUF E) bs (j + 1) BUFRO ltac:(lia)) as RD1. fold c in RD1.
    pose proof (utbl_read m1 _ c TBL CR) as RD2.
    zstep. if_cases G1; zify_cond G1; [|exfalso; lia].
    zstep. s1norm. zstep. zstep. s1norm. zstep. zstep.
    if_cases K3; zify_cond K3.
    -
      assert (TS : t_space_or_op c = true) by (unfold t_space_or_op; rewrite (proj2 (Z.eqb_neq _ _) K3); reflexivity).
      rewrite TS in HBOT. cbn [negb andb] in HBOT.
      zstep. zstep.
      replace (Z_to_bv 64 (j + 1 + -1)) with (Z_to_bv 64 j) by (f_equal; lia).
      apply (HBOT idxc). exact INV.
    - assert (TS : t_space_or_op c = false) by (unfold t_space_or_op; rewrite (proj2 (Z.eqb_eq _ _) K3); reflexivity).
      rewrite TS in HBOT. cbn [negb andb] in HBOT.
      zstep. if_cases G2; zify_cond G2; [|exfalso; lia].
      zstep.
      if_cases K30; zify_cond K30.
      +
        rewrite (proj2 (Z.eqb_eq _ _) K30) in HBOT. cbn [negb] in HBOT.
        apply (HBOT idxc). exact INV.
      + rewrite (proj2 (Z.eqb_neq _ _) K30) in HBOT. cbn [negb] in HBOT.
        zstep. zstep. s1norm. zstep. zstep. zstep. zstep. zstep.
        assert (INV2 : U1INV E m out (j + 1) err) by u1_close_inv.
        if_cases KNE; zify_cond KNE.
        *
          eapply evt_eq; [| eapply (IH (j + 1)%Z out (j + 1)%Z err)]; [s1_st_eq| try assumption; lia ..].
        *
          rewrite (prim_run_end bs f (j + 1)) in HBOT by lia.
          zstep. zstep.
          replace (Z_to_bv 64 (j + 1 + 1 + -1)) with (Z_to_bv 64 (j + 1)) by (f_equal; lia).
          apply (HBOT (j + 1)%Z). exact INV2.
  Qed.
End PRIM.
