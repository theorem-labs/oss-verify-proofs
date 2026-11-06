(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_stage2_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.

Section ArrValue.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Definition arrprim_k (Q : machine_state -> Prop) (pc : Z) (s : st) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa1 xa2 xa4 xa7 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMJ E (scopes s) fc m1 ->
      evt psegs Q (S2R E pc xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 (Z_to_bv 64 (e_tok E (k s))) xa1 xa2 (Z_to_bv 64 (e_off E (k s))) xa4
                       (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))) xa7 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xs3
                       (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 (Z_to_bv 64 (e_TAPE E + 8 * W s)) xs9 xs10 (Z_to_bv 64 (e_SBUF E + sb s))
                       xt3 xt4 xt5 xt6 F fc m1).

  Definition arrstr_k (Q : machine_state -> Prop) (s : st) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa2 xa4 xa7 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMJ E (scopes s) fc m1 ->
      evt psegs Q (S2R E 0x4acfc xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 (Z_to_bv 64 (e_tok E (k s))) (Z_to_bv 64 34) xa2 (Z_to_bv 64 (e_off E (k s))) xa4
                       (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))) xa7 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xs3
                       (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 (Z_to_bv 64 (e_TAPE E + 8 * W s)) xs9 xs10 (Z_to_bv 64 (e_SBUF E + sb s))
                       xt3 xt4 xt5 xt6 F fc m1).

  Lemma arrv_empty_tail : forall (Q : machine_state -> Prop) (s : st) (oc a0z a2z a3z : Z)
      xra xt0 xt1 xt2 xs1 xa1 xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    (oc = 91 \/ oc = 123)%Z -> a0z = tword (oc + 2) (W s) -> a2z = (oc * 2^56)%Z -> a3z = ((W s + 2) * 2^32)%Z ->
    Z.of_nat (length (e_tws E)) = W s ->
    (W s + 2 <= e_tcap E)%Z -> (0 <= W s)%Z -> (W s + 2 < 2^32)%Z -> MEMJ E (scopes s) fc m1 ->
    lab_k (empty_env E oc (W s)) Q 0x4abe0 (mkst (k s + 2) (depth s) (W s + 2) (sb s) (scopes s)) ->
    evt psegs Q (S2ML E 0x4ace4 xra xt0 xt1 xt2 xs1 (Z_to_bv 64 a0z) xa1 (Z_to_bv 64 a2z) (Z_to_bv 64 a3z) xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6
                      (depth s) (k s + 2) (W s) (sb s) F fc m1).
  Proof using OK.
    intros Q s oc a0z a2z a3z xra xt0 xt1 xt2 xs1 xa1 xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 F fc m1 HOC -> -> -> GL HW HW0 HW32 HM KC.
    s2_env OK.
    s2_open_memj HM.
    pose proof (tape_store_ok E m1 (W s) TAPEW ltac:(lia)) as SOK1.
    zstep. zstep. zstep. rewrite (empty_word_machine (W s) oc) by lia. s2_note_store. store_done.
    s2_cur_mem ltac:(fun m => pose proof (tape_store_ok E m (W s + 1) TAPEW ltac:(lia)) as SOK2).
    replace (e_TAPE E + 8 * (W s + 1))%Z with (e_TAPE E + 8 * W s + 8)%Z in SOK2 by lia.
    zstep. s2_note_store. store_done. zstep. zstep.
    replace (e_TAPE E + 8 * W s + 16)%Z with (e_TAPE E + 8 * (W s + 2))%Z by lia.
    s2_cur_mem ltac:(fun m =>
      apply (tape_img_app2 E _ _ m (cword oc (W s + 2) 0) (tword (oc + 2) (W s)) (e_TAPE E + 8 * W s)%Z (e_TAPE E + 8 * W s + 8)%Z OK) in TIMG;
      [ | exact NEWCH | exact NEWCH0 | lia | lia | lia | apply cword_range; lia | apply tword_range; lia ]).
    eapply KC. cbn [scopes]. s2_close_memj0.
  Qed.

  Lemma seg_arr_value : forall (Q : machine_state -> Prop) (s : st)
      xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    INV ArrValue s -> MEMJ E (scopes s) fc m1 -> Z.of_nat (length (e_tws E)) = W s ->
    exit_k E Q ->
    (e_tok E (k s) = c_quote -> arrstr_k Q s) ->
    (e_tok E (k s) = c_lbrack -> e_tok E (k s + 1) = c_rbrack -> lab_k (empty_env E 91 (W s)) Q 0x4abe0 (mkst (k s + 2) (depth s) (W s + 2) (sb s) (scopes s))) ->
    (e_tok E (k s) = c_lbrace -> e_tok E (k s + 1) = c_rbrace -> lab_k (empty_env E 123 (W s)) Q 0x4abe0 (mkst (k s + 2) (depth s) (W s + 2) (sb s) (scopes s))) ->
    (e_tok E (k s) = c_lbrack -> e_tok E (k s + 1) <> c_rbrack -> arrbegin_k E Q (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s))) ->
    (e_tok E (k s) = c_lbrace -> e_tok E (k s + 1) <> c_rbrace -> lab_k E Q 0x45cc0 (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s))) ->
    (e_tok E (k s) <> c_quote -> e_tok E (k s) <> c_lbrack -> e_tok E (k s) <> c_lbrace -> (e_tok E (k s) <= 57)%Z -> arrprim_k Q 0x4af80 s) ->
    (e_tok E (k s) <> c_quote -> e_tok E (k s) <> c_lbrack -> e_tok E (k s) <> c_lbrace -> (57 < e_tok E (k s))%Z -> arrprim_k Q 0x4b290 s) ->
    evt psegs Q (S2ML E 0x4ac1c xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6
                      (depth s) (k s) (W s) (sb s) F fc m1).
  Proof using OK.
    intros Q s xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 F fc m1 HI HM GL KX KS KEA KEO KAB KOB KN KA.
    pose proof (inv_k _ _ _ _ HI) as HK.
    pose proof (off_bound E OK (k s) HK) as HO. pose proof (tok_range E OK (k s)) as HT.
    pose proof (n_bound E OK) as HN. s2_env OK.
    assert (HM' := HM).
    s2_open_memj HM.
    pose proof (idx_read E OK m1 (k s) IDXA ltac:(lia)) as RD1.
    pose proof (tok_read E OK m1 (k s) BUFRO HK) as RD2.
    zstep. zstep. s2norm. zstep. zstep. s2norm. zstep. zstep. zstep.
    if_cases K; zify_cond K.
    -
      replace (e_IDX E + 4 * k s + 4)%Z with (e_IDX E + 4 * (k s + 1))%Z by lia.
      eapply (KS K). exact HM'.
    - zstep. zstep.
      if_cases K1; zify_cond K1.
      +
        assert (HK1 : (k s < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [exact HK| rewrite K1; lia]).
        pose proof (off_bound E OK (k s + 1) ltac:(lia)) as HO1. pose proof (tok_range E OK (k s + 1)) as HT1.
        pose proof (idx_read E OK m1 (k s + 1) IDXA ltac:(lia)) as RD3.
        replace (e_IDX E + 4 * (k s + 1))%Z with (e_IDX E + 4 * k s + 4)%Z in RD3 by lia.
        pose proof (tok_read E OK m1 (k s + 1) BUFRO ltac:(lia)) as RD4.
        zstep. s2norm. zstep. zstep. s2norm. zstep. zstep.
        if_cases K2; zify_cond K2.
        *
          zstep. zstep.
          replace (e_IDX E + 4 * k s + 4)%Z with (e_IDX E + 4 * (k s + 1))%Z by lia.
          eapply (KAB K1 K2). cbn [scopes W]. s2_close_mem0.
        *
          pose proof (inv_W _ _ _ _ HI) as HW. cbn [slackW] in HW. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL.
          assert (HK2 : (k s + 1 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [lia| rewrite K2; lia]).
          do 13 zstep.
          replace (e_IDX E + 4 * k s + 8)%Z with (e_IDX E + 4 * (k s + 2))%Z by lia.
          eapply (arrv_empty_tail Q s 91); [left; reflexivity | change 6701356245527298048%Z with (93 * 72057594037927936)%Z; apply close_word_machine; lia | reflexivity | apply next2_machine; lia | exact GL | lia | lia | lia | exact HM' | exact (KEA K1 K2)].
      + zstep. zstep.
        if_cases K3; zify_cond K3.
        *
          zstep. zstep.
          replace (e_IDX E + 4 * k s + 4)%Z with (e_IDX E + 4 * (k s + 1))%Z by lia.
          if_cases K4; zify_cond K4.
          -- eapply (KA K K1 K3 ltac:(lia)). exact HM'.
          -- eapply (KN K K1 K3 ltac:(lia)). exact HM'.
        *
          assert (HK1 : (k s < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [exact HK| rewrite K3; lia]).
          pose proof (off_bound E OK (k s + 1) ltac:(lia)) as HO1. pose proof (tok_range E OK (k s + 1)) as HT1.
          pose proof (idx_read E OK m1 (k s + 1) IDXA ltac:(lia)) as RD3.
          replace (e_IDX E + 4 * (k s + 1))%Z with (e_IDX E + 4 * k s + 4)%Z in RD3 by lia.
          pose proof (tok_read E OK m1 (k s + 1) BUFRO ltac:(lia)) as RD4.
          zstep. s2norm. zstep. zstep. s2norm. zstep. zstep.
          if_cases K2; zify_cond K2.
          --
             replace (e_IDX E + 4 * k s + 4)%Z with (e_IDX E + 4 * (k s + 1))%Z by lia.
             zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
             if_false. zstep.
             eapply (KOB K3 K2). cbn [scopes].
             eapply MEMJ_of_MEMI; [s2_close_mem0 | reflexivity ..].
          --
             pose proof (inv_W _ _ _ _ HI) as HW. cbn [slackW] in HW. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL.
             assert (HK2 : (k s + 1 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [lia| rewrite K2; lia]).
             do 14 zstep.
             replace (e_IDX E + 4 * k s + 8)%Z with (e_IDX E + 4 * (k s + 2))%Z by lia.
             eapply (arrv_empty_tail Q s 123); [right; reflexivity | change 9007199254740992000%Z with (125 * 72057594037927936)%Z; apply close_word_machine; lia | reflexivity | apply next2_machine; lia | exact GL | lia | lia | lia | exact HM' | exact (KEO K3 K2)].
  Qed.
End ArrValue.
