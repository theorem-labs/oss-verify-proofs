(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf Zpi Zpa SjTape Zpj Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zwd Z107 Zwa Zyt Zwq.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_buf | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].

Section KeyB2.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).
  Notation bs := (e_bs E).

  Lemma seg_key_b : forall (Q : machine_state -> Prop) (s0 : st),
    INV ObjCont s0 -> e_tok E (k s0) = c_comma -> e_tok E (k s0 + 1) = c_quote ->
    Z.of_nat (length (e_tws E)) = W s0 -> Z.of_nat (length (e_sbs E)) = sb s0 ->
    exit_k (gapp E [tword t_str (sb s0)] []) Q ->
    (forall d, string_ok (e_bs E) (e_idxs E) (k s0 + 1) d ->
       keyend_k (gapp E [tword t_str (sb s0)] []) Q (k s0 + 1) (depth s0) (W s0 + 1) (sb s0) d (scopes s0)) ->
    keyb_k E Q (mkst (k s0 + 1) (depth s0) (W s0) (sb s0) (scopes s0)).
  Proof using OK.
    intros Q s0 HI HC0 HQ GLT GLS KX KE. unfold keyb_k. cbn [k depth W sb scopes].
    intros xra xt0 xt1 xt2 xs1 xa0 xa3 xa4 xa5 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 j0 j1 j2 j3 j4 j6 j7 j8 j9 F fc m1 HM.
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_W _ _ _ _ HI) as HW.
    destruct (inv_sb _ _ _ _ HI) as [HSB0 _]. cbn [slackW slackS] in *.
    pose proof (n_bound E OK) as HN. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL.
    assert (HKN : (k s0 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [exact HK | rewrite HC0; unfold c_comma; lia]).
    assert (HKN1 : (k s0 + 1 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [lia | rewrite HQ; unfold c_quote; lia]).
    destruct (tok_string _ _ (ok_s1 _ OK) (k s0 + 1) ltac:(lia) HQ) as (j & HC & HJ1 & HJ2).
    pose proof (string_pre _ _ (ok_s1 _ OK) ObjCont s0 1 HI ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as HPRE.
    pose proof (off_range _ _ (ok_s1 _ OK) (k s0 + 1) ltac:(lia)) as HO. pose proof (off_range _ _ (ok_s1 _ OK) (k s0 + 1 + 1) ltac:(lia)) as HO1.
    s2_env OK.
    s2_open_mem HM.
    do 28 zstep. s2norm.
    zstep. s2norm. rewrite (str_word_machine (e_SBUF E) (sb s0)) by lia. s2_note_store. s2_store_done_wr.
    s2_cur_mem ltac:(fun m => apply (tape_img_app1 E _ _ m (tword t_str (sb s0)) (e_TAPE E + 8 * W s0)%Z OK) in TIMG;
      [ | exact NEWCH | lia | lia | apply tword_range; unfold t_str; lia ]).
    do 5 zstep.
    set (E' := gapp E [tword t_str (sb s0)] []) in *.
    assert (OK' : env_ok E') by (apply env_ok_gapp; exact OK).
    assert (HROOM : (0 <= sb s0 /\ sb s0 + (j - e_off E' (k s0 + 1)) + 4 <= e_scap E')%Z) by (subst E'; cbn [gapp s2_ghost e_scap e_bs e_idxs e_sbs] in *; lia).
    assert (KE' : forall d', (0 <= d' <= j - e_off E' (k s0 + 1) - 1)%Z ->
                   keyend_k E' Q (k s0 + 1) (depth s0) (W s0 + 1) (sb s0) d' (scopes s0)).
    { intros d' Hd'. apply KE. exists j. split; [exact HC | subst E'; cbn [gapp s2_ghost e_scap e_bs e_idxs e_sbs] in *; lia]. }
    pose proof (keyb_loop E' OK' Q (k s0 + 1) (depth s0) (W s0 + 1) (sb s0) (scopes s0) (e_off E' (k s0 + 1)) j
                  HROOM ltac:(subst E'; cbn [gapp s2_ghost e_scap e_bs e_idxs e_sbs] in *; lia) ltac:(subst E'; cbn [gapp s2_ghost e_sbs]; rewrite length_app; cbn [length]; lia)
                  KX KE' (S (Z.to_nat (j - e_off E' (k s0 + 1)))) (e_off E' (k s0 + 1) + 1)%Z 0%Z) as L.
    replace (e_SBUF E' + sb s0 + 4 + 0)%Z with (e_SBUF E' + sb s0 + 4)%Z in L by lia.
    replace (e_BUF E' + (e_off E' (k s0 + 1) + 1))%Z with (e_BUF E' + e_off E' (k s0 + 1) + 1)%Z in L by lia.
    replace (e_TAPE E' + 8 * (W s0 + 1))%Z with (e_TAPE E' + 8 * W s0 + 8)%Z in L by lia.
    eapply L; [apply PS_init; exact HC | subst E'; cbn [gapp s2_ghost e_bs e_idxs]; lia | s2_close_mem0].
  Qed.
End KeyB2.
