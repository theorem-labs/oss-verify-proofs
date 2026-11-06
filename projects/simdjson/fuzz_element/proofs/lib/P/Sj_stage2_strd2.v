(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage2_defs Sj_tables Sj_stage2_auto Sj_stage2_arrv Sj_stage2_strend Sj_stage2_strd.
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

Section StrD2.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).

  Lemma seg_str_a : forall (Q : machine_state -> Prop) (s : st),
    (0 <= k s < e_n E)%Z -> (0 <= W s /\ W s + 1 <= e_tcap E)%Z -> (0 <= sb s /\ 3 * sb s <= 5 * e_off E (k s))%Z ->
    e_tok E (k s) = c_quote ->
    Z.of_nat (length (e_tws E)) = W s -> Z.of_nat (length (e_sbs E)) = sb s ->
    exit_k (gapp E [tword t_str (sb s)] []) Q ->
    (forall d cb, string_ok (e_bs E) (e_idxs E) (k s) d -> Z.of_nat (length cb) = d ->
       lab_k (gapp (gapp E [tword t_str (sb s)] []) [] (srec d cb)) Q 0x4766c (mkst (k s + 1) (depth s) (W s + 1) (sb s + d + 5) (scopes s))) ->
    arrstr_k E Q s.
  Proof using OK.
    intros Q s HK HW HSB HQ GLT GLS KX KC. unfold arrstr_k.
    intros xra xt0 xt1 xt2 xs1 xa2 xa4 xa7 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 F fc m1 HM.
    pose proof (n_bound E OK) as HN. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL.
    destruct (tok_string _ _ (ok_s1 _ OK) (k s) HK HQ) as (j & HC & HJ1 & HJ2).
    pose proof (off_range _ _ (ok_s1 _ OK) (k s) ltac:(lia)) as HO. pose proof (off_range _ _ (ok_s1 _ OK) (k s + 1) ltac:(lia)) as HO1.
    s2_env OK.
    s2_open_memj HM.
    rewrite HQ. unfold c_quote.
    do 30 zstep. s2norm.
    zstep. s2norm. rewrite (str_word_machine (e_SBUF E) (sb s)) by lia. s2_note_store. s2_store_done_wr.
    s2_cur_mem ltac:(fun m => apply (tape_img_app1 E _ _ m (tword t_str (sb s)) (e_TAPE E + 8 * W s)%Z OK) in TIMG;
      [ | exact NEWCH | lia | lia | apply tword_range; unfold t_str; lia ]).
    do 4 zstep.
    set (E' := gapp E [tword t_str (sb s)] []) in *.
    assert (OK' : env_ok E') by (apply env_ok_gapp; exact OK).
    assert (HROOM : (0 <= sb s /\ sb s + (j - e_off E' (k s)) + 4 <= e_scap E')%Z) by (subst E'; cbn [gapp s2_ghost e_scap e_bs e_idxs]; lia).
    assert (KE' : forall d', (0 <= d' <= j - e_off E' (k s) - 1)%Z -> strenda_k E' Q (k s) (depth s) (W s + 1) (sb s) d' (scopes s)).
    { intros d' Hd'. apply (seg_str_end_a E' OK'); [lia | subst E'; cbn [gapp s2_ghost e_scap e_bs e_idxs] in *; lia
        | subst E'; cbn [gapp s2_ghost e_scap e_bs e_idxs] in *; lia
        | subst E'; cbn [gapp s2_ghost e_sbs]; rewrite length_app; cbn [length]; lia |].
      intros cb HCB. apply KC; [|exact HCB]. exists j. split; [exact HC | subst E'; cbn [gapp s2_ghost e_bs e_idxs] in *; lia]. }
    pose proof (strd_loop E' OK' Q (k s) (depth s) (W s + 1) (sb s) (scopes s) (e_off E' (k s)) j
                  HROOM ltac:(subst E'; cbn [gapp s2_ghost e_bs e_idxs]; lia)
                  ltac:(subst E'; cbn [gapp s2_ghost e_sbs]; rewrite length_app; cbn [length]; lia)
                  KX KE' (S (Z.to_nat (j - e_off E' (k s)))) (e_off E' (k s) + 1)%Z 0%Z) as L.
    replace (e_SBUF E' + sb s + 4 + 0)%Z with (e_SBUF E' + sb s + 4)%Z in L by lia.
    replace (e_BUF E' + (e_off E' (k s) + 1))%Z with (e_BUF E' + e_off E' (k s) + 1)%Z in L by lia.
    replace (e_TAPE E' + 8 * (W s + 1))%Z with (e_TAPE E' + 8 * W s + 8)%Z in L by lia.
    eapply L; [apply PS_init; exact HC | subst E'; cbn [gapp s2_ghost e_bs e_idxs]; lia | s2_close_mem0].
  Qed.
End StrD2.
