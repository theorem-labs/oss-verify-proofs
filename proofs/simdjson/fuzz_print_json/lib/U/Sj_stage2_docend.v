(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage2_defs Sj_stage2_traps Sj_stage2_guard.
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

Section DocEnd.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Definition docend_env (Wv : Z) : s2env := gpatch (gapp E [tword t_root 0] []) 0 (tword t_root (Wv + 1)).

  Lemma seg_doc_end : forall (Q : machine_state -> Prop) (s : st)
      xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6
      j0 j8 j16 j24 j32 j56 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    INV DocEnd s ->
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * k s)); CB 8 j56; C8 (Z_to_bv 64 (e_THIS E)); CB 8 j72]
         ([]) fc m1 ->
    Z.of_nat (length (e_tws E)) = W s ->
    exit_k (docend_env (W s)) Q -> tape_ok (e_tws (docend_env (W s))) (e_sbs (docend_env (W s))) ->
    evt usegs Q (S2R E 0x47028 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK.
    intros Q s xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j56 j72 F fc m1 HI HM GLT KX TOK.
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_W _ _ _ _ HI) as HW. cbn [slackW] in HW.
    pose proof (n_bound E OK) as HN. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL. s2_env OK.
    s2_open_mem HM.
    grun_to 0x47040%Z.

    zstep. gnorm. s2_note_store. s2_store_done_wr_v2.
    s2_cur_mem ltac:(fun m => apply (tape_img_app1 E _ _ m (tword t_root 0) (e_TAPE E + 8 * W s)%Z OK) in TIMG;
      [ | exact NEWCH | lia | lia | vm_compute; split; [discriminate | reflexivity] ]).
    grun_to 0x470a4%Z.

    zstep. gnorm.
    replace (e_TAPE E + 8 * W s + 8 - e_TAPE E)%Z with (e_TAPE E + 8 * (W s + 1) - e_TAPE E)%Z by lia.
    change 8214565720323784704%Z with (t_root * 72057594037927936)%Z. rewrite (close_word_machine (e_TAPE E) (W s + 1) t_root) by lia.
    s2_old_mem ltac:(fun m => apply (tape_img_patchZ E _ _ m 0 (tword t_root (W s + 1)) OK) in TIMG;
      [ | rewrite length_app; cbn [length]; lia | apply tword_range; unfold t_root; lia ]).
    replace (e_TAPE E + 8 * 0)%Z with (e_TAPE E) in TIMG by lia.
    s2_store_done_wr_v2.
    grun_to 0x4be14%Z.

    lazymatch goal with |- context [Z.b2z ?c] => destruct c end; cbn [Z.b2z].
    - change (Z.land ((1 + -1) mod 18446744073709551616) 3) with 0%Z. eapply (KX 0%Z); [right; split; [reflexivity | exact TOK]|].
      eapply (MEMX_of_MEMI _ _); [ s2_close_mem; [ rewrite ?upd_length; eassumption | apply oc_rel_nil | rewrite ?upd_length; eassumption | apply ia_rel_nil ] | reflexivity .. ].
    - change (Z.land ((0 + -1) mod 18446744073709551616) 3) with 3%Z. eapply (KX 3%Z); [s2_errlit|].
      eapply (MEMX_of_MEMI _ _); [ s2_close_mem; [ rewrite ?upd_length; eassumption | apply oc_rel_nil | rewrite ?upd_length; eassumption | apply ia_rel_nil ] | reflexivity .. ].
  Qed.
End DocEnd.
