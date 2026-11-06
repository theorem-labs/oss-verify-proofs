(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_stage2_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.

Section DocEnd.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Definition docend_env (Wv : Z) : s2env := gpatch (gapp E [tword t_root 0] []) 0 (tword t_root (Wv + 1)).

  Lemma seg_doc_end : forall (Q : machine_state -> Prop) (s : st), INV DocEnd s -> Z.of_nat (length (e_tws E)) = W s ->
    exit_k (docend_env (W s)) Q -> succ_k (docend_env (W s)) Q -> docend_k E Q s.
  Proof using OK.
    intros Q s HI GLT KX KS. unfold docend_k.
    intros x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
           j0 j1 j2 j3 j4 j5 j8 j9 F fc m1 HM.
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_W _ _ _ _ HI) as HW. cbn [slackW] in HW.
    pose proof (n_bound E OK) as HN. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL. s2_env OK.
    s2_open_mem HM.
    pose proof (tape_store_ok E m1 (W s) TAPEW ltac:(lia)) as SOK1.
    zstep. zstep. zstep. zstep. s2_note_store. store_done.
    s2_cur_mem ltac:(fun m => apply (tape_img_app1 E _ _ m (tword t_root 0) (e_TAPE E + 8 * W s)%Z OK) in TIMG;
      [ | exact NEWCH | lia | lia | vm_compute; split; [discriminate | reflexivity] ]).
    s2_cur_mem ltac:(fun m => pose proof (tape_store_ok E m 0 TAPEW ltac:(lia)) as SOK2).
    replace (e_TAPE E + 8 * 0)%Z with (e_TAPE E) in SOK2 by lia.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep.
    replace (e_TAPE E + 8 * W s - e_TAPE E + 8)%Z with (e_TAPE E + 8 * (W s + 1) - e_TAPE E)%Z by lia.
    change 8214565720323784704%Z with (t_root * 72057594037927936)%Z. rewrite (close_word_machine (e_TAPE E) (W s + 1) t_root) by lia.
    s2_old_mem ltac:(fun m => apply (tape_img_patchZ E _ _ m 0 (tword t_root (W s + 1)) OK) in TIMG;
      [ | rewrite length_app; cbn [length]; lia | apply tword_range; unfold t_root; lia ]).
    replace (e_TAPE E + 8 * 0)%Z with (e_TAPE E) in TIMG by lia.
    store_done.
    do 13 zstep.

    match goal with |- context [Z.b2z ?b] => destruct b eqn:EB end; cbn [Z.b2z].
    - change (Z.land ((1 + -1) mod 18446744073709551616) 3) with 0%Z. apply KS.
      eapply MEMX_of_MEMI; [s2_close_mem0 | reflexivity ..].
    - change (Z.land ((0 + -1) mod 18446744073709551616) 3) with 3%Z. s2_err_exit KX.
      eapply MEMX_of_MEMI; [s2_close_mem0 | reflexivity ..].
  Qed.
End DocEnd.
