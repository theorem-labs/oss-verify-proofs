(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf Zpi Zpa SjTape Zpj Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zwd Z107 Zwa Zwb Zwg Zz4.
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
Local Ltac s2_store_done_wr ::= s2_note_tape; s2_store_done_wr_v2.

Section RootStr2.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).

  Lemma seg_root_str : forall (Q : machine_state -> Prop),
    e_tok E 0 = c_quote -> Z.of_nat (length (e_tws E)) = 1%Z -> Z.of_nat (length (e_sbs E)) = 0%Z ->
    exit_k (gapp E [tword t_str 0] []) Q ->
    (forall d cb, string_ok (e_bs E) (e_idxs E) 0 d -> Z.of_nat (length cb) = d ->
       docend_k (gapp (gapp E [tword t_str 0] []) [] (srec d cb)) Q (mkst 1 0 2 (d + 5) [])) ->
    rootprim_k E Q 0x2b1a4.
  Proof using OK.
    intros Q HQ GLT GLS KX KD. unfold rootprim_k.
    intros xra xt0 xt1 xt2 xs1 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j1 j2 j3 j4 j5 j9 F fc m1 HM.
    pose proof (n_bound E OK) as HN. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL.
    destruct (tok_string _ _ (ok_s1 _ OK) 0 ltac:(lia) HQ) as (j & HC & HJ1 & HJ2).
    pose proof (off_range _ _ (ok_s1 _ OK) 0 ltac:(lia)) as HO. pose proof (off_range _ _ (ok_s1 _ OK) (0 + 1) ltac:(lia)) as HO1.
    s2_env OK.
    s2_open_mem HM.
    do 14 sstep. lstep. do 4 sstep. sstep. sstep. sstep. sstep. sstep.
    match goal with TI : tape_img _ _ _ _, NW : bytes_at _ _ _ (le8 _) |- evt _ _ (MS _ _ _ _ _ ?m _) =>
      apply (tape_img_app1 E _ _ m (tword t_str 0) (e_TAPE E + 8)%Z OK) in TI;
      [ | exact NW | lia | lia | vm_compute; split; [discriminate | reflexivity] ] end.
    set (E' := gapp E [tword t_str 0] []) in *.
    assert (OK' : env_ok E') by (apply env_ok_gapp; exact OK).
    assert (HROOM : ((j - e_off E' 0) + 4 <= e_scap E')%Z) by (subst E'; cbn [gapp s2_ghost e_scap e_bs e_idxs]; lia).
    assert (KE' : forall d', (0 <= d' <= j - e_off E' 0 - 1)%Z -> rootstrend_k E' Q d').
    { intros d' Hd'. apply (seg_root_str_end E' OK'); [subst E'; cbn [gapp s2_ghost e_scap e_bs e_idxs] in *; lia
        | subst E'; cbn [gapp s2_ghost e_scap e_bs e_idxs] in *; lia
        | subst E'; cbn [gapp s2_ghost e_sbs]; rewrite length_app; cbn [length]; lia |].
      intros cb HCB. apply KD; [|exact HCB]. exists j. split; [exact HC | subst E'; cbn [gapp s2_ghost e_bs e_idxs] in *; lia]. }
    pose proof (rootstr_loop E' OK' Q (e_off E' 0) j HROOM ltac:(subst E'; cbn [gapp s2_ghost e_bs e_idxs]; lia)
                  ltac:(subst E'; cbn [gapp s2_ghost e_sbs]; rewrite length_app; cbn [length]; lia)
                  KX KE' (S (Z.to_nat (j - e_off E' 0))) (e_off E' 0 + 1)%Z 0%Z) as L.
    replace (e_SBUF E' + 4 + 0)%Z with (e_SBUF E' + 4)%Z in L by lia.
    replace (e_BUF E' + (e_off E' 0 + 1))%Z with (e_BUF E' + e_off E' 0 + 1)%Z in L by lia.
    eapply L; [apply PS_init; exact HC | subst E'; cbn [gapp s2_ghost e_bs e_idxs]; lia | s2_close_mem0].
  Qed.
End RootStr2.
