(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_buf | s2_load_sown | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].
Local Ltac g_store_hook ::= s2_note_tape.

Section RootT.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Notation bs := (e_bs E).

  Lemma seg_root_t : forall (Q : machine_state -> Prop)
      xra xt0 xt1 xt2 xs0 xs1 xa4 xa5 xa6 xa7 xs4 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6
      j0 j8 j16 j24 j32 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_SBUF E)); C8 (Z_to_bv 64 (e_THIS E)); CB 8 j72]
         [] fc m1 ->
    Z.of_nat (length (e_tws E)) = 1%Z -> exit_k E Q ->
    docend_k (gapp E [tword t_true 0] []) Q (mkst 1 0 2 0 []) ->
    evt usegs Q (S2R E 0x43f08 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (3)) (Z_to_bv 64 (Z.lxor (e_IDX E) 18446744073709551615)) (Z_to_bv 64 (e_n E)) (Z_to_bv 64 (e_off E 0)) xa4 xa5 xa6 xa7 (Z_to_bv 64 (e_BUF E + e_off E 0)) (Z_to_bv 64 (e_IDX E)) xs4 (Z_to_bv 64 (e_BUF E)) xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_TAPE E)) xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK.
    intros Q xra xt0 xt1 xt2 xs0 xs1 xa4 xa5 xa6 xa7 xs4 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j72 F fc m1 HM GLT KX KD.
    pose proof (n_bound E OK) as HN. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL. s2_env OK.
    pose proof (ok_bytes _ OK) as BOK. pose proof (ok_tcap _ OK) as HTC.
    pose proof (off_range _ _ (ok_s1 _ OK) 0 ltac:(lia)) as HOR0.
    pose proof (B_range bs (e_off E 0 + 4) BOK) as HB4. pose proof (B_range bs (e_off E 0 + 5) BOK) as HB5.
    pose proof (sown_range (B bs (e_off E 0 + 4))) as HS4. pose proof (sown_range (B bs (e_off E 0 + 5))) as HS5.
    s2_open_mem HM.
    gexplore ltac:(fun pc => lazymatch pc with 0x4be14%Z => fail | 0x47028%Z => fail | _ => idtac end)
             ltac:(fun _ => first [ gexit KX
                                  | (replace (e_TAPE E + 16)%Z with (e_TAPE E + 8 * 2)%Z in FR by lia;
                                     replace (e_IDX E + 4)%Z with (e_IDX E + 4 * 1)%Z in FR by lia;
                                     match goal with TI : tape_img _ _ _ _, NW : bytes_at _ _ _ (le8 _) |- evt _ _ (MS _ _ _ _ _ ?m _) =>
                                       eapply (tape_img_app1 E _ _ m (tword t_true 0) _ OK) in TI;
                                       [ | exact NW | lia | lia | vm_compute; split; [discriminate | reflexivity] ] end;
                                     eapply KD; cbn [scopes k depth W sb];
                                     s2_close_forget; [exact OCL | exact OCR | exact IAL | exact IAR | forgets_tac]) ]).
  Qed.

End RootT.
