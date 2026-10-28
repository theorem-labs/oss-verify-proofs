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

Section AtomO.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Notation bs := (e_bs E).

  Lemma seg_atoms_o : forall (Q : machine_state -> Prop) (s : st)
      xra xt0 xt1 xt2 xs0 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5
      j0 j8 j16 j24 j40 j48 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    (0 <= k s <= e_n E)%Z ->
    (0 <= W s /\ W s + 1 <= e_tcap E)%Z ->
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; C8 (Z_to_bv 64 (depth s)); CB 8 j40; CB 8 j48; C8 (Z_to_bv 64 (e_SBUF E + sb s)); C8 (Z_to_bv 64 (e_THIS E)); CB 8 j72]
         (scopes s) fc m1 ->
    Z.of_nat (length (e_tws E)) = W s -> exit_k E Q ->
    (forall v, atom_word v -> is_atomstart (e_tok E (k s)) = true -> objcont_k (gapp E [v] []) Q (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s))) ->
    evt usegs Q (S2R E 0x4b374 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xa0 (Z_to_bv 64 (e_tok E (k s))) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 (Z_to_bv 64 (e_BUF E)) xs6 xs7 xs8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))) xs10 xs11 xt3 xt4 xt5 (Z_to_bv 64 (e_TAPE E + 8 * W s)) F fc m1).
  Proof using OK.
    intros Q s xra xt0 xt1 xt2 xs0 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 j0 j8 j16 j24 j40 j48 j72 F fc m1 HK HW HM GLT KX KC.
    pose proof (ok_bytes _ OK) as BOK.
    pose proof (off_bound E OK (k s) HK) as HO. pose proof (tok_range E OK (k s)) as HT.
    pose proof (B_range bs (e_off E (k s) + 4) BOK) as HB4. pose proof (B_range bs (e_off E (k s) + 5) BOK) as HB5.
    pose proof (off_range _ _ (ok_s1 _ OK) (k s) HK) as HOR.
    s2_env OK.
    s2_open_mem HM.
    pose proof (sown_range (B bs (e_off E (k s) + 4))) as HS4. pose proof (sown_range (B bs (e_off E (k s) + 5))) as HS5.
    grun.
    if_cases K; zify_cond K.
    -
      grun.
      if_cases K2; clear K2; gforget_all ltac:(fun n => lazymatch n with 21%Z => fail | 25%Z => fail | 31%Z => fail | _ => idtac end).
      + grun_to 0x4e4c4%Z. rename K into KK.
        replace (e_TAPE E + 8 * W s + 8)%Z with (e_TAPE E + 8 * (W s + 1))%Z in FR by lia;
        s2_cur_mem ltac:(fun m => apply (tape_img_app1 E _ _ m (tword t_false 0) (e_TAPE E + 8 * W s)%Z OK) in TIMG;
          [ | exact NEWCH | lia | lia | vm_compute; split; [discriminate | reflexivity] ]);
        eapply (KC (tword t_false 0)); [right; left; reflexivity | unfold is_atomstart; rewrite KK; reflexivity | cbn [scopes k depth W sb]; s2_close_forget; [exact OCL | exact OCR | exact IAL | exact IAR | forgets_tac]].
      + grun_to 0x4be14%Z. eapply (KX 7%Z); [s2_errlit|]. s2_close_memx.
    - grun.
      if_cases K1; zify_cond K1.
      +
        grun.
        if_cases K2; clear K2; gforget_all ltac:(fun n => lazymatch n with 21%Z => fail | 25%Z => fail | 31%Z => fail | _ => idtac end).
        * grun_to 0x4e4c4%Z. rename K1 into KK.
          replace (e_TAPE E + 8 * W s + 8)%Z with (e_TAPE E + 8 * (W s + 1))%Z in FR by lia;
        s2_cur_mem ltac:(fun m => apply (tape_img_app1 E _ _ m (tword t_null 0) (e_TAPE E + 8 * W s)%Z OK) in TIMG;
          [ | exact NEWCH | lia | lia | vm_compute; split; [discriminate | reflexivity] ]);
        eapply (KC (tword t_null 0)); [right; right; reflexivity | unfold is_atomstart; rewrite KK; reflexivity | cbn [scopes k depth W sb]; s2_close_forget; [exact OCL | exact OCR | exact IAL | exact IAR | forgets_tac]].
        * grun_to 0x4be14%Z. eapply (KX 8%Z); [s2_errlit|]. s2_close_memx.
      + grun.
        if_cases K3; zify_cond K3.
        *
          grun.
          if_cases K2; clear K2; gforget_all ltac:(fun n => lazymatch n with 21%Z => fail | 25%Z => fail | 31%Z => fail | _ => idtac end).
          -- grun_to 0x4e4c4%Z. rename K3 into KK.
             replace (e_TAPE E + 8 * W s + 8)%Z with (e_TAPE E + 8 * (W s + 1))%Z in FR by lia;
        s2_cur_mem ltac:(fun m => apply (tape_img_app1 E _ _ m (tword t_true 0) (e_TAPE E + 8 * W s)%Z OK) in TIMG;
          [ | exact NEWCH | lia | lia | vm_compute; split; [discriminate | reflexivity] ]);
        eapply (KC (tword t_true 0)); [left; reflexivity | unfold is_atomstart; rewrite KK; reflexivity | cbn [scopes k depth W sb]; s2_close_forget; [exact OCL | exact OCR | exact IAL | exact IAR | forgets_tac]].
          -- grun_to 0x4be14%Z. eapply (KX 6%Z); [s2_errlit|]. s2_close_memx.
        *
          grun_to 0x4be14%Z. eapply (KX 3%Z); [s2_errlit|]. s2_close_memx.
  Qed.
End AtomO.
