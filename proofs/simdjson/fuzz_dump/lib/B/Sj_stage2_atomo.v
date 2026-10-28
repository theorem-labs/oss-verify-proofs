(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_fkit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow | s2_load_buf | s2_load_sown | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].
Local Ltac g_store_hook ::= s2_note_tape.

Section AtomO.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Notation bs := (e_bs E).

  Lemma seg_atoms_o : forall (Q : machine_state -> Prop) (s : st)
      xra xt0 xt1 xt2 xa1 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs8 xs11 xt4 xt5 xt6
      j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    (0 <= k s <= e_n E)%Z ->
    (0 <= W s /\ W s + 1 <= e_tcap E)%Z ->
    (0 <= sb s <= e_scap E)%Z ->
    Z.of_nat (length (e_tws E)) = W s -> exit_k E Q ->
    (forall v, atom_word v -> is_atomstart (e_tok E (k s)) = true -> objcont_k (gapp E [v] []) Q (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s))) ->
    evt bsegs Q (S2R E 0xc2ac8 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_tok E (k s))) xa1 (Z_to_bv 64 (e_off E (k s))) xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (SHA (e_BUF E + e_off E (k s)))) xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xt4 xt5 xt6 F fc m1).
  Proof using OK SHZ.
    intros Q s xra xt0 xt1 xt2 xa1 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs8 xs11 xt4 xt5 xt6 j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j272 j288 j304 F fc m1 HM.
    intros HK HW HSB GLT KX KC.
    pose proof (ok_bytes _ OK) as BOK.
    pose proof (off_bound E OK (k s) HK) as HO. pose proof (tok_range E OK (k s)) as HT.
    pose proof (B_range bs (e_off E (k s) + 4) BOK) as HB4. pose proof (B_range bs (e_off E (k s) + 5) BOK) as HB5.
    s2_env OK.
    s2_open_mem HM.
    pose proof (sown_range (B bs (e_off E (k s) + 4))) as HS4. pose proof (sown_range (B bs (e_off E (k s) + 5))) as HS5.
    grun.
    if_cases K; zify_cond K.
    -
      assert (KK : is_atomstart (e_tok E (k s)) = true) by (unfold is_atomstart; rewrite K; reflexivity).
      gexplore_f ltac:(fun pc => lazymatch pc with 0xcd104%Z => fail | 0xcd17c%Z => fail | _ => idtac end)
               ltac:(fun _ => first [ gexit KX
                                    | (s2_cur_mem ltac:(fun m => apply (tape_img_app1 E _ _ m (tword t_false 0) (e_TAPE E + 8 * W s)%Z OK) in TIMG;
                                         [ | exact NEWCH | lia | lia | vm_compute; split; [discriminate | reflexivity] ]);
                                       eapply (KC (tword t_false 0) ltac:(right; left; reflexivity) KK); cbn [scopes k depth W sb]; s2_close_auto) ]).
    - grun.
      if_cases K1; zify_cond K1.
      +
        assert (KK : is_atomstart (e_tok E (k s)) = true) by (unfold is_atomstart; rewrite K1; reflexivity).
        gexplore_f ltac:(fun pc => lazymatch pc with 0xcd104%Z => fail | 0xcd17c%Z => fail | _ => idtac end)
               ltac:(fun _ => first [ gexit KX
                                    | (s2_cur_mem ltac:(fun m => apply (tape_img_app1 E _ _ m (tword t_null 0) (e_TAPE E + 8 * W s)%Z OK) in TIMG;
                                         [ | exact NEWCH | lia | lia | vm_compute; split; [discriminate | reflexivity] ]);
                                       eapply (KC (tword t_null 0) ltac:(right; right; reflexivity) KK); cbn [scopes k depth W sb]; s2_close_auto) ]).
      + grun.
        if_cases K3; zify_cond K3.
        *
          assert (KK : is_atomstart (e_tok E (k s)) = true) by (unfold is_atomstart; rewrite K3; reflexivity).
          gexplore_f ltac:(fun pc => lazymatch pc with 0xcd104%Z => fail | 0xcd17c%Z => fail | _ => idtac end)
               ltac:(fun _ => first [ gexit KX
                                    | (s2_cur_mem ltac:(fun m => apply (tape_img_app1 E _ _ m (tword t_true 0) (e_TAPE E + 8 * W s)%Z OK) in TIMG;
                                         [ | exact NEWCH | lia | lia | vm_compute; split; [discriminate | reflexivity] ]);
                                       eapply (KC (tword t_true 0) ltac:(left; reflexivity) KK); cbn [scopes k depth W sb]; s2_close_auto) ]).
        *
          grun_to 0xcd104%Z. gexit KX.
  Qed.
End AtomO.
