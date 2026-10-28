(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_fkit.
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

Section AtomA.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Notation bs := (e_bs E).

  Lemma seg_atoms_a : forall (Q : machine_state -> Prop) (s : st)
      xra xt1 xa0 xa1 xa5 xs7 xs9 xt4 xt5 xt6
      j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j168 j176 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); CB 8 j168; CB 8 j176; CB 8 j208; CB 8 j272]
         (scopes s) fc m1 ->
    (0 <= k s <= e_n E)%Z ->
    (0 <= W s /\ W s + 1 <= e_tcap E)%Z ->
    Z.of_nat (length (e_tws E)) = W s -> exit_k E Q ->
    (forall v, atom_word v -> is_atomstart (e_tok E (k s)) = true -> arrcont_k (gapp E [v] []) Q (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s))) ->
    evt asegs Q (S2R E 0xc6770 xra (Z_to_bv 64 (SHA (e_THIS E + 88))) xt1 (Z_to_bv 64 (e_BUF E + e_off E (k s))) (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 (Z_to_bv 64 (e_off E (k s))) (Z_to_bv 64 (e_tok E (k s))) (Z_to_bv 64 (SHA (e_BUF E + e_off E (k s)))) xa5 (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_THIS E + 88)) (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_SBUF E + sb s)) xs7 (Z_to_bv 64 (e_BUF E)) xs9 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (e_TAPE E + 8 * W s)) (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))) xt4 xt5 xt6 F fc m1).
  Proof using OK SHZ.
    intros Q s xra xt1 xa0 xa1 xa5 xs7 xs9 xt4 xt5 xt6 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j168 j176 j208 j272 F fc m1 HM.
    intros HK HW GLT KX KC.
    pose proof (ok_bytes _ OK) as BOK.
    pose proof (off_bound E OK (k s) HK) as HO. pose proof (tok_range E OK (k s)) as HT.
    pose proof (B_range bs (e_off E (k s) + 4) BOK) as HB4. pose proof (B_range bs (e_off E (k s) + 5) BOK) as HB5.
    s2_env OK.
    s2_open_mem HM.
    pose proof (sown_range (B bs (e_off E (k s) + 4))) as HS4. pose proof (sown_range (B bs (e_off E (k s) + 5))) as HS5.
    assert (FIN : forall KK : is_atomstart (e_tok E (k s)) = true, True) by (intros; exact I).
    grun.
    if_cases K; zify_cond K.
    -
      assert (KK : is_atomstart (e_tok E (k s)) = true) by (unfold is_atomstart; rewrite K; reflexivity).
      gexplore_f ltac:(fun pc => lazymatch pc with 0xcb1dc%Z => fail | 0xcf560%Z => fail | _ => idtac end)
               ltac:(fun _ => first [ gexit KX
                                    | (replace (e_TAPE E + 8 * W s + 8)%Z with (e_TAPE E + 8 * (W s + 1))%Z by lia;
                                       s2_cur_mem ltac:(fun m => apply (tape_img_app1 E _ _ m (tword t_false 0) (e_TAPE E + 8 * W s)%Z OK) in TIMG;
                                         [ | exact NEWCH | lia | lia | vm_compute; split; [discriminate | reflexivity] ]);
                                       eapply (KC (tword t_false 0) ltac:(right; left; reflexivity) KK); cbn [scopes k depth W sb]; s2_close_auto) ]).
    - grun.
      if_cases K1; zify_cond K1.
      +
        assert (KK : is_atomstart (e_tok E (k s)) = true) by (unfold is_atomstart; rewrite K1; reflexivity).
        gexplore_f ltac:(fun pc => lazymatch pc with 0xcb1dc%Z => fail | 0xcf560%Z => fail | _ => idtac end)
                 ltac:(fun _ => first [ gexit KX
                                      | (replace (e_TAPE E + 8 * W s + 8)%Z with (e_TAPE E + 8 * (W s + 1))%Z by lia;
                                         s2_cur_mem ltac:(fun m => apply (tape_img_app1 E _ _ m (tword t_null 0) (e_TAPE E + 8 * W s)%Z OK) in TIMG;
                                         [ | exact NEWCH | lia | lia | vm_compute; split; [discriminate | reflexivity] ]);
                                       eapply (KC (tword t_null 0) ltac:(right; right; reflexivity) KK); cbn [scopes k depth W sb]; s2_close_auto) ]).
      + grun.
        if_cases K3; zify_cond K3.
        *
          assert (KK : is_atomstart (e_tok E (k s)) = true) by (unfold is_atomstart; rewrite K3; reflexivity).
          gexplore_f ltac:(fun pc => lazymatch pc with 0xcb1dc%Z => fail | 0xcf560%Z => fail | _ => idtac end)
                   ltac:(fun _ => first [ gexit KX
                                        | (replace (e_TAPE E + 8 * W s + 8)%Z with (e_TAPE E + 8 * (W s + 1))%Z by lia;
                                           s2_cur_mem ltac:(fun m => apply (tape_img_app1 E _ _ m (tword t_true 0) (e_TAPE E + 8 * W s)%Z OK) in TIMG;
                                         [ | exact NEWCH | lia | lia | vm_compute; split; [discriminate | reflexivity] ]);
                                       eapply (KC (tword t_true 0) ltac:(left; reflexivity) KK); cbn [scopes k depth W sb]; s2_close_auto) ]).
        *
          grun_to 0xcb1dc%Z. eapply (KX 3%Z); [s2_errlit|]. s2_close_memx.
  Qed.
End AtomA.
