(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast SFModel ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjPjNum SjPjDig.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit Sj_akit Sj_acps Sj_hkit Sj_num_akit Sj_num_amem
     Pj_defsA Pj_copyA Pj_tocharsA_defs Pj_fmtB_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Ltac gref G ::= exfalso; rewrite ?unsigned_lit in G by lia; rewrite ?signed_of_Z in G by lia; lia.
Ltac gfall := let G := fresh "G" in zstep; if_cases G; zify_cond G; [|gref G]; try clear G.
Ltac unot := rewrite ?ZBridge.zb_lxor_ones by lia.
Ltac scond H := unfold bv_lts in H; rewrite ?signed_of_Z in H by lia; zify_bool H.

Section FM.
  Variable J : fmI.
  Hypothesis OK : fm_ok J.
  Variables (fc : bv 32) (mb : mem).
  Variable Q : machine_state -> Prop.

  Notation p := (fi_p J). Notation NB := (fi_NB J). Notation sg := (fi_sg J). Notation n := (fi_n J). Notation e := (fi_e J). Notation lo := (fi_lo J).

  Notation FMS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt4 xt5 xt6 xF m :=
    (MS (mkR xra (Z_to_bv 64 (p + -80)) (fi_gp J) (Z_to_bv 64 TPV_A) xt0 xt1 xt2 (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 n) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
              xs2 (Z_to_bv 64 2147450880) (Z_to_bv 64 (n + e)) xs5 (fi_s6 J) (fi_s7 J) (fi_s8 J) (fi_s9 J) (fi_s10 J) (fi_s11 J) xt3 xt4 xt5 xt6)
        xF (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).

  Definition fm_exit_k : Prop := forall (e' : Z) xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt4 xt5 xt6 xF mm,
    FINV J mb mm -> (NB + sg < e' <= NB + sg + 26)%Z ->
    evt bsegs Q (FMS 0xc0854 xra xt0 xt1 xt2 (Z_to_bv 64 e') xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt4 xt5 xt6 xF mm).

  Definition fm_exp_k : Prop := forall (d : Z) xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt4 xt5 xt6 xF mm,
    FINV J mb mm -> (1 <= d <= 21)%Z ->
    evt bsegs Q (FMS 0xc08d4 xra xt0 xt1 xt2 (Z_to_bv 64 d) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt4 xt5 xt6 xF mm).

  Definition fm_l1_k : Prop := forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 xF mm,
    FINV J mb mm -> (n <= n + e <= 15)%Z ->
    evt bsegs Q (FMS e_asan_memset (Z_to_bv 64 0xc06a8) xt0 xt1 xt2 (Z_to_bv 64 (NB + sg + n)) (Z_to_bv 64 48) (Z_to_bv 64 16) xa3 xa4 xa5 xa6 xa7
                   (Z_to_bv 64 1) xs5 xt3 xt4 xt5 xt6 xF mm).
  Definition fm_l2_k : Prop := forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF mm,
    FINV J mb mm -> (1 <= n + e <= 15)%Z ->
    evt bsegs Q (FMS e_asan_memmove (Z_to_bv 64 0xc0768) xt0 xt1 xt2 (Z_to_bv 64 (NB + sg + (n + e) + 1)) (Z_to_bv 64 (NB + sg + (n + e))) (Z_to_bv 64 16) xa3 xa4 xa5 xa6 xa7
                   (Z_to_bv 64 (NB + sg + (n + e))) (Z_to_bv 64 (18446744073709551615 - (NB + sg))) xt3 xt4 xt5 xt6 xF mm).
  Definition fm_l3_k : Prop := forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt4 xt5 xt6 xF mm,
    FINV J mb mm -> (-3 <= n + e <= 0)%Z ->
    evt bsegs Q (FMS e_asan_memcpy (Z_to_bv 64 0xc07a4) xt0 xt1 xt2 (Z_to_bv 64 (p + -80 + 7)) (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 17) xa3 xa4 xa5 xa6 xa7
                   xs2 xs5 xt3 xt4 xt5 xt6 xF mm).
  Definition fm_l4_k : Prop := forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 xF mm,
    FINV J mb mm -> (2 <= n)%Z ->
    evt bsegs Q (FMS e_asan_memmove (Z_to_bv 64 0xc08ac) xt0 xt1 xt2 (Z_to_bv 64 (NB + sg + 2)) (Z_to_bv 64 (NB + sg + 1)) (Z_to_bv 64 16) xa3 xa4 xa5 xa6 xa7
                   (Z_to_bv 64 (NB + sg + 1)) xs5 xt3 xt4 xt5 xt6 xF mm).

  Hypothesis KX : fm_exit_k.
  Hypothesis KE : fm_exp_k.
  Hypothesis KL1 : fm_l1_k.
  Hypothesis KL2 : fm_l2_k.
  Hypothesis KL3 : fm_l3_k.
  Hypothesis KL4 : fm_l4_k.
  Hypothesis SHPN : nb_shzB J mb.

  Ltac fm_open TI :=
    fi_open TI; fi_env OK;
    match goal with M : munch _ mb _ |- _ => unfold fm_W in M end;
    match goal with P : nb_shzB _ _ |- _ => unfold nb_shzB, fm_W in P end;
    match goal with H : rw_cells _ _ _ (fm_saved _) |- _ => unfold fm_saved in H end.

  Lemma fm_entry : forall xt0 xt1 xt2 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF (nb : list byte),
    u8arr bsegs mb NB nb -> length nb = 40%nat -> mem_inv bsegs mb -> stk bsegs mb lo p -> client_consts mb ->
    evt bsegs Q (MS (mkR (fi_ra J) (Z_to_bv 64 p) (fi_gp J) (Z_to_bv 64 TPV_A) xt0 xt1 xt2 (fi_s0 J) (fi_s1 J) (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 n) (Z_to_bv 64 e)
                          (Z_to_bv 64 (-4)) (Z_to_bv 64 15) xa5 xa6 xa7 (fi_s2 J) (fi_s3 J) (fi_s4 J) (fi_s5 J) (fi_s6 J) (fi_s7 J) (fi_s8 J) (fi_s9 J) (fi_s10 J) (fi_s11 J)
                          xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 FMT_ENTRY_B) fc None mb (seg_rom bsegs)).
  Proof using OK KX KE KL1 KL2 KL3 KL4 SHPN.
    intros until nb. intros NA NL MI ST (G1 & G2 & _ & _). fi_env OK. unfold nb_shzB, fm_W in SHPN. unfold FMT_ENTRY_B.
    unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB in G1, G2.
    pose proof (munch_refl (fm_W J) mb) as MU. pose proof (wmono_refl bsegs mb) as WM. unfold fm_W in MU.
    zstep. carve_frame 80%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 80 junk [] [7; 17; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 7 nstep.
    zstep. zstep.
    replace (bv_swrap 32 (n + Z.land e 18446744073709551615)) with (n + e)%Z
      by (rewrite land_W64; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite swrap32_Z; clear - Kn Ke; Z.div_mod_to_equations; lia).
    zstep. if_cases G; zify_cond G; [gref G| clear G].

    destruct (proj1 (num_rw_cells_app bsegs _ _ [_; _] _) FR) as [LOC SAVED]. clear FR. cbn [cells_size csize Nat.add] in SAVED.
    replace (p + -80 + Z.of_nat 24)%Z with (p + -56)%Z in SAVED by lia.
    assert (TI : FINV J mb m) by fi_close.

    zstep. zstep. zstep. zstep. zstep. clear G1 G2.
    assert (K38 : forall ya0 ya2, evt bsegs Q (FMS 0xc0738 (fi_ra J) xt0 xt1 xt2 ya0 (Z_to_bv 64 n) ya2 (Z_to_bv 64 (-4)) (Z_to_bv 64 15) xa5 xa6 xa7 (fi_s2 J) (fi_s5 J) xt3 xt4 xt5 xt6 xF m)).
    { intros ya0 ya2.
      assert (K8c : evt bsegs Q (FMS 0xc078c (fi_ra J) xt0 xt1 xt2 ya0 (Z_to_bv 64 n) ya2 (Z_to_bv 64 (-4)) (Z_to_bv 64 15) xa5 xa6 xa7 (fi_s2 J) (fi_s5 J) xt3 xt4 xt5 xt6 xF m)).
      {
        assert (K78 : evt bsegs Q (FMS 0xc0878 (fi_ra J) xt0 xt1 xt2 ya0 (Z_to_bv 64 n) ya2 (Z_to_bv 64 (-4)) (Z_to_bv 64 15) xa5 xa6 xa7 (fi_s2 J) (fi_s5 J) xt3 xt4 xt5 xt6 xF m)).
        {
          zstep. zstep. if_cases K; zify_cond K.
          -
            zstep. zstep. gtrap. zstep. zstep. zstep. zstep.
            eapply evt_eq; [| eapply KL4; [exact TI| clear - K Kn; lia]]. num_st_eq.
          -
            zstep. zstep. gfall.
            eapply evt_eq; [| eapply (KE 1%Z); [exact TI| clear; lia]]. num_st_eq. }
        zstep. if_cases K; scond K; [exact K78|].
        zstep. if_cases K'; scond K'; [exact K78|].
        zstep. zstep. zstep. zstep.
        eapply evt_eq; [| eapply KL3; [exact TI| clear - K K' Kn Ke; lia]]. num_st_eq. }

      zstep. if_cases K; scond K; [exact K8c|].
      zstep. if_cases K'; scond K'; [exact K8c|].

      gtrap. zstep. gtrap. gtrap. zstep. unot. gtrap.
      zstep. zstep. zstep. zstep.
      eapply evt_eq; [| eapply KL2; [exact TI| clear - K K' Kn Ke; lia]]. num_st_eq. }
    zstep. if_cases K1; scond K1; [eapply evt_eq; [| eapply K38]; num_st_eq|].
    zstep. if_cases K2; scond K2; [eapply evt_eq; [| eapply K38]; num_st_eq|].

    zstep. zstep. zstep. unz. zstep. if_false.
    zstep. zstep. zstep. zstep. uov. zstep. if_false.
    zstep. zstep. zstep. zstep.
    eapply evt_eq; [| eapply KL1; [exact TI| clear - K1 K2 Kn Ke; lia]]. num_st_eq.
  Qed.

  Ltac chk := zastep; zastep; zastep; zastep; if_false.

  Ltac mark_data :=
    repeat match goal with
    | x : word |- _ => lazymatch goal with _ : IsData x |- _ => fail | _ => idtac end; let M := fresh "DM" in assert (M : IsData x) by exact Logic.I
    end.

  Lemma fm_l1b : forall xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 xF mm,
    FINV J mb mm -> (n <= n + e <= 15)%Z ->
    evt bsegs Q (FMS 0xc06a8 (Z_to_bv 64 0xc06a8) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 1) xs5 xt3 xt4 xt5 xt6 xF mm).
  Proof using OK KX SHPN.
    intros until mm. intros TI P15. pose proof TI as TI0. fm_open TI.
    zstep. zstep. unz. zstep. if_false.
    zstep. zstep. zstep. zstep. uov. zstep. if_false.
    gtrap.
    chk.
    zastep. zastep. rewrite (swrap32_id (n + e + 1)) by lia.
    astep. gtrap.
    zastep. gtrap. zastep. zastep. zastep. zastep. uov. zastep. if_false.
    chk.
    zastep. zastep. unot. astep. gtrap. zastep. gtrap. zastep. zastep.
    eapply evt_eq; [| eapply (KX (NB + sg + (n + e) + 2)%Z); [fi_close| clear - P15 Kn; lia]]. num_st_eq.
  Qed.

  Lemma fm_l2b : forall xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF mm,
    FINV J mb mm -> (1 <= n + e <= 15)%Z ->
    evt bsegs Q (FMS 0xc0768 (Z_to_bv 64 0xc0768) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                   (Z_to_bv 64 (NB + sg + (n + e))) (Z_to_bv 64 (18446744073709551615 - (NB + sg))) xt3 xt4 xt5 xt6 xF mm).
  Proof using OK KX SHPN.
    intros until mm. intros TI P15. fm_open TI.
    chk. zastep. zastep. astep. gfall. zastep.
    eapply evt_eq; [| eapply (KX (NB + sg + (n + 1))%Z); [fi_close| clear - Kn; lia]]. num_st_eq.
  Qed.

  Lemma fm_l3c : forall xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 xF mm,
    FINV J mb mm -> (-3 <= n + e <= 0)%Z ->
    evt bsegs Q (FMS 0xc0840 (Z_to_bv 64 0xc0840) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (- (n + e))) xs5 xt3 xt4 xt5 xt6 xF mm).
  Proof using OK KX SHPN.
    intros until mm. intros TI P3. fm_open TI.
    zastep. zastep. zastep. unot. gtrap. zastep.
    eapply evt_eq; [| eapply (KX (NB + sg + (n - (n + e) + 2))%Z); [fi_close| clear - Kn P3; lia]]. num_st_eq.
  Qed.

  Definition fm_l3c_k : Prop := forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 xF mm,
    FINV J mb mm -> (-3 <= n + e <= 0)%Z ->
    evt bsegs Q (FMS e_asan_memcpy (Z_to_bv 64 0xc0840) xt0 xt1 xt2 (Z_to_bv 64 (NB + sg + 2 - (n + e))) (Z_to_bv 64 (p + -80 + 7)) (Z_to_bv 64 17) xa3 xa4 xa5 xa6 xa7
                   (Z_to_bv 64 (- (n + e))) xs5 xt3 xt4 xt5 xt6 xF mm).
  Hypothesis KL3C : fm_l3c_k.

  Lemma fm_l3b : forall xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt4 xt5 xt6 xF mm,
    FINV J mb mm -> (-3 <= n + e <= 0)%Z ->
    evt bsegs Q (FMS 0xc07a4 (Z_to_bv 64 0xc07a4) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt4 xt5 xt6 xF mm).
  Proof using OK KL3C SHPN.
    intros until mm. intros TI P3. fm_open TI.
    chk. zastep. zastep. astep. gtrap.
    zastep. chk. zastep. zastep. astep. gtrap.
    zastep. chk. zastep. chk.
    zastep.
    replace (bv_swrap 32 (0 - Z.land (n + e) 18446744073709551615)) with (- (n + e))%Z
      by (assert (n + e = -3 \/ n + e = -2 \/ n + e = -1 \/ n + e = 0)%Z as [E|[E|[E|E]]] by (clear - P3; lia); rewrite E; reflexivity).
    zastep. zastep. unot.
    astep. astep. astep. astep.
    gtrap.
    zastep. zastep. zastep. zastep.
    eapply evt_eq; [| eapply KL3C; [fi_close| exact P3]]. num_st_eq.
  Qed.

  Lemma fm_l4b : forall xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 xF mm,
    FINV J mb mm -> (2 <= n)%Z ->
    evt bsegs Q (FMS 0xc08ac (Z_to_bv 64 0xc08ac) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (NB + sg + 1)) xs5 xt3 xt4 xt5 xt6 xF mm).
  Proof using OK KE SHPN.
    intros until mm. intros TI HN2. fm_open TI.
    chk. zastep. astep. gtrap. zastep. zastep. unot. gtrap.
    eapply evt_eq; [| eapply (KE (n + 1)%Z); [fi_close| clear - Kn; lia]]. num_st_eq.
  Qed.

  Lemma fm_epi : forall (e' : Z) xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt4 xt5 xt6 xF mm,
    FINV J mb mm ->
    (forall (nb : list byte), stk bsegs mm lo p -> u8arr bsegs mm NB nb -> length nb = 40%nat ->
       Q (MS (mkR (fi_ra J) (Z_to_bv 64 p) (fi_gp J) (Z_to_bv 64 TPV_A) xt0 xt1 xt2 (fi_s0 J) (fi_s1 J) (Z_to_bv 64 e') xa1 xa2 xa3 xa4 xa5 xa6 xa7
                   (fi_s2 J) (fi_s3 J) (fi_s4 J) (fi_s5 J) (fi_s6 J) (fi_s7 J) (fi_s8 J) (fi_s9 J) (fi_s10 J) (fi_s11 J) xt3 xt4 xt5 xt6)
             xF (ret_pc (fi_ra J)) fc None mm (seg_rom bsegs))) ->
    evt bsegs Q (FMS 0xc0854 xra xt0 xt1 xt2 (Z_to_bv 64 e') xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt4 xt5 xt6 xF mm).
  Proof using OK.
    intros until mm. intros TI HK. fm_open TI.
    do 7 zastep. zastep. replace (p + -80 + 80)%Z with p by lia. zastep.
    pose proof (stk_release bsegs _ lo _ _ ST LOC ltac:(lia)) as ST1. cbn [cells_size csize Nat.add] in ST1.
    replace (p + -80 + Z.of_nat 24)%Z with (p + -56)%Z in ST1 by lia.
    pose proof (stk_release bsegs _ lo _ _ ST1 SAVED ltac:(lia)) as ST2. cbn [cells_size csize Nat.add] in ST2.
    replace (p + -56 + Z.of_nat 56)%Z with p in ST2 by lia.
    apply evt_done. exact (HK nb ST2 NA NL).
  Qed.

  Lemma fm_exp : forall (d : Z) xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt4 xt5 xt6 xF mm,
    FINV J mb mm -> (1 <= d <= 21)%Z ->
    evt bsegs Q (FMS 0xc08d4 xra xt0 xt1 xt2 (Z_to_bv 64 d) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt4 xt5 xt6 xF mm).
  Proof using OK KX SHPN.
    intros until mm. intros TI HD.

    assert (K2 : forall ya3 ya4 ya6 mm', FINV J mb mm' ->
      evt bsegs Q (FMS 0xc0968 xra xt0 xt1 xt2 (Z_to_bv 64 (NB + sg + d)) (Z_to_bv 64 (NB + sg + d + 3)) (Z_to_bv 64 (NB + sg + d + 2)) ya3 ya4 (Z_to_bv 64 99) ya6 xa7
                     xs2 xs5 xt3 xt4 xt5 xt6 xF mm')).
    { intros until mm'. intros TI'. fm_open TI'. mark_data.
      zastep. gtrap. chk.
      astep. zastep. astep. astep. astep. zastep. astep. gtrap. chk.
      zastep. zastep. astep. astep. astep. astep. zastep.
      eapply evt_eq; [| eapply (KX (NB + sg + d + 4)%Z); [fi_close| clear - HD; lia]]. num_st_eq. }

    assert (K3 : forall ya3 ya4 ya6 mm', FINV J mb mm' ->
      evt bsegs Q (FMS 0xc09cc xra xt0 xt1 xt2 (Z_to_bv 64 (NB + sg + d)) (Z_to_bv 64 (NB + sg + d + 3)) (Z_to_bv 64 (NB + sg + d + 2)) ya3 ya4 (Z_to_bv 64 99) ya6 xa7
                     xs2 xs5 xt3 xt4 xt5 xt6 xF mm')).
    { intros until mm'. intros TI'. fm_open TI'. mark_data.
      zastep. gtrap. chk.
      zastep. astep. zastep. zastep. astep. astep. astep. zastep. astep. gtrap. chk.
      zastep. zastep. zastep. astep. astep. astep. astep. astep. astep. zastep. astep. gtrap. chk.
      astep. zastep. zastep. astep. astep. astep. astep. zastep.
      eapply evt_eq; [| eapply (KX (NB + sg + d + 5)%Z); [fi_close| clear - HD; lia]]. num_st_eq. }

    assert (KJ : forall ya3 ya4 mm', FINV J mb mm' ->
      evt bsegs Q (FMS 0xc0940 xra xt0 xt1 xt2 (Z_to_bv 64 (NB + sg + d)) (Z_to_bv 64 (NB + sg + d + 1)) (Z_to_bv 64 (NB + sg + d + 1 + 1)) ya3 ya4 (Z_to_bv 64 1) xa6 xa7
                     xs2 xs5 xt3 xt4 xt5 xt6 xF mm')).
    { intros until mm'. intros TI'. fm_open TI'. mark_data.
      chk. zastep. astep. astep. zastep. zastep.
      zastep. if_cases KD; clear KD.
      - eapply evt_eq; [| eapply K3; fi_close]. num_st_eq.
      - eapply evt_eq; [| eapply K2; fi_close]. num_st_eq. }
    clear K2 K3. fm_open TI.

    zastep. zastep. gtrap. chk. zastep. zastep.
    rewrite land_W64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    rewrite swrap32_Z. change ((?x + 2147483648) mod 4294967296 - 2147483648)%Z with (sw32 x).
    rewrite (sw32_mod64_add (n + e) (-1)) by (clear - Kn Ke; lia).
    astep. gtrap.

    zastep. if_cases K.
    -
      zastep. zastep.
      assert (PN : (n + e + -1 < 0)%Z).
      { unfold bv_lts in K. rewrite signed_of_Z in K by (clear - Kn Ke; lia). change (bv_signed (Z_to_bv 64 0)) with 0%Z in K. apply Z.ltb_lt in K. exact K. }
      clear K.
      replace (Z.land (n + e + -1) 18446744073709551615) with (n + e + -1 + 18446744073709551616)%Z
        by (rewrite land_W64; change (2 ^ 64)%Z with 18446744073709551616%Z; clear - PN Kn Ke; Z.div_mod_to_equations; lia).
      replace (bv_swrap 32 (0 - (n + e + -1 + 18446744073709551616))) with (1 - (n + e))%Z by (rewrite swrap32_Z; clear - PN Kn Ke; Z.div_mod_to_equations; lia).
      replace (Z_to_bv 64 (0 - (n + e + -1 + 18446744073709551616))) with (Z_to_bv 64 (1 - (n + e))) by (apply Z_to_bv_eqm; clear - PN Kn Ke; Z.div_mod_to_equations; lia).
      zastep. if_false.

      zastep. zastep. zastep. zastep. gtrap.
      eapply evt_eq; [| eapply KJ; fi_close]. num_st_eq.
    -
      clear K. zastep. zastep. zastep. zastep. zastep. gfall.
      eapply evt_eq; [| eapply KJ; fi_close]. num_st_eq.
  Qed.
End FM.
