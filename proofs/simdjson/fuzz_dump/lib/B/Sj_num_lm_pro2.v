(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_lm_pro Sj_num_lm_kit Sj_num_lm_runs Sj_num_lm_runs2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_ptr_hook | asan_zr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Section LMPRO2.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo d spq f : Z) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Hypothesis SPQ : ((d = 0 \/ d = 16) /\ spq = SP - 224 - d)%Z.
  Hypothesis ROOM : (lo + LMB_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis F64 : (f mod 64 = 0)%Z.
  Hypothesis FLO : (0x6cd000 <= f /\ f + 2040 <= lo)%Z.
  Hypothesis FSH : (f + 2040 <= S \/ S + 255 <= f)%Z.
  Hypothesis FS0 : (0 <= S /\ S + 255 <= lo)%Z.
  Hypothesis XR : (0 <= X /\ X + 504 <= lo)%Z.
  Variable Q : machine_state -> Prop.

  Notation W2 := [(spq, spq + 120); (f, f + 32); (S, S + 148)]%Z.

  Definition lm_fa4_k : Prop :=
    forall xt0 xt2 xa7 xt3 xt4 xt5 xt6 ja jb jm h jz jzi (mm : mem),
      rw_cells bsegs mm spq [CB 40 ja; C8 (Z_to_bv 64 (X + 496)); C8 (Z_to_bv 64 f); CB 32 jb; C8 (Z_to_bv 64 5); CB 24 jm] ->
      rw_cells bsegs mm f [CB 32 h] ->
      rw_cells bsegs mm (f / 8 + 2147450884) [CB 63 jz] ->
      rw_cells bsegs mm (f / 8 + 2147450956) [CB 63 jzi] ->
      mem_inv bsegs mm -> munch W2 m0 mm -> wmono bsegs m0 mm ->
      evt bsegs Q
        (MS (mkR (Z_to_bv 64 0xecd50) (Z_to_bv 64 spq) gp tp xt0 (Z_to_bv 64 5) xt2 sp (Z_to_bv 64 spq) (Z_to_bv 64 (-8)) (Z_to_bv 64 (-13)) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 (-14))
                 (Z_to_bv 64 92762) (Z_to_bv 64 969940) (Z_to_bv 64 f) xa7 s2 (Z_to_bv 64 S) (Z_to_bv 64 X) (Z_to_bv 64 ((X + 496) / 8)) s6 (Z_to_bv 64 2147450880) (Z_to_bv 64 B_P5LARGE) s9 s10 s11
                 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0xed024) fc None mm (seg_rom bsegs)).

  Lemma lm_poison : lm_fa4_k -> forall xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 ja j40 j48 jb jm h jsh0 jz jsh1 jzi (mm : mem),
    rw_cells bsegs mm spq [CB 40 ja; CB 8 j40; CB 8 j48; CB 32 jb; C8 (Z_to_bv 64 5); CB 24 jm] ->
    rw_cells bsegs mm f (mk_CB_cells [8;8;8;8]%nat h) ->
    rw_cells bsegs mm S (mk_CB_cells (repeat 1%nat 4) jsh0) ->
    rw_cells bsegs mm (f / 8 + 2147450884) [CB 63 jz] ->
    rw_cells bsegs mm (f / 8 + 2147450947) (mk_CB_cells (repeat 1%nat 9) jsh1) ->
    rw_cells bsegs mm (f / 8 + 2147450956) [CB 72 jzi] ->
    mem_inv bsegs mm -> munch W2 m0 mm -> wmono bsegs m0 mm ->
    evt bsegs Q
      (MS (mkR (Z_to_bv 64 0xecd50) (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) (Z_to_bv 64 f) xa1 xa2 xa3 xa4 xa5 xa6 xa7
               s2 s3 (Z_to_bv 64 X) s5 s6 (Z_to_bv 64 2147450880) (Z_to_bv 64 B_P5LARGE) s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0xecd50) fc None mm (seg_rom bsegs)).
  Proof using SPQ ROOM TOP F64 FLO FSH FS0 XR.
    intros KC. intros until mm. intros LOW HDR SH0 SHZ SH1 SHZI MI MU WM.
    destruct SPQ as [Hd Hspq]. pose proof ROOM as ROOM'. pose proof TOP as TOP'. unfold LMB_STACK, RT_STACK, USTACK_TOP in ROOM', TOP'. unfold B_P5LARGE in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    apply (rw_cells_split_CB bsegs _ _ [] 63 jz [] [60; 1; 1; 1]%nat) in SHZ; [| reflexivity]. cbn [app] in SHZ. rewrite app_nil_r in SHZ.
    cbn [mk_CB_cells repeat] in HDR, SH0, SHZ, SH1.
    repeat match goal with H : rw_cells _ _ _ ?l |- _ => match l with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in H; clearbody j end end.
    astep. astep. astep. astep.
    if_cases K0; zify_cond K0; [| exfalso; lia]. clear K0.
    awalk ltac:(fun pc => lazymatch pc with 0xece14%Z => idtac end).
    pose proof (rw_cells_merge_all _ _ _ SHZ) as SHZ'. cbn [cells_size csize Nat.add] in SHZ'. clear SHZ.
    destruct (rw_cells_forget bsegs _ _ _ HDR) as [h' HDR']. cbn [cells_size csize Nat.add] in HDR'. clear HDR SH0 SH1.

    num_cur_mem ltac:(fun m1 => eapply (lm_runP2 f m1 ltac:(lia) Q); [exact SHZ' | exact MI | apply munch_refl | apply wmono_refl |];
      clear MI SHZ'; intros jz2 mm' SHZ2 MI' MU' WM'; transport_after_call bsegs m1 mm' MU' WM'; clear MU' WM').

    num_cur_mem ltac:(fun m1 => eapply (lm_runP3 f m1 ltac:(lia) Q); [exact SHZI | exact MI' | apply munch_refl | apply wmono_refl |];
      clear MI' SHZI; intros jzi2 mm2 SHZI2 MI2 MU2 WM2; transport_after_call bsegs m1 mm2 MU2 WM2; clear MU2 WM2).
    apply (rw_cells_split_CB bsegs _ _ [] 72 jzi2 [] [63; 9]%nat) in SHZI2; [| reflexivity]. cbn [mk_CB_cells app] in SHZI2.
    destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 63 _] _) SHZI2) as [SHZI3 _]. clear SHZI2.
    eapply evt_eq; [| eapply KC; [exact LOW | exact HDR' | exact SHZ2 | exact SHZI3 | exact MI2 | exact MU | exact WM]].
    num_st_eq.
  Qed.
End LMPRO2.
