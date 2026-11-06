(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_lm_pro Sj_num_lm_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac addr_near k ::= let inb := eval vm_compute in (andb (Z.leb 0 k) (Z.ltb k 16384))%Z in lazymatch inb with true => idtac end.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section FCPRO2.
  Variables (f FIRST : Z) (m0 : mem).
  Notation S := (f / 8 + 2147450880)%Z.
  Hypothesis F64 : (f mod 64 = 0)%Z.
  Hypothesis FLO : (0x6ca000 <= f /\ f + 1016 < 2^62)%Z.
  Hypothesis FSH : (f + 1016 <= S \/ S + 127 <= f)%Z.
  Hypothesis FS0 : (0 <= S /\ S + 127 < 2^62)%Z.
  Hypothesis FIRSTR : (0 <= FIRST < 2^63)%Z.
  Variable Q : machine_state -> Prop.
  Notation W2 := [(f, f + 32); (S, S + 92)]%Z.

  Lemma fc_poison : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 F fc h j0 jz j1 jp j3 (mm : mem),
    (forall a1' a2' a3' h' jz' (mm' : mem), rw_cells asegs mm' f [CB 32 h'] -> rw_cells asegs mm' (f / 8 + 2147450884) [CB 63 jz'] ->
       rw_cells asegs mm' (f / 8 + 2147450956) [CB 9 (repeat (Z_to_bv 8 0) 9)] ->
       mem_inv asegs mm' -> munch W2 m0 mm' -> wmono asegs m0 mm' ->
       evt asegs Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (FIRST / 8)) a1' a2' a3' a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 f) (Z_to_bv 64 S) s5 (Z_to_bv 64 FIRST) s7 s8
                  (Z_to_bv 64 2147450880) s10 s11 s2 t4 s3 t6)
             F (Z_to_bv 64 0xe3a7c) fc None mm' (seg_rom asegs))) ->
    rw_cells asegs mm f (mk_CB_cells [8;8;8;8]%nat h) ->
    rw_cells asegs mm S [CB 4 j0] -> rw_cells asegs mm (f / 8 + 2147450884) [CB 63 jz] -> rw_cells asegs mm (f / 8 + 2147450947) [CB 9 j1] ->
    rw_cells asegs mm (f / 8 + 2147450956) [CB 9 jp] -> rw_cells asegs mm (f / 8 + 2147450965) [CB 7 j3] ->
    mem_inv asegs mm -> munch W2 m0 mm -> wmono asegs m0 mm ->
    evt asegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 FIRST) s7 s8 (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xe386c) fc None mm (seg_rom asegs)).
  Proof using F64 FLO FSH FS0 FIRSTR.
    intros until mm. intros KC HDR SH0 SHZ SH1 SHP SH3 MI MU WM.
    apply (rw_cells_split_CB asegs _ _ [] 4 j0 [] (repeat 1%nat 4)) in SH0; [| reflexivity]. cbn [app] in SH0. rewrite app_nil_r in SH0.
    apply (rw_cells_split_CB asegs _ _ [] 63 jz [] (repeat 1%nat 63)) in SHZ; [| reflexivity]. cbn [app] in SHZ. rewrite app_nil_r in SHZ.
    apply (rw_cells_split_CB asegs _ _ [] 9 j1 [] (repeat 1%nat 9)) in SH1; [| reflexivity]. cbn [app] in SH1. rewrite app_nil_r in SH1.
    apply (rw_cells_split_CB asegs _ _ [] 9 jp [] (repeat 1%nat 9)) in SHP; [| reflexivity]. cbn [app] in SHP. rewrite app_nil_r in SHP.
    apply (rw_cells_split_CB asegs _ _ [] 7 j3 [] (repeat 1%nat 7)) in SH3; [| reflexivity]. cbn [app] in SH3. rewrite app_nil_r in SH3.
    cbn [mk_CB_cells repeat] in HDR, SH0, SHZ, SH1, SHP, SH3.
    repeat match goal with H : rw_cells _ _ _ ?l |- _ => match l with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in H; clearbody j end end.
    do 5 astep.
    if_cases K0; zify_cond K0; [| exfalso; lia]. clear K0.
    awalk ltac:(fun pc => lazymatch pc with 0xe3a7c%Z => idtac end).
    destruct (rw_cells_forget asegs _ _ _ HDR) as [h' HDR']. cbn [cells_size csize Nat.add] in HDR'.
    destruct (rw_cells_forget asegs _ _ _ SHZ) as [jz' SHZ']. cbn [cells_size csize Nat.add] in SHZ'.
    pose proof (rw_cells_merge_all _ _ _ SHP) as SHP'.
    eapply evt_eq; [| eapply KC; [exact HDR' | exact SHZ' | exact SHP' | exact MI | exact MU | exact WM]].
    num_st_eq.
  Qed.
End FCPRO2.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section FCPRO1.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (F : bvmap 5 word) (fc : bv 32).
  Variables (lo : Z) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Hypothesis ROOM : (lo + SPA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOIMG : (0x6ca000 <= lo)%Z.
  Variable Q : machine_state -> Prop.

  Definition FCREAL (d spq : Z) (mm : mem) : Prop :=
    (d = 0 \/ d = 16)%Z /\ spq = (SP - 192 - d)%Z /\
    (exists jsp, rw_cells asegs mm spq [CB 88 jsp]) /\
    (exists jh, rw_cells asegs mm (spq + 88) [CB (Z.to_nat d) jh]) /\
    rw_cells asegs mm (SP + -104) (LM_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

  Definition fc_call1_k (xa0 xa1 xa2 xa3 xa4 xa5 : word) : Prop :=
    forall (d spq : Z) xt0 xt1 xt2 ya1 ya2 a6 a7 t4 t6 (mm : mem),
      FCREAL d spq mm ->
      mem_inv asegs mm -> munch [(SP - 208, SP)]%Z m0 mm -> wmono asegs m0 mm -> stk asegs mm lo spq ->
      evt asegs Q
        (MS (mkR (Z_to_bv 64 0xe386c) (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) (Z_to_bv 64 736) ya1 ya2 xa3 xa4 xa5 a6 a7
                 xa4 xa3 s4 s5 xa0 xa1 xa2 (Z_to_bv 64 2147450880) xa5 s11 xa4 t4 xa3 t6)
            F (Z_to_bv 64 0x66fb4) fc None mm (seg_rom asegs)).

  Lemma fc_pro1 : forall (xa0 xa1 xa2 xa3 xa4 xa5 : word), fc_call1_k xa0 xa1 xa2 xa3 xa4 xa5 ->
    forall t0 t1 t2 a6 a7 t3 t4 t5 t6,
    mem_inv asegs m0 -> stk asegs m0 lo SP -> client_consts m0 ->
    evt asegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xe37e0) fc None m0 (seg_rom asegs)).
  Proof using ROOM TOP SP16 LOIMG.
    intros xa0 xa1 xa2 xa3 xa4 xa5 KC. intros until t6. intros MI ST (G1 & G2 & G3 & G4).
    unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in G1, G2, G3, G4.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold SPA_STACK, NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in ROOM, TOP.
    pose proof (munch_refl [(SP - 208, SP)]%Z m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    set (m := m0) in MI, ST, G1, G2, G3, G4, MU at 2, WM at 2 |- *. clearbody m.
    destruct (land_m32u (SP + -192) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (d & Hd & LAND).
    step.
    destruct Hd as [-> | ->].
    -
      carve_frame 192%nat ST.
      apply (rw_cells_split_CB asegs m _ [] 192 junk [] [8;80;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
      cbn [mk_CB_cells app] in FR.
      repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
      do 15 nstep. zstep. rewrite LAND. replace (SP + -192 - 0)%Z with (SP + -192)%Z by lia.
      do 10 zstep. step. zstep. zstep. zstep. if_false. do 4 zstep.
      destruct (proj1 (num_rw_cells_app asegs _ _ [C8 (Z_to_bv 64 0); CB 80 j0] _) FR) as [SPILLc SAVEDc]. clear FR.
      cbn [cells_size csize Nat.add] in SAVEDc. change (Z.of_nat 88) with 88%Z in *.
      destruct (rw_cells_forget asegs _ _ _ SPILLc) as [jsp SPILLf]. cbn [cells_size csize Nat.add] in SPILLf.
      eapply evt_eq; [| eapply (KC 0%Z (SP + -192)%Z)]; [num_st_eq | | eassumption | eassumption | eassumption | eassumption].
      split; [left; reflexivity|]. split; [lia|]. split; [exists jsp; exact SPILLf|].
      split; [exists []; apply rw_cells_nil_CB; lia|].
      replace (SP + -104)%Z with (SP + -192 + 88)%Z by lia. exact SAVEDc.
    -
      carve_frame 192%nat ST.
      apply (rw_cells_split_CB asegs m _ [] 192 junk [] [8;64;16;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
      cbn [mk_CB_cells app] in FR.
      repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
      destruct (stk_carve asegs m lo (SP + -192) 16 ST ltac:(lia)) as [ST2 [jl LOWc]]. clear ST. change (Z.of_nat 16) with 16%Z in ST2, LOWc.
      replace (SP + -192 - 16)%Z with (SP + -208)%Z in ST2, LOWc by lia.
      do 15 nstep. zstep. rewrite LAND. replace (SP + -192 - 16)%Z with (SP + -208)%Z by lia.
      do 10 zstep. step. zstep. zstep. zstep. if_false. do 4 zstep.
      destruct (proj1 (num_rw_cells_app asegs _ _ [C8 (Z_to_bv 64 0); CB 64 j0] _) FR) as [SPILLc REST]. clear FR.
      destruct (proj1 (num_rw_cells_app asegs _ _ [CB 16 j1] _) REST) as [HIGHc SAVEDc]. clear REST.
      cbn [cells_size csize Nat.add] in HIGHc, SAVEDc. change (Z.of_nat 72) with 72%Z in *. change (Z.of_nat 16) with 16%Z in *.
      assert (SPILLa : rw_cells asegs m (SP + -208) ([CB 16 jl] ++ [C8 (Z_to_bv 64 0); CB 64 j0])).
      { apply (proj2 (num_rw_cells_app asegs m (SP + -208) [CB 16 jl] [C8 (Z_to_bv 64 0); CB 64 j0])). split; [exact LOWc|].
        cbn [cells_size csize Nat.add]. change (Z.of_nat 16) with 16%Z. replace (SP + -208 + 16)%Z with (SP + -192)%Z by lia. exact SPILLc. }
      destruct (rw_cells_forget asegs _ _ _ SPILLa) as [jsp SPILLf]. cbn [app cells_size csize Nat.add] in SPILLf.
      eapply evt_eq; [| eapply (KC 16%Z (SP + -208)%Z)]; [num_st_eq | | eassumption | eassumption | eassumption | eassumption].
      split; [right; reflexivity|]. split; [lia|]. split; [exists jsp; exact SPILLf|].
      split; [exists j1; replace (SP + -208 + 88)%Z with (SP + -192 + 72)%Z by lia; exact HIGHc|].
      replace (SP + -104)%Z with (SP + -192 + 72 + 16)%Z by lia. exact SAVEDc.
  Qed.
End FCPRO1.
