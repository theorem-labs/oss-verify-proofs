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
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_lm_pro Sj_num_lm_kit Sj_num_nd_runs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac addr_near k ::= let inb := eval vm_compute in (andb (Z.leb 0 k) (Z.ltb k 16384))%Z in lazymatch inb with true => idtac end.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_ptr_hook | asan_zr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Ltac nnorm_ndc :=
  repeat match goal with
  | |- context [bv_swrap 32 (?p mod 4294967296 + ?k)] => rewrite (swrap32_zext_add p k) by lia
  | |- context [bv_swrap 32 (?p mod 4294967296)] => rewrite (swrap32_zext p) by lia
  end;
  nnorm_u.
Local Ltac nnorm ::= nnorm_ndc.
Local Ltac num_abstract_data ::= num_abstract_data_u.

Section NDPRO1.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (F : bvmap 5 word) (fc : bv 32).
  Variables (lo : Z) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Hypothesis ROOM : (lo + NDCB_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOIMG : (0x6cd000 <= lo)%Z.
  Variable Q : machine_state -> Prop.

  Definition NDREAL (d spq : Z) (mm : mem) : Prop :=
    (d = 0 \/ d = 16)%Z /\ spq = (SP - 160 - d)%Z /\
    (exists jsp, rw_cells bsegs mm spq [CB 56 jsp]) /\
    (exists jh, rw_cells bsegs mm (spq + 56) [CB (Z.to_nat d) jh]) /\
    rw_cells bsegs mm (SP + -104) (LM_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

  Lemma nd_pro1 : forall (xa0 xa1 xa2 xa3 : word), (forall d spq xt0 xt1 xt2 a4 a5 a6 a7 t3 t4 t5 t6 mm, NDREAL d spq mm ->
      mem_inv bsegs mm -> munch [(SP - 176, SP)]%Z m0 mm -> wmono bsegs m0 mm -> stk bsegs mm lo spq ->
      evt bsegs Q
        (MS (mkR (Z_to_bv 64 0xebf8c) (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) (Z_to_bv 64 608) (Z_to_bv 64 1536312) (Z_to_bv 64 1) xa3 a4 a5 a6 a7
                 xa1 s3 xa2 s5 xa0 xa3 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x64af4) fc None mm (seg_rom bsegs))) ->
    forall t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6,
    mem_inv bsegs m0 -> stk bsegs m0 lo SP -> client_consts m0 ->
    evt bsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 xa0 xa1 xa2 xa3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 B_NDC) fc None m0 (seg_rom bsegs)).
  Proof using ROOM TOP SP16 LOIMG.
    intros xa0 xa1 xa2 xa3 KC t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 MI ST (G1 & G2 & G3 & G4).
    unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in G1, G2, G3, G4.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold NDCB_STACK, P5B_STACK, LMB_STACK, RT_STACK, USTACK_TOP in ROOM, TOP. unfold B_NDC.
    pose proof (munch_refl [(SP - 176, SP)]%Z m0) as MU. pose proof (wmono_refl bsegs m0) as WM.
    set (m := m0) in MI, ST, G1, G2, G3, G4, MU at 2, WM at 2 |- *. clearbody m.
    destruct (land_m32u (SP + -160) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (d & Hd & LAND).
    step.
    destruct Hd as [-> | ->].
    -
      carve_frame 160%nat ST.
      apply (rw_cells_split_CB bsegs m _ [] 160 junk [] [8;48;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
      cbn [mk_CB_cells app] in FR.
      repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
      zstep. change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). mem_after_store_fast. do 13 step. zstep. zstep. rewrite LAND. replace (SP + -160 - 0)%Z with (SP + -160)%Z by lia.
      do 8 zstep. step. replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity). clear G3 G4. zstep. clear G1 G2. zstep.
      zstep. if_false. zstep. zstep.
      destruct (proj1 (num_rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0); CB 48 j0] _) FR) as [SPILLc SAVEDc]. clear FR.
      cbn [cells_size csize Nat.add] in SAVEDc. change (Z.of_nat 56) with 56%Z in *.
      destruct (rw_cells_forget bsegs _ _ _ SPILLc) as [jsp SPILLf]. cbn [cells_size csize Nat.add] in SPILLf.
      eapply evt_eq; [| eapply (KC 0%Z (SP + -160)%Z)]; [num_st_eq | | eassumption | eassumption | eassumption | eassumption].
      split; [left; reflexivity|]. split; [lia|]. split; [exists jsp; exact SPILLf|].
      split; [exists []; apply (rw_cells_nil_CB sp); lia|].
      replace (SP + -104)%Z with (SP + -160 + 56)%Z by lia. exact SAVEDc.
    -
      carve_frame 160%nat ST.
      apply (rw_cells_split_CB bsegs m _ [] 160 junk [] [8;32;16;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
      cbn [mk_CB_cells app] in FR.
      repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
      destruct (stk_carve bsegs m lo (SP + -160) 16 ST ltac:(lia)) as [ST2 [jl LOWc]]. clear ST. change (Z.of_nat 16) with 16%Z in ST2, LOWc.
      replace (SP + -160 - 16)%Z with (SP + -176)%Z in ST2, LOWc by lia.
      zstep. change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). mem_after_store_fast. do 13 step. zstep. zstep. rewrite LAND. replace (SP + -160 - 16)%Z with (SP + -176)%Z by lia.
      do 8 zstep. step. replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity). clear G3 G4. zstep. clear G1 G2. zstep.
      zstep. if_false. zstep. zstep.
      destruct (proj1 (num_rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0); CB 32 j0] _) FR) as [SPILLc REST]. clear FR.
      destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 16 j1] _) REST) as [HIGHc SAVEDc]. clear REST.
      cbn [cells_size csize Nat.add] in HIGHc, SAVEDc. change (Z.of_nat 40) with 40%Z in *. change (Z.of_nat 16) with 16%Z in *.
      num_cur_mem ltac:(fun mm => assert (SPILLa : rw_cells bsegs mm (SP + -176) ([CB 16 jl] ++ [C8 (Z_to_bv 64 0); CB 32 j0]))).
      { apply (proj2 (num_rw_cells_app bsegs _ (SP + -176) [CB 16 jl] [C8 (Z_to_bv 64 0); CB 32 j0])). split; [exact LOWc|].
        cbn [cells_size csize Nat.add]. change (Z.of_nat 16) with 16%Z. replace (SP + -176 + 16)%Z with (SP + -160)%Z by lia. exact SPILLc. }
      destruct (rw_cells_forget bsegs _ _ _ SPILLa) as [jsp SPILLf]. cbn [app cells_size csize Nat.add] in SPILLf.
      eapply evt_eq; [| eapply (KC 16%Z (SP + -176)%Z)]; [num_st_eq | | eassumption | eassumption | eassumption | eassumption].
      split; [right; reflexivity|]. split; [lia|]. split; [exists jsp; exact SPILLf|].
      split; [exists j1; replace (SP + -176 + 56)%Z with (SP + -160 + 40)%Z by lia; exact HIGHc|].
      replace (SP + -104)%Z with (SP + -160 + 40 + 16)%Z by lia. exact SAVEDc.
  Qed.
End NDPRO1.

Section NDPRO2.
  Variables (f p2 : Z) (m0 : mem).
  Notation S := (f / 8 + 2147450880)%Z.
  Hypothesis F64 : (f mod 64 = 0)%Z.
  Hypothesis FLO : (0x6cd000 <= f /\ f + 1016 < 2^62)%Z.
  Hypothesis FSH : (f + 1016 <= S \/ S + 127 <= f)%Z.
  Hypothesis FS0 : (0 <= S /\ S + 127 < 2^62)%Z.
  Hypothesis PR : (- NDCB_RANGE <= p2 <= NDCB_RANGE)%Z.
  Variable Q : machine_state -> Prop.
  Notation W2 := [(f, f + 32); (S, S + 76)]%Z.

  Lemma nd_poison : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc h j0 jz (mm : mem),
    (forall h' jz' (mm' : mem), rw_cells bsegs mm' f [CB 32 h'] -> rw_cells bsegs mm' (f / 8 + 2147450884) [CB 72 jz'] ->
       mem_inv bsegs mm' -> munch W2 m0 mm' -> wmono bsegs m0 mm' ->
       evt bsegs Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 (-13)) (Z_to_bv 64 p2) (Z_to_bv 64 106811) (Z_to_bv 64 966416) (Z_to_bv 64 (-8)) a6 a7
                  s2 (Z_to_bv 64 S) (Z_to_bv 64 (p2 mod 4294967296)) s5 s6 s7 s8 (Z_to_bv 64 f) (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xec12c) fc None mm' (seg_rom bsegs))) ->
    rw_cells bsegs mm f (mk_CB_cells [8;8;8;8]%nat h) ->
    rw_cells bsegs mm S [CB 4 j0] -> rw_cells bsegs mm (f / 8 + 2147450884) [CB 72 jz] ->
    mem_inv bsegs mm -> munch W2 m0 mm -> wmono bsegs m0 mm ->
    evt bsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (p2 mod 4294967296)) s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xebf8c) fc None mm (seg_rom bsegs)).
  Proof using F64 FLO FSH FS0 PR.
    intros until mm. intros KC HDR SH0 SHZ MI MU WM. pose proof PR as PR'. unfold NDCB_RANGE in PR'.
    apply (rw_cells_split_CB bsegs _ _ [] 4 j0 [] (repeat 1%nat 4)) in SH0; [| reflexivity]. cbn [app] in SH0. rewrite app_nil_r in SH0.
    cbn [mk_CB_cells repeat] in HDR, SH0.
    repeat match goal with H : rw_cells _ _ _ ?l |- _ => match l with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in H; clearbody j end end.
    bstep. bstep.
    if_cases K0; zify_cond K0; [| exfalso; lia]. clear K0.
    bwalk ltac:(fun pc => lazymatch pc with 0xec00c%Z => idtac end).
    destruct (rw_cells_forget bsegs _ _ _ HDR) as [h' HDR']. cbn [cells_size csize Nat.add] in HDR'. clear HDR SH0.
    num_cur_mem ltac:(fun m1 => eapply (nd_runP f m1 ltac:(lia) Q); [exact SHZ | exact MI | apply munch_refl | apply wmono_refl |];
      clear MI SHZ; intros jz2 mm' SHZ2 MI' MU' WM'; transport_after_call bsegs m1 mm' MU' WM'; clear MU' WM').
    eapply evt_eq; [| eapply KC; [exact HDR' | exact SHZ2 | exact MI' | exact MU | exact WM]].
    num_st_eq.
  Qed.
End NDPRO2.
