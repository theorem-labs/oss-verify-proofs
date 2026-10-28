(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber SjNumU SjNumN SjNumSwar.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow Sj_num_lm_pro.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_fc_defs Sj_num_fc_rel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac addr_near k ::= let inb := eval vm_compute in (andb (Z.leb 0 k) (Z.ltb k 16384))%Z in lazymatch inb with true => idtac end.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_ptr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Lemma fcb_nil_CB : forall (m : mem) A, (0 <= A < 2^64)%Z -> rw_cells bsegs m A [CB 0 []].
Proof.
  intros m A HA. split.
  - split; [repeat constructor|]. cbn. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Lemma land_m32_spq : forall x q, (0 <= x < 2^64)%Z -> (x - 16 <= q <= x)%Z -> (q mod 32 = 0)%Z -> Z.land x 18446744073709551584 = q.
Proof.
  intros x q Hx Hq Q32.
  change 18446744073709551584%Z with (Z.land (Z.ones 64) (-32)). rewrite Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  change (-32)%Z with (Z.lnot (Z.ones 5)). rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5)%Z with 32%Z. Z.div_mod_to_equations. lia.
Qed.

Section FCBPRO1.
  Variable E : fcbenv.

  Hypothesis ROOM0 : (q_lo E + SPB_STACK <= q_SP E)%Z.
  Hypothesis TOP0 : (q_SP E + 16 <= USTACK_TOP)%Z.
  Hypothesis SPQ0 : (q_SP E - 272 <= q_spq E <= q_SP E - 256 /\ q_spq E mod 32 = 0)%Z.
  Hypothesis LOIMG : (FCB_GTOP <= q_lo E)%Z.
  Hypothesis SP16 : (q_SP E mod 16 = 0)%Z.
  Variables (F : bvmap 5 word) (fc : bv 32).
  Variable Q : machine_state -> Prop.
  Notation SP := (q_SP E).
  Notation spq := (q_spq E).

  Definition FCBREAL (mm : mem) : Prop :=
    (exists jsp, rw_cells bsegs mm spq [CB 152 jsp]) /\
    (exists jh, rw_cells bsegs mm (spq + 152) [CB (Z.to_nat (SP - 256 - spq)) jh]) /\
    rw_cells bsegs mm (SP + -104) (fcb_saved E).

  Definition fcb_call1_k : Prop :=
    forall xt0 xt1 ya1 ya2 a6 a7 xs4 xs7 xs11 t3 t4 t5 t6 (mm : mem),
      FCBREAL mm ->
      mem_inv bsegs mm -> munch [(SP - 272, SP)]%Z (q_m0 E) mm -> wmono bsegs (q_m0 E) mm -> stk bsegs mm (q_lo E) spq ->
      evt bsegs Q
        (MS (mkR (Z_to_bv 64 0xe7b64) (Z_to_bv 64 spq) (q_gp E) (q_tp E) xt0 xt1 (Z_to_bv 64 53) (q_sp E) (Z_to_bv 64 spq) (Z_to_bv 64 608) ya1 ya2
                 (Z_to_bv 64 53) (Z_to_bv 64 42949673006) (Z_to_bv 64 1) a6 a7
                 (Z_to_bv 64 53) (Z_to_bv 64 2147450880) xs4 (Z_to_bv 64 (q_FIRST E)) (Z_to_bv 64 (q_LAST E)) xs7 (Z_to_bv 64 1) (Z_to_bv 64 42949673006) (Z_to_bv 64 (q_OUT E)) xs11
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x65118) fc None mm (seg_rom bsegs)).

  Lemma fcb_pro1 : fcb_call1_k ->
    forall t0 t1 t2 a6 a7 t3 t4 t5 t6,
    mem_inv bsegs (q_m0 E) -> stk bsegs (q_m0 E) (q_lo E) SP -> client_consts (q_m0 E) ->
    evt bsegs Q
      (MS (mkR (q_ra E) (q_sp E) (q_gp E) (q_tp E) t0 t1 t2 (q_s0 E) (q_s1 E) (Z_to_bv 64 (q_FIRST E)) (Z_to_bv 64 (q_LAST E)) (Z_to_bv 64 (q_OUT E)) (Z_to_bv 64 53)
               (Z_to_bv 64 42949673006) (Z_to_bv 64 1) a6 a7 (q_s2 E) (q_s3 E) (q_s4 E) (q_s5 E) (q_s6 E) (q_s7 E) (q_s8 E) (q_s9 E) (q_s10 E) (q_s11 E) t3 t4 t5 t6)
          F (Z_to_bv 64 0xe7adc) fc None (q_m0 E) (seg_rom bsegs)).
  Proof using ROOM0 TOP0 SPQ0 LOIMG SP16.
    intros KC. intros until t6. intros MI ST (G1 & G2 & G3 & G4).
    unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in G1, G2, G3, G4.
    pose proof ROOM0 as ROOM. pose proof TOP0 as TOP. destruct SPQ0 as [SPQ1 SPQ2]. pose proof LOIMG as LO0.
    unfold SPB_STACK, NDCB_STACK, P5B_STACK, LMB_STACK, RT_STACK, FCB_GTOP, NUM_TXT_MAX, USTACK_TOP in *.
    pose proof (bv_unsigned_in_range 64 (q_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR. unfold fcb_saved in *.
    pose proof (munch_refl [(SP - 272, SP)]%Z (q_m0 E)) as MU. pose proof (wmono_refl bsegs (q_m0 E)) as WM.
    set (m := q_m0 E) in MI, ST, G1, G2, G3, G4, MU at 2, WM at 2 |- *. clearbody m.
    assert (LAND : Z.land (SP + -256) 18446744073709551584 = spq) by (apply land_m32_spq; [lia | lia | exact SPQ2]).
    step.
    destruct (Z.eq_dec spq (SP + -256)) as [ESPQ | NSPQ].
    -
      carve_frame 256%nat ST.
      apply (rw_cells_split_CB bsegs m _ [] 256 junk [] [8;144;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
      cbn [mk_CB_cells app] in FR.
      repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
      do 15 nstep. zstep. rewrite LAND.
      do 8 zstep. step. zstep. zstep. clear G3 G4. zstep. zstep. change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1). zstep. if_false. do 3 zstep.
      destruct (proj1 (num_rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0); CB 144 j0] _) FR) as [SPILLc SAVEDc]. clear FR.
      cbn [cells_size csize Nat.add] in SAVEDc. change (Z.of_nat 152) with 152%Z in *.
      destruct (rw_cells_forget bsegs _ _ _ SPILLc) as [jsp SPILLf]. cbn [cells_size csize Nat.add] in SPILLf.
      eapply evt_eq; [| eapply KC]; [num_st_eq | | eassumption | eassumption | eassumption | rewrite ESPQ; eassumption].
      split; [exists jsp; rewrite ESPQ; exact SPILLf|].
      split; [exists []; replace (Z.to_nat (SP - 256 - spq)) with 0%nat by lia; apply fcb_nil_CB; lia|].
      replace (SP + -104)%Z with (SP + -256 + 152)%Z by lia. exact SAVEDc.
    -
      assert (ESPQ : spq = (SP + -272)%Z) by (Z.div_mod_to_equations; lia).
      carve_frame 256%nat ST.
      apply (rw_cells_split_CB bsegs m _ [] 256 junk [] [8;128;16;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
      cbn [mk_CB_cells app] in FR.
      repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
      destruct (stk_carve bsegs m (q_lo E) (SP + -256) 16 ST ltac:(lia)) as [ST2 [jl LOWc]]. clear ST. change (Z.of_nat 16) with 16%Z in ST2, LOWc.
      replace (SP + -256 - 16)%Z with (SP + -272)%Z in ST2, LOWc by lia.
      do 15 nstep. zstep. rewrite LAND.
      do 8 zstep. step. zstep. zstep. clear G3 G4. zstep. zstep. change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1). zstep. if_false. do 3 zstep.
      destruct (proj1 (num_rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0); CB 128 j0] _) FR) as [SPILLc REST]. clear FR.
      destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 16 j1] _) REST) as [HIGHc SAVEDc]. clear REST.
      cbn [cells_size csize Nat.add] in HIGHc, SAVEDc. change (Z.of_nat 136) with 136%Z in *. change (Z.of_nat 16) with 16%Z in *.
      assert (SPILLa : rw_cells bsegs m (SP + -272) ([CB 16 jl] ++ [C8 (Z_to_bv 64 0); CB 128 j0])).
      { apply (proj2 (num_rw_cells_app bsegs m (SP + -272) [CB 16 jl] [C8 (Z_to_bv 64 0); CB 128 j0])). split; [exact LOWc|].
        cbn [cells_size csize Nat.add]. change (Z.of_nat 16) with 16%Z. replace (SP + -272 + 16)%Z with (SP + -256)%Z by lia. exact SPILLc. }
      destruct (rw_cells_forget bsegs _ _ _ SPILLa) as [jsp SPILLf]. cbn [app cells_size csize Nat.add] in SPILLf.
      eapply evt_eq; [| eapply KC]; [num_st_eq | | eassumption | eassumption | eassumption | rewrite ESPQ; eassumption].
      split; [exists jsp; rewrite ESPQ; exact SPILLf|].
      split; [exists j1; replace (Z.to_nat (SP - 256 - spq)) with 16%nat by lia; replace (spq + 152)%Z with (SP + -256 + 136)%Z by lia; exact HIGHc|].
      replace (SP + -104)%Z with (SP + -256 + 136 + 16)%Z by lia. exact SAVEDc.
  Qed.
End FCBPRO1.
