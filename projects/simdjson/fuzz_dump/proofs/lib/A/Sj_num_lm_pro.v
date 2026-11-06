(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac addr_near k ::= let inb := eval vm_compute in (andb (Z.leb 0 k) (Z.ltb k 16384))%Z in lazymatch inb with true => idtac end.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Lemma land_m32 : forall x, (0 <= x)%Z -> (x mod 16 = 0)%Z -> exists d, (d = 0 \/ d = 16)%Z /\ Z.land x (-32) = (x - d)%Z.
Proof.
  intros x X0 X16. change (-32)%Z with (Z.lnot (Z.ones 5)). rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5)%Z with 32%Z.
  exists (x mod 32)%Z. split; [| pose proof (Z.div_mod x 32 ltac:(lia)); lia].
  pose proof (Z.mod_pos_bound x 32 ltac:(lia)). assert (E : (x mod 32 = 16 * ((x mod 32) / 16))%Z).
  { pose proof (Z.div_mod (x mod 32) 16 ltac:(lia)) as D. replace ((x mod 32) mod 16)%Z with 0%Z in D; [lia|].
    symmetry. rewrite <- (Znumtheory.Zmod_div_mod 16 32 x) by (try lia; exists 2%Z; lia). exact X16. }
  assert ((x mod 32) / 16 = 0 \/ (x mod 32) / 16 = 1)%Z by (assert (0 <= (x mod 32) / 16 < 2)%Z by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]); lia).
  lia.
Qed.

Lemma land_m32u : forall x, (0 <= x < 2^64)%Z -> (x mod 16 = 0)%Z ->
  exists d, (d = 0 \/ d = 16)%Z /\ Z.land x 18446744073709551584 = (x - d)%Z.
Proof.
  intros x Hx X16. destruct (land_m32 x ltac:(lia) X16) as (d & Hd & E). exists d. split; [exact Hd|]. rewrite <- E.
  change 18446744073709551584%Z with (Z.land (Z.ones 64) (-32)). rewrite Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma rw_cells_nil_CB : forall (m : mem) A, (0 <= A < 2^64)%Z -> rw_cells asegs m A [CB 0 []].
Proof.
  intros m A HA. split.
  - split; [repeat constructor|]. cbn. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Definition LM_SAVED (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section LMPRO1.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo : Z) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Hypothesis ROOM : (lo + LMA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOIMG : (0x6c1000 <= lo)%Z.
  Variable Q : machine_state -> Prop.

  Definition LMREAL (d spq : Z) (mm : mem) (spill : list cell) : Prop :=
    (d = 0 \/ d = 16)%Z /\ spq = (SP - 256 - d)%Z /\
    (exists jl, rw_cells asegs mm spq [CB 16 jl]) /\
    rw_cells asegs mm (spq + 16) spill /\
    (exists jh, rw_cells asegs mm (spq + 152) [CB (Z.to_nat d) jh]) /\
    rw_cells asegs mm (SP + -104) (LM_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

  Definition lm_call1_k : Prop :=
    forall (d spq : Z) xt0 xt1 xt2 xa1 a3 a4 a5 a6 a7 t3 t4 t5 t6 ja jb (mm : mem),
      LMREAL d spq mm [CB 104 ja; C8 (Z_to_bv 64 X); CB 24 jb] ->
      mem_inv asegs mm -> munch [(SP - 272, SP)]%Z m0 mm -> wmono asegs m0 mm -> stk asegs mm lo spq ->
      evt asegs Q
        (MS (mkR (Z_to_bv 64 0xe0e90) (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) (Z_to_bv 64 1184) xa1 (Z_to_bv 64 1) a3 a4 a5 a6 a7
                 s2 s3 s4 (Z_to_bv 64 0x2b3e0) s6 s7 s8 (Z_to_bv 64 5) (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x64e50) fc None mm (seg_rom asegs)).

  Lemma lm_pro1 : lm_call1_k -> forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    mem_inv asegs m0 -> stk asegs m0 lo SP -> client_consts m0 ->
    evt asegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 0x2b3e0) (Z_to_bv 64 5) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xe0e18) fc None m0 (seg_rom asegs)).
  Proof using ROOM TOP SP16 LOIMG.
    intros KC t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 MI ST (G1 & G2 & G3 & G4).
    unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in G1, G2, G3, G4.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold LMA_STACK, RT_STACK, USTACK_TOP in ROOM, TOP.
    pose proof (munch_refl [(SP - 272, SP)]%Z m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    set (m := m0) in MI, ST, G1, G2, G3, G4, MU at 2, WM at 2 |- *. clearbody m.
    destruct (land_m32u (SP + -256) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (d & Hd & LAND).
    step.
    destruct Hd as [-> | ->].
    -
      carve_frame 256%nat ST.
      apply (rw_cells_split_CB asegs m _ [] 256 junk [] [8;8;104;8;24;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
      cbn [mk_CB_cells app] in FR.
      repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
      do 14 nstep. zstep. zstep. rewrite LAND. replace (SP + -256 - 0)%Z with (SP + -256)%Z by lia.
      do 9 zstep. step. zstep. if_false. zstep. zstep.
      destruct (proj1 (num_rw_cells_app asegs _ _ [C8 (Z_to_bv 64 0); CB 8 j0] _) FR) as [LOWc REST]. clear FR.
      destruct (proj1 (num_rw_cells_app asegs _ _ [CB 104 j1; C8 (Z_to_bv 64 X); CB 24 j3] _) REST) as [SPILLc SAVEDc]. clear REST.
      cbn [cells_size csize Nat.add] in SPILLc, SAVEDc. change (Z.of_nat 16) with 16%Z in *. change (Z.of_nat 136) with 136%Z in *.
      destruct (rw_cells_forget asegs _ _ _ LOWc) as [jl LOWf]. cbn [cells_size csize Nat.add] in LOWf.
      eapply evt_eq; [| eapply (KC 0%Z (SP + -256)%Z)]; [num_st_eq | | eassumption | eassumption | eassumption | eassumption].
      split; [left; reflexivity|]. split; [lia|]. split; [exists jl; exact LOWf|].
      split; [replace (SP + -256 + 16)%Z with (SP + -256 + 16)%Z by lia; exact SPILLc|].
      split; [exists []; apply rw_cells_nil_CB; lia|].
      replace (SP + -104)%Z with (SP + -256 + 16 + 136)%Z by lia. exact SAVEDc.
    -
      carve_frame 256%nat ST.
      apply (rw_cells_split_CB asegs m _ [] 256 junk [] [8;96;8;24;16;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
      cbn [mk_CB_cells app] in FR.
      repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
      destruct (stk_carve asegs m lo (SP + -256) 16 ST ltac:(lia)) as [ST2 [jl LOWc]]. clear ST. change (Z.of_nat 16) with 16%Z in ST2, LOWc.
      replace (SP + -256 - 16)%Z with (SP + -272)%Z in ST2, LOWc by lia.
      do 14 nstep. zstep. zstep. rewrite LAND. replace (SP + -256 - 16)%Z with (SP + -272)%Z by lia.
      do 9 zstep. step. zstep. if_false. zstep. zstep.
      destruct (proj1 (num_rw_cells_app asegs _ _ [C8 (Z_to_bv 64 0); CB 96 j0; C8 (Z_to_bv 64 X); CB 24 j2] _) FR) as [SPILLc REST]. clear FR.
      destruct (proj1 (num_rw_cells_app asegs _ _ [CB 16 j3] _) REST) as [HIGHc SAVEDc]. clear REST.
      cbn [cells_size csize Nat.add] in HIGHc, SAVEDc. change (Z.of_nat 136) with 136%Z in *. change (Z.of_nat 16) with 16%Z in *.
      pose proof (rw_cells_merge asegs _ _ [] [C8 (Z_to_bv 64 0); CB 96 j0] _ SPILLc) as SPILLm. cbn [app cells_size csize Nat.add] in SPILLm.
      eapply evt_eq; [| eapply (KC 16%Z (SP + -272)%Z)]; [num_st_eq | | eassumption | eassumption | eassumption | eassumption].
      split; [right; reflexivity|]. split; [lia|]. split; [exists jl; exact LOWc|].
      split; [replace (SP + -272 + 16)%Z with (SP + -256)%Z by lia; exact SPILLm|].
      split; [exists j3; replace (SP + -272 + 152)%Z with (SP + -256 + 136)%Z by lia; exact HIGHc|].
      replace (SP + -104)%Z with (SP + -256 + 136 + 16)%Z by lia. exact SAVEDc.
  Qed.
End LMPRO1.
