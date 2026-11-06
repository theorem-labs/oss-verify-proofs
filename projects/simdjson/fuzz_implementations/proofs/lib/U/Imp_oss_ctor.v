(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image ZBridge MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel ImpModel Target Prog PjImpl.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Pj_steps Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit F_memset Pj_loc_defs Pj_loc_kit Pj_loc_get Pj_os_kit.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Pj_copy Pj_kit Imp_oss_defs.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Ubsan.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac PROBEH := try (match goal with H : ?T |- _ => lazymatch T with rw_cells _ _ _ _ => idtac H ":" T | munch _ _ _ => idtac H ":" T | stk _ _ _ _ => idtac H ":" T | u8arr _ _ _ _ => idtac H ":" T | _ => fail end; fail end).
Ltac PROBE := PROBEH; match goal with |- evt _ _ (MS ?r _ ?pc _ _ ?m _) => idtac "PC:" pc "MEM:" m; idtac "REGS:" r end; fail "PROBE".

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition locale_ctor_postZ (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo D : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0' t1' t2' s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(q - 32, q); (D, D + 8)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo q
    /\ rw_cells usegs m' D [C8 (Z_to_bv 64 OSS_CLASSIC)]
    /\ LOCB m'.
Lemma locale_ctor_specZ : forall ra q gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo D : Z) (j : list byte),
  stk usegs m lo q -> lo <= q - 32 -> 0x117000 <= lo ->
  LOCB m -> rw_cells usegs m D [CB 8 j] -> q <= D -> D < 2^63 -> mem_inv usegs m ->
  evt usegs (locale_ctor_postZ ra q gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo D m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xaba40) fc None m (seg_rom usegs)).
Proof.
  intros until j. intros ST LO GLO LB DC QD DH MI.
  assert (Q0 : 0 <= q) by (destruct ST as [? _]; lia).
  assert (U : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  eapply evt_mono.
  - eapply (locale_ctor_specB ra (Z_to_bv 64 q)) with (lo := lo) (D := D) (j := j); rewrite ?U; try assumption; lia.
  - intros ms' PO. unfold locale_ctor_post in PO. unfold locale_ctor_postZ, OSS_CLASSIC. rewrite U in PO. cbn [app] in PO. exact PO.
Qed.

Definition append_short0_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo P : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(q - 80, q); (P, P + 24)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo q
    /\ rw_cells usegs m' P [C1 (Z_to_bv 8 44)] /\ rw_cells usegs m' (P + 1) [CB 22 (repeat (Z_to_bv 8 0) 22)] /\ rw_cells usegs m' (P + 23) [C1 (Z_to_bv 8 0)].

Lemma append_short0_spec : forall ra q gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo P : Z),
  stk usegs m lo q -> lo <= q - 80 -> GLOBALS_TOP <= lo ->
  rw_cells usegs m P [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> q <= P -> P + 24 < 2^62 -> mem_inv usegs m ->
  evt usegs (append_short0_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo P m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 22) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 OSS_APPEND) fc None m (seg_rom usegs)).
Proof.
  intros until P. intros ST LO GLO REP PLO PHI MI. unfold OSS_APPEND, GLOBALS_TOP in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(q - 80, q); (P, P + 24)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  carve_frame 80%nat ST.

  do 11 lstep. lstep. lstep. if_false. lstep.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (rw_cells_C8_read1_g usegs mx _ _ _ REP) as RD end. change (bv_unsigned (Z_to_bv 64 0)) with 0 in RD.
  lstep. lstep. lstep. lstep. if_false.

  lstep. lstep. lstep. if_false. lstep. lstep. lstep. lstep. if_false.

  lstep. if_true. lstep. lstep. lstep. lstep. lstep. lstep.

  clear RD. retype REP [C1 (Z_to_bv 8 0); CB 22 (repeat (Z_to_bv 8 0) 22); C1 (Z_to_bv 8 0)].
  takeZ REP 1%nat (P + 1) R0. takeZ REP 1%nat (P + 23) RZ.
  lstep. call memset_callZ; [exact RZ| assumption| lia| lia| lia| lia|].
  rename POST into RZ. change (Z.to_nat 22) with 22%nat in RZ. change (0 mod 256) with 0 in RZ.

  lstep. lstep. lstep. if_false. lstep. lstep. lstep. lstep. lstep.

  lstep. do 10 lstep. lstep. release_frame FR ST q. lstep.
  apply evt_done. unfold append_short0_post. sys_finish.
Qed.

Definition init_buf_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo O : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(q - 128, q); (O + 48, O + 104)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo q
    /\ rw_cells usegs m' (O + 8) (sb_cellsI (oss0 O))
    /\ rw_cells usegs m' (O + 96) [C8 (Z_to_bv 64 (O + 73))]
    /\ rw_cells usegs m' (O + 72) [C1 (Z_to_bv 8 44)] /\ rw_cells usegs m' (O + 73) [CB 23 (repeat (Z_to_bv 8 0) 23)].

Lemma init_buf_spec : forall ra q gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo O : Z) (j108 : list byte),
  stk usegs m lo q -> lo <= q - 128 -> GLOBALS_TOP <= lo ->
  rw_cells usegs m (O + 8) [C8 (Z_to_bv 64 OSS_SB_VPTR); C8 (Z_to_bv 64 OSS_CLASSIC); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                          C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells usegs m (O + 72) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells usegs m (O + 96) [C8 (Z_to_bv 64 0)] -> rw_cells usegs m (O + 104) [CB 4 mode16; CB 4 j108] ->
  q <= O -> O + 264 < 2^62 -> mem_inv usegs m ->
  evt usegs (init_buf_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo O m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 (O + 8)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 OSS_INIT_BUF) fc None m (seg_rom usegs)).
Proof.
  intros until j108. intros ST LO GLO SBC REP HMC MODE OLO OHI MI. unfold OSS_INIT_BUF, OSS_SB_VPTR, OSS_CLASSIC, GLOBALS_TOP in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(q - 128, q); (O + 48, O + 104)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  carve_frame 48%nat ST.

  do 6 lstep. lstep.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (rw_cells_C8_read1_g usegs mx _ _ _ REP) as RD end. change (bv_unsigned (Z_to_bv 64 0)) with 0 in RD.
  lstep. lstep. lstep. lstep. if_true.

  lstep. lstep. lstep. lstep. lstep. if_true.

  lstep. lstep. if_false. zstep. gtrap.

  zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. zstep. if_false.

  lstep. lstep. lstep. if_false. lstep. lstep. lstep. lstep.

  clear RD. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (rw_cells_C8_read1_g usegs mx _ _ _ REP) as RD end. change (bv_unsigned (Z_to_bv 64 0)) with 0 in RD.
  lstep. lstep. lstep. if_true. lstep. lstep. if_false. lstep. lstep. clear RD.

  replace (Z_to_bv 64 (O + 8 + 64)) with (Z_to_bv 64 (O + 72)) by (f_equal; lia).
  try replace (Z_to_bv 64 (22 - 0)) with (Z_to_bv 64 22) by (f_equal; lia). try replace (Z_to_bv 64 (22 + - 0)) with (Z_to_bv 64 22) by (f_equal; lia).
  call (append_short0_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo (O + 72)); [exact ST| lia| unfold GLOBALS_TOP; lia| exact REP| lia| lia| assumption|].
    rename PC into ST. rename PC0 into R44. rename PC1 into RZ22. rename POST into RNUL.

  lstep. lstep. lstep. if_true. lstep. zstep. gtrap.

  zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. zstep. if_false.

  lstep. lstep. lstep. lstep. lstep. lstep. if_true.

  do 5 lstep. lstep. release_frame FR ST q. lstep.
  retype_at RNUL 0%nat 1%nat [CB 1 [Z_to_bv 8 0]].
  pose proof (rw_cells_CB_join2 _ _ _ _ _ _ _ RZ22 RNUL ltac:(lia)) as RZ23. clear RZ22 RNUL.
  change (repeat (Z_to_bv 8 0) 22 ++ [Z_to_bv 8 0]) with (repeat (Z_to_bv 8 0) 23) in RZ23. change (22 + 1)%nat with 23%nat in RZ23.
  replace (O + 72 + 1) with (O + 73) in RZ23 by lia.
  replace (0 + (O + 73)) with (O + 73) in HMC by lia.
  try (replace (0 + (O + 73)) with (O + 73) in SBC by lia). try (replace (22 + (O + 73)) with (O + 95) in SBC by lia).
  apply evt_done. unfold init_buf_post, sb_cellsI, oss0, os_lim, OSS_SB_VPTR, OSS_CLASSIC. cbn [os_data os_w os_blk os_cap].
  replace (O + 73 + 0) with (O + 73) by lia. replace (O + 73 + 22) with (O + 95) by lia.
  sys_finish.
Qed.

Theorem oss_ctor_proof : oss_ctor_stmt.
Proof.
  unfold oss_ctor_stmt, OSS_CTOR, OSS_CTOR_STACK. intros until junk. intros ST GLO LO Q0 QO OHI OSR VT LB MI HLEN.
  unfold GLOBALS_TOP in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  destruct VT as (V1 & V2 & V3 & V4).
  unfold OSS_GOT_VT, OSS_VTT, OSS_VBOFF, OSS_SBVT, OSS_XSPUTN, OSS_OVERFLOW, OSS_OS_VPTR, OSS_OS_CVPTR, OSS_IOS_CVPTR, OSS_IOS_VPTR, OSS_SB_VPTR, OSS_SBB_VPTR in V1, V2, V3, V4.
  replace (914144 - 16) with 914128 in V1 by reflexivity. replace (913568 - 16) with 913552 in V1 by reflexivity.
  pose proof (munch_refl [(q - 240, q); (O, O + 264)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  apply (rw_cells_split_CB usegs _ _ [] 264 junk [] [8; 8; 8; 48; 8; 8; 8; 8; 4; 4; 8; 4; 4; 8; 8; 4; 4; 8; 8; 80; 8; 4; 4]%nat) in OSR; [|reflexivity].
  cbn [mk_CB_cells app] in OSR. forget_junk OSR.
  carve_frame 64%nat ST.

  do 29 lstep.

  carve_frame 16%nat ST.
  do 18 lstep.
  replace (O + 8 <? 1) with false in OSR by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z] in OSR.

  takeZ OSR 19%nat (O + 168) P0. takeZ OSR 1%nat (O + 248) MS1.
  lstep. call memset_callZ; [exact MS1| assumption| lia| lia| lia| lia|].
  rename POST into MS1. change (Z.to_nat 80) with 80%nat in MS1. change (0 mod 256) with 0 in MS1.
  retype MS1 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
              C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
  glueZ MS1 OSR. glueZ P0 MS1. rename P0 into OSR.

  do 4 lstep. release_frame FR0 ST (q + -64). lstep.
  takeZ OSR 18%nat (O + 160) P0. takeZ OSR 1%nat (O + 168) LOC2.
  retype LOC2 [CB 8 (repeat (Z_to_bv 8 0) 8)].
  call (locale_ctor_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo (O + 160));
    [exact ST| lia| lia| eapply LOCB_transport; [exact LB| exact MU| exact WM| cbv [disjoint_from fst snd]; repeat split; lia]| exact LOC2| lia| lia| assumption|].
  rename PC into ST. rename PC0 into LOC2. rename POST into LB2. clear LB.
  glueZ LOC2 OSR. glueZ P0 LOC2. rename P0 into OSR.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (munch_refl [(q - 240, q); (O, O + 264)]%Z mx) as MU2; pose proof (wmono_refl usegs mx) as WM2 end.

  takeZ OSR 30%nat (O + 256) P0. takeZ OSR 1%nat (O + 260) FILL.
  apply (rw_cells_split_CB usegs _ _ [] 4 _ [] [1; 1; 1; 1]%nat) in FILL; [|reflexivity]. cbn [mk_CB_cells app] in FILL. forget_junk FILL.
  rename OSR into OSRP. rename P0 into OSR.

  lstep. lstep. zstep. change (le1 (Z_to_bv 64 (-1))) with [Z_to_bv 8 18446744073709551615]. mem_after_store.
  lstep.
  do 3 (zstep; change (le1 (Z_to_bv 64 (-1))) with [Z_to_bv 8 18446744073709551615]; mem_after_store).
  retype_at FILL 0%nat 4%nat [C4 (Z_to_bv 64 0xFFFFFFFF)].
  lstep. lstep. lstep. lstep. lstep.

  carve_frame 48%nat ST.
  do 14 lstep. lstep.
  replace (Z_to_bv 64 (O + 8 + 8)) with (Z_to_bv 64 (O + 16)) by (f_equal; lia).
  takeZ OSR 2%nat (O + 16) P0. takeZ OSR 1%nat (O + 24) LOC1.
  call (locale_ctor_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo (O + 16));
    [exact ST| lia| lia| eapply LOCB_transport; [exact LB2| exact MU2| exact WM2| cbv [disjoint_from fst snd]; repeat split; lia]| exact LOC1| lia| lia| assumption|].
  rename PC into ST. rename PC0 into LOC1. rename POST into LB3. clear LB2 MU2 WM2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (munch_refl [(q - 240, q); (O, O + 264)]%Z mx) as MU3; pose proof (wmono_refl usegs mx) as WM3 end.
  glueZ LOC1 OSR. glueZ P0 LOC1. rename P0 into OSR.

  lstep. lstep. lstep. lstep.
  replace (Z_to_bv 64 (O + 8 + 16)) with (Z_to_bv 64 (O + 24)) by (f_equal; lia).
  takeZ OSR 3%nat (O + 24) P0. takeZ OSR 1%nat (O + 72) MS2.
  call memset_callZ; [exact MS2| assumption| lia| lia| lia| lia|].
  rename POST into MS2. change (Z.to_nat 48) with 48%nat in MS2. change (0 mod 256) with 0 in MS2.
  retype MS2 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
  glueZ MS2 OSR. glueZ P0 MS2. rename P0 into OSR.

  do 10 lstep. lstep.

  takeZ OSR 1%nat (O + 8) OSV. takeZ OSR 8%nat (O + 72) SBC. takeZ OSR 3%nat (O + 96) REP. takeZ OSR 1%nat (O + 104) HMC. takeZ OSR 2%nat (O + 112) MODE.
  retype_at MODE 0%nat 1%nat [CB 4 mode16].
  call (init_buf_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo O jk8);
    [exact ST| lia| unfold GLOBALS_TOP; lia| exact SBC| exact REP| exact HMC| exact MODE| lia| lia| assumption|].
  rename PC into ST. rename PC0 into SBC. rename PC1 into HMC. rename PC2 into R44. rename POST into RZ23.

  do 5 lstep. lstep. release_frame FR0 ST (q + -64). lstep.
  do 7 lstep. lstep. release_frame FR ST q. lstep.
  glueZ FILL OSRP. glueZ OSR FILL. rename OSR into IOSC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
  assert (LB9 : LOCB m9) by (eapply LOCB_transport; [exact LB3| exact MU3| exact WM3| cbv [disjoint_from fst snd]; repeat split; lia]).
  apply evt_done. unfold oss_ctor_post. do 15 eexists. exists m9.
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact LB9].
  unfold OSSINV, SBINV, PUTCELLS, STRREP, OSNUM, IOSINV, oss0, os_lim, os_k. cbn [os_data os_cap os_blk os_fuel os_w].
  split.
  - split; [| split].
    + split; [exact SBC|]. split; [exists (O + 73); split; [exact HMC| lia]| exists jk8; exact MODE].
    + split; [exact R44|]. split; [eexists; exact RZ23| reflexivity].
    + unfold PJ_CAPMAX, PJ_OUTMAX, IMP_SCAP0, PJ_FUEL. rewrite Z.sub_diag, Z.pow_0_r. repeat split; lia.
  - split; [exact OSV|]. exists jk11, jk21. unfold ios_cellsI, OSS_IOS_VPTR. exact IOSC.
Qed.

End WithCeiling0.
