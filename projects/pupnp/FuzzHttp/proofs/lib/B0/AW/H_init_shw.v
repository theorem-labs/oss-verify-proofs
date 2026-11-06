(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import AWUb2 HttpRepA AWKit AWAuto AWRng.
Import ListNotations.
Open Scope Z_scope.

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.

Definition FreeListInit_post_S (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (FL esz mx lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(FL, FL + 24); (lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' FL [C8 (wz 0); C8 (wz esz); C4 (wz mx); C4 (wz 0)]
    /\ stk asegs m' lo q /\ asan_env asegs m'.

#[using="Type"] Lemma FreeListInit_shw : forall (FL esz mx lo : Z) (junk : list byte)
    (q : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells asegs m FL [CB 24%nat junk] -> 0 <= esz < 2^64 -> 0 <= mx < 2^31 ->
  asan_env asegs m -> 0x609000 <= FL -> FL + 24 <= alloc_ceiling -> FL mod 8 = 0 -> shw m FL 24 ->
  stk asegs m lo q -> alloc_ceiling <= lo -> q < 2^64 -> lo <= q - 16 ->
  mem_inv asegs m -> a0 = wz FL -> a1 = wz esz -> a2 = wz mx ->
  evt asegs (FreeListInit_post_S ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FL esz mx lo m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz FreeListInit_entryA) fc None m (seg_rom asegs)).
Proof.
  intros FL esz mx lo junk q ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros FC E1 E2 AE0 FLO FHI AL SHWF ST CLO QHI LO MI -> -> ->. unfold FreeListInit_entryA.
  a0_prologue AE0 [(FL, FL + 24); (lo, q)]%Z m.
  carve_frame 16%nat ST.
  walk_ub_to 0x8c32c%Z.
  step. release_to q. step. step.
  env_now AE0 MU WM.
  unfold FreeListInit_post_S. finish.
Qed.

Definition ListInit_post_S (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L fcmp ffree lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(L, L + 96); (lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' L (llist_cells (L + 24) L 0 0 0 ffree fcmp)
    /\ stk asegs m' lo q /\ asan_env asegs m'.

#[using="Type"] Lemma ListInit_shw : forall (L fcmp ffree lo : Z) (junk : list byte)
    (q : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells asegs m L [CB 96%nat junk] -> 0 <= fcmp < 2^64 -> 0 <= ffree < 2^64 ->
  asan_env asegs m -> 0x609000 <= L -> L + 96 <= alloc_ceiling -> L mod 8 = 0 -> shw m L 96 ->
  stk asegs m lo q -> alloc_ceiling <= lo -> q < 2^64 -> lo <= q - 48 ->
  mem_inv asegs m -> a0 = wz L -> a1 = wz fcmp -> a2 = wz ffree ->
  evt asegs (ListInit_post_S ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L fcmp ffree lo m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ListInit_entryA) fc None m (seg_rom asegs)).
Proof.
  intros L fcmp ffree lo junk q ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros LC R1 R2 AE0 LLO LHI AL SHWL ST CLO QHI LO MI -> -> ->. unfold ListInit_entryA.
  a0_prologue AE0 [(L, L + 96); (lo, q)]%Z m.
  carve_frame 32%nat ST.
  walk_ub_to 0x8baf8%Z. step.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (rw_cells_take3 asegs mm L [CB 48 (firstn 48 junk); C8 (Z_to_bv 64 0)] [CB 24 (firstn 24 (firstn 32 (skipn 56 junk)))]
                [C8 (Z_to_bv 64 ffree); C8 (Z_to_bv 64 fcmp)] LC) as (LC1 & LC2 & LC3); clear LC;
    cbn [cells_size csize Nat.add] in LC2, LC3;
    replace (L + Z.of_nat 56)%Z with (L + 56)%Z in LC2 by lia;
    replace (L + Z.of_nat 56 + Z.of_nat 24)%Z with (L + 80)%Z in LC3 by lia;
    pose proof (shw_frame _ m mm L 96 SHWL MU ltac:(app_ivs_tac)) as SHWLn
  end.
  env_now AE0 MU WM.
  call (FreeListInit_shw (L + 56)%Z 24%Z 100%Z lo).
  all: side (try (first [ eassumption | reflexivity | (eapply shw_sub; [exact SHWLn| lia| lia| lia]) | (clear - AL; Z.div_mod_to_equations; lia) | lia ])).
  clear SHWLn.

  walk_ub_to 0x8bb88%Z.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with P1 : rw_cells asegs mm L _, P2 : rw_cells asegs mm (L + 56)%Z _, P3 : rw_cells asegs mm (L + 80)%Z _ |- _ =>
      pose proof (rw_cells_put3 asegs _ L _ _ _ P1 ltac:(cbn [cells_size csize Nat.add]; replace (L + Z.of_nat 56)%Z with (L + 56)%Z by lia; exact P2)
                ltac:(cbn [cells_size csize Nat.add]; replace (L + Z.of_nat 56 + Z.of_nat 24)%Z with (L + 80)%Z by lia; exact P3)) as LCF;
      cbn [app] in LCF; clear P1 P2 P3 end end.
  walk_ub_to 0x8bb94%Z. release_to q. step. step.
  env_now AE0 MU WM.
  unfold ListInit_post_S, llist_cells, LISTNODE_SIZEOF, FREELISTSIZE. finish.
Qed.

Definition membuffer_init_post_S (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (MB lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(MB, MB + 32); (lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' MB (mbuf_cells 0 0 0)
    /\ stk asegs m' lo q /\ asan_env asegs m'.

#[using="Type"] Lemma membuffer_init_shw : forall (MB lo : Z) (junk : list byte)
    (q : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells asegs m MB [CB 32%nat junk] -> 0x609000 <= MB -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 -> shw m MB 32 ->
  asan_env asegs m -> stk asegs m lo q -> alloc_ceiling <= lo -> q < 2^64 -> lo <= q - 16 - A0_RT_STACK ->
  mem_inv asegs m -> a0 = wz MB ->
  evt asegs (membuffer_init_post_S ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc MB lo m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x8c8bc) fc None m (seg_rom asegs)).
Proof.
  intros MB lo junk q ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros BLK MBLO MBHI AL SHW AE0 ST CLO QHI LO MI ->. unfold A0_RT_STACK in LO.
  a0_prologue AE0 [(MB, MB + 32); (lo, q)]%Z m.
  carve_frame 16%nat ST.

  apply (rw_cells_split_CB asegs _ MB [] 32%nat junk [] [8%nat; 8%nat; 8%nat; 8%nat]) in BLK; [| cbn; lia]. cbn [app mk_CB_cells] in BLK.
  walk_ub_to 0x8c93c%Z.
  step. env_now AE0 MU WM. release_to q. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with J0 : rw_cells asegs mm MB _ |- _ => pose proof J0 as J; clear J0 end end.
  reshape J (mbuf_cells 0 0 0).
  unfold membuffer_init_post_S. finish.
Qed.

End W.
