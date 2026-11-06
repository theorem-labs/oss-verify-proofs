(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import ITree Nodes Decode ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow SysStepF ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg RtCells AProto ABase ABytes AModelFacts F_memset F_apoison F_m2s F_annot F_annot_sg APoisonR_iface F_annot_grow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AKit AKit2 FsKit ShadowTac AU_steptac AU_h_kit AAnnot_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UM_guards.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Stdlib.micromega.Lia.lia ::=
  first [ OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.LiaTuning.zify_prune_relevant; OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.LiaTuning.zify_noeuclid_nosat; Z.euclidean_division_equations_cleanup; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.
Definition bxw (P : Prop) : Prop := P.
Local Ltac box H := lazymatch type of H with ?P => change P with (bxw P) in H end.
Local Tactic Notation "blia" "-" ne_hyp_list(hs) := clear - hs; unfold bxw in *; lia.

Section CANSEC1. Context {rc : runConstT}.
Definition AANNOTW_CORE : Z := 0xb2b7c.
Definition AANNOTW_SHRINK : Z := 0xb2d88.
Definition ANNOTW_STACK : Z := 2736.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sh3_read : forall m A (i : Z), 0 <= i < 3 ->
  rw_cells bsegs m A [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  ov_read_bytes bsegs m (wa (A + i)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m A i Hi H.
  assert (C : i = 0 \/ i = 1 \/ i = 2) by lia.
  destruct C as [->|[->| ->]].
  - rewrite <- (Z.add_0_r A) at 1. rewrite Z.add_0_r. exact (rw_cells_read bsegs m A _ 0%nat (C1 (Z_to_bv 8 0)) H eq_refl).
  - exact (rw_cells_read bsegs m A _ 1%nat (C1 (Z_to_bv 8 0)) H eq_refl).
  - exact (rw_cells_read bsegs m A _ 2%nat (C1 (Z_to_bv 8 0)) H eq_refl).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition annotw_core_post (ra sp gp tp s0 s1 om nm s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (beg cap lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 beg) (Z_to_bv 64 (beg + cap)) om nm a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 AANNOT) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma annotw_core : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (V beg cap e1 lo : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp + 32 <= 2^47 ->
  poison_cells m -> annot_cells m -> rt_got m -> rt_shbase m ->
  a0 = Z_to_bv 64 V ->
  rw_cells bsegs m V [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 e1); C8 (Z_to_bv 64 (beg + cap))] ->
  rw_cells bsegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  V mod 8 = 0 -> ablk V (V + 24) ->
  0 < beg -> 0 <= cap -> beg + cap < 2^64 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG V 24 -> rng RNG (shad V) 3 ->
  evtF bsegs RNG (annotw_core_post ra sp gp tp s0 s1 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc beg cap lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AANNOTW_CORE) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI ST CEIL LO SPH PC AC GOT SHB -> VEC VSH V8 VBLK B0 C0 BC RIMG RSTK RV RVS.
  unfold AANNOTW_CORE in *. pose proof atop_range as ATR.
  pose proof (ablk_lin _ _ VBLK) as (VLO & _ & VHI & _). unfold AIMG_HI in VLO.
  assert (VNS : V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V) by (unfold ablk, AIMG_HI, KLS in VBLK; clear - VBLK; lia).
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SHV : shad V = Z.shiftr V 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  assert (SHV16 : Z.shiftr (V + 16) 3 + 2147450880 = shad V + 2) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
  assert (SHVB : 0x7fff8000 <= shad V /\ shad V + 3 <= 0x10007fff8000) by (rewrite SHV, Z.shiftr_div_pow2 by lia; clear - VLO VHI ATR; Z.div_mod_to_equations; lia).
  pose proof PC as PC'. destruct PC' as (PC1 & PC2 & PC3 & PC4 & PC5 & PC6 & PC7). pose proof AC as AC'. destruct AC' as (AC1 & AC2 & AC3).
  assert (ACC0 : rng RNG (Z.shiftr V 3 + 2147450880) 1) by (rewrite <- SHV; eapply rng_sub'; [exact RVS| lia]).
  assert (ACC2 : rng RNG (Z.shiftr (V + 16) 3 + 2147450880) 1) by (rewrite SHV16; eapply rng_sub'; [exact RVS| lia]).
  box SHV; box SHV16.
  unfold annotw_core_post.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 16%nat ST.
  zstep. zstep.               (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (sh3_read mm (shad V) 0 ltac:(lia) VSH) as HR0; rewrite Z.add_0_r in HR0; unfold bxw in SHV; rewrite SHV in HR0; box SHV;
    pose proof (sh3_read mm (shad V) 2 ltac:(lia) VSH) as HR2; unfold bxw in SHV16; rewrite <- SHV16 in HR2; box SHV16
  end.
  zstep.                      (* [comment removed for export] *)
  zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep. zstep. zstep.        (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K B0 C0 BC; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K B0 C0 BC; ubguard K; lia| clear K]).   (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K B0 C0 BC; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  lazymatch goal with H : stk bsegs _ lo _ |- _ => release_frame FR H (bv_unsigned sp) end.
  finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition annotw_sg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (beg cap old k lo : Z) (full : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - ANNOTW_STACK, bv_unsigned sp); (shad beg + k / 8, shad beg + shlen (rup8 old))] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (shad beg) [CB (Z.to_nat (shlen (rup8 cap))) (sg_out full k old)].

Lemma annotw_shrink_sg : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (V beg cap old k lo : Z) (full : list byte),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ANNOTW_STACK -> bv_unsigned sp + 16 <= 2^47 ->
  poison_cells m -> annot_cells m -> rt_got m -> rt_shbase m ->
  a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 old ->
  rw_cells bsegs m V [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 (beg + k)); C8 (Z_to_bv 64 (beg + cap))] ->
  rw_cells bsegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  V mod 8 = 0 -> ablk V (V + 24) -> (V + 24 <= beg \/ beg + rup8 cap <= V) ->
  beg mod 8 = 0 -> 0 < cap <= 2^40 -> 0 <= k -> k < old -> old <= cap ->
  ablk beg (beg + rup8 cap) -> beg + rup8 cap <= 2^47 ->
  rw_cells bsegs m (shad beg) [CB (Z.to_nat (shlen (rup8 cap))) full] ->
  (cap mod 8 <> 0 -> rdn8 cap < old -> exists sb, nth_error full (Z.to_nat (cap / 8)) = Some sb /\ end_byte_ok cap sb) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad beg) (shlen (rup8 cap)) -> rng RNG V 24 -> rng RNG (shad V) 3 ->
  evtF bsegs RNG (annotw_sg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc beg cap old k lo full m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AANNOTW_SHRINK) fc None m (seg_rom bsegs)).
Proof.
  intros until full. intros MI ST CEIL LO SPH PC AC GOT SHB -> -> VEC VSH V8 VBLK VDJ AL CAP K0 KO OC KH HE FULL HSB RIMG RSTK RSH RV RVS.
  unfold ANNOTW_STACK, AANNOTW_SHRINK in *. pose proof atop_range as ATR.
  pose proof (ablk_lin _ _ VBLK) as (VLO & _ & VHI & _). unfold AIMG_HI in VLO.
  assert (VNS : V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V) by (unfold ablk, AIMG_HI, KLS in VBLK; clear - VBLK; lia).
  pose proof (ablk_lin _ _ KH) as (KH1 & KH2 & KH3 & KH4). unfold AIMG_HI in KH1.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (BNZ : beg <> 0) by (clear - KH1; lia).
  assert (R8B : cap <= rup8 cap <= cap + 7) by (unfold rup8, rdn8; clear - CAP; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  assert (AR : exists G qo gk, shlen (rup8 cap) = G /\ shlen (rup8 old) = qo /\ k / 8 = gk /\ 0 <= gk /\ gk <= qo /\ qo <= G /\ 8 * G <= cap + 7 /\ 0 <= G)
    by (exists (shlen (rup8 cap)), (shlen (rup8 old)), (k / 8); unfold shlen, rup8, rdn8; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8;
        repeat split; clear - CAP K0 KO OC; Z.div_mod_to_equations; lia).
  destruct AR as (G & qo & gk & EG & EQO & EGK & GK0 & GKQ & QOG & GC & G0).
  unfold annotw_sg_post. rewrite EG in FULL, RSH |- *. rewrite EQO, EGK.
  (* [comment removed for export] *)
  assert (SHV : shad V = Z.shiftr V 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  assert (SHV8 : Z.shiftr (V + 8) 3 + 2147450880 = shad V + 1) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
  assert (SHVB : 0x7fff8000 <= shad V /\ shad V + 3 <= 0x10007fff8000) by (rewrite SHV, Z.shiftr_div_pow2 by lia; clear - VLO VHI ATR; Z.div_mod_to_equations; lia).
  assert (SHBB : 0x7fff8000 <= shad beg /\ shad beg + G <= 0x10007fff8000).
  { unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. clear - KH1 KH3 CAP ATR GC G0 R8B. Z.div_mod_to_equations. lia. }
  assert (SHDJ : shad V + 3 <= shad beg \/ shad beg + G <= shad V).
  { rewrite SHV. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. clear - VDJ V8 AL GC G0 R8B CAP. Z.div_mod_to_equations. lia. }
  pose proof PC as PC'. destruct PC' as (PC1 & PC2 & PC3 & PC4 & PC5 & PC6 & PC7). pose proof AC as AC'. destruct AC' as (AC1 & AC2 & AC3).
  assert (ACC0 : rng RNG (Z.shiftr V 3 + 2147450880) 1) by (rewrite <- SHV; eapply rng_sub'; [exact RVS| lia]).
  assert (ACC1 : rng RNG (Z.shiftr (V + 8) 3 + 2147450880) 1) by (rewrite SHV8; eapply rng_sub'; [exact RVS| lia]).
  box SHV; box SHV8.
  pose proof (munch_refl [(bv_unsigned sp - 2736, bv_unsigned sp); (shad beg + gk, shad beg + qo)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 16%nat ST.
  zstep. zstep. zstep.        (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (sh3_read mm (shad V) 0 ltac:(lia) VSH) as HR0; rewrite Z.add_0_r in HR0; unfold bxw in SHV; rewrite SHV in HR0; box SHV;
    pose proof (sh3_read mm (shad V) 1 ltac:(lia) VSH) as HR1; unfold bxw in SHV8; rewrite <- SHV8 in HR1; box SHV8
  end.
  zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K KH1 KH4 R8B CAP OC KO K0; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K KH1 KH4 R8B CAP OC KO K0; ubguard K; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep. zstep.        (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K KH1 KH4 R8B CAP OC KO K0; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K KH1 KH4 R8B CAP OC KO K0; ubguard K; lia| clear K]).   (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  name_sp sp (-16)%Z.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evtF_cut; [ eapply (annotw_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V beg cap (beg + k) lo)
                     | cbv beta; unfold annotw_core_post; post_call bsegs mm ]
  end;
    first [ exact CEIL | reflexivity | (rewrite Hsp; exact ST) | eassumption
          | (unfold poison_cells; repeat lazymatch goal with |- _ /\ _ => split end; assumption)
          | (unfold annot_cells; repeat lazymatch goal with |- _ /\ _ => split end; assumption)
          | (rewrite Hsp; clear - LO SPH; lia)
          | (clear - KH1 KH4 R8B CAP; lia)
          | (rewrite Hsp; solve_rng) | solve_rng | idtac ].
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evtF_cut; [ eapply (annot_sg_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ beg cap old k)
                     | cbv beta; unfold annot_sg_post, ANNOT_STACK; rewrite ?EG, ?EQO, ?EGK; post_call bsegs mm ]
  end;
    first [ exact CEIL | reflexivity | (rewrite Hsp; exact ST) | (rewrite EG; exact FULL) | exact HSB | eassumption
          | (unfold poison_cells; repeat lazymatch goal with |- _ /\ _ => split end; assumption)
          | (unfold annot_cells; repeat lazymatch goal with |- _ /\ _ => split end; assumption)
          | (rewrite Hsp; unfold ANNOT_STACK; clear - LO; lia)
          | (rewrite EG; exact RSH)
          | (f_equal; clear; lia)
          | lia | (rewrite Hsp; solve_rng) | solve_rng | idtac ].
  unname_sp.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  lazymatch goal with H : stk bsegs _ lo _ |- _ => release_frame FR H (bv_unsigned sp) end.
  finish.
Qed.

(* [comment removed for export] *)
Definition annotw_nop_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - ANNOTW_STACK, bv_unsigned sp)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma annotw_shrink_nop : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (V beg cap k lo : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ANNOTW_STACK -> bv_unsigned sp + 16 <= 2^47 ->
  poison_cells m -> annot_cells m -> rt_got m -> rt_shbase m ->
  a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 k ->
  rw_cells bsegs m V [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 (beg + k)); C8 (Z_to_bv 64 (beg + cap))] ->
  rw_cells bsegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  V mod 8 = 0 -> ablk V (V + 24) ->
  0x6d4000 <= beg -> 0 <= cap <= 2^40 -> 0 <= k <= cap -> beg + cap + 8 <= 2^47 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG V 24 -> rng RNG (shad V) 3 ->
  evtF bsegs RNG (annotw_nop_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AANNOTW_SHRINK) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI ST CEIL LO SPH PC AC GOT SHB -> -> VEC VSH V8 VBLK B0 CAP KK HE RIMG RSTK RV RVS.
  unfold ANNOTW_STACK, AANNOTW_SHRINK in *. pose proof atop_range as ATR.
  pose proof (ablk_lin _ _ VBLK) as (VLO & _ & VHI & _). unfold AIMG_HI in VLO.
  assert (VNS : V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V) by (unfold ablk, AIMG_HI, KLS in VBLK; clear - VBLK; lia).
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (BNZ : beg <> 0) by (clear - B0; lia).
  assert (SHV : shad V = Z.shiftr V 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  assert (SHV8 : Z.shiftr (V + 8) 3 + 2147450880 = shad V + 1) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
  assert (SHVB : 0x7fff8000 <= shad V /\ shad V + 3 <= 0x10007fff8000) by (rewrite SHV, Z.shiftr_div_pow2 by lia; clear - VLO VHI ATR; Z.div_mod_to_equations; lia).
  pose proof PC as PC'. destruct PC' as (PC1 & PC2 & PC3 & PC4 & PC5 & PC6 & PC7). pose proof AC as AC'. destruct AC' as (AC1 & AC2 & AC3).
  assert (ACC0 : rng RNG (Z.shiftr V 3 + 2147450880) 1) by (rewrite <- SHV; eapply rng_sub'; [exact RVS| lia]).
  assert (ACC1 : rng RNG (Z.shiftr (V + 8) 3 + 2147450880) 1) by (rewrite SHV8; eapply rng_sub'; [exact RVS| lia]).
  box SHV; box SHV8.
  pose proof (munch_refl [(bv_unsigned sp - 2736, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 16%nat ST.
  zstep. zstep. zstep.        (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (sh3_read mm (shad V) 0 ltac:(lia) VSH) as HR0; rewrite Z.add_0_r in HR0; unfold bxw in SHV; rewrite SHV in HR0; box SHV;
    pose proof (sh3_read mm (shad V) 1 ltac:(lia) VSH) as HR1; unfold bxw in SHV8; rewrite <- SHV8 in HR1; box SHV8
  end.
  zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K B0 CAP KK HE; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K B0 CAP KK HE; ubguard K; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep. zstep.        (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K B0 CAP KK HE; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K B0 CAP KK HE; ubguard K; lia| clear K]).   (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  name_sp sp (-16)%Z.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evtF_cut; [ eapply (annotw_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V beg cap (beg + k) lo)
                     | cbv beta; unfold annotw_core_post; post_call bsegs mm ]
  end;
    first [ exact CEIL | reflexivity | (rewrite Hsp; exact ST) | eassumption
          | (unfold poison_cells; repeat lazymatch goal with |- _ /\ _ => split end; assumption)
          | (unfold annot_cells; repeat lazymatch goal with |- _ /\ _ => split end; assumption)
          | (rewrite Hsp; clear - LO SPH; lia)
          | (clear - B0 CAP KK HE; lia)
          | (rewrite Hsp; solve_rng) | solve_rng | idtac ].
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evtF_cut; [ eapply (annot_nopg_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ beg cap k)
                     | cbv beta; unfold annot_nopg_post, ANNOT_STACK; post_call bsegs mm ]
  end;
    first [ exact CEIL | reflexivity | (rewrite Hsp; exact ST) | eassumption
          | (unfold poison_cells; repeat lazymatch goal with |- _ /\ _ => split end; assumption)
          | (unfold annot_cells; repeat lazymatch goal with |- _ /\ _ => split end; assumption)
          | (rewrite Hsp; unfold ANNOT_STACK; clear - LO; lia)
          | (f_equal; clear; lia)
          | lia | (rewrite Hsp; solve_rng) | solve_rng | idtac ].
  unname_sp.
  zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  lazymatch goal with H : stk bsegs _ lo _ |- _ => release_frame FR H (bv_unsigned sp) end.
  finish.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AANNOTW_DELETE : Z := 0xb2fd4.

Lemma aannotate_grow_any : forall st p ch cap,
  (a_live st) !! p = Some ch -> 0 < cap <= 2^40 -> aannotate st p cap 0 cap = aret st.
Proof.
  intros st p ch cap L HC. rewrite (aannotate_grow_tree st p ch cap L HC). destruct ch; [reflexivity|].
  unfold poison0. destruct (0 <? AsanCtrl.rdn cap 8); reflexivity.
Qed.

Lemma implS_aret_evtF : forall RNG (st : astate) (Q : astate -> footprint -> machine_state -> Prop) ms,
  implS bsegs RNG (aembed ATOP (aret st)) (epostF Q) ms -> evtF bsegs RNG (Q st RNG) ms.
Proof. intros RNG st Q ms H. unfold aret in H. rewrite aembed_ret in H. exact H. Qed.

Definition annotw_grow_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (beg cap lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - ANNOTW_STACK, bv_unsigned sp); (shad beg, shad beg + shlen (rup8 cap))] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (shad beg) [CB (Z.to_nat (cap / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (cap / 8)))]
    /\ (cap mod 8 <> 0 -> rw_cells bsegs m' (shad beg + cap / 8) [C1 (Z_to_bv 8 (cap mod 8))]).

Lemma annotw_delete_grow : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (V beg cap lo : Z) (st : astate) (p : AsanCtrl.aptr) (ch : achunk),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ANNOTW_STACK -> bv_unsigned sp + 16 <= 2^47 ->
  poison_cells m -> annot_cells m -> artcells m -> premap_cells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rt_got m -> rt_shbase m ->
  a0 = Z_to_bv 64 V ->
  rw_cells bsegs m V [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 (beg + cap))] ->
  rw_cells bsegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  V mod 8 = 0 -> ablk V (V + 24) -> (V + 24 <= beg \/ beg + rup8 cap <= V) ->
  ablock_range beg cap -> 0 < cap <= AREQMAX ->
  (a_live st) !! p = Some ch -> chunk_size ch = cap -> (is_primary cap = false -> beg = chunk_user_beg ch) ->
  match ch with CPrim _ _ => is_primary cap = true | CSec _ _ _ => is_primary cap = false end ->
  rw_cells bsegs m (shad beg) [CB (Z.to_nat (shlen (rup8 cap))) (repeat (Z_to_bv 8 252) (Z.to_nat (shlen (rup8 cap))))] ->   (* [comment removed for export] *)
  (exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= beg /\ beg + cap + 64 <= RHI
       /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at bsegs m (shad RLO) (shlen (RHI - RLO))) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad beg) (shlen (rup8 cap)) -> rng RNG V 24 -> rng RNG (shad V) 3 ->
  evtF bsegs RNG (annotw_grow_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc beg cap lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AANNOTW_DELETE) fc None m (seg_rom bsegs)).
Proof.
  intros until ch. intros MI ST CEIL LO SPH PC AC ART PRM RR GOT SHB -> VEC VSH V8 VBLK VDJ BR CAP LIVE CSZ UBEG KIND FULL ARENA RIMG RSTK RSH RV RVS.
  unfold ANNOTW_STACK, AANNOTW_DELETE in *. pose proof atop_range as ATR. unfold AREQMAX in CAP.
  pose proof (ablk_lin _ _ VBLK) as (VLO & _ & VHI & _). unfold AIMG_HI in VLO.
  assert (VNS : V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V) by (unfold ablk, AIMG_HI, KLS in VBLK; clear - VBLK; lia).
  pose proof BR as (BR1 & BR2 & BR3 & BR4). pose proof (ablk_lin _ _ BR1) as (KH1 & KH2 & KH3 & KH4). unfold AIMG_HI in KH1.
  assert (AL : beg mod 8 = 0) by (clear - BR4; Z.div_mod_to_equations; lia).
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (BNZ : beg <> 0) by (clear - KH1; lia).
  assert (R8B : cap <= rup8 cap <= cap + 7) by (unfold rup8, rdn8; clear - CAP; Z.div_mod_to_equations; lia).
  assert (AR : exists G gc, shlen (rup8 cap) = G /\ cap / 8 = gc /\ 0 <= gc /\ gc <= G /\ G <= gc + 1 /\ 8 * G <= cap + 7 /\ 8 * gc <= cap)
    by (exists (shlen (rup8 cap)), (cap / 8); unfold shlen, rup8, rdn8; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8;
        repeat split; clear - CAP; Z.div_mod_to_equations; lia).
  destruct AR as (G & gc & EG & EGC & GC0 & GCG & GGC & GC7 & GC8).
  unfold annotw_grow_post. rewrite EG in RSH, FULL |- *. rewrite EGC.
  assert (SHV : shad V = Z.shiftr V 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  assert (SHV8 : Z.shiftr (V + 8) 3 + 2147450880 = shad V + 1) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
  assert (SHV16 : Z.shiftr (V + 16) 3 + 2147450880 = shad V + 2) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
  assert (SHVB : 0x7fff8000 <= shad V /\ shad V + 3 <= 0x10007fff8000) by (rewrite SHV, Z.shiftr_div_pow2 by lia; clear - VLO VHI ATR; Z.div_mod_to_equations; lia).
  assert (SHBB : 0x7fff8000 <= shad beg /\ shad beg + G <= 0x10007fff8000 /\ shad beg + gc + 1 <= 0x10007fff8000).
  { unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. pose proof (ablk_rup8 _ _ BR1 AL ltac:(lia)) as BRU. pose proof (ablk_lin _ _ BRU) as (_ & _ & U3 & _).
    clear - KH1 U3 CAP ATR GC7 GC8 GCG GGC GC0 R8B. Z.div_mod_to_equations. lia. }
  assert (SHDJ : shad V + 3 <= shad beg \/ shad beg + G <= shad V).
  { rewrite SHV. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. clear - VDJ V8 AL GC7 GC0 GCG R8B CAP. Z.div_mod_to_equations. lia. }
  pose proof PC as PC'. destruct PC' as (PC1 & PC2 & PC3 & PC4 & PC5 & PC6 & PC7). pose proof AC as AC'. destruct AC' as (AC1 & AC2 & AC3).
  assert (ACC0 : rng RNG (Z.shiftr V 3 + 2147450880) 1) by (rewrite <- SHV; eapply rng_sub'; [exact RVS| lia]).
  assert (ACC1 : rng RNG (Z.shiftr (V + 8) 3 + 2147450880) 1) by (rewrite SHV8; eapply rng_sub'; [exact RVS| lia]).
  assert (ACC2 : rng RNG (Z.shiftr (V + 16) 3 + 2147450880) 1) by (rewrite SHV16; eapply rng_sub'; [exact RVS| lia]).
  box SHV; box SHV8; box SHV16.
  pose proof (munch_refl [(bv_unsigned sp - 2736, bv_unsigned sp); (shad beg, shad beg + G)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 16%nat ST.
  zstep. zstep. zstep.        (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (sh3_read mm (shad V) 0 ltac:(lia) VSH) as HR0; rewrite Z.add_0_r in HR0; unfold bxw in SHV; rewrite SHV in HR0; box SHV;
    pose proof (sh3_read mm (shad V) 1 ltac:(lia) VSH) as HR1; unfold bxw in SHV8; rewrite <- SHV8 in HR1; box SHV8;
    pose proof (sh3_read mm (shad V) 2 ltac:(lia) VSH) as HR2; unfold bxw in SHV16; rewrite <- SHV16 in HR2; box SHV16
  end.
  zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep. zstep. zstep.        (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K KH1 KH4 R8B CAP; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K KH1 KH4 R8B CAP; ubguard K; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep. zstep.        (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K KH1 KH4 R8B CAP; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K KH1 KH4 R8B CAP; ubguard K; lia| clear K]).   (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  name_sp sp (-16)%Z.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evtF_cut; [ eapply (annotw_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V beg cap beg lo)
                     | cbv beta; unfold annotw_core_post; post_call bsegs mm ]
  end;
    first [ exact CEIL | reflexivity | (rewrite Hsp; exact ST) | eassumption
          | (unfold poison_cells; repeat lazymatch goal with |- _ /\ _ => split end; assumption)
          | (unfold annot_cells; repeat lazymatch goal with |- _ /\ _ => split end; assumption)
          | (rewrite Hsp; clear - LO SPH; lia)
          | (clear - KH1 KH4 R8B CAP; lia)
          | (rewrite Hsp; solve_rng) | solve_rng | idtac ].
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ ?R _ (MS ?regs ?FF ?pc ?fcc _ ?mm ?ro) =>
    assert (HW : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) [(bv_unsigned sp - 2736, bv_unsigned sp); (shad beg, shad beg + G)])
      by (apply Forall_cons; [cbn; unfold AIMG_HI; clear - CEIL LO ATR; lia| apply Forall_cons; [cbn; unfold AIMG_HI; clear - SHBB; lia| apply Forall_nil]]);
    lazymatch goal with MU' : munch _ m mm, WM' : wmono bsegs m mm |- _ =>
    pose proof (artcells_frame _ _ _ ART MU' WM' HW) as ART1;
    pose proof (premap_cells_frameA _ _ _ PRM MU' WM' HW) as PRM1;
    pose proof (arelro_munchA _ _ _ RR MU' HW) as RR1;
    (let FU := fresh "FU" in
     lazymatch goal with H : rw_cells bsegs mm (shad _) [CB _ (repeat _ _)] |- _ => rename H into FU end;
     rewrite <- EG in FU; destruct (poisoned_chunks mm beg cap ltac:(clear - CAP; lia) FU) as [BODY1 LAST1]; rewrite EG in FU);
    (let RLO := fresh "RLO" in let RHI := fresh "RHI" in
     destruct ARENA as (RLO & RHI & AR1 & AR2 & AR3 & AR4 & AR5 & AR6);
     assert (ARENA1 : exists RLO' RHI', RLO' mod 4096 = 0 /\ RHI' mod 4096 = 0 /\ RLO' + 64 <= beg /\ beg + cap + 64 <= RHI'
               /\ rng R (shad RLO') (shlen (RHI' - RLO')) /\ wr_at bsegs mm (shad RLO') (shlen (RHI' - RLO')))
       by (exists RLO, RHI; repeat (split; [assumption|]); eapply wr_at_transport; [exact AR6| exact WM']));
    eassert (G1 : implS bsegs R (aembed ATOP (aannotate st p cap 0 cap)) _ (MS regs FF pc fcc None mm ro));
    [ eapply (annot_grow_full R) with (lo := lo) (sb := Z_to_bv 8 252) (A := beg) (cap := cap);
      first [ exact CEIL | reflexivity | exact LIVE | exact CSZ | exact UBEG | exact KIND | exact BR | exact ARENA1
            | exact BODY1 | (intros NE; split; [exact (LAST1 NE) | apply end_byte_ok_poisoned; clear - CAP; lia]) | exact ART1 | exact PRM1 | exact RR1 | eassumption
            | (unfold poison_cells; repeat lazymatch goal with |- _ /\ _ => split end; assumption)
            | (unfold annot_cells; repeat lazymatch goal with |- _ /\ _ => split end; assumption)
            | (rewrite Hsp; unfold ANNOT_STACK; clear - LO; lia)
            | (unfold AREQMAX; clear - CAP; lia)
            | (rewrite EG; exact RSH)
            | (f_equal; clear; lia)
            | (rewrite Hsp; solve_rng) | solve_rng ]
    | ]
    end
  end.
  rewrite (aannotate_grow_any st p ch cap LIVE ltac:(clear - CAP; lia)) in G1. apply implS_aret_evtF in G1.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evtF_cut; [ eapply evtF_mono; [exact G1| cbv beta; unfold annot_grow_postF; intros ms1 (_ & _ & PO1); exact PO1]
                     | cbv beta; unfold ANNOT_STACK; rewrite ?EG, ?EGC; clear G1; post_call bsegs mm ]
  end.
  unname_sp.
  zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  lazymatch goal with H : stk bsegs _ lo _ |- _ => release_frame FR H (bv_unsigned sp) end.
  finish.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AANNOTW_INCREASE : Z := 0xb2ce4.

Lemma annotw_increase_grow : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (V beg cap lo : Z) (st : astate) (p : AsanCtrl.aptr) (ch : achunk),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ANNOTW_STACK -> bv_unsigned sp + 16 <= 2^47 ->
  poison_cells m -> annot_cells m -> artcells m -> premap_cells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rt_got m -> rt_shbase m ->
  a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 cap ->
  rw_cells bsegs m V [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 (beg + cap))] ->
  rw_cells bsegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  V mod 8 = 0 -> ablk V (V + 24) -> (V + 24 <= beg \/ beg + rup8 cap <= V) ->
  ablock_range beg cap -> 0 < cap <= AREQMAX ->
  (a_live st) !! p = Some ch -> chunk_size ch = cap -> (is_primary cap = false -> beg = chunk_user_beg ch) ->
  match ch with CPrim _ _ => is_primary cap = true | CSec _ _ _ => is_primary cap = false end ->
  rw_cells bsegs m (shad beg) [CB (Z.to_nat (shlen (rup8 cap))) (repeat (Z_to_bv 8 252) (Z.to_nat (shlen (rup8 cap))))] ->
  (exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= beg /\ beg + cap + 64 <= RHI
       /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at bsegs m (shad RLO) (shlen (RHI - RLO))) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad beg) (shlen (rup8 cap)) -> rng RNG V 24 -> rng RNG (shad V) 3 ->
  evtF bsegs RNG (annotw_grow_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc beg cap lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AANNOTW_INCREASE) fc None m (seg_rom bsegs)).
Proof.
  intros until ch. intros MI ST CEIL LO SPH PC AC ART PRM RR GOT SHB -> -> VEC VSH V8 VBLK VDJ BR CAP LIVE CSZ UBEG KIND FULL ARENA RIMG RSTK RSH RV RVS.
  unfold ANNOTW_STACK, AANNOTW_INCREASE in *. pose proof atop_range as ATR. unfold AREQMAX in CAP.
  pose proof (ablk_lin _ _ VBLK) as (VLO & _ & VHI & _). unfold AIMG_HI in VLO.
  assert (VNS : V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V) by (unfold ablk, AIMG_HI, KLS in VBLK; clear - VBLK; lia).
  pose proof BR as (BR1 & BR2 & BR3 & BR4). pose proof (ablk_lin _ _ BR1) as (KH1 & KH2 & KH3 & KH4). unfold AIMG_HI in KH1.
  assert (AL : beg mod 8 = 0) by (clear - BR4; Z.div_mod_to_equations; lia).
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (BNZ : beg <> 0) by (clear - KH1; lia).
  assert (R8B : cap <= rup8 cap <= cap + 7) by (unfold rup8, rdn8; clear - CAP; Z.div_mod_to_equations; lia).
  assert (AR : exists G gc, shlen (rup8 cap) = G /\ cap / 8 = gc /\ 0 <= gc /\ gc <= G /\ G <= gc + 1 /\ 8 * G <= cap + 7 /\ 8 * gc <= cap)
    by (exists (shlen (rup8 cap)), (cap / 8); unfold shlen, rup8, rdn8; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8;
        repeat split; clear - CAP; Z.div_mod_to_equations; lia).
  destruct AR as (G & gc & EG & EGC & GC0 & GCG & GGC & GC7 & GC8).
  unfold annotw_grow_post. rewrite EG in RSH, FULL |- *. rewrite EGC.
  assert (SHV : shad V = Z.shiftr V 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  assert (SHV8 : Z.shiftr (V + 8) 3 + 2147450880 = shad V + 1) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
  assert (SHVB : 0x7fff8000 <= shad V /\ shad V + 3 <= 0x10007fff8000) by (rewrite SHV, Z.shiftr_div_pow2 by lia; clear - VLO VHI ATR; Z.div_mod_to_equations; lia).
  assert (SHBB : 0x7fff8000 <= shad beg /\ shad beg + G <= 0x10007fff8000 /\ shad beg + gc + 1 <= 0x10007fff8000).
  { unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. pose proof (ablk_rup8 _ _ BR1 AL ltac:(lia)) as BRU. pose proof (ablk_lin _ _ BRU) as (_ & _ & U3 & _).
    clear - KH1 U3 CAP ATR GC7 GC8 GCG GGC GC0 R8B. Z.div_mod_to_equations. lia. }
  assert (SHDJ : shad V + 3 <= shad beg \/ shad beg + G <= shad V).
  { rewrite SHV. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. clear - VDJ V8 AL GC7 GC0 GCG R8B CAP. Z.div_mod_to_equations. lia. }
  pose proof PC as PC'. destruct PC' as (PC1 & PC2 & PC3 & PC4 & PC5 & PC6 & PC7). pose proof AC as AC'. destruct AC' as (AC1 & AC2 & AC3).
  assert (ACC0 : rng RNG (Z.shiftr V 3 + 2147450880) 1) by (rewrite <- SHV; eapply rng_sub'; [exact RVS| lia]).
  assert (ACC1 : rng RNG (Z.shiftr (V + 8) 3 + 2147450880) 1) by (rewrite SHV8; eapply rng_sub'; [exact RVS| lia]).
  box SHV; box SHV8.
  pose proof (munch_refl [(bv_unsigned sp - 2736, bv_unsigned sp); (shad beg, shad beg + G)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 16%nat ST.
  zstep. zstep. zstep.        (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (sh3_read mm (shad V) 0 ltac:(lia) VSH) as HR0; rewrite Z.add_0_r in HR0; unfold bxw in SHV; rewrite SHV in HR0; box SHV;
    pose proof (sh3_read mm (shad V) 1 ltac:(lia) VSH) as HR1; unfold bxw in SHV8; rewrite <- SHV8 in HR1; box SHV8
  end.
  zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep. zstep. zstep.        (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K KH1 KH4 R8B CAP; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K KH1 KH4 R8B CAP; ubguard K; lia| clear K]).   (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K KH1 KH4 R8B CAP; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K KH1 KH4 R8B CAP; ubguard K; lia| clear K]).   (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  name_sp sp (-16)%Z.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evtF_cut; [ eapply (annotw_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V beg cap beg lo)
                     | cbv beta; unfold annotw_core_post; post_call bsegs mm ]
  end;
    first [ exact CEIL | reflexivity | (rewrite Hsp; exact ST) | eassumption
          | (unfold poison_cells; repeat lazymatch goal with |- _ /\ _ => split end; assumption)
          | (unfold annot_cells; repeat lazymatch goal with |- _ /\ _ => split end; assumption)
          | (rewrite Hsp; clear - LO SPH; lia)
          | (clear - KH1 KH4 R8B CAP; lia)
          | (rewrite Hsp; solve_rng) | solve_rng | idtac ].
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ ?R _ (MS ?regs ?FF ?pc ?fcc _ ?mm ?ro) =>
    assert (HW : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) [(bv_unsigned sp - 2736, bv_unsigned sp); (shad beg, shad beg + G)])
      by (apply Forall_cons; [cbn; unfold AIMG_HI; clear - CEIL LO ATR; lia| apply Forall_cons; [cbn; unfold AIMG_HI; clear - SHBB; lia| apply Forall_nil]]);
    lazymatch goal with MU' : munch _ m mm, WM' : wmono bsegs m mm |- _ =>
    pose proof (artcells_frame _ _ _ ART MU' WM' HW) as ART1;
    pose proof (premap_cells_frameA _ _ _ PRM MU' WM' HW) as PRM1;
    pose proof (arelro_munchA _ _ _ RR MU' HW) as RR1;
    (let FU := fresh "FU" in
     lazymatch goal with H : rw_cells bsegs mm (shad _) [CB _ (repeat _ _)] |- _ => rename H into FU end;
     rewrite <- EG in FU; destruct (poisoned_chunks mm beg cap ltac:(clear - CAP; lia) FU) as [BODY1 LAST1]; rewrite EG in FU);
    (let RLO := fresh "RLO" in let RHI := fresh "RHI" in
     destruct ARENA as (RLO & RHI & AR1 & AR2 & AR3 & AR4 & AR5 & AR6);
     assert (ARENA1 : exists RLO' RHI', RLO' mod 4096 = 0 /\ RHI' mod 4096 = 0 /\ RLO' + 64 <= beg /\ beg + cap + 64 <= RHI'
               /\ rng R (shad RLO') (shlen (RHI' - RLO')) /\ wr_at bsegs mm (shad RLO') (shlen (RHI' - RLO')))
       by (exists RLO, RHI; repeat (split; [assumption|]); eapply wr_at_transport; [exact AR6| exact WM']));
    eassert (G1 : implS bsegs R (aembed ATOP (aannotate st p cap 0 cap)) _ (MS regs FF pc fcc None mm ro));
    [ eapply (annot_grow_full R) with (lo := lo) (sb := Z_to_bv 8 252) (A := beg) (cap := cap);
      first [ exact CEIL | reflexivity | exact LIVE | exact CSZ | exact UBEG | exact KIND | exact BR | exact ARENA1
            | exact BODY1 | (intros NE; split; [exact (LAST1 NE) | apply end_byte_ok_poisoned; clear - CAP; lia]) | exact ART1 | exact PRM1 | exact RR1 | eassumption
            | (unfold poison_cells; repeat lazymatch goal with |- _ /\ _ => split end; assumption)
            | (unfold annot_cells; repeat lazymatch goal with |- _ /\ _ => split end; assumption)
            | (rewrite Hsp; unfold ANNOT_STACK; clear - LO; lia)
            | (unfold AREQMAX; clear - CAP; lia)
            | (rewrite EG; exact RSH)
            | (f_equal; clear; lia)
            | (rewrite Hsp; solve_rng) | solve_rng ]
    | ]
    end
  end.
  rewrite (aannotate_grow_any st p ch cap LIVE ltac:(clear - CAP; lia)) in G1. apply implS_aret_evtF in G1.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evtF_cut; [ eapply evtF_mono; [exact G1| cbv beta; unfold annot_grow_postF; intros ms1 (_ & _ & PO1); exact PO1]
                     | cbv beta; unfold ANNOT_STACK; rewrite ?EG, ?EGC; clear G1; post_call bsegs mm ]
  end.
  unname_sp.
  zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  lazymatch goal with H : stk bsegs _ lo _ |- _ => release_frame FR H (bv_unsigned sp) end.
  finish.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AANNOTW_NEW : Z := 0xb2ad8.

Lemma annotw_new_shrink : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (V beg cap e1 lo : Z) (full : list byte),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ANNOTW_STACK -> bv_unsigned sp + 16 <= 2^47 ->
  poison_cells m -> annot_cells m -> rt_got m -> rt_shbase m ->
  a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 0 ->
  rw_cells bsegs m V [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 e1); C8 (Z_to_bv 64 (beg + cap))] ->
  rw_cells bsegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  V mod 8 = 0 -> ablk V (V + 24) -> (V + 24 <= beg \/ beg + rup8 cap <= V) ->
  beg mod 8 = 0 -> 0 < cap <= 2^40 ->
  ablk beg (beg + rup8 cap) -> beg + rup8 cap <= 2^47 ->
  rw_cells bsegs m (shad beg) [CB (Z.to_nat (shlen (rup8 cap))) full] ->
  (cap mod 8 <> 0 -> rdn8 cap < cap -> exists sb, nth_error full (Z.to_nat (cap / 8)) = Some sb /\ end_byte_ok cap sb) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad beg) (shlen (rup8 cap)) -> rng RNG V 24 -> rng RNG (shad V) 3 ->
  evtF bsegs RNG (annotw_sg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc beg cap cap 0 lo full m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AANNOTW_NEW) fc None m (seg_rom bsegs)).
Proof.
  intros until full. intros MI ST CEIL LO SPH PC AC GOT SHB -> -> VEC VSH V8 VBLK VDJ AL CAP KH HE FULL HSB RIMG RSTK RSH RV RVS.
  unfold ANNOTW_STACK, AANNOTW_NEW in *. pose proof atop_range as ATR.
  pose proof (ablk_lin _ _ VBLK) as (VLO & _ & VHI & _). unfold AIMG_HI in VLO.
  assert (VNS : V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V) by (unfold ablk, AIMG_HI, KLS in VBLK; clear - VBLK; lia).
  pose proof (ablk_lin _ _ KH) as (KH1 & KH2 & KH3 & KH4). unfold AIMG_HI in KH1.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (R8B : cap <= rup8 cap <= cap + 7) by (unfold rup8, rdn8; clear - CAP; Z.div_mod_to_equations; lia).
  assert (BNZ : beg <> 0) by (clear - KH1; lia).
  assert (AR : exists G, shlen (rup8 cap) = G /\ 0 / 8 = 0 /\ 0 <= G /\ 8 * G <= cap + 7)
    by (exists (shlen (rup8 cap)); unfold shlen, rup8, rdn8; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8;
        repeat split; clear - CAP; Z.div_mod_to_equations; lia).
  destruct AR as (G & EG & E08 & G0 & GC).
  unfold annotw_sg_post. rewrite EG in FULL, RSH |- *. rewrite E08.
  assert (SHV : shad V = Z.shiftr V 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  assert (SHV16 : Z.shiftr (V + 16) 3 + 2147450880 = shad V + 2) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
  assert (SHVB : 0x7fff8000 <= shad V /\ shad V + 3 <= 0x10007fff8000) by (rewrite SHV, Z.shiftr_div_pow2 by lia; clear - VLO VHI ATR; Z.div_mod_to_equations; lia).
  assert (SHBB : 0x7fff8000 <= shad beg /\ shad beg + G <= 0x10007fff8000).
  { unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. clear - KH1 KH3 CAP ATR GC G0 R8B. Z.div_mod_to_equations. lia. }
  assert (SHDJ : shad V + 3 <= shad beg \/ shad beg + G <= shad V).
  { rewrite SHV. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. clear - VDJ V8 AL GC G0 R8B CAP. Z.div_mod_to_equations. lia. }
  pose proof PC as PC'. destruct PC' as (PC1 & PC2 & PC3 & PC4 & PC5 & PC6 & PC7). pose proof AC as AC'. destruct AC' as (AC1 & AC2 & AC3).
  assert (ACC0 : rng RNG (Z.shiftr V 3 + 2147450880) 1) by (rewrite <- SHV; eapply rng_sub'; [exact RVS| lia]).
  assert (ACC2 : rng RNG (Z.shiftr (V + 16) 3 + 2147450880) 1) by (rewrite SHV16; eapply rng_sub'; [exact RVS| lia]).
  box SHV; box SHV16.
  pose proof (munch_refl [(bv_unsigned sp - 2736, bv_unsigned sp); (shad beg + 0, shad beg + G)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 16%nat ST.
  zstep. zstep. zstep.        (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (sh3_read mm (shad V) 0 ltac:(lia) VSH) as HR0; rewrite Z.add_0_r in HR0; unfold bxw in SHV; rewrite SHV in HR0; box SHV;
    pose proof (sh3_read mm (shad V) 2 ltac:(lia) VSH) as HR2; unfold bxw in SHV16; rewrite <- SHV16 in HR2; box SHV16
  end.
  zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep. zstep. zstep.        (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K KH1 KH4 R8B CAP; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K KH1 KH4 R8B CAP; ubguard K; lia| clear K]).   (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K KH1 KH4 R8B CAP; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K KH1 KH4 R8B CAP; ubguard K; lia| clear K]).   (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  name_sp sp (-16)%Z.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evtF_cut; [ eapply (annotw_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V beg cap e1 lo)
                     | cbv beta; unfold annotw_core_post; post_call bsegs mm ]
  end;
    first [ exact CEIL | reflexivity | (rewrite Hsp; exact ST) | eassumption
          | (unfold poison_cells; repeat lazymatch goal with |- _ /\ _ => split end; assumption)
          | (unfold annot_cells; repeat lazymatch goal with |- _ /\ _ => split end; assumption)
          | (rewrite Hsp; clear - LO SPH; lia)
          | (clear - KH1 KH4 R8B CAP; lia)
          | (rewrite Hsp; solve_rng) | solve_rng | idtac ].
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evtF_cut; [ eapply (annot_sg_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ beg cap cap 0)
                     | cbv beta; unfold annot_sg_post, ANNOT_STACK; rewrite ?EG, ?E08; post_call bsegs mm ]
  end;
    first [ exact CEIL | reflexivity | (rewrite Hsp; exact ST) | (rewrite EG; exact FULL) | exact HSB | eassumption
          | (unfold poison_cells; repeat lazymatch goal with |- _ /\ _ => split end; assumption)
          | (unfold annot_cells; repeat lazymatch goal with |- _ /\ _ => split end; assumption)
          | (rewrite Hsp; unfold ANNOT_STACK; clear - LO; lia)
          | (rewrite EG; exact RSH)
          | (f_equal; clear; lia)
          | lia | (rewrite Hsp; solve_rng) | solve_rng | idtac ].
  unname_sp.
  zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  lazymatch goal with H : stk bsegs _ lo _ |- _ => release_frame FR H (bv_unsigned sp) end.
  finish.
Qed.
End CANSEC1.
