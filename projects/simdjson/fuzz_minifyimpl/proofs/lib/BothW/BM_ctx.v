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
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AKit AKit2 FsKit ShadowTac AU_steptac AU_h_kit AAnnot_iface AM_kitB AM_annotw.
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
Definition bxx (P : Prop) : Prop := P.
Local Ltac box H := lazymatch type of H with ?P => change P with (bxx P) in H end.

Section CANSEC1. Context {rc : runConstT}.
Definition ACTX_DTOR : Z := 0xb2c04.

(* [comment removed for export] *)
Lemma ush_read : forall m ULO UHI a,
  unpoisoned m ULO UHI -> ULO <= a -> a mod 8 = 0 -> a + 8 <= UHI ->
  ov_read_bytes bsegs m (wa (Z.shiftr a 3 + 2147450880)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m ULO UHI a U H1 H2 H3. pose proof U as (U0 & U1 & _).
  pose proof (unpoisoned_full m ULO UHI (a / 8) U ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)) as B.
  replace (Z.shiftr a 3 + 2147450880) with (shad a) by (unfold shad, ASHOFF; lia).
  pose proof (rw_cells_C1_of_byte bsegs m (shad a) (Z_to_bv 8 0)) as C.
  assert (R : rw_cells bsegs m (shad a) [C1 (Z_to_bv 8 0)]).
  { apply C; [rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia| rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia|].
    rewrite shad_div. replace (ASHOFF + a / 8) with (ASHOFF + a / 8) by reflexivity. exact B. }
  pose proof (rw_cells_read bsegs m (shad a) [C1 (Z_to_bv 8 0)] 0 (C1 (Z_to_bv 8 0)) R eq_refl) as RD. rewrite Z.add_0_r in RD. exact RD.
Qed.

Definition ctx_dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (T V e lo : Z) (b0 b2 : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (V + 8, V + 16)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' T [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 e); C8 (Z_to_bv 64 e)]
    /\ rw_cells bsegs m' V [C8 b0; C8 (Z_to_bv 64 e); C8 b2]
    /\ rw_cells bsegs m' (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

(* [comment removed for export] *)
Lemma ctx_dtor_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (T V e lo ULO UHI : Z) (b0 b1 b2 : word),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= T -> T + 24 <= 2^47 -> T mod 8 = 0 ->
  poison_cells m -> annot_cells m -> rt_got m -> rt_shbase m ->
  a0 = Z_to_bv 64 T ->
  rw_cells bsegs m T [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 e); C8 (Z_to_bv 64 e)] ->
  unpoisoned m ULO UHI -> ULO <= T -> T + 24 <= UHI -> UHI <= 2^47 ->
  rw_cells bsegs m V [C8 b0; C8 b1; C8 b2] ->
  rw_cells bsegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  V mod 8 = 0 -> ablk V (V + 24) -> 0 <= e < 2^64 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG T 24 -> rng RNG (shad T) 3 -> rng RNG V 24 -> rng RNG (shad V) 3 ->
  evtF bsegs RNG (ctx_dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T V e lo b0 b2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ACTX_DTOR) fc None m (seg_rom bsegs)).
Proof.
  intros until b2. intros MI ST CEIL LO HT TH T8 PC AC GOT SHB -> TX USH U1 U2 U3 VEC VSH V8 VBLK HE RIMG RSTK RT RTS RV RVS.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold ACTX_DTOR in *. pose proof atop_range as ATR.
  pose proof (ablk_lin _ _ VBLK) as (VLO & _ & VHI & _). unfold AIMG_HI in VLO.
  assert (VNS : V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V) by (unfold ablk, AIMG_HI, KLS in VBLK; clear - VBLK; lia).
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SHV : shad V = Z.shiftr V 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  assert (SHV8 : Z.shiftr (V + 8) 3 + 2147450880 = shad V + 1) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
  assert (SHVB : 0x7fff8000 <= shad V /\ shad V + 3 <= 0x10007fff8000) by (rewrite SHV, Z.shiftr_div_pow2 by lia; clear - VLO VHI ATR; Z.div_mod_to_equations; lia).
  assert (SHT : shad T = Z.shiftr T 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  assert (SHT8 : Z.shiftr (T + 8) 3 + 2147450880 = shad T + 1) by (rewrite SHT, !Z.shiftr_div_pow2 by lia; clear - T8; Z.div_mod_to_equations; lia).
  assert (SHT16 : Z.shiftr (T + 16) 3 + 2147450880 = shad T + 2) by (rewrite SHT, !Z.shiftr_div_pow2 by lia; clear - T8; Z.div_mod_to_equations; lia).
  pose proof PC as PC'. destruct PC' as (PC1 & PC2 & PC3 & PC4 & PC5 & PC6 & PC7). pose proof AC as AC'. destruct AC' as (AC1 & AC2 & AC3).
  assert (ACC1 : rng RNG (Z.shiftr (V + 8) 3 + 2147450880) 1) by (rewrite SHV8; eapply rng_sub'; [exact RVS| lia]).
  assert (ACT0 : rng RNG (Z.shiftr T 3 + 2147450880) 1) by (rewrite <- SHT; eapply rng_sub'; [exact RTS| lia]).
  assert (ACT1 : rng RNG (Z.shiftr (T + 8) 3 + 2147450880) 1) by (rewrite SHT8; eapply rng_sub'; [exact RTS| lia]).
  assert (ACT2 : rng RNG (Z.shiftr (T + 16) 3 + 2147450880) 1) by (rewrite SHT16; eapply rng_sub'; [exact RTS| lia]).
  box SHV; box SHV8; box SHT; box SHT8; box SHT16.
  unfold ctx_dtor_post.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (V + 8, V + 16)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 16%nat ST.
  zstep. zstep.               (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (USHX : forall mm, munch [(bv_unsigned sp - 16, bv_unsigned sp); (V + 8, V + 16)] m mm -> unpoisoned mm ULO UHI).
  { intros mm MUx. eapply unpoisoned_munch; [exact USH| exact MUx|]. cbn [disjoint_from]. pose proof USH as X; unfold unpoisoned in X; destruct X as (X0 & X1 & _).
    rewrite !shad_div. unfold ASHOFF. clear - X0 X1 U1 U2 U3 TH VNS VLO CEIL LO ATR HT RSP. Z.div_mod_to_equations. lia. }
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MUx : munch _ m mm |- _ =>
    pose proof (ush_read mm ULO UHI T (USHX mm MUx) ltac:(lia) T8 ltac:(lia)) as HT0;
    pose proof (ush_read mm ULO UHI (T + 8) (USHX mm MUx) ltac:(lia) ltac:(clear - T8; Z.div_mod_to_equations; lia) ltac:(lia)) as HT1
    end;
    pose proof (sh3_read mm (shad V) 1 ltac:(lia) VSH) as HR1; unfold bxx in SHV8; rewrite <- SHV8 in HR1; box SHV8
  end.
  zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K V8 VLO VHI ATR; ubalign K; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep. zstep.        (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MUx : munch _ m mm |- _ =>
    pose proof (ush_read mm ULO UHI (T + 16) (USHX mm MUx) ltac:(lia) ltac:(clear - T8; Z.div_mod_to_equations; lia) ltac:(lia)) as HT2 end end.
  zstep. zstep.               (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; clear - K HE; lia]).   (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  lazymatch goal with H : stk bsegs _ lo _ |- _ => release_frame FR H (bv_unsigned sp) end.
  zstep.                      (* [comment removed for export] *)
  finish.
Qed.
End CANSEC1.
