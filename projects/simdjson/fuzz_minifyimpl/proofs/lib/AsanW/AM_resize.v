(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow SysStepF ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells AProto ABase ABytes ARep AModelFacts F_memset F_apoison F_m2s F_annot F_annot_sg APoisonR_iface F_annot_grow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AKit AKit2 FsKit ShadowTac AU_steptac AU_h_kit AAnnot_iface AM_kitB AM_annotw.
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
Definition bxr (P : Prop) : Prop := P.
Local Ltac box H := lazymatch type of H with ?P => change P with (bxr P) in H end.

Section CANSEC1. Context {rc : runConstT}.
Definition AVRESIZE : Z := 0xb24c4.
Definition AVRESIZE_STACK : Z := ANNOTW_STACK.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition aresize_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (V beg n k lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - ANNOTW_STACK, bv_unsigned sp); (V + 8, V + 16); (shad beg + k / 8, shad beg + shlen (rup8 n))] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' V [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 (beg + k)); C8 (Z_to_bv 64 (beg + n))]
    /\ rw_cells asegs m' (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' (shad beg) [CB (Z.to_nat (shlen (rup8 n))) (vpat n k)].

Lemma aresize_lt : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (V beg n k lo : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ANNOTW_STACK -> bv_unsigned sp + 16 <= 2^47 ->
  poison_cells m -> annot_cells m -> rt_got m -> rt_shbase m ->
  a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 k ->
  rw_cells asegs m V [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 (beg + n)); C8 (Z_to_bv 64 (beg + n))] ->
  rw_cells asegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  V mod 8 = 0 -> ablk V (V + 24) -> (V + 24 <= beg \/ beg + rup8 n <= V) ->
  beg mod 8 = 0 -> 0 <= k -> k < n -> n <= 2^40 ->
  ablk beg (beg + rup8 n) -> beg + rup8 n <= 2^47 ->
  rw_cells asegs m (shad beg) [CB (Z.to_nat (shlen (rup8 n))) (block_shadow_bytes n)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad beg) (shlen (rup8 n)) -> rng RNG V 24 -> rng RNG (shad V) 3 ->
  evtF asegs RNG (aresize_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc V beg n k lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AVRESIZE) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI ST CEIL LO SPH PC AC GOT SHB -> -> VEC VSH V8 VBLK VDJ AL K0 KN NH KH HE FULL RIMG RSTK RSH RV RVS.
  unfold AVRESIZE. pose proof atop_range as ATR. pose proof LO as LO'. unfold ANNOTW_STACK in LO'.
  pose proof (ablk_lin _ _ VBLK) as (VLO & _ & VHI & _). unfold AIMG_HI in VLO.
  assert (VNS : V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V) by (unfold ablk, AIMG_HI, KLS in VBLK; clear - VBLK; lia).
  pose proof (ablk_lin _ _ KH) as (KH1 & KH2 & KH3 & KH4). unfold AIMG_HI in KH1.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (R8B : n <= rup8 n <= n + 7) by (unfold rup8, rdn8; clear - KN K0; Z.div_mod_to_equations; lia).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  (* [comment removed for export] *)
  assert (AR : exists G gk, shlen (rup8 n) = G /\ k / 8 = gk /\ 0 <= gk /\ gk <= G /\ 8 * G <= n + 7 /\ 0 <= G)
    by (exists (shlen (rup8 n)), (k / 8); unfold shlen, rup8, rdn8; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8;
        repeat split; clear - KN K0 NH; Z.div_mod_to_equations; lia).
  destruct AR as (G & gk & EG & EGK & GK0 & GKG & GC & G0).
  unfold aresize_post. rewrite EG in FULL, RSH |- *. rewrite EGK.
  (* [comment removed for export] *)
  assert (SHV : shad V = Z.shiftr V 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  assert (SHV8 : Z.shiftr (V + 8) 3 + 2147450880 = shad V + 1) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
  assert (SHVB : 0x7fff8000 <= shad V /\ shad V + 3 <= 0x10007fff8000) by (rewrite SHV, Z.shiftr_div_pow2 by lia; clear - VLO VHI ATR; Z.div_mod_to_equations; lia).
  assert (SHBB : 0x7fff8000 <= shad beg /\ shad beg + G <= 0x10007fff8000).
  { unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. clear - KH1 KH3 NH KN K0 ATR GC G0 R8B. Z.div_mod_to_equations. lia. }
  assert (SHDJ : shad V + 3 <= shad beg \/ shad beg + G <= shad V).
  { rewrite SHV. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. clear - VDJ V8 AL GC G0 R8B KN K0. Z.div_mod_to_equations. lia. }
  assert (ACC0 : rng RNG (Z.shiftr V 3 + 2147450880) 1) by (rewrite <- SHV; eapply rng_sub'; [exact RVS| lia]).
  assert (ACC1 : rng RNG (Z.shiftr (V + 8) 3 + 2147450880) 1) by (rewrite SHV8; eapply rng_sub'; [exact RVS| lia]).
  box SHV; box SHV8.
  pose proof (munch_refl [(bv_unsigned sp - 2736, bv_unsigned sp); (V + 8, V + 16); (shad beg + gk, shad beg + G)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  zstep. zstep.               (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with VSHx : rw_cells asegs mm (shad V) _ |- _ =>
    pose proof (sh3_read mm (shad V) 0 ltac:(lia) VSHx) as HR0; rewrite Z.add_0_r in HR0; unfold bxr in SHV; rewrite SHV in HR0; box SHV;
    pose proof (sh3_read mm (shad V) 1 ltac:(lia) VSHx) as HR1; unfold bxr in SHV8; rewrite <- SHV8 in HR1; box SHV8 end
  end.
  zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep. zstep. zstep.        (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep. zstep. zstep.        (* [comment removed for export] *)
  try replace (beg + n - beg) with n by lia.
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; clear - K KN K0 NH; lia]).   (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K KN K0 NH; lia| clear K]).   (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  zstep. zstep. zstep.        (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo _ |- _ => release_frame FR H (bv_unsigned sp) end.
  zstep.                      (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with VECx : rw_cells asegs mm V _, VSHx : rw_cells asegs mm (shad V) _, FULLx : rw_cells asegs mm (shad beg) _, STx : stk asegs mm lo _ |- _ =>
    eapply evtF_cut;
    [ eapply (annotw_shrink_sg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V beg n n k lo (block_shadow_bytes n));
      first [ exact CEIL | exact LO | exact SPH | exact GOT | exact SHB | exact STx | exact VECx | exact VSHx | exact V8 | exact VBLK | exact VDJ | exact AL | exact K0 | exact KN
            | exact KH | exact HE | exact RIMG | exact RSTK | exact RV | exact RVS | reflexivity | eassumption
            | (rewrite EG; exact FULLx) | (apply bsb_hsb; clear - KN K0; lia) | (rewrite EG; exact RSH)
            | (eapply poison_cells_frame; [exact PC| eassumption| eassumption| repeat constructor; cbn; unfold AIMG_HI; clear - SHBB LO' CEIL ATR VLO RSP GK0; lia])
            | (eapply annot_cells_frame; [exact AC| eassumption| eassumption| repeat constructor; cbn; unfold AIMG_HI; clear - SHBB LO' CEIL ATR VLO RSP GK0; lia])
            | (clear - KN K0 NH; lia) | lia ]
    | cbv beta; unfold annotw_sg_post, ANNOTW_STACK; rewrite ?EG, ?EGK; rewrite ?unsigned_lit by lia; post_call asegs mm ]
    end end.
  (* [comment removed for export] *)
  lazymatch goal with OUT : rw_cells asegs _ (shad beg) [CB _ (sg_out _ _ _)] |- _ => rewrite sg_out_tight in OUT by lia end.
  apply evtF_done.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
    lazymatch goal with MUx : munch _ m mm, WMx : wmono asegs m mm, MIx : mem_inv asegs mm, STx : stk asegs mm lo _,
                        VECx : rw_cells asegs mm V _, VSHx : rw_cells asegs mm (shad V) _, OUTx : rw_cells asegs mm (shad beg) _ |- _ =>
    do 15 eexists; exists mm; split; [reflexivity|];
    split; [exact MUx|]; split; [exact WMx|]; split; [exact MIx|]; split; [exact STx|]; split; [exact VECx|]; split; [exact VSHx| exact OUTx]
    end end.
Qed.

(* [comment removed for export] *)
Definition aresize_nop_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma aresize_eq : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (V beg n lo : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp + 16 <= 2^47 ->
  rt_got m -> rt_shbase m ->
  a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 n ->
  rw_cells asegs m V [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 (beg + n)); C8 (Z_to_bv 64 (beg + n))] ->
  rw_cells asegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  V mod 8 = 0 -> ablk V (V + 24) -> 0 <= n -> n <= 2^40 -> ablk beg (beg + rup8 n) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG V 24 -> rng RNG (shad V) 3 ->
  evtF asegs RNG (aresize_nop_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AVRESIZE) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI ST CEIL LO SPH GOT SHB -> -> VEC VSH V8 VBLK N0 NH KH RIMG RSTK RV RVS.
  unfold AVRESIZE. pose proof atop_range as ATR.
  assert (R8B : n <= rup8 n <= n + 7) by (unfold rup8, rdn8; clear - N0 NH; Z.div_mod_to_equations; lia).
  pose proof (ablk_lin _ _ KH) as (KH1 & KH2 & KH3 & KH4). unfold AIMG_HI in KH1.
  pose proof (ablk_lin _ _ VBLK) as (VLO & _ & VHI & _). unfold AIMG_HI in VLO.
  assert (VNS : V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V) by (unfold ablk, AIMG_HI, KLS in VBLK; clear - VBLK; lia).
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (SHV : shad V = Z.shiftr V 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  assert (SHV8 : Z.shiftr (V + 8) 3 + 2147450880 = shad V + 1) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
  assert (SHVB : 0x7fff8000 <= shad V /\ shad V + 3 <= 0x10007fff8000) by (rewrite SHV, Z.shiftr_div_pow2 by lia; clear - VLO VHI ATR; Z.div_mod_to_equations; lia).
  assert (ACC0 : rng RNG (Z.shiftr V 3 + 2147450880) 1) by (rewrite <- SHV; eapply rng_sub'; [exact RVS| lia]).
  assert (ACC1 : rng RNG (Z.shiftr (V + 8) 3 + 2147450880) 1) by (rewrite SHV8; eapply rng_sub'; [exact RVS| lia]).
  box SHV; box SHV8.
  unfold aresize_nop_post.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  zstep. zstep.               (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with VSHx : rw_cells asegs mm (shad V) _ |- _ =>
    pose proof (sh3_read mm (shad V) 0 ltac:(lia) VSHx) as HR0; rewrite Z.add_0_r in HR0; unfold bxr in SHV; rewrite SHV in HR0; box SHV;
    pose proof (sh3_read mm (shad V) 1 ltac:(lia) VSHx) as HR1; unfold bxr in SHV8; rewrite <- SHV8 in HR1; box SHV8 end
  end.
  zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep. zstep. zstep.        (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep. zstep. zstep.        (* [comment removed for export] *)
  try replace (beg + n - beg) with n by lia.
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; clear - K N0 NH; lia]).   (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; clear - K N0 NH; lia]).   (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo _ |- _ => release_frame FR H (bv_unsigned sp) end.
  zstep.                      (* [comment removed for export] *)
  finish.
Qed.
End CANSEC1.
