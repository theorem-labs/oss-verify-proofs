(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import DrvAgree F_fmt_fp_lib.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import BImg RtCells ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import AU_kit AU_iface AU_consts AU_client_kit AU_steptac AU_ubsan_tac AU_fuzz_A.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import ShadowTac.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

Ltac zland K := try (change 18446744073709551615 with (2^64-1) in K; rewrite ?zb_land_mask in K by lia; rewrite ?Z.mod_small in K by lia).
Ltac bcase K := if_cases K; zify_cond K; zland K.


Section CANSEC1. Context {rc : runConstT}.
Definition bx (P : Prop) : Prop := P.
Section S.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (D SZ : Z) (lo : Z) (SPA : Z).
  Notation SP := (bv_unsigned sp).
  Hypothesis LOS : lo <= SP - AHARNESS_STACK.
  Hypothesis LOC : ATOP <= lo.
  Hypothesis SPT : SP + 16 <= 2^47.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis ESPA : SPA = SP - 192 - (SP - 192) mod 32.
  Hypothesis HD : 0 <= D /\ D + SZ <= ATOP.
  Hypothesis HSZ : 0 <= SZ < 2^26.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.

  (* [comment removed for export] *)
  Lemma f_load : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x28 x29 x30 x31 : word) m (F V : Z) (l32 l64 : list byte) (c1 c2 c3 c4 : word) (c5 : word),
    mem_inv bsegs m ->
    rw_cells bsegs m (SPA + 32) [CB 8 l32] ->
    rw_cells bsegs m (SPA + 56) [C8 (Z_to_bv 64 SZ); CB 8 l64; C8 (Z_to_bv 64 F)] ->
    rw_cells bsegs m AVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8)); C8 (Z_to_bv 64 (V + 8))] ->
    rw_cells bsegs m V [C8 (Z_to_bv 64 AFALLBACK)] ->
    rw_cells bsegs m AFALLBACK [C8 (Z_to_bv 64 AFALLBACK_VT); C8 c1; C8 c2; C8 c3; C8 c4; C4 c5] ->
    client_img m -> client_sh m ->
    unpoisoned m V (V + 8) -> V mod 8 = 0 -> ablk V (V + 8) ->
    rng RNG V 8 -> rng RNG (shad V) 1 ->
    evtF bsegs RNG (fun ms' => exists m' y14,
        ms' = MS (mkR (Z_to_bv 64 0xb14bc) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 AFALLBACK) (Z_to_bv 64 D) (Z_to_bv 64 SZ) (Z_to_bv 64 AVU8_FN) y14 x15 x16 x17
                     x18 (Z_to_bv 64 D) (Z_to_bv 64 F) (Z_to_bv 64 (V + 8)) x22 (Z_to_bv 64 V) x24 (Z_to_bv 64 ASHOFF) (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) x28 x29 x30 x31)
                 FR (Z_to_bv 64 AVU8_FN) fc None m' (seg_rom bsegs)
        /\ munch [(SPA + 32, SPA + 40)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SPA + 32) [C8 (Z_to_bv 64 AVEC)])
      (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 D) (Z_to_bv 64 F) x21 x22 x23 x24 (Z_to_bv 64 ASHOFF) (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0xb143c) fc None m (seg_rom bsegs)).
  Proof.
    intros until c5. intros MI FRA LSZ VEC VB SGL (_ & _ & VT) CSH UNV V8 VH RV RSV.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof (spa_props sp SPA SP16 ESPA) as (SPAB & SPA32 & ESPA').
    pose proof (ablk_lin _ _ VH) as (VH1 & VH2 & VH3 & VH4). unfold AIMG_HI in VH1. band_ind VH bVH. unfold AHARNESS_STACK, AVEC, AFALLBACK, AFALLBACK_VT, AVTAB_VU8, AVU8_FN in *.
    pose proof (munch_refl [(SPA + 32, SPA + 40)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (RLOC : rng RNG (SPA + 32) 48) by (eapply rng_sub'; [exact RSTK| lia]).
    (* [comment removed for export] *)
    assert (RD1 : ov_read_bytes bsegs m (wa (Z.shiftr V 3 + ASHOFF)) 1 = Some [Z_to_bv 8 0]).
    { replace (Z.shiftr V 3 + ASHOFF) with (shad V) by (unfold shad; lia).
      apply (unpoisoned_full_rd bsegs m V (V + 8)); [exact UNV| lia|]. rewrite shad_div. Z.div_mod_to_equations. lia. }
    assert (RD2 : ov_read_bytes bsegs m (wa (875292 + ASHOFF)) 1 = Some [Z_to_bv 8 0]).
    { change (875292 + ASHOFF) with (shad 0x6ad8e0). apply ov_read1_of_byte; [vm_compute; discriminate| vm_compute; discriminate|]. apply CSH. unfold client_sh_addrs. cbn. tauto. }
    assert (RD3 : ov_read_bytes bsegs m (wa (186475 + ASHOFF)) 1 = Some [Z_to_bv 8 0]).
    { change (186475 + ASHOFF) with (shad 0x16c358). apply ov_read1_of_byte; [vm_compute; discriminate| vm_compute; discriminate|]. apply CSH. unfold client_sh_addrs. cbn. tauto. }
    replace (shad V) with (Z.shiftr V 3 + ASHOFF) in RSV by (unfold shad; lia).
    assert (RS2 : rng RNG (875292 + ASHOFF) 1) by (eapply rng_sub'; [exact RISH| unfold ASHOFF; lia]).
    assert (RS3 : rng RNG (186475 + ASHOFF) 1) by (eapply rng_sub'; [exact RISH| unfold ASHOFF; lia]).
    usteps_to 0xb7cc4.
    apply evtF_done. eexists _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact FRA].
  Qed.

  (* [comment removed for export] *)
  Lemma f_epi : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x24 x28 x29 x30 x31 : word) m (F V FLG : Z) (h1 h2 : word) csA shc,
    rw_cells bsegs m (shad F) shc -> cells_size shc = 16%nat -> (forall c, In c shc -> exists v, c = C1 v) ->
    rw_cells bsegs m F [C8 (Z_to_bv 64 0x41b58ab3); C8 h1; C8 h2] ->
    rw_cells bsegs m (F + 120) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m (SP + -104) (FZRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) -> rw_cells bsegs m (SPA + 32) csA -> cells_size csA = 48%nat ->
    stk bsegs m lo (SPA + 32) -> stk bsegs m (SPA + 80) (SP + -104) -> mem_inv bsegs m ->
    ablk F (F + 128) -> F + 128 <= ATOP -> F mod 128 = 0 -> ablk FLG (FLG + 1) -> FLG + 1 <= ATOP -> (FLG + 1 <= F \/ F + 128 <= FLG) ->
    ablk V (V + 8) ->
    rng RNG F 128 -> rng RNG (shad F) 16 -> rng RNG FLG 1 ->
    evtF bsegs RNG (fun ms' => exists mp m' y11 y12,
        ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 0) y11 y12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                 FR (ret_pc ra) fc None m' (seg_rom bsegs)
        /\ munch [(shad F, shad F + 16); (F, F + 8)] m mp /\ wmono bsegs m mp /\ mem_inv bsegs mp
        /\ munch [(FLG, FLG + 1)] mp m' /\ wmono bsegs mp m' /\ mem_inv bsegs m'
        /\ stk bsegs m' lo SP /\ rw_cells bsegs m' FLG [C1 (Z_to_bv 8 0)])
      (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 D) (Z_to_bv 64 F) (Z_to_bv 64 (V + 8)) x22 (Z_to_bv 64 V) x24 (Z_to_bv 64 ASHOFF) (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0xb14bc) fc None m (seg_rom bsegs)).
  Proof.
    intros until shc. intros SH SHS SH1 HDR FLP FLC FRB FRA CSA STL STG MI FH FC F128 GH GC GF VH RF RSF RG.
    pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1. band_ind FH bFH.
    pose proof (ablk_lin _ _ GH) as (GH1 & GH2 & GH3 & GH4). unfold AIMG_HI in GH1. band_ind GH bGH.
    pose proof (ablk_lin _ _ VH) as (VH1 & VH2 & VH3 & VH4).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND, KHIGH, AHARNESS_STACK in *. atop_facts.
    replace (shad F) with (Z.shiftr F 3 + ASHOFF) in * by (unfold shad; lia).
    assert (BSF : 2147450880 <= Z.shiftr F 3 + ASHOFF /\ Z.shiftr F 3 + ASHOFF + 16 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; unfold ASHOFF; Z.div_mod_to_equations; lia).
    unfold FZRB in FRB.
    pose proof (spa_props sp SPA SP16 ESPA) as (SPAB & SPA32 & ESPA').
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    (* [comment removed for export] *)
    assert (SHC : exists b : nat -> byte, shc = map (fun i => C1 (b i)) (seq 0 16)).
    { clear - SHS SH1. exists (fun i => match nth_error shc i with Some (C1 v) => v | _ => Z_to_bv 8 0 end).
      assert (CS : forall l, (forall c, In c l -> exists v, c = C1 v) -> cells_size l = length l).
      { induction l as [|c l IH]; intros ALL; cbn; [reflexivity|]. destruct (ALL c ltac:(left; reflexivity)) as [v ->]. cbn. rewrite IH; [reflexivity|]. intros c' H'; apply ALL; right; exact H'. }
      rewrite CS in SHS by exact SH1.
      assert (GEN : forall k l, (forall c, In c l -> exists v, c = C1 v) ->
                l = map (fun i => C1 (match nth_error (k ++ l) i with Some (C1 v) => v | _ => Z_to_bv 8 0 end)) (seq (length k) (length l))).
      { intros k l. revert k. induction l as [|c l IH]; intros k ALL; cbn; [reflexivity|].
        destruct (ALL c ltac:(left; reflexivity)) as [v ->]. f_equal.
        - rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity.
        - specialize (IH (k ++ [C1 v]) ltac:(intros c' H'; apply ALL; right; exact H')). rewrite <- app_assoc in IH. cbn in IH. rewrite length_app in IH. cbn in IH.
          rewrite Nat.add_1_r in IH. exact IH. }
      pose proof (GEN [] shc SH1) as E. cbn [app length] in E. rewrite SHS in E. exact E. }
    destruct SHC as [b ->]. cbn [map seq] in SH. clear SHS SH1.
    pose proof (munch_refl [(Z.shiftr F 3 + ASHOFF, Z.shiftr F 3 + ASHOFF + 16); (F, F + 8)] m) as MU1. pose proof (wmono_refl bsegs m) as WM1.
    zstep. (* [comment removed for export] *)
    zstep. ubf. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. bcase K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia]. (* [comment removed for export] *)
    zstep. zstep. zstep. (* [comment removed for export] *)
    zstep. bcase K1; try (exfalso; rewrite ?unsigned_lit in K1 by lia; lia). (* [comment removed for export] *)
    zstep. replace (Z_to_bv 64 (-11)) with (Z_to_bv 64 18446744073709551605) by (apply Z_to_bv_eqm; reflexivity). (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SHx : rw_cells bsegs mx (Z.shiftr F 3 + ASHOFF) _ |- _ =>
      pose proof (rw_cells_store_ok bsegs mx _ _ 0%nat _ 1%nat SHx ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK. zstep. zstep. zstep. (* [comment removed for export] *)
    do 8 zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MIx : mem_inv bsegs mx |- _ => pose proof MIx as MIp; change (mem_inv bsegs mx) with (bx (mem_inv bsegs mx)) in MIp end end.
    lazymatch type of MU1 with ?T => change T with (bx T) in MU1 end.
    lazymatch type of WM1 with ?T => change T with (bx T) in WM1 end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => pose proof (munch_refl [(FLG, FLG + 1)] mx) as MU2; pose proof (wmono_refl bsegs mx) as WM2 end.
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. zstep. zstep. (* [comment removed for export] *)
    do 13 zstep. zstep. zstep.
    (* [comment removed for export] *)
    eapply stk_release in FRA; [| exact STL| lia]. rewrite CSA in FRA. change (Z.of_nat 48) with 48 in FRA. replace (SPA + 32 + 48) with (SPA + 80) in FRA by lia.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (stk_merge bsegs mx lo (SPA + 80) (SP + -104) FRA STG ltac:(lia)) as ST2 end.
    release_frame FRB ST2 (bv_unsigned sp).
    apply evtF_done. unfold bx in MU1, WM1, MIp.
    eexists _, _, _, _. split; [reflexivity|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact MIp|].
    split; [exact MU2|]. split; [exact WM2|]. split; [eassumption|]. split; [exact ST2| exact FLC].
  Qed.
End S.
End CANSEC1.
