(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes.
From OSSVerify.simdjson.fuzz_element.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import STree Malloc MallocCtrl Prog Monad Target SjModel AtpModel ElModel.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks MallocKit_B F_malloc_free F_malloc_fast Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import AxSymExec3.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Layout Sj_iface Sj_kit El_xs_core El_xs_kitP El_xs_adapt El_throw El_xcxa.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import El_xr_cast0 El_xr_cast4 El_xr_cast7 El_xr_cast1 El_xr_cast5 El_xr_cast2 El_xr_cast3 El_xr_cast6 El_xr_begin El_xr_end.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Ltac st1 := step; fix_lit_store; try nrm.
Ltac probe := match goal with |- ?g => idtac "PROBE"; idtac g end; fail "PROBE".
Import AX2.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma pj_relro_rheap : forall LB SP m m', rheap_pres LB SP m m' -> pj_relro m -> pj_relro m'.
Proof.
  intros LB SP m m' RP H a Ha. destruct (RP a ltac:(lia)) as [E _].
  { right. left. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
  rewrite E. apply H. exact Ha.
Qed.

Definition site_post (gp tp s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (s : PState) (LB : list block) (usp lo B : Z) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 F' m' (errv' : word),
    ms' = MS (mkR ra (wz (usp + 16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (wz 0x3bfb4) fc None m' (seg_rom psegs)
    /\ (forall r : reg, reg_get F' r = reg_get F r)
    /\ mem_inv psegs m' /\ stk psegs m' lo (usp + 16)
    /\ rw_cells psegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ RHEAP s' LB m' /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ rw_cells psegs m' 0xe1c98 [C8 (wz 0); C4 (wz 0)]
    /\ rw_cells psegs m' 0xe35b0 (uw_cells true)
    /\ (forall a, 0 <= a < 2^64 -> rclient_addr LB (usp + 16) a ->
          ~ (0xe1c98 <= a < 0xe1c98 + 12) -> ~ (0xe35b0 <= a < 0xe35b0 + 8) ->
          m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None)).

Definition throw_site_stmt (pcs raval : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (lo B : Z) (canary errv w0 : word) (uw : bool),
  let usp := bv_unsigned sp in
  RHEAP s LB m -> usp mod 16 = 0 ->
  stk psegs m lo usp -> alloc_ceiling <= lo -> lo <= usp - 16384 -> usp + 16 <= B -> B < 2^62 ->
  rauxv_ok m B -> mem_inv psegs m -> pj_relro m -> ssp_cells m canary ->
  rw_cells psegs m EL_XDATA [C8 (wz EL_XDATA_V0); C8 (wz EL_XDATA_V1)] ->
  rw_cells psegs m EL_HDLR [C8 (wz EL_HDLR_V0); C8 (wz EL_HDLR_V1)] ->
  rw_cells psegs m EL_MREPL [C4 (wz 0); C4 (wz 0)] ->
  rw_cells psegs m EL_EHG [C8 (wz 0); C4 (wz 0)] ->
  rw_cells psegs m EL_UNW (uw_cells uw) ->
  rw_cells psegs m usp [C8 w0] -> rw_cells psegs m (usp + 8) [C8 (wz raval)] ->
  rw_cells psegs m (errno_addr tp) [C4 errv] -> tp = wz RATP ->
  implM psegs (bind lops (AtpModel.newnt lops EL_EXC) (fun e => AtpModel.del lops e)) s (site_post gp tp s9 s10 s11 F fc s LB usp lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcs) fc None m (seg_rom psegs)).

Section Site.
  Variables (pcs pc0 raval : Z) (IT : itab).
  Hypothesis ITS : itab_sound psegs IT.
  Hypothesis RUN : forall uw : bool, exit_ok (xautoP IT xs_W xs_RW 0x705b8 XS_FUEL XS_K (xs_ss0 pc0 raval uw)) = true.
  Hypothesis PC0 : pc0 = pcs + 8.
  Hypothesis PCS : 0 <= pcs /\ pcs + 8 < 2^32 /\ (pcs + 8) mod 2 = 0.
  Hypothesis RAV : 0 <= raval < 2^64.

  Hypothesis CODE : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    mem_inv psegs m ->
    evt psegs (fun ms1 => ms1 = MS (mkR (wz (pcs + 8)) sp gp tp t0 t1 t2 s0 s1 (wz 16) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x6fd04) fc None m (seg_rom psegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcs) fc None m (seg_rom psegs)).

  Theorem throw_site_core : throw_site_stmt pcs raval.
  Proof.
    intros until uw. intros usp HP AL ST LO LOW SPB B62 AUX MI RELRO SSP XD HD MREPL EHG UNW W0S RAS ERR TP. subst usp.
    pose proof alloc_ceiling_range as CR. pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    cbn [bind lops Target.ops].

    eapply implM_evt; [apply CODE; exact MI|]. intros ms1 ->.

    eapply implM_bind.
    { eapply (cxa_alloc_spec (wz (pcs + 8)) sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB lo B errv HP AUX);
        [lia| exact ST| exact LO| unfold RMALLOC_STACK; lia| exact ERR| exact MI| exact TP| exact MREPL]. }
    intros p s1' ms2 POST. unfold cxa_post in POST.
    destruct POST as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m1 & blk & errv1 & -> & MI1 & ST1 & ERR1 & AUX1 & RP1 & FA1 & SO1 & RB & HP1 & HB).
    rewrite ret_pc_even by (clear - PCS; lia).

    assert (AG : forall A cs, rw_cells psegs m A cs -> rclient_range LB (bv_unsigned sp) A (Z.of_nat (cells_size cs)) -> rw_cells psegs m1 A cs).
    { intros A cs H HR. eapply rheap_pres_rw_cells; [exact RP1| exact H| exact HR]. }
    pose proof (RHEAP_blocks_nodup_proof _ _ _ HP1) as ND.

    cbn [del lib_free lops Target.ops lib_free_opt].
    eapply implM_post_evt.
    rewrite <- PC0.
    { eapply (xs_throw_A IT pc0 raval ITS RUN (wz pc0) sp gp tp u0 u1 u2 s0 s1 v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
                F fc m1 s1' ((p, blk, 144) :: LB) p blk lo B canary errv1 w0 uw HP1 ltac:(left; reflexivity) HB RB).
      - pose proof (stk_of_rw_cells psegs m1 _ _ (AG _ _ W0S ltac:(left; lia))) as S1. pose proof (stk_of_rw_cells psegs m1 _ _ (AG _ _ RAS ltac:(left; lia))) as S2.
        cbn [cells_size csize Nat.add] in S1, S2. replace (bv_unsigned sp + 8 + 8) with (bv_unsigned sp + 16) in S2 by lia.
        eapply stk_merge; [exact ST1| eapply stk_merge; [exact S1| exact S2| lia]| lia].
      - exact LO.
      - lia.
      - lia.
      - lia.
      - exact AL.
      - exact AUX1.
      - exact MI1.
      - eapply pj_relro_rheap; [exact RP1| exact RELRO].
      - rewrite (ssp_canary_0 _ _ _ _ HP SSP). exact (RHEAP_ssp _ _ _ HP1).
      - apply AG; [exact XD| right; left; cbn; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia].
      - apply AG; [exact HD| right; left; cbn; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia].
      - apply AG; [exact EHG| right; left; cbn; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia].
      - apply AG; [exact UNW| right; left]. replace (Z.of_nat (cells_size (uw_cells uw))) with 8 by (destruct uw; reflexivity).
        unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia.
      - apply AG; [exact W0S| left; lia].
      - apply AG; [exact RAS| left; lia].
      - exact RAV.
      - exact ERR1.
      - exact TP. }

    intros [] s' ms' X. apply evt_done. unfold xs_post in X. unfold site_post.
    rewrite (lb_remove_hd p blk 144 LB ND) in X.
    destruct X as (zra & z0 & z1 & z2 & y0 & y1 & q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & z3 & z4 & z5 & z6 & F' & m' &
                   -> & HF & MI' & ST' & ERR' & AUX' & HP' & FA' & SO' & EHG' & UNW' & FR').
    do 27 eexists. exists errv1. split; [reflexivity|]. split; [exact HF|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
    split; [exact HP'|]. split; [rewrite FA'; exact FA1|]. split; [rewrite SO'; exact SO1|]. split; [exact EHG'|]. split; [exact UNW'|].
    intros a Ha HC N1 N2. destruct (FR' a Ha HC N1 N2) as [E1 W1].
    destruct (RP1 a Ha) as [E0 W0]. { destruct HC as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H]. }
    rewrite E1, E0. split; [reflexivity|]. intros W. apply W1. apply W0. exact W.
  Qed.
End Site.

Theorem throw_site_cast0 : throw_site_stmt 0x3c15c 0x3bf00.
Proof.
  apply (throw_site_core 0x3c15c 0x3c164 0x3bf00 el_IT_cast0 (itab_of_ranges_soundP el_ranges_cast0) xr_cast0_ok); [reflexivity| lia| lia|].
  intros until m. intros MI. unfold wz. st1. st1. apply evt_done. reflexivity.
Qed.
Theorem throw_site_cast4 : throw_site_stmt 0x3c1a8 0x3bf00.
Proof.
  apply (throw_site_core 0x3c1a8 0x3c1b0 0x3bf00 el_IT_cast4 (itab_of_ranges_soundP el_ranges_cast4) xr_cast4_ok); [reflexivity| lia| lia|].
  intros until m. intros MI. unfold wz. st1. st1. apply evt_done. reflexivity.
Qed.
Theorem throw_site_cast7 : throw_site_stmt 0x3c278 0x3bf00.
Proof.
  apply (throw_site_core 0x3c278 0x3c280 0x3bf00 el_IT_cast7 (itab_of_ranges_soundP el_ranges_cast7) xr_cast7_ok); [reflexivity| lia| lia|].
  intros until m. intros MI. unfold wz. st1. st1. apply evt_done. reflexivity.
Qed.
Theorem throw_site_cast1 : throw_site_stmt 0x3c2e4 0x3bf00.
Proof.
  apply (throw_site_core 0x3c2e4 0x3c2ec 0x3bf00 el_IT_cast1 (itab_of_ranges_soundP el_ranges_cast1) xr_cast1_ok); [reflexivity| lia| lia|].
  intros until m. intros MI. unfold wz. st1. st1. apply evt_done. reflexivity.
Qed.
Theorem throw_site_cast5 : throw_site_stmt 0x3c334 0x3bf00.
Proof.
  apply (throw_site_core 0x3c334 0x3c33c 0x3bf00 el_IT_cast5 (itab_of_ranges_soundP el_ranges_cast5) xr_cast5_ok); [reflexivity| lia| lia|].
  intros until m. intros MI. unfold wz. st1. st1. apply evt_done. reflexivity.
Qed.
Theorem throw_site_cast2 : throw_site_stmt 0x3c398 0x3bf00.
Proof.
  apply (throw_site_core 0x3c398 0x3c3a0 0x3bf00 el_IT_cast2 (itab_of_ranges_soundP el_ranges_cast2) xr_cast2_ok); [reflexivity| lia| lia|].
  intros until m. intros MI. unfold wz. st1. st1. apply evt_done. reflexivity.
Qed.
Theorem throw_site_cast3 : throw_site_stmt 0x3c3c8 0x3bf00.
Proof.
  apply (throw_site_core 0x3c3c8 0x3c3d0 0x3bf00 el_IT_cast3 (itab_of_ranges_soundP el_ranges_cast3) xr_cast3_ok); [reflexivity| lia| lia|].
  intros until m. intros MI. unfold wz. st1. st1. apply evt_done. reflexivity.
Qed.
Theorem throw_site_cast6 : throw_site_stmt 0x3c3f4 0x3bf00.
Proof.
  apply (throw_site_core 0x3c3f4 0x3c3fc 0x3bf00 el_IT_cast6 (itab_of_ranges_soundP el_ranges_cast6) xr_cast6_ok); [reflexivity| lia| lia|].
  intros until m. intros MI. unfold wz. st1. st1. apply evt_done. reflexivity.
Qed.
Theorem throw_site_begin : throw_site_stmt 0x3c458 0x3bed8.
Proof.
  apply (throw_site_core 0x3c458 0x3c460 0x3bed8 el_IT_begin (itab_of_ranges_soundP el_ranges_begin) xr_begin_ok); [reflexivity| lia| lia|].
  intros until m. intros MI. unfold wz. st1. st1. apply evt_done. reflexivity.
Qed.
Theorem throw_site_end : throw_site_stmt 0x3c4c8 0x3bf38.
Proof.
  apply (throw_site_core 0x3c4c8 0x3c4d0 0x3bf38 el_IT_end (itab_of_ranges_soundP el_ranges_end) xr_end_ok); [reflexivity| lia| lia|].
  intros until m. intros MI. unfold wz. st1. st1. apply evt_done. reflexivity.
Qed.
End WithCeiling0.
