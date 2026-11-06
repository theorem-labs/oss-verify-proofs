(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge ITree Nodes Decode SysStep Arr FP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio Driver AsanCtrl AsanEmbed HarnessM ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AU_kit AU_iface AHarnessU_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import F_syscalls StdioFiles Stdio_kit MonadF AExit F_module_dtor_pre F_module_dtor AAtexit_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AIos_iface AExitU_wr AExitU_kit AExitU2 AExitU_se AExitU_asm ADriver_iface AD_kit AD_ctx.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow ExecF ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section CANSEC1. Context {rc : runConstT} {XP : ExitParams}.
Section Closed.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv CI.
  Hypothesis EXIT_CI : forall iv, In iv exit_ci_need -> In iv CI.
  (* [comment removed for export] *)
  Hypothesis WCR : wcrtomb0_stmt xp_ICPT xp_ICPTR xp_SLO xp_SHI.
  Hypothesis FW0 : fwrite0_out_stmt xp_ICPT xp_ICPTR.
  Hypothesis FW0E : fwrite0_err_stmt xp_ICPT xp_ICPTR.
  Hypothesis FFL : fflush_out_stmt xp_ICPT xp_ICPTR aps_so aset_so.
  Hypothesis FFLS : fflush_out_stmt xp_ICPT xp_ICPTR (St := stdout_st) (fun so => so) (fun so _ => so).
  Hypothesis FFLE : fflush_err_stmt xp_ICPT xp_ICPTR.
  Hypothesis AVD : avdtor_stmt AI.

  (* [comment removed for export] *)
  Lemma exit_wr_outside : forall W a, Forall exit_wr_ok W ->
    a < ATOP -> ~ (RSTDERR <= a < RSTDOUT + 232) -> ~ (0x6a4db8 <= a < 0x6a4dc0) -> ~ (0x6c4e38 <= a < 0x6c5060) -> a <> 0x16cd50 -> outside W a.
  Proof.
    intros W a HW H1 H2 H3 H4 H5. induction HW as [|[lo hi] W Hx HW IH]; cbn [outside]; [exact I|].
    split; [| exact IH]. unfold exit_wr_ok in Hx. cbn [fst snd] in Hx. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma mdtor_pre_frame_exit : forall W m m', mdtor_pre m -> munch W m m' -> wmono asegs m m' -> Forall exit_wr_ok W -> mdtor_pre m'.
  Proof.
    intros W m m' PRE MU WM HW. pose proof (magree_of_munch asegs _ _ _ MU WM) as AG. pose proof atop_range as AR.
    pose proof (mdtor_stat_of_pre _ PRE) as STAT. destruct PRE as (RT & G & _).
    apply mdtor_pre_of_stat.
    - unfold mdtor_rt in *. destruct RT as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
      repeat match goal with |- _ /\ _ => split end;
        (eapply rw_cells_magree; [exact AG | eassumption | cbn [cells_size csize Nat.add]; intros a Ha; apply exit_wr_outside; [exact HW | lia | lia | lia | lia | lia]]).
    - eapply rw_cells_magree; [exact AG | exact G | cbn [cells_size csize Nat.add]; intros a Ha; apply exit_wr_outside; [exact HW | lia | lia | lia | lia | lia]].
    - eapply mdtor_stat_magree; [exact AG | | exact STAT]. intros a Ha. apply exit_wr_outside; [exact HW | | | | |];
        unfold mdtor_stat_app, mdtor_stat_sh in Ha; lia.
  Qed.
  (* [comment removed for export] *)
  Ltac in_drv lo hi := exists (lo, hi); split; [apply DRV_CI; unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto] | cbn [fst snd]; lia].
  Lemma mdtor_addr_client : forall LB SP a, mdtor_stat_app a \/ mdtor_stat_sh a \/ (0x16dbd0 <= a < 0x16dbd4) ->
    aclient_addr CI LB SP a /\ ~ (AVEC <= a < AVEC + 24).
  Proof.
    intros LB SP a Ha. split; [| unfold mdtor_stat_app, mdtor_stat_sh, AVEC in *; lia].
    destruct Ha as [Ha|[Ha|Ha]].
    - right; left. unfold mdtor_stat_app in Ha.
      destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [in_drv 0x16bb40 0x16cd08 | in_drv 0x16bb40 0x16cd08 | in_drv 0x16dc70 0x16dc78 | in_drv 0x6a2a10 0x6a2c58].
    - right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad]. right; left.
      unfold mdtor_stat_sh in Ha. unfold ASHOFF.
      destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]]; [in_drv 0x23680 0x29da0 | in_drv 0x2c660 0x2c9c0 | in_drv 0x1610a0 0x1614c0 | in_drv 0x6a2a40 0x6a2c40 | in_drv 0x16bb40 0x16cd08].
    - right; left. in_drv 0x16dbd0 0x16dbd4.
  Qed.

  Lemma mdtor_pre_vdtor : forall L RNG st LB LB' SP m m',
    vdtor_pres CI LB SP m m' -> AHEAP AI L RNG st LB' m' -> mem_inv asegs m' -> mdtor_pre m -> mdtor_pre m'.
  Proof.
    intros L RNG st LB LB' SP m m' HPR AH' MI' PRE. unfold vdtor_pres in HPR.
    pose proof (mdtor_stat_of_pre _ PRE) as STAT. destruct PRE as (RT & _). destruct RT as (_ & _ & _ & _ & _ & _ & _ & _ & P9).
    destruct (AD_ctx.exit_relro_of_aheap AI 0 _ _ _ _ _ AH') as (_ & _ & G' & _).   (* [comment removed for export] *)
    apply mdtor_pre_of_stat.
    - eapply (AD_ctx.mdtor_rt_of_aheap AI 0); [exact AH'|].
      eapply rw_cells_magree; [exact HPR | exact P9 | cbn [cells_size csize Nat.add]; intros a Ha; apply mdtor_addr_client; right; right; lia].
    - exact G'.
    - eapply mdtor_stat_magree; [exact HPR | | exact STAT]. intros a Ha. apply mdtor_addr_client. destruct Ha as [Ha|Ha]; [left | right; left]; exact Ha.
  Qed.

  (* [comment removed for export] *)
  Lemma icpt_vdtor : forall L RNG st LB LB' RNG0 st0 LB0 SP m m',
    vdtor_pres CI LB SP m m' -> AHEAP AI L RNG st LB' m' -> mem_inv asegs m' -> xp_ICPT m -> AHEAP AI L RNG0 st0 LB0 m -> xp_ICPT m'.
  Proof.
    intros L RNG st LB LB' RNG0 st0 LB0 SP m m' HPR AH' MI' IC AH0. unfold vdtor_pres in HPR.
    eapply (xp_agree AI); [exact HPR | | exact AH' | exact MI' | exact IC | exact AH0].
    intros a Ha. split; [exact (xp_cli CI LB SP a DRV_CI Ha)|].
    destruct (xp_far a Ha) as [[_ NT] | SH]; [| unfold AVEC; lia].
    intros IN. apply NT. unfold drv_touch, AVEC in *. cbn [xin_ivs]. lia.
  Qed.
  (* [comment removed for export] *)
  Theorem aexit_closed : forall code (s : APS) RNG ms (Q : Empty_set -> APS -> footprint -> machine_state -> Prop),
    aat_exit AI code s RNG ms -> implMA RNG (mbind (client_exitA AAllocAsan) (fun _ => exit_model (ioA AAllocAsan) code)) s Q ms.
  Proof.
    intros code s RNG ms Q H. unfold aat_exit in H.
    exact (aexitU2_proof AI mdtor_pre xp_ICPT xp_ICPTR xp_SLO xp_SHI module_dtor_proof mdtor_pre_frame_exit xp_frame_exit stdio_exit_ghost
             WCR FW0 FW0E FFL FFLS FFLE AVD EXIT_CI (DRV_CI _ ltac:(unfold drv_img_ranges; right; left; reflexivity))      (* [comment removed for export] *)
             mdtor_pre_vdtor icpt_vdtor xp_ICPTR_mono code s RNG ms Q H).
  Qed.
End Closed.
End CANSEC1.
