(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the five startup certificates CERT_A_T to CERT_2_T checked at the run's CONFIG_RSEQ flag (RZ, from the kernel build) against StartupRegenBoth's renumbered plans and computed hand-off tables, counters and shapes (planA to plan2, hsA to hs2, nxB to nx2, shapeA to shape2), in place of the fixed plans (startup_plan, startup_plan_segA to startup_plan_segC, startup2_plan of StartupPlanBoth and StartupPlan2Both), tables HS_asanA to HS_asan2 of StartupHSBoth and StartupHS2Both, counters NXB to NXS2 and shapes; section variables kb, execfn and sdef and hypotheses valid_launch and entry_launch_ok_va added, SINV, argH and E0a taking the new launch arguments; shapeA_holes, shapeB_holes, shapeC_holes, shapeD_holes and shape2_holes added; asan_boot_shape and asan_boot restated over init_config with the launch input INP; seg_sound, S2_sound, D_sound, C_sound and B_sound restated at RZ, AH (passing AsanInit.argH0_high the section's apc) and AH2 proved as lemmas; 9 recorded proofs replaced by written proofs (HH_agree, HH_nil, sd_allH and 6 more); imports PlanRegen and StartupRegenBoth in place of StartupHSBoth and StartupHS2Both; the port of zstd/zstd_frame_info's same file). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.zstd.huf_decompress.images Require Import AsanUbsan.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 BothPlanImages AsanInit
  AsanNodesIface AsanNodesMmA AsanNodesMmB SumsBothClose AsanNodesStartX AsanNodesStartXBoth AsanNodesWJoin BothStartup
StartupPlanBoth StartupPlan2Both BothCertDefs PlanRegen StartupRegenBoth.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint holes_only (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SCase _ _ a b => holes_only a && holes_only b
  | SAlt2 a b => holes_only a && holes_only b
  | _ => false
  end.
(* the computed result shapes are made of holes only, at each CONFIG_RSEQ value *)
Lemma shapeA_holes : forall r, holes_only (shapeA r) = true.
Proof. intros r. unfold shapeA. destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.
Lemma shapeB_holes : forall r, holes_only (shapeB r) = true.
Proof. intros r. unfold shapeB. destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.
Lemma shapeC_holes : forall r, holes_only (shapeC r) = true.
Proof. intros r. unfold shapeC. destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.
Lemma shapeD_holes : forall r, holes_only (shapeD r) = true.
Proof. intros r. unfold shapeD. destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.
Lemma shape2_holes : forall r, holes_only (shape2 r) = true.
Proof. intros r. unfold shape2. destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.

Section Boot.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid : word.
  Variable hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nof sigm : word.   (* [comment removed for export] *)
  Variable abt : bool.
  Variable urnd : InputStream.   (* [comment removed for export] *)
Variable kb : KernelBuild.
(* the exec file name and the SIGPIPE disposition, free as in AsanInit (LPS 727298f3) *)
Variable execfn : list byte.
Variable sdef : bool.
Let INP := AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb execfn sdef.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

Hypothesis Hlaunch : valid_launch INP.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
#[local] Notation APC := AsanUbsan.M.init_pc.
#[local] Notation SINV := (SINV0 APH APC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb execfn sdef).
#[local] Notation argH := (argH0 sp rdraw argv envp kb execfn).
#[local] Notation E0a := (AsanInit.E0 sp rdraw brk0 argv envp uid gid hw kb execfn).
  (* [comment removed for export] *)
  Variable LIM : Z.
(* the run's CONFIG_RSEQ flag as the plan's 0 or 1: every certificate is checked at it
   (model commit 0c15dd4) *)
#[local] Notation RZ := (rseq_z (kb_rseq kb)).
  Hypothesis HLIM : source_alloc_limit <= LIM.
(* LPS 727298f3: the five plans renumbered by the probe-read maps and checked against the
   hand-off tables, counters and shapes computed in the build (StartupRegenBoth), at RZ *)
#[local] Notation CERT_A_T := (check ASEGS IT0 BOTH NX0 LIM RZ (XNS ASEGS BOTH NX0 LIM) XE0 XB0 (hsA RZ) KC0 BFUEL FUEL None (both_init RZ) (planA RZ) = COk (shapeA RZ)).
#[local] Notation CERT_B_T := (check ASEGS ITB BOTH (nxB RZ) LIM RZ (XNS ASEGS BOTH (nxB RZ) LIM) XE0 XB0 (hsB RZ) KC0 BFUEL FUEL None (stA RZ) (planB RZ) = COk (shapeB RZ)).
#[local] Notation CERT_C_T := (check ASEGS ITC BOTH (nxC RZ) LIM RZ (XNS ASEGS BOTH (nxC RZ) LIM) XE0 XB0 (hsC RZ) KC0 BFUEL FUEL None (stB RZ) (planC RZ) = COk (shapeC RZ)).
#[local] Notation CERT_D_T := (check ASEGS ITD BOTH (nxD RZ) LIM RZ (XNS ASEGS BOTH (nxD RZ) LIM) XE0 XB0 (hsD RZ) KC0 BFUEL FUEL None (stC RZ) (planD RZ) = COk (shapeD RZ)).
#[local] Notation CERT_2_T := (check ASEGS IT2 BOTH (nx2 RZ) LIM RZ (XNS ASEGS BOTH (nx2 RZ) LIM) XE0 XB0 (hs2 RZ) KC0 BFUEL FUEL None (stD RZ) (plan2 RZ) = COk (shape2 RZ)).

  (* [comment removed for export] *)
  Variable H : env -> Fs.Fs -> TSet.
  Hypothesis H_agree : forall E E' fs', env_agree NX0 E E' -> H E fs' = H E' fs'.
  Hypothesis H_nil : forall E fs', H E fs' [].
Hypothesis MAIN : holes_stmt ASEGS BOTH LIM (hs2 RZ) SINV argH (fun _ => H) fs.
Let AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Proof. intros E a H0. eapply argH0_high with (apc := APC); eassumption. Qed.
Let AH2 : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.
Proof. intros E M a HS H0. eapply argH0_high2; eassumption. Qed.
Let AA := argH0_agree sp rdraw argv envp kb execfn.
Let SF := SINV0_frame APH APC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb execfn sdef.
Let SA := SINV0_agree APH APC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb execfn sdef.

  (* [comment removed for export] *)
  Definition HH (h : nat) (E : env) (fs' : Fs.Fs) : TSet := H E fs'.
  #[using="H_agree"] Lemma HH_agree : forall h E E' fs', env_agree NX0 E E' -> HH h E fs' = HH h E' fs'.
  Proof. intros. unfold HH. apply H_agree. assumption. Qed.
  #[using="H_nil"] Lemma HH_nil : forall h E fs', HH h E fs' [].
  Proof. intros. unfold HH. apply H_nil. Qed.

  (* [comment removed for export] *)
  #[using="H_nil"] Lemma sd_allH : forall E fs' s, holes_only s = true -> t_eq (sd HH t_nil E fs' s) (H E fs').
  Proof.
    assert (ID : forall X Y Z : TSet, Z [] -> t_eq X Z -> t_eq Y Z -> t_eq (t_alt2 X Y) Z).
    { intros X Y Z HZ HX HY tr. unfold t_alt2. specialize (HX tr). specialize (HY tr). tauto. }
    intros E fs' s. induction s as [| |fd ps s IH|a IHa b IHb|e mid a IHa b IHb|h|]; cbn [holes_only sd]; intros Hs; try discriminate.
    - apply andb_prop in Hs as [Ha Hb]. apply ID; [apply H_nil | exact (IHa Ha) | exact (IHb Hb)].
    - apply andb_prop in Hs as [Ha Hb]. destruct (_ <=? _); [exact (IHa Ha) | exact (IHb Hb)].
    - unfold HH. apply t_eq_refl.
  Qed.

  (* [comment removed for export] *)
  Section Seg.
    Variable nx : nat.
    Hypothesis Hnx : (NX0 <= nx)%nat.
    #[using="Hnx"] Lemma env_agree_nx : forall E E', env_agree nx E E' -> env_agree NX0 E E'.
    Proof. intros E E' [Hag Hb]. split; [|exact Hb]. intros n Hn. apply Hag. lia. Qed.
    Let AAn : forall E E' (a : word), env_agree nx E E' -> argH E a = argH E' a :=
      fun E E' a Hag => AA E E' a (env_agree_nx E E' Hag).
    Let SAn : forall E E' M, env_agree nx E E' -> SINV E M -> SINV E' M :=
      fun E E' M Hag => SA E E' M (env_agree_nx E E' Hag).

    (* [comment removed for export] *)
#[using="Hsp Hva Hve Hfit Hlaunch Hlau H_agree H_nil AH AH2 AA SF SA Hnx AAn SAn"] Lemma seg_sound : forall (IT : itab) (IT_ok : itab_sound ASEGS IT) (HSn : nat -> option acs) (FUEL BFUEL KC : nat)
                             (p : plan) (start : acs) (shp : shape),
      holes_stmt ASEGS BOTH LIM HSn SINV argH HH fs ->
check ASEGS IT BOTH nx LIM RZ (XNS ASEGS BOTH nx LIM) XE0 XB0 HSn KC BFUEL FUEL None start p = COk shp ->
      holes_only shp = true ->
      forall E R FULL model, cs_ok ASEGS BOTH LIM SINV argH fs E start R FULL model ->
        srealizes ASEGS (cfg_of ASEGS R (pc start) FULL model) (H E (m_fs model)).
    Proof.
      intros IT IT_ok HSn FUEL BFUEL KC p start shp HSOUND CERT Hshp E R FULL model HC.
pose proof (check_sound ASEGS IT IT_ok BOTH nx Hnx LIM RZ HSn (XNS ASEGS BOTH nx LIM) XE0 XB0
                asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AH AAn SF SAn
                HH (fun h E1 E2 fs' Hag => HH_agree h E1 E2 fs' (env_agree_nx E1 E2 Hag)) HH_nil fs KC
                (AsanNodesMmB.node_sys_sound ASEGS BOTH nx LIM SINV argH fs asan_res_len asan_hull_ok asan_shadow_ok AH2 AAn SF SAn)
                (AsanNodesMmB.node_brk2_sound ASEGS BOTH nx LIM SINV argH fs asan_in_hull asan_res_len asan_hull_ok asan_shadow_ok AH AH2 SF)
                (node_mmap2_sound_OBL ASEGS BOTH nx LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AAn SF SAn)
                (node_mmapin_sound_OBL ASEGS BOTH nx LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AAn SF SAn)
                (node_mprotect2_sound_OBL ASEGS BOTH nx LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AAn SF SAn)
                (AsanNodesMmB.node_exit_sound ASEGS BOTH LIM SINV argH fs)
(asan_node_x_sound_all APC sp rdraw brk0 mbase argv envp fs stdin fs uid gid hw groups net nof sigm abt urnd kb execfn sdef Hsp Hva Hve Hfit Hlaunch Hlau SINV (fun E M HH0 => HH0) SF nx Hnx SAn LIM)
                (node_join_sound ASEGS BOTH nx LIM SINV argH fs)
                (XNS_sound ASEGS BOTH nx LIM SINV argH fs AAn SAn asan_in_hull asan_hull_ok asan_shadow_ok AH AH2) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
                HSOUND FUEL BFUEL None p start shp CERT
                E R FULL model t_nil HC I eq_refl) as R0.
      eapply srz_conseq; [exact R0 | apply sd_allH; exact Hshp].
    Qed.

    (* [comment removed for export] *)
    #[using="Type"] Lemma seg_holes : forall (HSp : nat -> option acs) (h0 : nat) (start : acs),
      (forall h ch, HSp h = Some ch -> h = h0 /\ ch = start) ->
      (forall E R FULL model, cs_ok ASEGS BOTH LIM SINV argH fs E start R FULL model ->
         srealizes ASEGS (cfg_of ASEGS R (pc start) FULL model) (H E (m_fs model))) ->
      holes_stmt ASEGS BOTH LIM HSp SINV argH HH fs.
    Proof.
      intros HSp h0 start Hone Hseg h ch Hh E R FULL model HC. destruct (Hone h ch Hh) as [-> ->]. unfold HH. exact (Hseg E R FULL model HC).
    Qed.
  End Seg.

  (* [comment removed for export] *)
#[using="Hsp Hva Hve Hfit Hlaunch Hlau H_agree H_nil MAIN AH AH2 AA SF SA"] Lemma S2_sound : CERT_2_T -> holes_stmt ASEGS BOTH LIM (hsD RZ) SINV argH HH fs.
  Proof.
    intros CERT_2.
apply (seg_holes (hsD RZ) 0%nat (stD RZ) (hsD_one RZ)).
apply (seg_sound (nx2 RZ) (nx2_ge RZ) IT2 IT2_ok (hs2 RZ) FUEL BFUEL KC0 (plan2 RZ) (stD RZ) (shape2 RZ)); [| exact CERT_2 | apply shape2_holes].
    intros h ch Hh E R FULL model HC. unfold HH. exact (MAIN h ch Hh E R FULL model HC).
  Qed.
#[using="Hsp Hva Hve Hfit Hlaunch Hlau H_agree H_nil MAIN AH AH2 AA SF SA"] Lemma D_sound : CERT_D_T -> CERT_2_T -> holes_stmt ASEGS BOTH LIM (hsC RZ) SINV argH HH fs.
  Proof.
    intros CERT_D CERT_2.
apply (seg_holes (hsC RZ) 12%nat (stC RZ) (hsC_one RZ)).
apply (seg_sound (nxD RZ) (nxD_ge RZ) ITD ITD_ok (hsD RZ) FUEL BFUEL KC0 (planD RZ) (stC RZ) (shapeD RZ)); [exact (S2_sound CERT_2) | exact CERT_D | apply shapeD_holes].
  Qed.
#[using="Hsp Hva Hve Hfit Hlaunch Hlau H_agree H_nil MAIN AH AH2 AA SF SA"] Lemma C_sound : CERT_C_T -> CERT_D_T -> CERT_2_T -> holes_stmt ASEGS BOTH LIM (hsB RZ) SINV argH HH fs.
  Proof.
    intros CERT_C CERT_D CERT_2.
apply (seg_holes (hsB RZ) 11%nat (stB RZ) (hsB_one RZ)).
apply (seg_sound (nxC RZ) (nxC_ge RZ) ITC ITC_ok (hsC RZ) FUEL BFUEL KC0 (planC RZ) (stB RZ) (shapeC RZ)); [exact (D_sound CERT_D CERT_2) | exact CERT_C | apply shapeC_holes].
  Qed.
#[using="Hsp Hva Hve Hfit Hlaunch Hlau H_agree H_nil MAIN AH AH2 AA SF SA"] Lemma B_sound : CERT_B_T -> CERT_C_T -> CERT_D_T -> CERT_2_T -> holes_stmt ASEGS BOTH LIM (hsA RZ) SINV argH HH fs.
  Proof.
    intros CERT_B CERT_C CERT_D CERT_2.
apply (seg_holes (hsA RZ) 10%nat (stA RZ) (hsA_one RZ)).
apply (seg_sound (nxB RZ) (nxB_ge RZ) ITB ITB_ok (hsB RZ) FUEL BFUEL KC0 (planB RZ) (stA RZ) (shapeB RZ)); [exact (C_sound CERT_C CERT_D CERT_2) | exact CERT_B | apply shapeB_holes].
  Qed.

  (* [comment removed for export] *)
#[using="Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hlaunch Hlau HLIM H_agree H_nil MAIN AH AH2 AA SF SA"] Theorem asan_boot_shape : CERT_A_T -> CERT_B_T -> CERT_C_T -> CERT_D_T -> CERT_2_T ->
srealizes ASEGS (init_config ASEGS APC APH sp brk0 mbase rdraw LIM INP)
(sd HH t_nil E0a fs (shapeA RZ)).
  Proof.
    intros CERT_A CERT_B CERT_C CERT_D CERT_2.
exact (asan_startup sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb execfn sdef Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hlaunch Hlau LIM HLIM
IT0 IT0_ok (hsA RZ) (planA RZ) (shapeA RZ) KC0 BFUEL FUEL CERT_A HH HH_agree HH_nil (B_sound CERT_B CERT_C CERT_D CERT_2)).
  Qed.

  (* [comment removed for export] *)
#[using="Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hlaunch Hlau HLIM H_agree H_nil MAIN AH AH2 AA SF SA"] Theorem asan_boot : CERT_A_T -> CERT_B_T -> CERT_C_T -> CERT_D_T -> CERT_2_T ->
srealizes ASEGS (init_config ASEGS APC APH sp brk0 mbase rdraw LIM INP)
              (H E0a fs).
Proof. intros CERT_A CERT_B CERT_C CERT_D CERT_2. eapply srz_conseq; [exact (asan_boot_shape CERT_A CERT_B CERT_C CERT_D CERT_2) | apply sd_allH; apply shapeA_holes]. Qed.
End Boot.
