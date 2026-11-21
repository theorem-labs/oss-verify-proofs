(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up chain over the launch's ProcInput, kernel build, exec file name and SIGPIPE disposition; the five start-up certificates taken as premises CERT_A_T to CERT_2_T at the run's CONFIG_RSEQ flag RZ, against StartupRegenBoth's renumbered plans planA to plan2, computed hand-off tables hsA to hs2, counters nxB to nx2 and shapes shapeA to shape2, in place of the recorded plans, tables HS_bothA to HS_both2, counters NXB to NXS2 and shapes; shapeA_holes to shape2_holes added; imports BothCertDefs, PlanRegen and StartupRegenBoth in place of StartupHSBoth, StartupHS2Both and the certificate files; AH, the hidden argument block's bound, passes argH0_high the image's entry pc (apc := APC)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.zstd.simple_decompress.images Require Import AsanUbsan.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AS Require Import
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
  Variable tmp : Fs.Fs.          (* [comment removed for export] *)
  (* the kernel build, the exec file name and the SIGPIPE disposition, free as in AsanInit
     (LPS 727298f3) *)
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable sdef : bool.
  Let INP := AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmp kb execfn sdef.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  (* [comment removed for export] *)
  Hypothesis Hlaunch : valid_launch INP.
  (* [comment removed for export] *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.

  #[local] Notation APC := AsanUbsan.M.init_pc.
  #[local] Notation SINV := (SINV0 BPH APC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmp kb execfn sdef).
  #[local] Notation argH := (argH0 sp rdraw argv envp kb execfn).
  #[local] Notation E0a := (AsanInit.E0 sp rdraw brk0 argv envp uid gid hw kb execfn).
  #[local] Notation LIM := AsanInit.LIMIT.
  (* the run's CONFIG_RSEQ flag as the plan's 0 or 1: every certificate is checked at it
     (model commit 0c15dd4) *)
  #[local] Notation RZ := (rseq_z (kb_rseq kb)).
  (* LPS 727298f3: the five plans renumbered by the probe-read maps and checked against the
     hand-off tables, counters and shapes computed in the build (StartupRegenBoth), at RZ *)
  #[local] Notation CERT_A_T := (check BSEGS IT0 BOTH NX0 LIM RZ (XNS BSEGS BOTH NX0 LIM) XE0 XB0 (hsA RZ) KC0 BFUEL FUEL None (both_init RZ) (planA RZ) = COk (shapeA RZ)).
  #[local] Notation CERT_B_T := (check BSEGS ITB BOTH (nxB RZ) LIM RZ (XNS BSEGS BOTH (nxB RZ) LIM) XE0 XB0 (hsB RZ) KC0 BFUEL FUEL None (stA RZ) (planB RZ) = COk (shapeB RZ)).
  #[local] Notation CERT_C_T := (check BSEGS ITC BOTH (nxC RZ) LIM RZ (XNS BSEGS BOTH (nxC RZ) LIM) XE0 XB0 (hsC RZ) KC0 BFUEL FUEL None (stB RZ) (planC RZ) = COk (shapeC RZ)).
  #[local] Notation CERT_D_T := (check BSEGS ITD BOTH (nxD RZ) LIM RZ (XNS BSEGS BOTH (nxD RZ) LIM) XE0 XB0 (hsD RZ) KC0 BFUEL FUEL None (stC RZ) (planD RZ) = COk (shapeD RZ)).
  #[local] Notation CERT_2_T := (check BSEGS IT2 BOTH (nx2 RZ) LIM RZ (XNS BSEGS BOTH (nx2 RZ) LIM) XE0 XB0 (hs2 RZ) KC0 BFUEL FUEL None (stD RZ) (plan2 RZ) = COk (shape2 RZ)).

  (* [comment removed for export] *)
  Variable H : env -> Fs.Fs -> TSet.
  Hypothesis H_agree : forall E E' fs', env_agree NX0 E E' -> H E fs' = H E' fs'.
  Hypothesis H_nil : forall E fs', H E fs' [].
  Hypothesis MAIN : holes_stmt BSEGS BOTH LIM (hs2 RZ) SINV argH (fun _ => H) (fs_seed_tmp fs tmp).

  (* transparent (Defined), so that both_boot is not generalized over them at the section's end *)
  Let AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Proof. intros E a H0. eapply argH0_high with (apc := APC); eassumption. Defined.
  Let AH2 : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.
  Proof. intros E M a HS H0. eapply argH0_high2; eassumption. Defined.
  Let AA : forall E E' (a : word), env_agree NX0 E E' -> argH E a = argH E' a.
  Proof. intros E E' a HE. eapply argH0_agree. exact HE. Defined.
  Let SF : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Proof. intros E M M' Hf HS. eapply SINV0_frame; eassumption. Defined.
  Let SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  Proof. intros E E' M HE HS. eapply SINV0_agree; eassumption. Defined.

  (* [comment removed for export] *)
  Definition HH (h : nat) (E : env) (fs' : Fs.Fs) : TSet := H E fs'.
  Lemma HH_agree : forall h E E' fs', env_agree NX0 E E' -> HH h E fs' = HH h E' fs'.
  Proof. intros. unfold HH. apply H_agree. assumption. Qed.
  Lemma HH_nil : forall h E fs', HH h E fs' [].
  Proof. intros. unfold HH. apply H_nil. Qed.

  (* [comment removed for export] *)
  Lemma sd_allH : forall E fs' s, holes_only s = true -> t_eq (sd HH t_nil E fs' s) (H E fs').
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
    Lemma env_agree_nx : forall E E', env_agree nx E E' -> env_agree NX0 E E'.
    Proof. intros E E' [Hag Hb]. split; [|exact Hb]. intros n Hn. apply Hag. lia. Qed.
    Let AAn : forall E E' (a : word), env_agree nx E E' -> argH E a = argH E' a :=
      fun E E' a Hag => AA E E' a (env_agree_nx E E' Hag).
    Let SAn : forall E E' M, env_agree nx E E' -> SINV E M -> SINV E' M :=
      fun E E' M Hag => SA E E' M (env_agree_nx E E' Hag).

    (* [comment removed for export] *)
    Lemma seg_sound : forall (IT : itab) (IT_ok : itab_sound BSEGS IT) (HSn : nat -> option acs) (FUEL BFUEL KC : nat)
                             (p : plan) (start : acs) (shp : shape),
      holes_stmt BSEGS BOTH LIM HSn SINV argH HH (fs_seed_tmp fs tmp) ->
      check BSEGS IT BOTH nx LIM RZ (XNS BSEGS BOTH nx LIM) XE0 XB0 HSn KC BFUEL FUEL None start p = COk shp ->
      holes_only shp = true ->
      forall E R FULL model, cs_ok BSEGS BOTH LIM SINV argH (fs_seed_tmp fs tmp) E start R FULL model ->
        srealizes BSEGS (cfg_of BSEGS R (pc start) FULL model) (H E (m_fs model)).
    Proof.
      intros IT IT_ok HSn FUEL BFUEL KC p start shp HSOUND CERT Hshp E R FULL model HC.
      assert (XALL : forall x, x_stmt BSEGS BOTH nx LIM RZ SINV argH (fs_seed_tmp fs tmp) x)
        by (eapply both_node_x_sound_all; first [eassumption | exact (fun E M H => H) | exact Hnx | exact SAn]).
      pose proof (check_sound BSEGS IT IT_ok BOTH nx Hnx LIM RZ HSn (XNS BSEGS BOTH nx LIM) XE0 XB0
                both_wx both_in_hull both_hull_ok both_shadow_ok SINV argH AH AAn SF SAn
                HH (fun h E1 E2 fs' Hag => HH_agree h E1 E2 fs' (env_agree_nx E1 E2 Hag)) HH_nil (fs_seed_tmp fs tmp) KC
                (AsanNodesMmB.node_sys_sound BSEGS BOTH nx LIM SINV argH (fs_seed_tmp fs tmp) both_res_len both_hull_ok both_shadow_ok AH2 AAn SF SAn)
                (AsanNodesMmB.node_brk2_sound BSEGS BOTH nx LIM SINV argH (fs_seed_tmp fs tmp) both_in_hull both_res_len both_hull_ok both_shadow_ok AH AH2 SF)
                (node_mmap2_sound_OBL BSEGS BOTH nx LIM SINV argH (fs_seed_tmp fs tmp) both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AAn SF SAn)
                (node_mmapin_sound_OBL BSEGS BOTH nx LIM SINV argH (fs_seed_tmp fs tmp) both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AAn SF SAn)
                (node_mprotect2_sound_OBL BSEGS BOTH nx LIM SINV argH (fs_seed_tmp fs tmp) both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AAn SF SAn)
                (AsanNodesMmB.node_exit_sound BSEGS BOTH LIM SINV argH (fs_seed_tmp fs tmp))
                XALL
                (node_join_sound BSEGS BOTH nx LIM SINV argH (fs_seed_tmp fs tmp))
                (XNS_sound BSEGS BOTH nx LIM SINV argH (fs_seed_tmp fs tmp) AAn SAn both_in_hull both_hull_ok both_shadow_ok AH AH2) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
                HSOUND FUEL BFUEL None p start shp CERT
                E R FULL model t_nil HC I eq_refl) as R0.
      eapply srz_conseq; [exact R0 | apply sd_allH; exact Hshp].
    Qed.

    (* [comment removed for export] *)
    Lemma seg_holes : forall (HSp : nat -> option acs) (h0 : nat) (start : acs),
      (forall h ch, HSp h = Some ch -> h = h0 /\ ch = start) ->
      (forall E R FULL model, cs_ok BSEGS BOTH LIM SINV argH (fs_seed_tmp fs tmp) E start R FULL model ->
         srealizes BSEGS (cfg_of BSEGS R (pc start) FULL model) (H E (m_fs model))) ->
      holes_stmt BSEGS BOTH LIM HSp SINV argH HH (fs_seed_tmp fs tmp).
    Proof.
      intros HSp h0 start Hone Hseg h ch Hh E R FULL model HC. destruct (Hone h ch Hh) as [-> ->]. unfold HH. exact (Hseg E R FULL model HC).
    Qed.
  End Seg.

  (* [comment removed for export] *)
  Lemma S2_sound : CERT_2_T -> holes_stmt BSEGS BOTH LIM (hsD RZ) SINV argH HH (fs_seed_tmp fs tmp).
  Proof.
    intros CERT_2.
    apply (seg_holes (hsD RZ) 0%nat (stD RZ) (hsD_one RZ)).
    apply (seg_sound (nx2 RZ) (nx2_ge RZ) IT2 IT2_ok (hs2 RZ) FUEL BFUEL KC0 (plan2 RZ) (stD RZ) (shape2 RZ)); [| exact CERT_2 | apply shape2_holes].
    intros h ch Hh E R FULL model HC. unfold HH. exact (MAIN h ch Hh E R FULL model HC).
  Qed.
  Lemma D_sound : CERT_D_T -> CERT_2_T -> holes_stmt BSEGS BOTH LIM (hsC RZ) SINV argH HH (fs_seed_tmp fs tmp).
  Proof.
    intros CERT_D CERT_2.
    apply (seg_holes (hsC RZ) 12%nat (stC RZ) (hsC_one RZ)).
    apply (seg_sound (nxD RZ) (nxD_ge RZ) ITD ITD_ok (hsD RZ) FUEL BFUEL KC0 (planD RZ) (stC RZ) (shapeD RZ)); [exact (S2_sound CERT_2) | exact CERT_D | apply shapeD_holes].
  Qed.
  Lemma C_sound : CERT_C_T -> CERT_D_T -> CERT_2_T -> holes_stmt BSEGS BOTH LIM (hsB RZ) SINV argH HH (fs_seed_tmp fs tmp).
  Proof.
    intros CERT_C CERT_D CERT_2.
    apply (seg_holes (hsB RZ) 11%nat (stB RZ) (hsB_one RZ)).
    apply (seg_sound (nxC RZ) (nxC_ge RZ) ITC ITC_ok (hsC RZ) FUEL BFUEL KC0 (planC RZ) (stB RZ) (shapeC RZ)); [exact (D_sound CERT_D CERT_2) | exact CERT_C | apply shapeC_holes].
  Qed.
  Lemma B_sound : CERT_B_T -> CERT_C_T -> CERT_D_T -> CERT_2_T -> holes_stmt BSEGS BOTH LIM (hsA RZ) SINV argH HH (fs_seed_tmp fs tmp).
  Proof.
    intros CERT_B CERT_C CERT_D CERT_2.
    apply (seg_holes (hsA RZ) 10%nat (stA RZ) (hsA_one RZ)).
    apply (seg_sound (nxB RZ) (nxB_ge RZ) ITB ITB_ok (hsB RZ) FUEL BFUEL KC0 (planB RZ) (stA RZ) (shapeB RZ)); [exact (C_sound CERT_C CERT_D CERT_2) | exact CERT_B | apply shapeB_holes].
  Qed.

  (* [comment removed for export] *)
  Theorem both_boot_shape : CERT_A_T -> CERT_B_T -> CERT_C_T -> CERT_D_T -> CERT_2_T ->
    srealizes BSEGS (init_config BSEGS APC BPH sp brk0 mbase rdraw LIM INP)
              (sd HH t_nil E0a (fs_seed_tmp fs tmp) (shapeA RZ)).
  Proof.
    intros CERT_A CERT_B CERT_C CERT_D CERT_2.
    pose proof (B_sound CERT_B CERT_C CERT_D CERT_2) as HB.
    eapply both_startup; first [ exact IT0_ok | exact HB | exact HH_agree | exact HH_nil | exact CERT_A | eassumption ].
  Qed.

  (* [comment removed for export] *)
  Theorem both_boot : CERT_A_T -> CERT_B_T -> CERT_C_T -> CERT_D_T -> CERT_2_T ->
    srealizes BSEGS (init_config BSEGS APC BPH sp brk0 mbase rdraw LIM INP)
              (H E0a (fs_seed_tmp fs tmp)).
  Proof.
    intros CERT_A CERT_B CERT_C CERT_D CERT_2.
    eapply srz_conseq; [exact (both_boot_shape CERT_A CERT_B CERT_C CERT_D CERT_2) | apply sd_allH; apply shapeA_holes].
  Qed.
End Boot.
