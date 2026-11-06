(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec ShapeAlg SpinAlg AgentLib Scfg AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanSoundSums AsanInit AsanNodesIface AsanNodesAux AsanNodesMmA AsanNodesMmB AsanNodesStartX AsanNodesStartXInit AsanPopFree AsanSmear BothImages BothPlanImages Bo_code_102bcc_102df8 BoSmearCode SumsBothSpecs SumsBothClose.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import APSX.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs := None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.

Lemma XN0_sound : forall SEGS (SC : StepCfg) A nx0 LIMIT SINV argH FS0, @ext_stmt SEGS SC A nx0 LIMIT XN0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs cs' E R FULL model T _ _ H. discriminate H. Qed.
Lemma XE0_sound : forall SEGS (SC : StepCfg) A nx0 LIMIT SINV argH FS0, @emit_stmt SEGS SC A nx0 LIMIT XE0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
Lemma XB0_sound : forall SEGS (SC : StepCfg) A nx0 LIMIT SINV argH FS0, @ext2_stmt SEGS SC A nx0 LIMIT XB0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

(* [comment removed for export] *)
Fixpoint holes_only (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SCase _ _ a b | SAlt2 a b => holes_only a && holes_only b
  | _ => false
  end.

Lemma sd_holes_only : forall HOLES D E fs T s,
  (forall h, HOLES h E fs = T) -> holes_only s = true -> t_eq (sd HOLES D E fs s) T.
Proof.
  intros HOLES D E fs T s HT. induction s as [|c|fd ps s IH|a IHa b IHb|e mid a IHa b IHb|h|]; cbn [holes_only sd]; intros H; try discriminate.
  - apply andb_prop in H as [H1 H2]. intros tr. unfold t_alt2. specialize (IHa H1 tr). specialize (IHb H2 tr). tauto.
  - apply andb_prop in H as [H1 H2]. destruct (bv_unsigned (edenot E e) <=? mid); [exact (IHa H1) | exact (IHb H2)].
  - rewrite HT. intros tr. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section XAll.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable argv envp : list (list byte).
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variables uid hw : word.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  #[local] Notation SINV := (SINV0 BPH2 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 BPH2 sp rdraw argv envp uid hw).
  Let AH := argH0_high BPH2 sp rdraw argv envp uid hw Hsp Hva.
  Let AS := argH0_sp0 BPH2 sp rdraw argv envp uid hw.
  Let AA := argH0_agree BPH2 sp rdraw argv envp uid hw.
  Let SF := SINV0_frame BPH2 sp rdraw brk0 argv envp uid hw.
  Let SA := SINV0_agree BPH2 sp rdraw brk0 argv envp uid hw.

  (* [comment removed for export] *)
  Theorem asan_node_x_sound_all : forall x, x_stmt BSEGS2 BOTH_H NX0 AsanInit.LIMIT SINV argH FS0 x.
  Proof.
    intros [ | | | | | | | | | | | ].
    - exact (both_node_x_sound_XIMemset NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (both_node_x_sound_XIMemcpy NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (both_node_x_sound_XMemset NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (both_node_x_sound_XMemcpy NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (both_node_x_sound_XMemIsZero NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - eapply (init_x_sound_envscan BSEGS2 BOTH_H BPH2 both_wx both_in_hull both_hull_ok
                W_102c04 W_102c08 W_102c0c
                ltac:(cbn [x_envscan x_envscan_k BOTH_H]; lia)
                (fetch_lit _ _ _ _ eq_refl F_102c04) (fetch_lit _ _ _ _ eq_refl F_102c08) (fetch_lit _ _ _ _ eq_refl F_102c0c)
                ltac:(repeat split; reflexivity)
                D_102c04 D_102c08 D_102c0c
                sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV (fun E M H => H) SF).
    - eapply (init_x_sound_pnscan BSEGS2 BOTH_H BPH2 both_wx both_in_hull both_hull_ok
                W_102cc0 W_102cc4 W_102cc8 W_102ccc W_102cd0
                ltac:(cbn [x_pnscan x_pnscan_k BOTH_H]; lia)
                (fetch_lit _ _ _ _ eq_refl F_102cc0) (fetch_lit _ _ _ _ eq_refl F_102cc4) (fetch_lit _ _ _ _ eq_refl F_102cc8)
                (fetch_lit _ _ _ _ eq_refl F_102ccc) (fetch_lit _ _ _ _ eq_refl F_102cd0)
                ltac:(repeat split; reflexivity)
                D_102cc0 D_102cc4 D_102cc8 D_102ccc D_102cd0
                sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV (fun E M H => H) SF SA).
    - apply (init_x_sound_layout BSEGS2 BOTH_H BPH2 sp rdraw argv envp FS0 uid hw SINV).
    - exact (both_node_x_sound_XIStrncpy NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (both_node_x_sound_XPopFree NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - (* [comment removed for export] *)
      intros args cs cs' E R FULL model T _ _ H. discriminate H.
    - (* [comment removed for export] *)
      exact (x_sound_smear BSEGS2 BOTH_H NX0 AsanInit.LIMIT SINV argH FS0 both_wx both_in_hull both_hull_ok SF both_smear_x both_smear_fwa).
  Qed.
End XAll.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition level_certified (KC0 BFUEL FUEL : nat) (HSs HSt : nat -> option acs) : Prop :=
  forall h ch, HSs h = Some ch ->
    exists (rs : list (Z * nat)) (p : plan) (s : shape),
      check BSEGS2 (mk_itab_ranges BSEGS2 rs) BOTH_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSt KC0 BFUEL FUEL None ch p = COk s
      /\ holes_only s = true.

Section Startup.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variable abterm : bool.
  Variable vasz : VaSize.
  Variable urandom : InputStream.   (* [comment removed for export] *)
  Variable tmp : Fs.Fs.             (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS2 brk0.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

  #[local] Notation SINV := (SINV0 BPH2 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 BPH2 sp rdraw argv envp uid hw).
  #[local] Notation E0a := (E0 BPH2 sp rdraw brk0 argv envp uid hw).
  #[local] Notation LIM := AsanInit.LIMIT.
  #[local] Notation INP := (AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urandom tmp).
  #[local] Notation FS := (fs_seed_tmp fs tmp).

  (* [comment removed for export] *)
  Variable RANGES : list (Z * nat).          (* [comment removed for export] *)
  Variables HS1 HSC HSA HSF : nat -> option acs.
  Variable plan1 : plan.
  Variable shape1 : shape.
  Variables KC0 BFUEL FUEL : nat.
  #[local] Notation IT := (mk_itab_ranges BSEGS2 RANGES).
  Hypothesis cert1 : check BSEGS2 IT BOTH_H NX0 LIM XN0 XE0 XB0 HS1 KC0 BFUEL FUEL None bhinit plan1 = COk shape1.
  Hypothesis shape1_holes : holes_only shape1 = true.
  #[local] Notation LEVEL := (level_certified KC0 BFUEL FUEL).
  Hypothesis cert2 : LEVEL HS1 HSC.
  Hypothesis cert3 : LEVEL HSC HSA.
  Hypothesis cert4 : LEVEL HSA HSF.

  (* [comment removed for export] *)
  Variable T : TSet.
  Hypothesis T_nil : T [].
  Definition HOLES (h : nat) (E : env) (fs' : Fs.Fs) : TSet := T.
  Hypothesis HOLESF_sound : holes_stmt BSEGS2 BOTH_H LIM HSF SINV argH HOLES FS.

  Let AH := argH0_high BPH2 sp rdraw argv envp uid hw Hsp Hva.
  Let AS := argH0_sp0 BPH2 sp rdraw argv envp uid hw.
  Let AA := argH0_agree BPH2 sp rdraw argv envp uid hw.
  Let SF := SINV0_frame BPH2 sp rdraw brk0 argv envp uid hw.
  Let SA := SINV0_agree BPH2 sp rdraw brk0 argv envp uid hw.
  (* [comment removed for export] *)
  Let SP := SINV0_pg BPH2 sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit SINV (fun E M H => H).

  (* [comment removed for export] *)
  Lemma both_check_sound : forall RS HS,
    holes_stmt BSEGS2 BOTH_H LIM HS SINV argH HOLES FS ->
    forall fuel bfuel p cs s,
      check BSEGS2 (mk_itab_ranges BSEGS2 RS) BOTH_H NX0 LIM XN0 XE0 XB0 HS KC0 bfuel fuel None cs p = COk s ->
      forall E R FULL model, cs_ok BSEGS2 BOTH_H LIM SINV argH FS E cs R FULL model ->
        srealizes BSEGS2 (cfg_of BSEGS2 R (pc cs) FULL model) (sd HOLES t_nil E (m_fs model) s).
  Proof.
    intros RS HS HS_sound fuel bfuel p cs s Hc E R FULL model HC.
    exact (check_sound BSEGS2 (mk_itab_ranges BSEGS2 RS) (itab_ranges_ok RS) BOTH_H NX0 LIM HS XN0 XE0 XB0
              both_wx both_in_hull both_hull_ok both_shadow_ok SINV argH AH E_SP0 AA SF SA
              HOLES (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => T_nil) (fun _ _ _ _ => eq_refl) FS KC0
              (AsanNodesMmB.node_sys_sound BSEGS2 BOTH_H NX0 LIM SINV argH FS both_res_len both_hull_ok both_shadow_ok AA SF SA AS E_SP0)
              (AsanNodesMmB.node_brk2_sound BSEGS2 BOTH_H NX0 LIM SINV argH FS both_in_hull both_hull_ok both_shadow_ok AH SF both_res_len both_res_cover AS)
              (node_mmap1_sound_OBL BSEGS2 BOTH_H NX0 LIM SINV argH FS both_in_hull both_res_len both_res_hull both_res_cover both_hull_ok both_shadow_ok AH AS E_SP0 AA SF SA SP)
              (node_mmapin1_sound_OBL BSEGS2 BOTH_H NX0 LIM SINV argH FS both_in_hull both_res_len both_res_hull both_res_cover both_hull_ok both_shadow_ok AH AS SF)
              (node_mprotect1_sound_OBL BSEGS2 BOTH_H NX0 LIM SINV argH FS both_in_hull both_res_len both_res_hull both_res_cover both_hull_ok both_shadow_ok AH AS SF)
              (node_mmapgaps_sound_OBL BSEGS2 BOTH_H NX0 LIM SINV argH FS both_in_hull both_res_len both_res_cover both_hull_ok both_shadow_ok AH AS E_SP0 AA SF SA SP)
              (AsanNodesMmB.node_exit_sound BSEGS2 BOTH_H LIM SINV argH FS)
              (asan_node_x_sound_all sp rdraw brk0 argv envp FS Hsp Hva Hve uid hw Hfit)
              (node_join_sound BSEGS2 BOTH_H NX0 LIM SINV argH FS)
              (XN0_sound _ _ _ _ _ _ _ _) (XE0_sound _ _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _ _)
              HS_sound
              (both_node_fillfz_sound NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS)   (* [comment removed for export] *)
              fuel bfuel None p cs s Hc E R FULL model t_nil HC I eq_refl).
  Qed.

  (* [comment removed for export] *)
  Lemma level_sound : forall HSs HSt, LEVEL HSs HSt ->
    holes_stmt BSEGS2 BOTH_H LIM HSt SINV argH HOLES FS -> holes_stmt BSEGS2 BOTH_H LIM HSs SINV argH HOLES FS.
  Proof.
    intros HSs HSt CERT HSt_sound h ch Hh E R FULL model HC. destruct (CERT h ch Hh) as (rs & p & s & Hc & Hho). unfold HOLES.
    eapply srz_conseq; [exact (both_check_sound rs HSt HSt_sound FUEL BFUEL p ch s Hc E R FULL model HC)|].
    apply sd_holes_only; [intros; reflexivity | exact Hho].
  Qed.

  Lemma HOLESA_sound : holes_stmt BSEGS2 BOTH_H LIM HSA SINV argH HOLES FS.
  Proof. exact (level_sound HSA HSF cert4 HOLESF_sound). Qed.
  Lemma HOLESC_sound : holes_stmt BSEGS2 BOTH_H LIM HSC SINV argH HOLES FS.
  Proof. exact (level_sound HSC HSA cert3 HOLESA_sound). Qed.
  Lemma HOLES1_sound : holes_stmt BSEGS2 BOTH_H LIM HS1 SINV argH HOLES FS.
  Proof. exact (level_sound HS1 HSC cert2 HOLESC_sound). Qed.

  Theorem as_startup_shape :
    srealizes BSEGS2 (init_config BSEGS2 AsanUbsan.M.init_pc BPH2 sp brk0 mbase rdraw LIM INP) (sd HOLES t_nil E0a FS shape1).
  Proof.
    pose proof both_img_facts as IMG.
    rewrite (init_cfg_eq BSEGS2 BOTH_H BPH2 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urandom tmp
               AsanUbsan.M.init_pc eq_refl).
    pose proof (init_cs_ok BSEGS2 BOTH_H BPH2 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urandom tmp
                  IMG Hsp Hbrk Hva Hve Hfit Huid Hhw) as HC.
    pose proof (both_check_sound RANGES HS1 HOLES1_sound FUEL BFUEL plan1 bhinit shape1 cert1 _ _ _ _ HC) as R.
    replace (m_fs (model0 BSEGS2 sp brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urandom tmp)) with FS in R by reflexivity.
    exact R.
  Qed.

  Theorem as_startup_T :
    srealizes BSEGS2 (init_config BSEGS2 AsanUbsan.M.init_pc BPH2 sp brk0 mbase rdraw LIM INP) T.
  Proof.
    eapply srz_conseq; [exact as_startup_shape|]. apply sd_holes_only; [intros; reflexivity | exact shape1_holes].
  Qed.
End Startup.
