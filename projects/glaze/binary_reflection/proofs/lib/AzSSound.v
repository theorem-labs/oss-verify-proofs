(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanPlacement OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanCeil.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AzSymExec3 AzSymExec3Sound AzSymRun3 AzPlanCore AzPlan AzAPS AzAPS2 AzGPS AzSIface.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AzSLibE AzSMmLib AzSMmA AzSMmB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module SPS.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Sound.
Variable SEGS : list Segment.
(* [comment removed for export] *)
Variable RR : shape_rel SEGS.
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable HS : nat -> option acs.
Variable XN : nat -> list expr -> acs -> option acs.
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Variable XA : nat -> list expr -> acs -> option (acs * acs).
Variable XT : nat -> list expr -> acs -> option (Z * list spiece * Z).   (* [comment removed for export] *)
Variable KC : nat.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Variable FXOK : GPS.FX -> Prop.
Variable HOLES : nat -> env -> Fs.Fs -> TSet.
(* [comment removed for export] *)
Variable D : TSet.

Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                            (segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok A.
Hypothesis SHADOW_ok : shadow_ok A.
(* [comment removed for export] *)
Variable ISP : expr.
Hypothesis ISP_vars : expr_vars_lt nx0 ISP = true.
Hypothesis argH_high : forall E (a : word), argH E a = true -> sp_window_lo <= bv_unsigned a /\ bv_unsigned (edenot E ISP) <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis HOLES_agree : forall h E E' fs, env_agree nx0 E E' -> HOLES h E fs = HOLES h E' fs.
Hypothesis HOLES_nil : forall h E fs, HOLES h E fs [].
(* [comment removed for export] *)
Hypothesis HOLES_same : forall h E fs, HOLES h E fs = HOLES 0%nat E fs.
Hypothesis D_nil : D [].
Hypothesis RES_tile : forall z, img_lo A <= z < img_hi A -> in_ivs z (segments_reserved SEGS) = true.
Hypothesis HULL_ne : img_lo A < img_hi A.
(* [comment removed for export] *)
Hypothesis RUN_sound : GPS.RUN_SOUND SEGS FXOK.

#[local] Notation CSOK := (APS.cs_ok SEGS A LIMIT SINV argH ISP FS0).
#[local] Notation HID := (APS.hid A argH).
#[local] Notation MR := (APS.Mr A argH).
#[local] Notation ALLOW := (APS.allowA A).
#[local] Notation cfg := (GPS.cfgF SEGS).
#[local] Notation SD := (APS.sd HOLES D).
Variable HOWN : bool.   (* [comment removed for export] *)
#[local] Notation CHECK := (AP.checkA SEGS IT A nx0 LIMIT ISP XN XE XB XA XT HS KC HOWN).

(* [comment removed for export] *)
Hypothesis node_sys_sound : forall y, SIF.sys_stmt SEGS RR A nx0 LIMIT SINV argH ISP FS0 FXOK y.
Hypothesis node_brk2_sound : SIF.brk2_stmt SEGS RR A nx0 LIMIT SINV argH ISP FS0 FXOK.
Hypothesis node_brk2x_sound : SIF.brk2x_stmt SEGS RR A nx0 LIMIT SINV argH ISP FS0 FXOK.   (* [comment removed for export] *)
Hypothesis node_exit_sound : SIF.exit_stmt SEGS RR A LIMIT SINV argH ISP FS0 FXOK.
Hypothesis node_mmap2_sound : SIF.mm2_stmt SEGS RR A nx0 LIMIT SINV argH ISP FS0 FXOK (node_mmap2 A nx0 LIMIT ISP).
Hypothesis node_mmap2h_sound : SIF.mm2_stmt SEGS RR A nx0 LIMIT SINV argH ISP FS0 FXOK (node_mmap2h A nx0 LIMIT ISP).   (* [comment removed for export] *)
Hypothesis node_mprotect2_sound : SIF.mm2_stmt SEGS RR A nx0 LIMIT SINV argH ISP FS0 FXOK (node_mprotect2 A LIMIT).
Hypothesis node_mmapin_sound : forall hole : bool, SIF.mm3_stmt SEGS RR A nx0 LIMIT SINV argH ISP FS0 FXOK (node_mmapin A LIMIT hole).
Hypothesis node_mmapw_sound : forall lo hi, SIF.mmw_stmt SEGS RR A nx0 LIMIT SINV argH ISP FS0 FXOK (node_mmapw A nx0 LIMIT ISP lo hi).
Hypothesis node_ext_sound : SIF.ext_stmt SEGS RR A nx0 LIMIT XN SINV argH ISP FS0 FXOK.
Hypothesis node_emit_sound : SIF.emit_stmt SEGS RR A nx0 LIMIT XE SINV argH ISP FS0 FXOK.
Hypothesis node_ext2_sound : SIF.ext2_stmt SEGS RR A nx0 LIMIT XB SINV argH ISP FS0 FXOK.
Hypothesis node_alt2_sound : SIF.alt2_stmt SEGS RR A nx0 LIMIT XA SINV argH ISP FS0 FXOK.
Hypothesis HS_sound : SIF.holes_stmt SEGS RR A LIMIT HS SINV argH ISP FS0 FXOK HOLES.

(* [comment removed for export] *)
Let HS' : nat -> option acs := fun _ => None.
Let XN' : nat -> list expr -> acs -> option acs := fun _ _ _ => None.
Let XE' : nat -> list expr -> acs -> option (Z * list spiece * acs) := fun _ _ _ => None.
Let XB' : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.

(* [comment removed for export] *)
Let cs_ok_agree' := APS.cs_ok_agree SEGS A nx0 LIMIT SINV argH ISP ISP_vars argH_agree SINV_agree FS0.
Let cs_ok_frame' := APS.cs_ok_frame SEGS A LIMIT SINV argH ISP SINV_frame FS0.
Let cs_ok_set_kn' := APS.cs_ok_set_kn SEGS A LIMIT SINV argH ISP FS0.
Let cs_gc_ok' := APS.cs_gc_ok SEGS A LIMIT SINV argH ISP FS0.
Let hid_agree' := APS.hid_agree A nx0 argH argH_agree.
Let A_wf_allowA' := APS.A_wf_allowA A.
Let lazy_cover_cs' := APS.lazy_cover_cs SEGS A LIMIT HULL_ok SINV argH ISP FS0.
Let H_off_segments_cs' := APS.H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH ISP argH_high.
Let sd_agree' := APS.sd_agree nx0 HOLES HOLES_agree D.
Let sd_has_nil' := APS.sd_has_nil HOLES HOLES_nil D.
Let sd_salt2' := APS.sd_salt2 nx0 HS' XN' XE' XB' HOLES HOLES_nil D.
Let check_vars' := APS.check_vars SEGS IT A nx0 LIMIT HS XN XE XB ISP KC XA XT HOWN.


(* [comment removed for export] *)
Fixpoint splan_ok (p : plan) : bool :=
  match p with
  | PRun _ k | PFact _ k | PJoin _ _ _ k | PForget _ k | PDropRange _ _ k | PGcKeep _ k | PBump _ k | PHavoc _ k
  | PHavocBig _ k | PFresh _ _ _ k | PExt _ _ k | PEmit _ _ k | PIntro _ _ k | PDiamond _ _ k | PRename _ k | PCompact k
  | PAbstractCell _ _ k | PHavocWords _ k | PRespell _ _ k | PFactVia _ _ _ _ k | PFactLe _ _ _ k | PFactScale _ _ _ k
  | PFactLeR _ _ _ _ k | PFactR _ _ _ _ k | PFactLeX _ _ _ _ _ k | PFactX _ _ _ _ _ k
  | PShDisj _ _ _ _ k | PSys _ k | PFog _ _ k | PFogNew _ _ k | PGhost _ _ k | PUnvis _ _ k | PHavocBrk _ _ k => splan_ok k
  | PSplit _ _ k1 k2 | PCase2 _ _ k1 k2 | PCaseDisj _ _ k1 k2 | PExt2 _ _ k1 k2 | PBranch k1 k2 | PBranchP k1 k2 | PCaseReg _ _ k1 k2
  | PAlt2 _ _ k1 k2 | PBrk2 k1 k2 => splan_ok k1 && splan_ok k2
  | PMmap _ kb | PMprotect _ kb => splan_ok kb       (* [comment removed for export] *)
  | PMmapIn _ kb _ | PMmapInH _ kb _ => splan_ok kb  (* [comment removed for export] *)
  | PContra | PHandoff _ | PExit | PHandoffW _ _ | PContraH _ => true
  | PSpin => false          (* [comment removed for export] *)
  | PTerm _ _ => false      (* [comment removed for export] *)
  | PLoop _ _ _ _ _ _ | PLoopM _ _ _ _ | PNext | PNextW _ | PVia _ _ _ _ _ | PViaM _ _ _ _ | PMerge _ | PMergeW _ _
  | PX _ _ _ | PUnreach => false
  | PMmapW _ _ _ kl kh => splan_ok kl && splan_ok kh   (* [comment removed for export] *)
  | PMmapH _ kb => splan_ok kb                          (* [comment removed for export] *)
  end%bool.


(* [comment removed for export] *)
Lemma sr_msteps_restricted_T : forall (H : word -> bool) (HH : H_off_segments SEGS H) AA ms msr' model T,
  lazy_cover H (m_vm_lazy model) AA -> A_wf AA -> MInv AA model ->
  m_halted model = None ->
  msteps SEGS (restrict H ms) msr' ->
  (forall model', MInv AA model' -> same_but_materialized model model' -> hclean H msr' ->
                  RR (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  RR (mkCfg ms model) T.
Proof.
  intros H HH AA ms msr' model T.
  exact (AsVocab.AsanAcct.rz_msteps_restricted' SEGS H HH SEGS_wx (fun c => RR c T)
           (fun c c' Hn Hr => sr_silent1 SEGS RR c c' T Hn Hr) AA ms msr' model).
Qed.

Lemma run_block_sound : forall gb bfuel stops cs cs' E fx R M model T,
  (nx0 <= gb)%nat ->
  run_block SEGS IT gb HOWN KC bfuel stops cs = Some cs' -> CSOK E cs R M model -> FXOK fx ->
  (forall E' fx' R' M' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' M' model' -> FXOK fx' -> m_fs model' = m_fs model ->
      RR (cfg fx' R' (pc cs') M' model') T) ->
  RR (cfg fx R (pc cs) M model) T.
Proof.
  intros gb bfuel stops cs cs' E fx R M model T Hgb Hrb HC HF Hk.
  rewrite run_block_eq in Hrb. unfold run_block_ref in Hrb.
  destruct (fresh_ok gb cs) eqn:Hf0; [|discriminate].
  pose proof (APS.fresh_ok_mono nx0 gb cs Hgb Hf0) as Hf.
  destruct (APS.fresh_ok_parts nx0 cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK. pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) as HR.
  unfold kn in HK, Fkn. unfold nxt in Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle, Hk.
  destruct (a_ss cs) as [p sr log k nx rsv] eqn:Hss.
  cbn [s_know s_regs s_pc s_next] in Hrb, HR, HK, Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle, Hk.
  set (ss' := sym_execTX SEGS IT KC bfuel true stops (SS p sr [] k nx)) in Hrb.
  match type of Hrb with (if negb ?o then _ else _) = _ => destruct o eqn:Hown; [|discriminate] end. cbn [negb] in Hrb.
  destruct (carry (s_log ss') (s_know ss') []) as [[kn' scs] hs] eqn:Hc.
  destruct scs; [|discriminate]. injection Hrb as <-.
  rewrite sr_vars_lt_eq in Fsr. rewrite kn_vars_lt_eq in Fkn.
  (* [comment removed for export] *)
  set (H := APS.hid A argH E cs model).
  set (Mr0 := APS.Mr A argH E cs model M). assert (HMr0 : Mr0 = mrestrict H M) by reflexivity.
  pose proof (A_wf_allowA' E cs) as Hwf.
  pose proof (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hminv.
  pose proof (H_off_segments_cs' E cs model) as HH.
  pose proof (lazy_cover_cs' E cs R M model HC) as Hcov.
  (* [comment removed for export] *)
  pose proof (RUN_sound IT KC bfuel stops p sr k nx E Mr0 R fx IT_ok HR HK Fsr Fkn HF) as HX.
  cbn zeta in HX. fold ss' in HX. destruct HX as (E' & R' & fx' & Hag & Hle & HR' & Hlf & HK' & HF' & Hms).
  assert (Hagc : env_agree (nxt cs) E E') by (unfold nxt; rewrite Hss; exact Hag).
  pose proof (cs_ok_agree' E E' cs R M model Hagc Hf HC) as HC'.
  unfold GPS.cfgF, pc. rewrite Hss. cbn [a_ss s_pc].
  assert (Hms' : msteps SEGS (restrict H (GPS.mkstF fx R (Z_to_bv 64 p) M (seg_rom SEGS)))
                             (GPS.mkstF fx' R' (Z_to_bv 64 (s_pc ss')) (mem_denot E' Mr0 (s_log ss')) (seg_rom SEGS))).
  { unfold restrict, GPS.mkstF, mkst. cbn. rewrite <- HMr0. exact Hms. }
  eapply (sr_msteps_restricted_T H HH (ALLOW E cs)); [exact Hcov | exact Hwf | exact Hminv | exact (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hms' |].
  intros model' Hminv' Hsame Hclean.
  assert (HKc : know_ok SEGS E' (mem_denot E' Mr0 (s_log ss')) kn').
  { eapply (carry_sound SEGS E' Mr0); [exact Hc | exact Hlf | exact HK' | constructor]. }
  specialize (Hk E' fx' R' (munrestrict H M (mem_denot E' Mr0 (s_log ss'))) model' (conj (APS.env_agree_le _ _ _ _ Hag Fle) Hag)).
  unfold GPS.cfgF, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk.
  unfold unrestrict. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom GPS.mkstF mkst].
  pose proof (same_but_materialized_frame model model' Hsame) as SF.
  apply Hk; [| exact HF' | apply SF].
  assert (Hhid' : APS.hid A argH E' cs model = H).
  { unfold H. apply (hid_agree' nx); [exact Hag | exact Fle | exact Fallow]. }
  eapply cs_ok_frame'; [exact HC' | exact Hsame | | exact HR' | reflexivity | | |].
  - (* [comment removed for export] *)
    rewrite (APS.allowA_agree A nx E E' cs Hag Fallow). exact Hminv'.
  - (* [comment removed for export] *)
    cbn [mk_ss s_know]. unfold APS.Mr. rewrite Hhid'.
    replace (mrestrict H (munrestrict H M (mem_denot E' Mr0 (s_log ss')))) with (mem_denot E' Mr0 (s_log ss')); [exact HKc|].
    apply functional_extensionality. intros a. unfold mrestrict, munrestrict. destruct (H a) eqn:EH; [|reflexivity].
    pose proof (Hclean a EH) as HX. cbn [ms_mem GPS.mkstF mkst] in HX. exact HX.
  - (* [comment removed for export] *)
    intros a Ha. rewrite Hhid' in Ha. unfold munrestrict. fold H in Ha. rewrite Ha. reflexivity.
  - (* [comment removed for export] *)
    intros a Hdef. unfold munrestrict. destruct (H a) eqn:EH; [exact Hdef|].
    destruct (GPS.mem_denot_same_or_some E' Mr0 (s_log ss') a) as [Hs|[b Hb]]; [|rewrite Hb; discriminate].
    rewrite Hs, HMr0. unfold mrestrict. rewrite EH. exact Hdef.
Qed.

Lemma run_block_gc_sound : forall gb bfuel stops cs cs' E fx R M model T,
  (nx0 <= gb)%nat ->
  run_block_gc SEGS IT gb HOWN KC bfuel stops cs = Some cs' -> CSOK E cs R M model -> FXOK fx ->
  (forall E' fx' R' M' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' M' model' -> FXOK fx' -> m_fs model' = m_fs model ->
      RR (cfg fx' R' (pc cs') M' model') T) ->
  RR (cfg fx R (pc cs) M model) T.
Proof.
  intros gb bfuel stops cs cs' E fx R M model T Hgb H HC HF Hk. unfold run_block_gc in H.
  destruct (run_block SEGS IT gb HOWN KC bfuel stops cs) as [cs1|] eqn:Hrb; [|discriminate]. injection H as <-.
  eapply run_block_sound; [exact Hgb | exact Hrb | exact HC | exact HF |].
  intros E' fx' R' M' model' Hag HC1 HF1 Hfs. rewrite <- (APS.pc_cs_gc gb cs1).
  apply (Hk E' fx' R' M' model'); [exact Hag | apply cs_gc_ok'; exact HC1 | exact HF1 | exact Hfs].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma split_sound : forall cs e mid lo hi E R M model,
  CSOK E cs R M model -> brange (kn cs) e = Some (lo, hi) ->
  (bv_unsigned (edenot E e) <= mid -> CSOK E (set_kn cs (KRange e lo mid :: kn cs)) R M model)
  /\ (mid < bv_unsigned (edenot E e) -> CSOK E (set_kn cs (KRange e (mid + 1) hi :: kn cs)) R M model).
Proof.
  intros cs e mid lo hi E R M model HC Hr.
  pose proof (APS.brange_sound SEGS E _ (kn cs) e lo hi (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) Hr) as Hb.
  split; intros Hm; (apply cs_ok_set_kn'; [exact HC|]); constructor; [cbn [kentry_ok]; lia | exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) | cbn [kentry_ok]; lia | exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC)].
Qed.

(* [comment removed for export] *)
Lemma sd_holes_only_eq : forall E fs s, holes_only s = true -> t_eq (SD E fs s) (HOLES 0%nat E fs).
Proof.
  intros E fs s. induction s; cbn [holes_only APS.sd]; intros H; try discriminate.
  - (* [comment removed for export] *) apply andb_prop in H as [H1 H2]. intros tr. unfold t_alt2.
    repeat match goal with IH : holes_only ?x = true -> t_eq _ _, HH : holes_only ?x = true |- _ => pose proof (IH HH tr); clear IH end. tauto.
  - apply andb_prop in H as [H1 H2]. destruct (Z.leb _ _); [apply IHs1; exact H1 | apply IHs2; exact H2].
  - rewrite (HOLES_same h). intros tr. tauto.
Qed.
Lemma shape_eqv_transfer : forall E fs s1 s2 c,
  AP.shape_eqv s1 s2 = true -> RR c (SD E fs s2) -> RR c (SD E fs s1).
Proof.
  intros E fs s1 s2 c H HR. unfold AP.shape_eqv in H. apply orb_prop in H as [H|H].
  - apply APS.shape_eqb_eq in H. subst. exact HR.
  - apply andb_prop in H as [H1 H2]. eapply (sr_conseq SEGS RR); [exact HR|].
    intros tr. pose proof (sd_holes_only_eq E fs s1 H1 tr). pose proof (sd_holes_only_eq E fs s2 H2 tr). tauto.
Qed.

(* [comment removed for export] *)
Lemma fresh_sound : forall r logc base cs cs' E R FULL model,
  CSOK E cs R FULL model -> node_fresh nx0 cs r logc base = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ CSOK E' cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros r logc base cs cs' E R FULL model HC Hn. rewrite node_fresh_eq in Hn. unfold node_fresh_ref in Hn.
  set (b := match base with Some b => b | None => ELit 0 end) in Hn.
  set (e := esub (reg cs r) b) in Hn.
  destruct (Nat.ltb 0 r && Nat.ltb r 32 && Z.leb 0 logc && Z.leb logc 40 && Z.leb logc (ealign (kn cs) e)
            && AP.expr_vars_lt (nxt cs) b && AP.expr_vars_lt (nxt cs) e && fresh_ok nx0 cs)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hc Hfresh]. apply andb_prop in Hc as [Hc Hve]. apply andb_prop in Hc as [Hc Hvb].
  apply andb_prop in Hc as [Hc Hal]. apply andb_prop in Hc as [Hc H40]. apply andb_prop in Hc as [Hc H0].
  apply andb_prop in Hc as [Hr0 Hr32].
  apply Nat.ltb_lt in Hr0. apply Nat.ltb_lt in Hr32. apply Z.leb_le in H0. apply Z.leb_le in H40. apply Z.leb_le in Hal.
  destruct (xlo2 (kn cs) e) as [lo|] eqn:Hlo; [|discriminate].
  destruct (xhi2 (kn cs) e) as [hi|] eqn:Hhi; [|discriminate].
  injection Hn as <-.
  set (c := 2 ^ logc) in *. set (v := nxt cs) in *.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (APS.xlo2_sound SEGS E _ (kn cs) e lo HK Hlo) as Hlo'.
  pose proof (APS.xhi2_sound SEGS E _ (kn cs) e hi HK Hhi) as Hhi'.
  destruct (ealign_sound SEGS E _ (kn cs) e HK) as [Hea Hdiv].
  assert (Hc : 0 < c) by (unfold c; apply Z.pow_pos_nonneg; lia).
  assert (Hc2 : c <= 2 ^ 40) by (unfold c; apply Z.pow_le_mono_r; lia).
  assert (Hcd : (c | bv_unsigned (edenot E e))%Z).
  { eapply Z.divide_trans; [|exact Hdiv]. unfold c. apply pow2_divide_le. lia. }
  destruct Hcd as [q Hq].
  pose proof (u64_range (edenot E e)) as Hue.
  assert (Hq0 : 0 <= q) by nia.
  assert (Hq64 : q < 2 ^ 64) by nia.
  set (a := Z_to_bv 64 q). set (E' := APS.ext1 E v a).
  assert (Hag : env_agree v E E') by apply APS.ext1_agree.
  destruct (APS.fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (cs_ok_agree' E E' cs R FULL model Hag Hfresh HC) as HC'.
  assert (Hev : edenot E' e = edenot E e) by (symmetry; eapply (APS.edenot_agree' v); [exact Hag | exact Hve]).
  assert (Hbv : edenot E' b = edenot E b) by (symmetry; eapply (APS.edenot_agree' v); [exact Hag | exact Hvb]).
  assert (Hrv : edenot E' (reg cs r) = edenot E (reg cs r)).
  { symmetry. eapply (APS.edenot_agree' v); [exact Hag|]. unfold reg. apply APS.nth_sr_vars_lt; [exact Fsr | lia]. }
  assert (Hne : edenot E' (escale c (EVar v)) = edenot E e).
  { unfold escale. rewrite mkMd_denot. cbn [edenot]. unfold E'. rewrite APS.ext1_at. unfold a.
    apply bv_eq. rewrite u_mul64. rewrite (APS.u_small c) by lia. rewrite (APS.u_small q) by lia. rewrite Z.mod_small by nia. lia. }
  assert (He_sem : edenot E e = alu64 ALU_SUB (edenot E (reg cs r)) (edenot E b)) by (unfold e, esub; apply mkAlu_denot).
  exists E'. split; [split; [eapply APS.env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  assert (HKf : know_ok SEGS E' (MR E' cs model FULL)
            ((KRange (EVar v) ((lo + c - 1) / c) (hi / c) :: KRange (esub e (escale c (EVar v))) 0 0
               :: residue_fact (kn cs) e (escale c (EVar v)))
             ++ kn cs)).
  { apply Forall_app. split; [|exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC')].
    constructor; [|constructor].
    - cbn [kentry_ok edenot]. unfold E' at 1 2. rewrite APS.ext1_at. unfold a. rewrite APS.u_small by lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      split; nia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - cbn [kentry_ok]. unfold esub. rewrite !mkAlu_denot, !Hne, !Hev.
      rewrite !u_sub64. rewrite Z.sub_diag, Z.mod_0_l by lia. lia.
    - eapply (APS.residue_fact_sound SEGS E E' _ _ (kn cs) e); [exact HK | exact Hne |].
      intros e1 s1 Hd1. symmetry. eapply (APS.edenot_agree' v); [exact Hag | exact (APS.deand_vars v e e1 s1 Hd1 Hve)]. }
  destruct HC'; constructor; cbn [bump set_reg add_kn set_kn with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset]; try assumption.
  - apply APS.regs_ok_respell; [exact co_regs0 | lia |].
    unfold eadd. rewrite mkAlu_denot, Hne, Hbv. fold (reg cs r). rewrite Hrv, He_sem.
    apply bv_eq. rewrite u_add64, u_sub64. pose proof (u64_range (edenot E (reg cs r))). pose proof (u64_range (edenot E b)).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite Zplus_mod_idemp_r. replace (bv_unsigned (edenot E b) + (bv_unsigned (edenot E (reg cs r)) - bv_unsigned (edenot E b))) with (bv_unsigned (edenot E (reg cs r))) by lia.
    rewrite Z.mod_small by lia. reflexivity.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - reflexivity.
Qed.

(* [comment removed for export] *)
Lemma join_sound : forall b off n cs cs' E R FULL model,
  CSOK E cs R FULL model -> node_join SEGS cs b off n = Some cs' -> CSOK E cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros b off n cs cs' E R FULL model HC Hn. unfold node_join in Hn.
  destruct (Nat.leb 1 n && Nat.leb n 8 && flat_x (kn cs) b off (ELit (Z.of_nat n)))%bool eqn:Ht; [|discriminate].
  apply andb_prop in Ht as [Ht Hfx]. apply andb_prop in Ht as [H1 H8]. apply Nat.leb_le in H1. apply Nat.leb_le in H8.
  destruct (kread_bytes SEGS n (kn cs) b off) as [zs|] eqn:Hr; [|discriminate].
  apply (f_equal (fun o => match o with Some x => x | None => cs end)) in Hn. cbn in Hn. subst cs'.
  split; [|reflexivity].
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (APS.flat_x_sound SEGS E _ (kn cs) b off (ELit (Z.of_nat n)) HK Hfx) as (F1 & F2 & F3).
  rewrite edenot_lit, u64_lit in F2, F3 by lia.
  destruct (AzAPS2.kread_bytes_sound SEGS E _ (kn cs) n b off zs HK Hr F1 F2) as [bs (Lb & Mb & Rb)].
  unfold add_kn. apply cs_ok_set_kn'; [exact HC|]. constructor; [|exact HK].
  cbn [kentry_ok]. split; [exact H8|]. split; [unfold flat; lia|].
  rewrite (AzAPS2.rdn_of_bytes1 SEGS _ n (adenot E (SA b off)) bs Lb).
  - f_equal. cbn [edenot]. unfold word_to_le_bytes. rewrite <- Mb, zbytes_map.
    pose proof (bytes_le_to_Z_bound bs) as Bb. rewrite Lb in Bb.
    assert (2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    rewrite u64_lit by lia. rewrite <- Lb. symmetry. apply AzAPS2.Z_to_le_bytes_to_Z.
  - rewrite (flat_u E _ (Z.of_nat n)); [lia | unfold flat; lia].
  - intros j Hj. rewrite (flat_u E _ (Z.of_nat n)) by (unfold flat; lia). exact (Rb j Hj).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma allowA_ptsubst : forall E th T cs,
  map (ptsubst th) (a_vis T) = a_vis cs -> map (ptsubst th) (a_ghost T) = a_ghost cs ->
  ALLOW E cs = ALLOW (GPS.tenv E th) T.
Proof.
  intros E th T cs Hv Hg. unfold APS.allowA. rewrite <- Hv, <- Hg, <- map_app, !flat_map_concat_map, map_map.
  f_equal. apply map_ext. intros [b n]. unfold APS.allow1, ptsubst, APS.sh_lo, APS.sh_hi, APS.uE. cbn [fst snd].
  rewrite !GPS.tsubst_denot. reflexivity.
Qed.

Lemma in_allow_ptsubst : forall E th T cs,
  map (ptsubst th) (a_vis T) = a_vis cs -> APS.in_allow A E cs = APS.in_allow A (GPS.tenv E th) T.
Proof.
  intros E th T cs Hv. apply functional_extensionality. intros z. unfold APS.in_allow, APS.in_vis, APS.in_sh. rewrite <- Hv.
  rewrite !APS.existsb_map'. f_equal; f_equal; apply functional_extensionality; intros [b n];
    unfold ptsubst, APS.sh_lo, APS.sh_hi, APS.uE; cbn [fst snd]; rewrite !GPS.tsubst_denot; reflexivity.
Qed.

Lemma in_ghost_ptsubst : forall E th T cs,
  map (ptsubst th) (a_ghost T) = a_ghost cs -> APS.in_ghost E cs = APS.in_ghost (GPS.tenv E th) T.
Proof.
  intros E th T cs Hg. apply functional_extensionality. intros z. unfold APS.in_ghost. rewrite <- Hg.
  rewrite !APS.existsb_map'. f_equal. apply functional_extensionality. intros [b n].
  unfold ptsubst, APS.uE. cbn [fst snd]. rewrite !GPS.tsubst_denot. reflexivity.
Qed.

Lemma hid_ptsubst : forall lo E th T cs model,
  th_id_below lo th = true -> (nx0 <= lo)%nat ->
  map (ptsubst th) (a_vis T) = a_vis cs -> HID E cs model = HID (GPS.tenv E th) T model.
Proof.
  intros lo E th T cs model Hid Hlo Hv. apply functional_extensionality. intros a. unfold APS.hid, APS.vis.
  rewrite (in_allow_ptsubst E th T cs Hv).
  rewrite (argH_agree E (GPS.tenv E th) a); [reflexivity|].
  eapply APS.env_agree_le; [apply GPS.th_id_below_agree; exact Hid | exact Hlo].
Qed.

Lemma entails_t_soundS : forall lo E cs T th R M model,
  CSOK E cs R M model -> entails_t A lo cs T th = true -> (nx0 <= lo)%nat ->
  exists E', env_agree lo E E' /\ CSOK E' T R M model /\ pc T = pc cs.
Proof.
  intros lo E cs T th R M model HC H Hlo. apply APC.entails_t_imp in H. unfold APC.entails_t_ref in H.   (* [comment removed for export] *)
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  rename H into Hpc. apply Z.eqb_eq in Hpc.
  match goal with Hl : match s_log (a_ss T) with _ => _ end = true |- _ => rename Hl into HL; destruct (s_log (a_ss T)) eqn:HL'; [clear HL; rename HL' into HL|discriminate] end.
  match goal with Hl : match s_resv (a_ss T) with _ => _ end = true |- _ => clear Hl end.
  match goal with Hl : th_id_below lo th = true |- _ => rename Hl into Hid end.
  match goal with Hl : regs_ent _ _ _ _ = true |- _ => rename Hl into Hregs end.
  match goal with Hl : kn_ent _ _ _ = true |- _ => rename Hl into Hkn end.
  match goal with Hl : list_eqb pair_eqb (map (ptsubst th) (a_vis T)) _ = true |- _ => apply (APS.list_eqb_eq pair_eqb APS.pair_eqb_eq) in Hl; rename Hl into Hvis end.
  match goal with Hl : list_eqb pair_eqb (map (ptsubst th) (a_ghost T)) _ = true |- _ => apply (APS.list_eqb_eq pair_eqb APS.pair_eqb_eq) in Hl; rename Hl into Hgh end.
  match goal with Hl : expr_eqb (tsubst th (a_brk T)) _ = true |- _ => apply expr_eqb_eq in Hl; rename Hl into Hbrk end.
  match goal with Hl : list_eqb amap_eqb (a_maps cs) (a_maps T) = true |- _ => apply (APS.list_eqb_eq amap_eqb APS.amap_eqb_eq) in Hl; rename Hl into Hmaps end.
  match goal with Hl : afd_eqb (ftsubst th (a_fd T)) _ = true |- _ => apply APS.afd_eqb_eq in Hl; rename Hl into Hfd end.
  match goal with Hl : Bool.eqb (a_tidset cs) (a_tidset T) = true |- _ => apply Bool.eqb_prop in Hl; rename Hl into Htid end.
  match goal with Hl : maps_vars_lt lo (a_maps T) = true |- _ => rename Hl into Hmv end.
  match goal with Hl : Z.leb (a_totsz cs) (a_totsz T) = true |- _ => apply Z.leb_le in Hl; rename Hl into Htot end.
  match goal with Hl : Z.leb (a_ylo T) (a_ylo cs) = true |- _ => apply Z.leb_le in Hl; rename Hl into Hylo end.
  match goal with Hl : Z.leb (a_eager cs) (a_eager T) = true |- _ => apply Z.leb_le in Hl; rename Hl into Heag end.
  match goal with Hl : Z.leb (a_abytes cs) (a_abytes T) = true |- _ => apply Z.leb_le in Hl; rename Hl into Haby end.
  set (E' := GPS.tenv E th). exists E'.
  assert (Hag : env_agree lo E E') by (apply GPS.th_id_below_agree; exact Hid).
  assert (Hag0 : env_agree nx0 E E') by (eapply APS.env_agree_le; [exact Hag | exact Hlo]).
  assert (HH : HID E' T model = HID E cs model) by (symmetry; eapply hid_ptsubst; eassumption).
  assert (HA : ALLOW E' T = ALLOW E cs) by (symmetry; apply allowA_ptsubst; assumption).
  assert (HG : APS.in_ghost E' T = APS.in_ghost E cs) by (symmetry; apply in_ghost_ptsubst; assumption).
  assert (HMD : forall m, In m (a_maps T) -> amap_den E' m = amap_den E m).
  { intros m Hin. exact (ext_in_map (APS.maps_den_agree lo E E' (a_maps T) Hag Hmv) m Hin). }
  split; [exact Hag|]. split; [|symmetry; exact Hpc].
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as CK.
  destruct HC. rewrite Hmaps in *. constructor; try assumption.
  - (* [comment removed for export] *)
    apply (proj1 (GPS.regs_ok_tsubst E th (s_regs (a_ss T)) R)).
    destruct (GPS.regs_ent_sound SEGS E _ (kn cs) _ _ 0%nat CK Hregs) as [Hlen Hn].
    intros r. rewrite (co_regs0 r). unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0; [reflexivity|]. symmetry. apply Hn.
    intros Hz. cbn in Hz. unfold ridx in Hz. unfold bv_eqb in Hr0. apply Z.eqb_neq in Hr0. apply Hr0.
    change (bv_unsigned r = 0). pose proof (u5_range r). lia.
  - (* [comment removed for export] *)
    unfold APS.Mr. fold E'. rewrite HH. apply (proj1 (GPS.know_ok_ktsubst SEGS E th _ (kn T))).
    eapply (GPS.kn_ent_sound SEGS A SEGS_in_hull HULL_ok); [exact CK | exact Hkn].
  - (* [comment removed for export] *) unfold E'. apply GPS.fds_ok_ftsubst. rewrite Hfd. assumption.
  - (* [comment removed for export] *) rewrite <- Htid. assumption.
  - (* [comment removed for export] *) eapply (APS.maps_match_agree lo E E'); [exact Hag | exact Hmv | assumption].
  - (* [comment removed for export] *) eapply (APS.holes_agree lo E E'); [exact Hag | exact Hmv |]. eapply APS.holes_mono; [eassumption | exact Hylo].
  - (* [comment removed for export] *) apply Forall_forall. intros m Hin Hk. rewrite (HMD m Hin). exact (proj1 (Forall_forall _ _) co_none0 m Hin Hk).
  - (* [comment removed for export] *) apply Forall_forall. intros m Hin Hk a Ha.
    pose proof (HMD m Hin) as X. unfold amap_den in X. injection X as X1 X2. rewrite X1, X2 in Ha.
    exact (proj1 (Forall_forall _ _) co_kinds0 m Hin Hk a Ha).
  - (* [comment removed for export] *) lia.
  - (* [comment removed for export] *) rewrite co_isp0. eapply (APS.edenot_agree' nx0); [exact Hag0 | exact ISP_vars].
  - (* [comment removed for export] *) unfold E'. rewrite <- GPS.tsubst_denot, Hbrk. assumption.
  - (* [comment removed for export] *) lia.
  - (* [comment removed for export] *) rewrite HA. lia.
  - (* [comment removed for export] *) rewrite HA. assumption.
  - (* [comment removed for export] *) intros a. unfold APS.Mr in *. rewrite HH, HG. exact (co_zero0 a).
  - (* [comment removed for export] *) intros a Ha. destruct (co_lazysub0 a Ha) as (m & Hin & Hk & Hr). exists m.
    split; [exact Hin|]. split; [exact Hk|]. rewrite (HMD m Hin). exact Hr.
  - (* [comment removed for export] *) eapply SINV_agree; [exact Hag0 | assumption].
  - (* [comment removed for export] *) apply Forall_forall. intros m Hin Hk. rewrite (HMD m Hin). exact (proj1 (Forall_forall _ _) co_etok0 m Hin Hk).
Qed.

Lemma entails_tw_soundS : forall lo hi w E cs T R M model,
  CSOK E cs R M model -> entails_tw A lo hi w cs T = true -> (nx0 <= lo)%nat ->
  exists E', env_agree lo E E' /\ CSOK E' T R M model /\ pc T = pc cs.
Proof. intros lo hi w E cs T R M model HC H Hlo. rewrite entails_tw_eq in H. apply andb_prop in H as [_ H]. eapply entails_t_soundS; eassumption. Qed.




(* [comment removed for export] *)

Section Main.
(* [comment removed for export] *)
Variable fuel bfuel : nat.
Hypothesis IH : forall p cs s, splan_ok p = true -> CHECK bfuel fuel None cs p = COk s ->
  forall E fx R M model, CSOK E cs R M model -> FXOK fx ->
  RR (cfg fx R (pc cs) M model) (SD E (m_fs model) s).

(* [comment removed for export] *)
Lemma cont_agree : forall k cs cs' s E model,
  splan_ok k = true -> CHECK bfuel fuel None cs' k = COk s ->
  forall E' fx' R' M' model',
    env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' M' model' -> FXOK fx' -> m_fs model' = m_fs model ->
    RR (cfg fx' R' (pc cs') M' model') (SD E (m_fs model) s).
Proof.
  intros k cs cs' s E model Hk Hc E' fx' R' M' model' [Hag _] HC' HF' Hfs.
  rewrite (sd_agree' E E' (m_fs model) s Hag (check_vars' _ _ _ _ _ _ Hc)), <- Hfs.
  exact (IH k cs' s Hk Hc E' fx' R' M' model' HC' HF').
Qed.

Lemma check_branch_sound : forall cs p e k1 k2 s E fx R M model,
  splan_ok k1 = true -> splan_ok k2 = true ->
  check_branch (CHECK bfuel fuel None) cs p e k1 k2 = COk s ->
  CSOK E cs R M model -> FXOK fx ->
  RR (cfg fx R (pc cs) M model) (SD E (m_fs model) s).
Proof.
  intros cs p e k1 k2 s E fx R M model Hk1 Hk2 Hc HC HF.
  assert (SAME : forall k cs' s', splan_ok k = true -> CHECK bfuel fuel None cs' k = COk s' -> CSOK E cs' R M model ->
            pc cs' = pc cs -> RR (cfg fx R (pc cs) M model) (SD E (m_fs model) s')).
  { intros k cs' s' Hk Hk' HC' Hpc. rewrite <- Hpc. exact (IH k cs' s' Hk Hk' E fx R M model HC' HF). }
  unfold check_branch in Hc. rewrite ?brangeM_fe, ?branch_probes_eq in Hc. cbv beta iota zeta in Hc.
  destruct (brange (kn cs) e) as [[lo hi]|] eqn:Hr; [|discriminate].
  destruct (Z.leb lo 0 && Z.ltb 0 hi)%bool.
  2: { cbn [negb] in Hc. destruct (Z.leb hi 0); [exact (SAME k1 _ s Hk1 Hc HC eq_refl) | exact (SAME k2 _ s Hk2 Hc HC eq_refl)]. }
  cbn [negb] in Hc. cbv zeta in Hc.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (APS.brange_sound SEGS E _ (kn cs) e lo hi HK Hr) as Hb.
  assert (HCl : bv_unsigned (edenot E e) <= 0 -> CSOK E (set_kn cs (KRange e lo 0 :: probe_lin_facts (kn cs) e false ++ kn cs)) R M model).
  { intros Hm. apply cs_ok_set_kn'; [exact HC|]. constructor; [cbn [kentry_ok]; lia|]. apply Forall_app. split; [|exact HK].
    apply (GPS.probe_lin_facts_sound SEGS E _ (kn cs) e false HK). exact Hm. }
  assert (HCr : 0 < bv_unsigned (edenot E e) -> CSOK E (set_kn cs (KRange e (0 + 1) hi :: probe_lin_facts (kn cs) e true ++ kn cs)) R M model).
  { intros Hm. apply cs_ok_set_kn'; [exact HC|]. constructor; [cbn [kentry_ok]; lia|]. apply Forall_app. split; [|exact HK].
    apply (GPS.probe_lin_facts_sound SEGS E _ (kn cs) e true HK). lia. }
  destruct (kn_contra (kn (set_kn cs (KRange e lo 0 :: probe_lin_facts (kn cs) e false ++ kn cs)))) eqn:Hc1.
  { destruct (Z.leb_spec (bv_unsigned (edenot E e)) 0) as [Hle|Hgt].
    - exfalso. exact (APS.kn_contra_sound SEGS E _ _ (co_know _ _ _ _ _ _ _ _ _ _ _ _ (HCl Hle)) Hc1).
    - exact (SAME k2 _ s Hk2 Hc (HCr ltac:(lia)) eq_refl). }
  destruct (kn_contra (kn (set_kn cs (KRange e (0 + 1) hi :: probe_lin_facts (kn cs) e true ++ kn cs)))) eqn:Hc2.
  { destruct (Z.leb_spec (bv_unsigned (edenot E e)) 0) as [Hle|Hgt].
    - exact (SAME k1 _ s Hk1 Hc (HCl Hle) eq_refl).
    - exfalso. exact (APS.kn_contra_sound SEGS E _ _ (co_know _ _ _ _ _ _ _ _ _ _ _ _ (HCr ltac:(lia))) Hc2). }
  destruct (CHECK bfuel fuel None (set_kn cs (KRange e lo 0 :: probe_lin_facts (kn cs) e false ++ kn cs)) k1) as [s1|] eqn:H1; [|discriminate].
  destruct (CHECK bfuel fuel None (set_kn cs (KRange e (0+1) hi :: probe_lin_facts (kn cs) e true ++ kn cs)) k2) as [s2|] eqn:H2; [|discriminate].
  destruct (AP.shape_eqv s1 s2) eqn:Hse; [|discriminate]. injection Hc as <-.
  destruct (Z.leb_spec (bv_unsigned (edenot E e)) 0) as [Hle|Hgt].
  + exact (SAME k1 _ s1 Hk1 H1 (HCl Hle) eq_refl).
  + eapply shape_eqv_transfer; [exact Hse|]. exact (SAME k2 _ s2 Hk2 H2 (HCr ltac:(lia)) eq_refl).
Qed.

(* [comment removed for export] *)
Lemma case2_sound : forall cs ce cmid ck1 ck2 p s E fx R M model,
  splan_ok ck1 = true -> splan_ok ck2 = true ->
  match brange (kn cs) ce with
  | Some (lo, hi) =>
      if negb (Z.leb lo cmid && Z.ltb cmid hi)%bool then (if Z.leb hi cmid then CHECK bfuel fuel None cs ck1 else CHECK bfuel fuel None cs ck2) else
      if (Z.leb lo cmid && Z.ltb cmid hi)%bool then
        let cs1 := set_kn cs (KRange ce lo cmid :: kn cs) in
        let cs2 := set_kn cs (KRange ce (cmid + 1) hi :: kn cs) in
        if kn_contra (kn cs1) then CHECK bfuel fuel None cs2 ck2
        else if kn_contra (kn cs2) then CHECK bfuel fuel None cs1 ck1
        else
        match CHECK bfuel fuel None cs1 ck1 with
        | COk s1 =>
            match CHECK bfuel fuel None cs2 ck2 with
            | COk s2 => if AP.shape_eqv s1 s2 then COk s1 else CErr 6 p cs
            | err => err
            end
        | err => err
        end
      else CErr 3 p cs
  | None => CErr 3 p cs
  end = COk s ->
  CSOK E cs R M model -> FXOK fx ->
  RR (cfg fx R (pc cs) M model) (SD E (m_fs model) s).
Proof.
  intros cs ce cmid ck1 ck2 p s E fx R M model Hk1 Hk2 Hc HC HF.
  assert (SAME : forall k cs' s', splan_ok k = true -> CHECK bfuel fuel None cs' k = COk s' -> CSOK E cs' R M model ->
            pc cs' = pc cs -> RR (cfg fx R (pc cs) M model) (SD E (m_fs model) s')).
  { intros k cs' s' Hk Hk' HC' Hpc. rewrite <- Hpc. exact (IH k cs' s' Hk Hk' E fx R M model HC' HF). }
  destruct (brange (kn cs) ce) as [[lo hi]|] eqn:Hr; [|discriminate].
  destruct (Z.leb lo cmid && Z.ltb cmid hi)%bool.
  2: { cbn [negb] in Hc. destruct (Z.leb hi cmid); [exact (SAME ck1 _ s Hk1 Hc HC eq_refl) | exact (SAME ck2 _ s Hk2 Hc HC eq_refl)]. }
  cbn [negb] in Hc. cbv zeta in Hc.
  destruct (split_sound cs ce cmid lo hi E R M model HC Hr) as [HCl HCr].
  destruct (kn_contra (kn (set_kn cs (KRange ce lo cmid :: kn cs)))) eqn:Hc1.
  { destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
    - exfalso. exact (APS.kn_contra_sound SEGS E _ _ (co_know _ _ _ _ _ _ _ _ _ _ _ _ (HCl Hle)) Hc1).
    - exact (SAME ck2 _ s Hk2 Hc (HCr ltac:(lia)) eq_refl). }
  destruct (kn_contra (kn (set_kn cs (KRange ce (cmid + 1) hi :: kn cs)))) eqn:Hc2.
  { destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
    - exact (SAME ck1 _ s Hk1 Hc (HCl Hle) eq_refl).
    - exfalso. exact (APS.kn_contra_sound SEGS E _ _ (co_know _ _ _ _ _ _ _ _ _ _ _ _ (HCr ltac:(lia))) Hc2). }
  destruct (CHECK bfuel fuel None (set_kn cs (KRange ce lo cmid :: kn cs)) ck1) as [s1|] eqn:H1; [|discriminate].
  destruct (CHECK bfuel fuel None (set_kn cs (KRange ce (cmid+1) hi :: kn cs)) ck2) as [s2|] eqn:H2; [|discriminate].
  destruct (AP.shape_eqv s1 s2) eqn:Hse; [|discriminate]. injection Hc as <-.
  destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
  + exact (SAME ck1 _ s1 Hk1 H1 (HCl Hle) eq_refl).
  + eapply shape_eqv_transfer; [exact Hse|]. exact (SAME ck2 _ s2 Hk2 H2 (HCr ltac:(lia)) eq_refl).
Qed.

(* [comment removed for export] *)
Lemma handoff_sound : forall cs p h w s E fx R M model,
  check_handoff A nx0 HS None cs p h w = COk s -> CSOK E cs R M model -> FXOK fx ->
  RR (cfg fx R (pc cs) M model) (SD E (m_fs model) s).
Proof.
  intros cs p h w s E fx R M model Hc HC HF. unfold check_handoff in Hc.
  destruct (HS h) as [ch|] eqn:Hh; [|discriminate].
  change (if entails A cs ch then true else entails_tw A nx0 (nxt ch) w cs ch) with (entails A cs ch || entails_tw A nx0 (nxt ch) w cs ch)%bool in Hc.   (* [comment removed for export] *)
  destruct (entails A cs ch || entails_tw A nx0 (nxt ch) w cs ch)%bool eqn:He; [|discriminate].
  injection Hc as <-. cbn [lc_xmode APS.sd].
  apply orb_prop in He as [He|He].
  - destruct (APS.entails_sound SEGS A LIMIT SINV argH ISP FS0 (GPS.kn_ent_sound SEGS A SEGS_in_hull HULL_ok) E cs ch R M model HC He) as [HC' Hpc].
    pose proof (HS_sound h ch Hh E fx R M model HC' HF) as HR. rewrite Hpc in HR. exact HR.
  - destruct (entails_tw_soundS nx0 (nxt ch) w E cs ch R M model HC He ltac:(lia)) as (E' & Hag & HC' & Hpc).
    pose proof (HS_sound h ch Hh E' fx R M model HC' HF) as HR. rewrite Hpc in HR.
    rewrite (HOLES_agree h E E' (m_fs model) Hag). exact HR.
Qed.
End Main.

Theorem check_soundS : forall fuel bfuel p cs s,
  splan_ok p = true ->
  CHECK bfuel fuel None cs p = COk s ->
  forall E fx R M model, CSOK E cs R M model -> FXOK fx ->
  RR (cfg fx R (pc cs) M model) (SD E (m_fs model) s).
Proof.
  induction fuel as [|fuel IH]; intros bfuel p cs s Hsp Hc E fx R M model HC HF; [discriminate|].
  cbn [AP.checkA] in Hc. rewrite ?fact_okM_fe, ?factle_okM_fe, ?factvia_okM_fe in Hc. cbn [negb] in Hc.
  assert (CONT : forall k cs' s', splan_ok k = true -> CHECK bfuel fuel None cs' k = COk s' ->
            forall E' fx' R' M' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' M' model' -> FXOK fx' ->
            m_fs model' = m_fs model -> RR (cfg fx' R' (pc cs') M' model') (SD E (m_fs model) s')).
  { intros k cs' s' Hk Hk'. exact (cont_agree fuel bfuel (IH bfuel) k cs cs' s' E model Hk Hk'). }
  assert (SAME : forall k cs' s', splan_ok k = true -> CHECK bfuel fuel None cs' k = COk s' -> CSOK E cs' R M model ->
            RR (cfg fx R (pc cs') M model) (SD E (m_fs model) s')).
  { intros k cs' s' Hk Hk' HC'. exact (IH bfuel k cs' s' Hk Hk' E fx R M model HC' HF). }
  destruct p as [stops k|e mid k1 k2|ce cmid ck1 ck2|db1 db2 dk1 dk2|sb1 sn1 sb2 sn2 k| |K k|jb joff jn k|ixs k|db dn k|gws k|bm k|hrs k|hbK k|r logc fb k|y k|ma mb|ia ib ic|qa qb|ka kb|x args k|xid xargs k|eid eargs k|bid bargs kb1 kb2|lJ lN linv lw lbody lk| |h| | |fi fsz fk|gi gsz gk|gb gn gk2|ub un uk|hlo hhi hk|ilo ihi ik|djp drs dk|rnm rnk|cpk|vj vjs vlo vka vk|mj|ab an ak|hws hwk|rsr rse rsk|iha ihb ihc|nw|mwj mww|bkf bkt|crr crmid crk1 crk2|fve fvv fvlo fvhi fvk|hwh hww|fle flb flhi flk|fse fsc fshi fsk|flr flo flb2 flh2 flk2|frr fro frlo frhi frk|fxr fxph fxe fxb fxhi fxk|gxr gxph gxe gxlo gxhi gxk|cth|mJ mN malts mw|wj walts wlo wka|bpz bpnz|aid aargs aka akb| |wlo whi wkr wkl wkh|hka hkb|tid targs];
    cbn [splan_ok] in Hsp; try discriminate Hsp.
  - (* [comment removed for export] *)
    destruct (run_block_gc SEGS IT nx0 HOWN KC bfuel (stops ++ STOPS A) cs) as [cs1|] eqn:Hrb; [|discriminate].
    eapply run_block_gc_sound; [apply Nat.le_refl | exact Hrb | exact HC | exact HF |].
    intros E' fx' R' M' model' Hag HC1 HF1 Hfs. exact (CONT k cs1 s Hsp Hc E' fx' R' M' model' Hag HC1 HF1 Hfs).
  - (* [comment removed for export] *)
    apply andb_prop in Hsp as [Hsp1 Hsp2].
    destruct (AP.expr_vars_lt nx0 e) eqn:Hv; [|discriminate].
    destruct (brange (kn cs) e) as [[lo hi]|] eqn:Hr; [|discriminate].
    destruct (Z.leb lo mid && Z.ltb mid hi)%bool.
    2: { destruct (Z.leb_spec hi mid) as [Hle|Hgt]; [exact (SAME k1 _ s Hsp1 Hc HC) | exact (SAME k2 _ s Hsp2 Hc HC)]. }
    destruct (CHECK bfuel fuel None (set_kn cs (KRange e lo mid :: kn cs)) k1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel None (set_kn cs (KRange e (mid+1) hi :: kn cs)) k2) as [s2|] eqn:H2; [|discriminate].
    injection Hc as <-. cbn [APS.sd].
    destruct (split_sound cs e mid lo hi E R M model HC Hr) as [HCl HCr].
    destruct (Z.leb_spec (bv_unsigned (edenot E e)) mid) as [Hle|Hgt].
    + exact (SAME k1 _ s1 Hsp1 H1 (HCl Hle)).
    + exact (SAME k2 _ s2 Hsp2 H2 (HCr ltac:(lia))).
  - (* [comment removed for export] *)
    apply andb_prop in Hsp as [Hsp1 Hsp2].
    exact (case2_sound fuel bfuel (IH bfuel) cs ce cmid ck1 ck2 _ s E fx R M model Hsp1 Hsp2 Hc HC HF).
  - (* [comment removed for export] *)
    apply andb_prop in Hsp as [Hsp1 Hsp2].
    destruct (node_casedisj cs db1 db2) as [[csa csb]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel None csa dk1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel None csb dk2) as [s2|] eqn:H2; [|discriminate].
    destruct (AP.shape_eqv s1 s2) eqn:Hse; [|discriminate]. injection Hc as <-.
    destruct (APS.casedisj_sound SEGS A LIMIT SINV argH ISP FS0 cs db1 db2 csa csb E R M model HC Hn) as [[HC' Hpc]|[HC' Hpc]]; rewrite <- Hpc.
    + exact (SAME dk1 _ s1 Hsp1 H1 HC').
    + eapply shape_eqv_transfer; [exact Hse|]. exact (SAME dk2 _ s2 Hsp2 H2 HC').
  - (* [comment removed for export] *)
    destruct (node_shdisj A cs sb1 sn1 sb2 sn2) as [cs1|] eqn:Hn; [|discriminate].
    destruct (APS.shdisj_sound SEGS A LIMIT SHADOW_ok SINV argH ISP FS0 cs sb1 sn1 sb2 sn2 cs1 E R M model HC Hn) as [HC1 Hpc].
    rewrite <- Hpc. exact (SAME k _ s Hsp Hc HC1).
  - (* [comment removed for export] *)
    destruct (kn_contra (kn cs)) eqn:Hk; [|discriminate]. exfalso.
    exact (APS.kn_contra_sound SEGS E _ (kn cs) (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) Hk).
  - (* [comment removed for export] *)
    destruct (fact_ok (kn cs) K) eqn:Hfk; [|discriminate].
    exact (SAME k _ s Hsp Hc (APS.fact_sound SEGS A LIMIT SINV argH ISP FS0 E cs R M model K HC Hfk)).
  - (* [comment removed for export] *)
    destruct (node_join SEGS cs jb joff jn) as [cs1|] eqn:Hn; [|discriminate].
    destruct (join_sound jb joff jn cs cs1 E R M model HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME k _ s Hsp Hc HC1).
  - (* [comment removed for export] *)
    exact (SAME k _ s Hsp Hc (APS.forget_sound SEGS A LIMIT SINV argH ISP FS0 E cs R M model ixs HC)).
  - (* [comment removed for export] *)
    assert (Hpc : pc (node_droprange cs db dn) = pc cs) by (unfold node_droprange; destruct (split_lit db); reflexivity).
    rewrite <- Hpc. exact (SAME k _ s Hsp Hc (APS.droprange_sound SEGS A LIMIT SINV argH ISP FS0 E cs R M model db dn HC)).
  - (* [comment removed for export] *)
    rewrite <- (APS.pc_set_kn cs (kn_keep (kn cs) gws)).
    refine (SAME k _ s Hsp Hc _). apply cs_ok_set_kn'; [exact HC|]. unfold kn_keep. apply APS.know_ok_filter. exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC).
  - (* [comment removed for export] *)
    destruct (node_bump cs bm) as [cs1|] eqn:Hn; [|discriminate].
    destruct (APS.bump_sound SEGS A LIMIT SINV argH ISP FS0 E cs R M model bm cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME k _ s Hsp Hc HC1).
  - (* [comment removed for export] *)
    destruct (node_havoc nx0 cs hrs) as [cs1|] eqn:Hn; [|discriminate].
    destruct (APS.havoc_sound SEGS A nx0 LIMIT SINV argH ISP ISP_vars argH_agree SINV_agree FS0 E cs R M model hrs cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT k cs1 s Hsp Hc E' fx R M model Hag HC1 HF eq_refl).
  - (* [comment removed for export] *)
    destruct (node_havocbig nx0 cs hbK) as [cs1|] eqn:Hn; [|discriminate].
    destruct (APS.havocbig_sound SEGS A nx0 LIMIT SINV argH ISP ISP_vars argH_agree SINV_agree FS0 E cs R M model hbK cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT k cs1 s Hsp Hc E' fx R M model Hag HC1 HF eq_refl).
  - (* [comment removed for export] *)
    destruct (node_fresh nx0 cs r logc fb) as [cs1|] eqn:Hn; [|discriminate].
    destruct (fresh_sound r logc fb cs cs1 E R M model HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT k cs1 s Hsp Hc E' fx R M model Hag HC1 HF eq_refl).
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_sys A nx0 y cs) as [cs1|] eqn:Hn; [|discriminate].
    eapply (node_sys_sound y cs cs1 E fx R M model); [exact HC | exact HF | exact Hec | exact Hn |].
    exact (CONT k cs1 s Hsp Hc).
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_mmap2 A nx0 LIMIT ISP cs) as [[csa csb]|] eqn:Hn; [|discriminate].
    eapply (node_mmap2_sound cs csa csb E fx R M model); [exact HC | exact HF | exact Hec | exact Hn |].
    exact (CONT mb csb s Hsp Hc).
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_mmapin A LIMIT false cs) as [[[csa csb] cscs]|] eqn:Hn; [|discriminate].
    eapply (node_mmapin_sound false cs csa csb cscs E fx R M model); [exact HC | exact HF | exact Hec | exact Hn |].
    exact (CONT ib csb s Hsp Hc).
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_mprotect2 A LIMIT cs) as [[csa csb]|] eqn:Hn; [|discriminate].
    eapply (node_mprotect2_sound cs csa csb E fx R M model); [exact HC | exact HF | exact Hec | exact Hn |].
    exact (CONT qb csb s Hsp Hc).
  - (* [comment removed for export] *)
    apply andb_prop in Hsp as [Hsp1 Hsp2].
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_brk2w A LIMIT ISP cs) as [[[csa csb] w]|] eqn:Hnw; [|discriminate].
    destruct (CHECK bfuel fuel None csa ka) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel None csb kb) as [sb|] eqn:H2; [|discriminate].
    destruct (AP.shape_eqv sa sb) eqn:Hw; [|discriminate].
    injection Hc as <-.
    assert (EQV : t_eq (SD E (m_fs model) sa) (SD E (m_fs model) sb)).
    { unfold AP.shape_eqv in Hw. apply orb_prop in Hw as [Hw|Hw].
      - apply APS.shape_eqb_eq in Hw. subst. apply t_eq_refl.
      - apply andb_prop in Hw as [Hw1 Hw2]. intros tr.
        pose proof (sd_holes_only_eq E (m_fs model) sa Hw1 tr). pose proof (sd_holes_only_eq E (m_fs model) sb Hw2 tr). tauto. }
    eapply (sr_conseq SEGS RR); [| apply sd_salt2'; exact D_nil].
    destruct (node_brk2w_cases A LIMIT ISP cs csa csb w Hnw) as [[-> Hn]|[-> Hn]].
    + eapply (node_brk2_sound cs csa csb E fx R M model); [exact HC | exact HF | exact Hec | exact Hn | exact EQV | |].
      * exact (CONT ka csa sa Hsp1 H1).
      * exact (CONT kb csb sb Hsp2 H2).
    + apply (sr_conseq _ RR _ (SD E (m_fs model) sa)); [| intros tr; unfold t_alt2; pose proof (EQV tr); tauto].
      eapply (node_brk2x_sound cs csa csb E fx R M model); [exact HC | exact HF | exact Hec | exact Hn | apply sd_has_nil'; exact D_nil | |].
      * exact (CONT ka csa sa Hsp1 H1).
      * intros E' fx' R' M' model' Hag HC' HF' Hfs. apply (sr_conseq _ RR _ (SD E (m_fs model) sb)); [| intros tr; pose proof (EQV tr); tauto].
        exact (CONT kb csb sb Hsp2 H2 E' fx' R' M' model' Hag HC' HF' Hfs).
  - (* [comment removed for export] *)
    destruct (XN xid xargs cs) as [cs1|] eqn:Hn; [|discriminate].
    eapply (node_ext_sound xid xargs cs cs1 E fx R M model); [(apply sd_has_nil'; exact D_nil) | exact HC | exact HF | reflexivity | exact Hn |].
    exact (CONT k cs1 s Hsp Hc).
  - (* [comment removed for export] *)
    destruct (XE eid eargs cs) as [[[fd ps] cs1]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel None cs1 k) as [s1|] eqn:H1; [|discriminate]. injection Hc as <-. cbn [APS.sd].
    change (APS.Wp E fd ps) with (GPS.Wp E fd ps).
    eapply (node_emit_sound eid eargs cs fd ps cs1 E fx R M model); [exact HC | exact HF | exact Hn | (apply sd_has_nil'; exact D_nil) |].
    exact (CONT k cs1 s1 Hsp H1).
  - (* [comment removed for export] *)
    apply andb_prop in Hsp as [Hsp1 Hsp2].
    destruct (XB bid bargs cs) as [[csa csb]|] eqn:Hn; [|discriminate].
    destruct (kn_contra (kn csa)) eqn:Hka.
    { eapply (node_ext2_sound bid bargs cs csa csb E fx R M model); [exact HC | exact HF | exact Hn | (apply sd_has_nil'; exact D_nil) | | exact (CONT kb2 csb s Hsp2 Hc)].
      intros E' fx' R' M' model' Hag HC' HF' Hfs. exfalso. exact (APS.kn_contra_sound SEGS E' _ _ (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC') Hka). }
    destruct (kn_contra (kn csb)) eqn:Hkb.
    { eapply (node_ext2_sound bid bargs cs csa csb E fx R M model); [exact HC | exact HF | exact Hn | (apply sd_has_nil'; exact D_nil) | exact (CONT kb1 csa s Hsp1 Hc) |].
      intros E' fx' R' M' model' Hag HC' HF' Hfs. exfalso. exact (APS.kn_contra_sound SEGS E' _ _ (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC') Hkb). }
    destruct (CHECK bfuel fuel None csa kb1) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel None csb kb2) as [sb|] eqn:H2; [|discriminate].
    destruct (AP.shape_eqv sa sb) eqn:Hse; [|discriminate]. injection Hc as <-.
    eapply (node_ext2_sound bid bargs cs csa csb E fx R M model); [exact HC | exact HF | exact Hn | (apply sd_has_nil'; exact D_nil)
      | exact (CONT kb1 csa sa Hsp1 H1) |].
    intros E' fx' R' M' model' Hag HC' HF' Hfs. eapply shape_eqv_transfer; [exact Hse|]. exact (CONT kb2 csb sb Hsp2 H2 E' fx' R' M' model' Hag HC' HF' Hfs).
  - (* [comment removed for export] *)
    exact (handoff_sound cs _ h [] s E fx R M model Hc HC HF).
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_exit cs) as [code|] eqn:Hn; [|discriminate]. injection Hc as <-. cbn [APS.sd].
    eapply node_exit_sound; eassumption.
  - (* [comment removed for export] *)
    destruct (node_fog cs fi fsz) as [cs1|] eqn:Hn; [|discriminate].
    destruct (APS.fog_sound SEGS A LIMIT SINV argH ISP FS0 E cs R M model fi fsz cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME fk _ s Hsp Hc HC1).
  - (* [comment removed for export] *)
    destruct (node_fognew cs gi gsz) as [cs1|] eqn:Hn; [|discriminate].
    destruct (APS.fognew_sound SEGS A LIMIT SINV argH ISP FS0 E cs R M model gi gsz cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME gk _ s Hsp Hc HC1).
  - (* [comment removed for export] *)
    destruct (node_ghost LIMIT cs gb gn) as [cs1|] eqn:Hn; [|discriminate].
    destruct (APS.ghost_sound SEGS A LIMIT SHADOW_ok SINV argH ISP FS0 E cs R M model gb gn cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME gk2 _ s Hsp Hc HC1).
  - (* [comment removed for export] *)
    destruct (node_unvis A cs ub un) as [cs1|] eqn:Hn; [|discriminate].
    destruct (APS.unvis_sound SEGS A LIMIT SHADOW_ok SINV argH ISP FS0 E cs R M model ub un cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME uk _ s Hsp Hc HC1).
  - (* [comment removed for export] *)
    destruct (node_havocbrk nx0 cs hlo hhi) as [cs1|] eqn:Hn; [|discriminate].
    destruct (APS.havocbrk_sound SEGS A nx0 LIMIT SINV argH ISP ISP_vars argH_agree SINV_agree FS0 E cs R M model hlo hhi cs1 HC Hn) as (E' & Hag & HC1 & Hpc).
    rewrite <- Hpc. exact (CONT hk cs1 s Hsp Hc E' fx R M model Hag HC1 HF eq_refl).
  - (* [comment removed for export] *)
    destruct (node_intro nx0 cs ilo ihi) as [cs1|] eqn:Hn; [|discriminate].
    destruct (APS.intro_sound SEGS A nx0 LIMIT SINV argH ISP ISP_vars argH_agree SINV_agree FS0 E cs R M model ilo ihi cs1 HC Hn) as (E' & Hag & HC1 & Hpc).
    rewrite <- Hpc. exact (CONT ik cs1 s Hsp Hc E' fx R M model Hag HC1 HF eq_refl).
  - (* [comment removed for export] *)
    destruct (branch_probe IT cs) as [e|] eqn:Hbp; [|discriminate].
    destruct (brange (kn cs) e) as [[lo hi]|] eqn:Hr; [|discriminate].
    destruct (Z.ltb hi 1 || Z.ltb 0 lo)%bool eqn:Hdec.
    { destruct (run_block_gc SEGS IT nx0 HOWN KC bfuel (djp :: STOPS A) cs) as [cs1|] eqn:Hrb; [|discriminate].
      destruct (Z.eqb (pc cs1) djp); [|discriminate].
      eapply run_block_gc_sound; [apply Nat.le_refl | exact Hrb | exact HC | exact HF |].
      intros E' fx' R' M' model' Hag HC1 HF1 Hfs. exact (CONT dk cs1 s Hsp Hc E' fx' R' M' model' Hag HC1 HF1 Hfs). }
    cbv zeta in Hc.
    destruct (run_block_gc SEGS IT nx0 HOWN KC bfuel (djp :: STOPS A) (set_kn cs (KRange e lo 0 :: kn cs))) as [ca|] eqn:Hra; [|discriminate].
    destruct (run_block_gc SEGS IT nx0 HOWN KC bfuel (djp :: STOPS A) (set_kn cs (KRange e 1 hi :: kn cs))) as [cb|] eqn:Hrb; [|discriminate].
    destruct (node_diamond_join A nx0 (nxt cs) djp drs ca cb) as [csj|] eqn:Hj; [|discriminate].
    destruct (split_sound cs e 0 lo hi E R M model HC Hr) as [HCl HCr].
    destruct (APS.diamond_join_sound SEGS A nx0 LIMIT SEGS_in_hull HULL_ok SINV argH ISP ISP_vars argH_agree SINV_agree FS0 (nxt cs) djp drs ca cb csj Hj) as [Ja Jb].
    destruct (Z.leb_spec (bv_unsigned (edenot E e)) 0) as [Hle|Hgt].
    + rewrite <- (APS.pc_set_kn cs (KRange e lo 0 :: kn cs)).
      eapply run_block_gc_sound; [apply Nat.le_refl | exact Hra | exact (HCl Hle) | exact HF |].
      intros E' fx' R' M' model' [Hag0 Hag1] HC1 HF1 Hfs.
      destruct (Ja E' R' M' model' HC1) as (E'' & [Hag2a Hag2b] & HC2 & Hpc2). rewrite <- Hpc2.
      change (env_agree (nxt cs) E E') in Hag1.
      exact (CONT dk csj s Hsp Hc E'' fx' R' M' model'
               (conj (APS.env_agree_trans _ _ _ _ Hag0 Hag2a) (APS.env_agree_trans _ _ _ _ Hag1 Hag2b)) HC2 HF1 Hfs).
    + rewrite <- (APS.pc_set_kn cs (KRange e 1 hi :: kn cs)).
      eapply run_block_gc_sound; [apply Nat.le_refl | exact Hrb | exact (HCr ltac:(lia)) | exact HF |].
      intros E' fx' R' M' model' [Hag0 Hag1] HC1 HF1 Hfs.
      destruct (Jb E' R' M' model' HC1) as (E'' & [Hag2a Hag2b] & HC2 & Hpc2). rewrite <- Hpc2.
      change (env_agree (nxt cs) E E') in Hag1.
      exact (CONT dk csj s Hsp Hc E'' fx' R' M' model'
               (conj (APS.env_agree_trans _ _ _ _ Hag0 Hag2a) (APS.env_agree_trans _ _ _ _ Hag1 Hag2b)) HC2 HF1 Hfs).
  - (* [comment removed for export] *)
    destruct (node_rename nx0 cs rnm) as [cs1|] eqn:Hn; [|discriminate].
    destruct (APS.rename_sound SEGS A nx0 LIMIT SINV argH ISP ISP_vars argH_agree SINV_agree FS0 nx0 E cs R M model rnm cs1 (Nat.le_refl _) HC Hn) as (E' & Hag & HC1 & Hpc).
    rewrite <- Hpc. rewrite (sd_agree' E E' (m_fs model) s Hag (check_vars' _ _ _ _ _ _ Hc)).
    exact (IH bfuel rnk cs1 s Hsp Hc E' fx R M model HC1 HF).
  - (* [comment removed for export] *)
    destruct (node_compact nx0 cs) as [cs1|] eqn:Hn; [|discriminate].
    destruct (APS.compact_sound SEGS A nx0 LIMIT SINV argH ISP ISP_vars argH_agree SINV_agree FS0 nx0 E cs R M model cs1 (Nat.le_refl _) HC Hn) as (E' & Hag & HC1 & Hpc).
    rewrite <- Hpc. rewrite (sd_agree' E E' (m_fs model) s Hag (check_vars' _ _ _ _ _ _ Hc)).
    exact (IH bfuel cpk cs1 s Hsp Hc E' fx R M model HC1 HF).
  - (* [comment removed for export] *)
    destruct (node_abstractcell A cs ab an) as [cs1|] eqn:Hn; [|discriminate].
    destruct (APS.abstractcell_sound SEGS A LIMIT SEGS_in_hull HULL_ok SINV argH ISP FS0 E cs R M model ab an cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME ak _ s Hsp Hc HC1).
  - (* [comment removed for export] *)
    destruct (node_havocwords nx0 cs hws) as [cs1|] eqn:Hn; [|discriminate].
    destruct (APS.havocwords_sound SEGS A nx0 LIMIT SINV argH ISP ISP_vars argH_agree SINV_agree FS0 E cs R M model hws cs1 HC Hn) as (E' & Hag & HC1 & Hpc).
    rewrite <- Hpc. exact (CONT hwk cs1 s Hsp Hc E' fx R M model Hag HC1 HF eq_refl).
  - (* [comment removed for export] *)
    destruct (node_respell cs rsr rse) as [cs1|] eqn:Hn; [|discriminate].
    destruct (APS.respell_sound SEGS A LIMIT SINV argH ISP FS0 E cs R M model rsr rse cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME rsk _ s Hsp Hc HC1).
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_mmapin A LIMIT true cs) as [[[csa csb] cscs]|] eqn:Hn; [|discriminate].
    eapply (node_mmapin_sound true cs csa csb cscs E fx R M model); [exact HC | exact HF | exact Hec | exact Hn |].
    exact (CONT ihb csb s Hsp Hc).
  - (* [comment removed for export] *)
    apply andb_prop in Hsp as [Hsp1 Hsp2].
    destruct (branch_probe2 IT cs) as [[e pos]|] eqn:Hbp; [|discriminate]. cbv zeta in Hc.
    eapply (check_branch_sound fuel bfuel (IH bfuel)); [ | | exact Hc | exact HC | exact HF]; destruct pos; assumption.
  - (* [comment removed for export] *)
    apply andb_prop in Hsp as [Hsp1 Hsp2]. cbv zeta in Hc.
    exact (case2_sound fuel bfuel (IH bfuel) cs (reg cs crr) crmid crk1 crk2 _ s E fx R M model Hsp1 Hsp2 Hc HC HF).
  - (* [comment removed for export] *)
    destruct (factvia_ok (kn cs) fve fvv fvlo fvhi) eqn:Hfk; [|discriminate].
    refine (SAME fvk _ s Hsp Hc _). unfold add_kn. apply cs_ok_set_kn'; [exact HC|].
    constructor; [eapply GPS.factvia_ok_sound; [exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hfk] | exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC)].
  - (* [comment removed for export] *)
    exact (handoff_sound cs _ hwh hww s E fx R M model Hc HC HF).
  - (* [comment removed for export] *)
    destruct (factle_ok (kn cs) fle flb flhi) eqn:Hfk; [|discriminate].
    refine (SAME flk _ s Hsp Hc _). unfold add_kn. apply cs_ok_set_kn'; [exact HC|].
    constructor; [eapply GPS.factle_ok_sound; [exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hfk] | exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC)].
  - (* [comment removed for export] *)
    destruct (factscale_ok (kn cs) fse fsc fshi) eqn:Hfk; [|discriminate].
    refine (SAME fsk _ s Hsp Hc _). unfold add_kn. apply cs_ok_set_kn'; [exact HC|].
    constructor; [eapply GPS.factscale_ok_sound; [exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hfk] | exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC)].
  - (* [comment removed for export] *)
    cbv zeta in Hc. destruct (factle_ok (kn cs) (eaddz (reg cs flr) flo) flb2 flh2) eqn:Hfk; [|discriminate].
    refine (SAME flk2 _ s Hsp Hc _). unfold add_kn. apply cs_ok_set_kn'; [exact HC|].
    constructor; [eapply GPS.factle_ok_sound; [exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hfk] | exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC)].
  - (* [comment removed for export] *)
    cbv zeta in Hc. destruct (fact_ok (kn cs) (KRange (eaddz (reg cs frr) fro) frlo frhi)) eqn:Hfk; [|discriminate].
    refine (SAME frk _ s Hsp Hc _). exact (APS.fact_sound SEGS A LIMIT SINV argH ISP FS0 E cs R M model _ HC Hfk).
  - (* [comment removed for export] *)
    cbv zeta in Hc. destruct (factle_ok (kn cs) (APC.esubst fxph (reg cs fxr) fxe) (APC.esubst fxph (reg cs fxr) fxb) fxhi) eqn:Hfk; [|discriminate].
    refine (SAME fxk _ s Hsp Hc _). unfold add_kn. apply cs_ok_set_kn'; [exact HC|].
    constructor; [eapply GPS.factle_ok_sound; [exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hfk] | exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC)].
  - (* [comment removed for export] *)
    cbv zeta in Hc. destruct (fact_ok (kn cs) (KRange (APC.esubst gxph (reg cs gxr) gxe) gxlo gxhi)) eqn:Hfk; [|discriminate].
    refine (SAME gxk _ s Hsp Hc _). exact (APS.fact_sound SEGS A LIMIT SINV argH ISP FS0 E cs R M model _ HC Hfk).
  - (* [comment removed for export] *)
    destruct (kn_contra (kn cs)) eqn:Hk; [|discriminate]. exfalso.
    exact (APS.kn_contra_sound SEGS E _ (kn cs) (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) Hk).
  - (* [comment removed for export] *)
    apply andb_prop in Hsp as [Hsp1 Hsp2].
    destruct (branch_probe2 IT cs) as [[e pos]|] eqn:Hbp; [|discriminate].
    eapply (check_branch_sound fuel bfuel (IH bfuel)); [exact Hsp1 | exact Hsp2 | exact Hc | exact HC | exact HF].
  - (* [comment removed for export] *)
    apply andb_prop in Hsp as [Hsp1 Hsp2].
    destruct (XA aid aargs cs) as [[csa csb]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel None csa aka) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel None csb akb) as [sb|] eqn:H2; [|discriminate].
    injection Hc as <-. cbn [APS.sd].
    eapply (node_alt2_sound aid aargs cs csa csb E fx R M model); [exact HC | exact HF | exact Hn | (apply sd_has_nil'; exact D_nil) | (apply sd_has_nil'; exact D_nil)
      | exact (CONT aka csa sa Hsp1 H1) | exact (CONT akb csb sb Hsp2 H2)].
  - (* [comment removed for export] *)
    apply andb_prop in Hsp as [Hsp2 Hsp3].
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_mmapw A nx0 LIMIT ISP wlo whi cs) as [[[csr csl] csh]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel None csh wkh) as [sh|] eqn:H3; [|discriminate].
    assert (GOAL : s = sh ->
              (forall csl' E' fx' R' M' model', csl = Some csl' ->
                  env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csl' R' M' model' -> FXOK fx' -> m_fs model' = m_fs model ->
                  RR (cfg fx' R' (pc csl') M' model') (SD E (m_fs model) sh)) ->
              RR (cfg fx R (pc cs) M model) (SD E (m_fs model) s)).
    { intros -> HKL.
      eapply (node_mmapw_sound wlo whi cs csr csl csh E fx R M model); [exact HC | exact HF | exact Hec | exact Hn | exact HKL |].
      exact (CONT wkh csh sh Hsp3 H3). }
    destruct csl as [csl'|].
    + destruct (CHECK bfuel fuel None csl' wkl) as [sl|] eqn:H2; [|discriminate].
      destruct (AP.shape_eqv sl sh) eqn:Hse; [|discriminate]. injection Hc as <-.
      apply GOAL; [reflexivity|]. intros csl'' E' fx' R' M' model' Hl. injection Hl as <-.
      intros Hag HC' HF' Hfs. apply (sr_conseq _ RR _ (SD E (m_fs model) sl)).
      * exact (CONT wkl csl' sl Hsp2 H2 E' fx' R' M' model' Hag HC' HF' Hfs).
      * (* [comment removed for export] *)
        unfold AP.shape_eqv in Hse. apply orb_prop in Hse as [Hse|Hse].
        -- apply APS.shape_eqb_eq in Hse. subst. apply t_eq_refl.
        -- apply andb_prop in Hse as [Hse1 Hse2]. intros tr.
           pose proof (sd_holes_only_eq E (m_fs model) sl Hse1 tr). pose proof (sd_holes_only_eq E (m_fs model) sh Hse2 tr). tauto.
    + injection Hc as <-. apply GOAL; [reflexivity|]. intros csl'' E' fx' R' M' model' Hl. discriminate Hl.
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_mmap2h A nx0 LIMIT ISP cs) as [[csa csb]|] eqn:Hn; [|discriminate].
    eapply (node_mmap2h_sound cs csa csb E fx R M model); [exact HC | exact HF | exact Hec | exact Hn |].
    exact (CONT hkb csb s Hsp Hc).
Qed.

End Sound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section Closed.
Variable SEGS : list Segment.
Variable RR : shape_rel SEGS.   (* [comment removed for export] *)
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable HS : nat -> option acs.
Variable XN : nat -> list expr -> acs -> option acs.
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Variable XA : nat -> list expr -> acs -> option (acs * acs).
Variable XT : nat -> list expr -> acs -> option (Z * list spiece * Z).   (* [comment removed for export] *)
Variable KC : nat.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Variable FXOK : GPS.FX -> Prop.
Variable HOLES : nat -> env -> Fs.Fs -> TSet.
Variable D : TSet.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                            (segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok A.
Hypothesis SHADOW_ok : shadow_ok A.
Variable ISP : expr.
Hypothesis ISP_vars : expr_vars_lt nx0 ISP = true.
Hypothesis argH_high : forall E (a : word), argH E a = true -> sp_window_lo <= bv_unsigned a /\ bv_unsigned (edenot E ISP) <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis HOLES_agree : forall h E E' fs, env_agree nx0 E E' -> HOLES h E fs = HOLES h E' fs.
Hypothesis HOLES_nil : forall h E fs, HOLES h E fs [].
Hypothesis HOLES_same : forall h E fs, HOLES h E fs = HOLES 0%nat E fs.
Hypothesis D_nil : D [].
Hypothesis RES_tile : forall z, img_lo A <= z < img_hi A -> in_ivs z (segments_reserved SEGS) = true.
Hypothesis HULL_ne : img_lo A < img_hi A.
Hypothesis RUN_sound : GPS.RUN_SOUND SEGS FXOK.
Hypothesis node_ext_sound : SIF.ext_stmt SEGS RR A nx0 LIMIT XN SINV argH ISP FS0 FXOK.
Hypothesis node_emit_sound : SIF.emit_stmt SEGS RR A nx0 LIMIT XE SINV argH ISP FS0 FXOK.
Hypothesis node_ext2_sound : SIF.ext2_stmt SEGS RR A nx0 LIMIT XB SINV argH ISP FS0 FXOK.
Hypothesis node_alt2_sound : SIF.alt2_stmt SEGS RR A nx0 LIMIT XA SINV argH ISP FS0 FXOK.
Hypothesis HS_sound : SIF.holes_stmt SEGS RR A LIMIT HS SINV argH ISP FS0 FXOK HOLES.
Theorem check_sound : forall (HOWN : bool) fuel bfuel p cs s,     (* [comment removed for export] *)
  splan_ok p = true ->
  AP.checkA SEGS IT A nx0 LIMIT ISP XN XE XB XA XT HS KC HOWN bfuel fuel None cs p = COk s ->
  forall E fx R M model, APS.cs_ok SEGS A LIMIT SINV argH ISP FS0 E cs R M model -> FXOK fx ->
  RR (GPS.cfgF SEGS fx R (pc cs) M model) (APS.sd HOLES D E (m_fs model) s).
Proof.
  intros HOWN. eapply check_soundS; try eassumption.
  - apply (AzSMmB.node_sys_sound SEGS RR A nx0 LIMIT SINV argH FS0 FXOK); assumption.
  - apply (AzSMmB.node_brk2_sound SEGS RR A nx0 LIMIT SINV argH FS0 FXOK); assumption.
  - apply (AzSMmB.node_brk2x_sound SEGS RR A nx0 LIMIT SINV argH FS0 FXOK); assumption.
  - apply (AzSMmB.node_exit_sound SEGS RR A); assumption.
  - apply (AzSMmA.node_mmap2_sound SEGS RR A nx0 LIMIT SINV argH FS0); assumption.
  - apply (AzSMmA.node_mmap2h_sound SEGS RR A nx0 LIMIT SINV argH FS0); assumption.
  - apply (AzSMmA.node_mprotect2_sound SEGS RR A nx0 LIMIT SINV argH FS0); assumption.
  - apply (AzSMmA.node_mmapin_sound SEGS RR A nx0 LIMIT SINV argH FS0); assumption.
  - apply (AzSMmA.node_mmapw_sound SEGS RR A nx0 LIMIT SINV argH FS0); assumption.
Qed.
End Closed.
End SPS.
