(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma RUN_sound_fx : forall SEGS, GPS.RUN_SOUND SEGS fx_ok.
Proof.
  intros SEGS t K fuel stops pc sr kn nx E M R fx Ht HR HK Hsr Hkn Hfx.
  exact (runTXF_sound SEGS t K fuel stops pc sr kn nx E M (seg_rom SEGS) R fx Ht HR HK Hsr Hkn Hfx).
Qed.

Section Sound.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable nx0 : nat.
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable SHC : list (Z * Z).      (* [comment removed for export] *)
Variable VSH : list (Z * Z).      (* [comment removed for export] *)
Variable AINV : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.   (* [comment removed for export] *)
Variable KCAP : Z.
Variable FTOPc : Z.   (* [comment removed for export] *)
Hypothesis AINV_frame : forall Lc Lf B C K M M' mdl,
  AINV Lc Lf B C K M mdl -> (forall a, M' a <> M a -> gowned SWIN PERMc SPTOPc SB Lc Lf a /\ M' a <> None) ->
  AINV Lc Lf B C K M' mdl.
(* [comment removed for export] *)
Hypothesis AINV_lazy : forall Lc Lf B C K M mdl,
  AINV Lc Lf B C K M mdl ->
  exists AA, A_wf AA /\ MInv AA mdl
    /\ (forall a : word, GPS.in_shc SHC (bv_unsigned a) = true -> page_allowedb AA (page_base a) = true)
    /\ (forall a : word, GPS.in_shv VSH (bv_unsigned a) = true -> page_allowedb AA (page_base a) = true)
    /\ (forall (a : word) b n, In (b, n) (Lc ++ Lf) -> in_shadow SB b n (bv_unsigned a) -> page_allowedb AA (page_base a) = true)
    /\ (forall mdl', MInv AA mdl' -> same_but_materialized mdl mdl' -> AINV Lc Lf B C K M mdl').
Variable A : atable.
Hypothesis AINV_facts : forall Lc Lf B C K M mdl,
  AINV Lc Lf B C K M mdl ->
  Forall (fun iv => 0 < bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL_run
                    /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_lo A \/ img_hi A <= bv_unsigned (fst iv))) (m_vm_lazy mdl).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 SEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT SEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable G : gtable.
(* [comment removed for export] *)
Hypothesis ROM_ok : forall x : word, g_ro_lo G <= bv_unsigned x -> bv_unsigned x < g_ro_hi G -> seg_rom SEGS x <> None.
Hypothesis RO_hi : g_ro_hi G < 2 ^ 64.

#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV).

Lemma rdn_rom_some : forall mem n (a : word),
  g_ro_lo G <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= g_ro_hi G ->
  exists bs, rdn SEGS mem a n = Some bs.
Proof.
  intros mem n. induction n as [|n IH]; intros a Hlo Hhi.
  - exists []. reflexivity.
  - cbn [rdn].
    assert (Hb : exists b, match mem a with Some b => Some b | None => seg_rom SEGS a end = Some b).
    { destruct (mem a) as [b|]; [exists b; reflexivity|].
      destruct (seg_rom SEGS a) as [b|] eqn:Hr; [exists b; reflexivity|].
      exfalso. apply (ROM_ok a); [lia | lia | exact Hr]. }
    destruct Hb as [b ->].
    pose proof (u64_range a) as Ha.
    destruct (IH (a + 1)%bv) as [bs ->].
    + rewrite u_add1 by lia. lia.
    + rewrite u_add1 by lia. lia.
    + exists (b :: bs). reflexivity.
Qed.

Lemma v_addi_pc4 : forall p, 0 <= p -> p + 4 < two64 -> v_addi (Z_to_bv 64 p) 4 = Z_to_bv 64 (p + 4).
Proof.
  intros p H0 H4. unfold v_addi. f_equal. rewrite Z_to_bv_unsigned. unfold two64 in H4.
  rewrite bv_wrap_small; [reflexivity | unfold bv_modulus; lia].
Qed.

Lemma load_range_fact_ok : forall E M sz sx v bs,
  length bs = AzSymStepR.msize_bytes sz ->
  ev E v = load_result sz sx bs ->
  know_ok SEGS E M (load_range_fact sz sx v).
Proof.
  intros E M sz sx v bs Hlen Hv. unfold know_ok, load_range_fact.
  pose proof (bytes_le_to_Z_bound bs) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hb0. rewrite Hlen in Hb.
  rewrite (load_result_val sz sx bs Hlen) in Hv.
  destruct sz, sx; cbn [AzSymStepR.msize_bytes msize_bytes] in *;
    first [ apply Forall_nil
          | constructor; [| apply Forall_nil]; cbn [kentry_ok edenot]; rewrite Hv; unfold extz, eff_sx;
            cbn in Hb; rewrite u_small by lia; lia ].
Qed.

Theorem node_imgload_sound : OBL_imgload SEGS IT nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ G.
Proof.
  intros cs cs' E fx R M model T HC _ Hn Hk.
  unfold node_imgload in Hn.
  destruct (itab_lookup IT (pc cs)) as [i|] eqn:Hit.
  2:{ injection Hn as <-. apply (Hk E fx R M model); [split; apply env_agree_refl | exact HC | reflexivity]. }
  destruct i as [| | | | |sz sx rd rs imm| | | | | | | | | | | | | | | | | | | | | | | | | | | | |];
    try (injection Hn as <-; apply (Hk E fx R M model); [split; apply env_agree_refl | exact HC | reflexivity]).
  set (ae := eaddz (sr_get (s_regs (a_ss cs)) rs) (bv_signed imm)) in Hn.
  destruct (xlo (kn cs) ae) as [lo|] eqn:Hxlo; [|discriminate].
  destruct (xhi (kn cs) ae) as [hi|] eqn:Hxhi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection Hn as <-.
  apply andb_prop in Hc as [Hc Hlen]. apply andb_prop in Hc as [Hc Hpc4]. apply andb_prop in Hc as [Hc Hpc0].
  apply andb_prop in Hc as [Hc Hrd]. apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hfresh Hlo].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. apply Z.leb_le in Hpc0. apply Z.ltb_lt in Hpc4.
  apply negb_true_iff in Hrd. apply Nat.eqb_eq in Hlen.
  pose proof (IT_ok _ _ Hit) as Hen. unfold itab_entry in Hen.
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:Hec; [discriminate|].
  destruct (decode_any w) as [[i' isz]|] eqn:Hd; [|discriminate].
  destruct (Z.eqb isz 4) eqn:Hsz; [|discriminate]. apply Z.eqb_eq in Hsz. subst isz.
  injection Hen as ->.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (co_regs HC) as HR.
  pose proof (co_know HC) as HK.
  assert (Haddr : v_addi (getr R rs) (bv_signed imm) = edenot E ae).
  { unfold ae, eaddz. rewrite mkAlu_denot. rewrite (HR rs). cbn [edenot]. rewrite alu_add. unfold v_addi, v_add.
    apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. }
  pose proof (xlo_sound SEGS E _ (kn cs) ae lo HK Hxlo) as Blo.
  pose proof (xhi_sound SEGS E _ (kn cs) ae hi HK Hxhi) as Bhi.
  set (H := GPS.hid SHC VSH E cs model).
  set (MR := GPS.Mr SHC VSH E cs model M) in *.
  destruct (rdn_rom_some MR (AzSymStepR.msize_bytes sz) (edenot E ae)) as [bs Hrdn]; [lia | |].
  { replace (Z.of_nat (AzSymStepR.msize_bytes sz)) with (Z.of_nat (msize_bytes sz)) by (destruct sz; reflexivity). lia. }
  pose proof (rdn_length _ _ _ _ _ Hrdn) as Hbslen.
  set (val := load_result sz sx bs).
  set (v := nxt cs) in *.
  set (E' := ext1 E v val).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  set (R' := regupd R rd val).
  (* [comment removed for export] *)
  assert (Hstep : RiscvSemantics.step SEGS (restrict H (mkstF fx R (Z_to_bv 64 (pc cs)) M (seg_rom SEGS)))
                  = MachineOk (mkstF fx R' (Z_to_bv 64 (pc cs + 4)) MR (seg_rom SEGS))).
  { change (restrict H (mkstF fx R (Z_to_bv 64 (pc cs)) M (seg_rom SEGS))) with (mkstF fx R (Z_to_bv 64 (pc cs)) MR (seg_rom SEGS)).
    unfold mkstF. rewrite <- !mkstR_None.
    rewrite (stepR_load fx SEGS R _ MR (seg_rom SEGS) None w sz sx rd rs imm bs Hf Hec Hd).
    - rewrite Hrd. rewrite v_addi_pc4 by assumption. reflexivity.
    - rewrite Haddr. exact Hrdn. }
  eapply (GPS.restricted_run_sound SEGS A PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc AINV_lazy AINV_facts FXOK UINV RZ RZ_silent1 SEGS_in_hull SEGS_wx);
    [exact HC | eapply msteps_one; [reflexivity | exact Hstep] |].
  intros model' Hsame Hhid Hhalt' Hfs' Hfds' HA' Hclean.
  unfold unrestrict. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom mkstF mkst].
  unfold MR, GPS.Mr. fold H. rewrite munrestrict_mrestrict.
  pose proof (cs_ok_agree SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV UINV_agree E E' cs fx R M model Hag Hfresh HC) as HC'.
  specialize (Hk E' fx R' M model' (conj (env_agree_le _ _ _ _ Hag Fle) Hag)).
  unfold cfgF, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk. unfold pc. apply Hk; [|exact Hfs'].
  eapply (cs_ok_frame_mat SEGS SWIN PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc AINV_frame FXOK UINV);
    [exact HC' | | reflexivity | | exact (co_fx HC) | | exact Hsame |].
  - (* [comment removed for export] *) cbn [mk_ss s_regs].
    pose proof (regs_ok_agree' (nxt cs) E E' _ R Hag Fsr HR) as HR1.
    pose proof (regs_ok_upd E' (s_regs (a_ss cs)) R rd val (EVar v) HR1) as HR2.
    rewrite Hrd in HR2. apply HR2. cbn [edenot]. unfold E'. apply ext1_at.
  - (* [comment removed for export] *)
    cbn [mk_ss s_know]. rewrite (GPS.Mr_agreeE nx0 SHC VSH E E' cs model' M Hag Hfresh).
    unfold GPS.Mr. rewrite Hhid. fold H. change (mrestrict H M) with MR.
    unfold know_ok. apply Forall_app. split.
    + eapply load_range_fact_ok; [exact Hbslen|]. unfold E'. rewrite ext1_at. reflexivity.
    + eapply know_ok_agree'; [exact Hag | exact Fkn | exact HK].
  - (* [comment removed for export] *) intros a Ha. exfalso. apply Ha. reflexivity.
  - (* [comment removed for export] *)
    destruct (GPS.fresh_ok_parts2 nx0 cs Hfresh) as [Ffk Fmt].
    rewrite (GPS.blocks_den_agree (nxt cs) E E' (a_vis cs) Hag (GPS.pairs_vars_lt_app_l _ _ _ Fallow)).
    rewrite (GPS.blocks_den_agree (nxt cs) E E' (a_fake cs) Hag Ffk).
    rewrite (GPS.bcost_agree (nxt cs) E E' (a_vis cs) Hag (GPS.pairs_vars_lt_app_l _ _ _ Fallow)).
    rewrite (GPS.uE_agree (nxt cs) E E' (a_meter cs) Hag Fmt). exact HA'.
Qed.

End Sound.
