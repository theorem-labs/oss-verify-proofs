(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallRec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgCutShare.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallRec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition kdead (cs : acs) : Prop := In (KRange (ELit 1) 0 0) (kn cs).
(* [comment removed for export] *)
Definition hs_sub (HS' HS : nat -> option acs) : Prop :=
  forall h ch, HS' h = Some ch -> (exists h', HS h' = Some ch) \/ kdead ch.

Lemma kdead_no_state : forall SEGS {RC : run_ceil} {SFL : stk_floor} PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV E cs fx R M model,
  kdead cs -> ~ GPS.cs_ok SEGS PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV E cs fx R M model.
Proof.
  intros SEGS RC SFL PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV E cs fx R M model Hd HC.
  pose proof (co_know HC) as K. unfold know_ok in K. rewrite Forall_forall in K.
  pose proof (K _ Hd) as X. cbn [kentry_ok edenot] in X.
  change (bv_unsigned (Z_to_bv 64 1)) with 1 in X. lia.
Qed.

(* [comment removed for export] *)
Definition kdeadb (cs : acs) : bool := match kn cs with KRange (ELit (Zpos xH)) Z0 Z0 :: _ => true | _ => false end.
Lemma kdeadb_sound : forall cs, kdeadb cs = true -> kdead cs.
Proof.
  intros cs H. unfold kdeadb in H. unfold kdead.
  destruct (kn cs) as [|K r]; [discriminate|]. left.
  destruct K as [| | | | |e lo hi| | | | | | ]; try discriminate H.
  destruct e as [z| | | | | | |]; try discriminate H.
  destruct z as [|p|]; try discriminate H. destruct p; try discriminate H.
  destruct lo; try discriminate H. destruct hi; try discriminate H. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma contract_upto_of_full : forall SEGS {RC : run_ceil} {SFL : stk_floor} SWIN G FXOK RZ SHC KCAP AINVH i n ce,
  callee_contract SEGS SWIN G FXOK RZ SHC KCAP AINVH ce -> callee_contract_upto SEGS SWIN G FXOK RZ SHC KCAP AINVH i n ce.
Proof.
  intros SEGS RC SFL SWIN G FXOK RZ SHC KCAP AINVH i n ce H. unfold callee_contract_upto, callee_contract, callee_contract_when in *.
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 E fx R M mdl T HB0 HC0 HBc HCc HFB HQ HC HT Hk.
  exact (H PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 E fx R M mdl T HB0 HC0 HBc HCc HFB I HC HT Hk).
Qed.

(* [comment removed for export] *)
Lemma holes_stmt_sub : forall SEGS {RC : run_ceil} {SFL : stk_floor} (HS HS' : nat -> option acs) PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV (T : TSet) RZ,
  hs_sub HS' HS ->
  GPS.holes_stmt SEGS HS PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV (fun _ _ _ => T) RZ ->
  GPS.holes_stmt SEGS HS' PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV (fun _ _ _ => T) RZ.
Proof.
  intros SEGS RC SFL HS HS' PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV T RZ Hsub H h ch Hh E fx R M model HC.
  destruct (Hsub h ch Hh) as [[h' Hh'] | Hd].
  - exact (H h' ch Hh' E fx R M model HC).
  - exfalso. exact (kdead_no_state SEGS PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV E ch fx R M model Hd HC).
Qed.

Section CertCutX.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable A : atable.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Variable SWIN : list (Z * Z).
Variable G : gtable.
Variable FXOK : FX -> Prop.
Hypothesis RUN : GPS.RUN_SOUND SEGS FXOK.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 SEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT SEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HP : hprops SWIN G SHC AINVH.
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_al : 0 <= g_img_lo G /\ g_img_lo G mod 8 = 0 /\ g_img_hi G mod 8 = 0.
Hypothesis G_img_shlo : g_img_hi G <= SHMAPLO.
Hypothesis G_priv : forall lo hi, In (lo, hi) (g_priv G) -> g_ro_hi G <= lo /\ hi <= g_img_hi G.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi G <= lo /\ hi <= g_img_hi G /\ (forall plo phi, In (plo, phi) (g_priv G) -> hi <= plo \/ phi <= lo).
Hypothesis SEGS_out : forall a : word, ~ (g_img_lo G <= bv_unsigned a < g_img_hi G) -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis A_img_hi : img_hi A = g_img_hi G.
Hypothesis A_img_lo : img_lo A = g_img_lo G.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
#[local] Notation AINVf := (AINV_f (nil_of SWIN) G AINVH).   (* [comment removed for export] *)
Variable ce : gcallee.
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable LIMIT : Z.
Variable KC bfuel fuel : nat.
Variable XN : nat -> list expr -> acs -> option acs.
Variable Q : env -> Prop.
Hypothesis Q_agree : forall E E', env_agree (ce_nxf ce) E E' -> Q E -> Q E'.
Hypothesis XN_sound : forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 (UINV : env -> Prop),
  0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> Q E) ->
  GPS.ext_stmt SEGS (ce_nxf ce) XN PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINVf PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf FXOK UINV RZ.
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Hypothesis XB_sound : forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 (UINV : env -> Prop),
  0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> Q E) ->
  GPS.ext2_stmt SEGS (ce_nxf ce) XB PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINVf PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf FXOK UINV RZ.
(* [comment removed for export] *)
Variable XNs : nat -> list expr -> acs -> option acs.
Hypothesis XNs_sound : forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 (UINV : env -> Prop),
  0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> Q E) ->
  GPS.ext_stmt SEGS (ce_nxf ce) XNs PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINVf PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf FXOK UINV RZ.
Variable XBs : nat -> list expr -> acs -> option (acs * acs).
Hypothesis XBs_sound : forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 (UINV : env -> Prop),
  0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> Q E) ->
  GPS.ext2_stmt SEGS (ce_nxf ce) XBs PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINVf PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf FXOK UINV RZ.

(* [comment removed for export] *)
Variable CUTS : list (acs * plan).
#[local] Notation NT := (AzCallCert.NT ce).
#[local] Notation HScut := (AzCallCert.HScut ce CUTS).
(* [comment removed for export] *)
Hypothesis CUTS_ok : forall i T k, nth_error CUTS i = Some (T, k) -> exists sh,
  gplan_ok k = true /\ holes_only sh = true /\
  (AP.check SEGS IT A (ce_nxf ce) LIMIT GPS.ISP0 XN XE0 XB (HScut (S i)) KC bfuel fuel None T k = COk sh \/
   exists HS', hs_sub HS' (HScut (S i)) /\ AP.check SEGS IT A (ce_nxf ce) LIMIT GPS.ISP0 XNs XE0 XBs HS' KC bfuel fuel None T k = COk sh).
Variable p : plan.
Variable s : shape.
Hypothesis p_ok : gplan_ok p = true.
Hypothesis s_ok : holes_only s = true.
Hypothesis CERT : AP.check SEGS IT A (ce_nxf ce) LIMIT GPS.ISP0 XN XE0 XB (HScut 0) KC bfuel fuel None (ce_tin ce) p = COk s.

Theorem contract_of_cert_when_cutX : callee_contract_when SEGS SWIN G FXOK RZ SHC KCAP AINVH Q ce.
Proof.
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 E fx R M mdl T HB0 HC0 HBc HCc HFB HQ HC HT Hexits.
  pose proof (hprops_nil SWIN G SHC AINVH HP) as HPn.
  set (UINV := fun E' => env_agree (ce_nxf ce) E E').
  assert (UINV_agree : forall E1 E2, env_agree (ce_nxf ce) E1 E2 -> UINV E1 -> UINV E2).
  { intros E1 E2 H12 H1. unfold UINV in *. eapply env_agree_trans; [exact H1 | exact H12]. }
  assert (UINV_Q : forall E1, UINV E1 -> Q E1).
  { intros E1 H1. eapply Q_agree; [exact H1 | exact HQ]. }
  (* [comment removed for export] *)
  #[local] Ltac exit_hole Hexits Hh HC1 HC :=
    match type of HC1 with GPS.cs_ok _ _ _ _ _ _ _ _ _ _ _ ?E1 ?ch ?fx1 ?R1 ?M1 ?mdl1 =>
      apply (Hexits ch E1 fx1 R1 M1 mdl1); [eapply nth_error_In; exact Hh | exact (co_uinv HC1)
                   | destruct HC1; constructor; try assumption; exact I
                   | rewrite (co_fs HC1); symmetry; exact (co_fs HC)] end.
  assert (HSall : forall d k, (length CUTS <= k + d)%nat ->
            GPS.holes_stmt SEGS (HScut k) PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINVf PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf FXOK UINV (fun _ _ _ => T) RZ).
  { induction d as [|d IHd]; intros k Hk h ch Hh E1 fx1 R1 M1 mdl1 HC1; unfold AzCallCert.HScut in Hh.
    - destruct (Nat.ltb h NT) eqn:Hlt; [exit_hole Hexits Hh HC1 HC|].
      destruct (Nat.leb k (h - NT)) eqn:Hle; [|discriminate]. apply Nat.leb_le in Hle.
      destruct (nth_error CUTS (h - NT)) as [c|] eqn:Hn; [|discriminate].
      exfalso. assert (Hl : (h - NT < length CUTS)%nat) by (apply nth_error_Some; rewrite Hn; discriminate). lia.
    - destruct (Nat.ltb h NT) eqn:Hlt; [exit_hole Hexits Hh HC1 HC|].
      destruct (Nat.leb k (h - NT)) eqn:Hle; [|discriminate]. apply Nat.leb_le in Hle.
      destruct (nth_error CUTS (h - NT)) as [[Tc kc]|] eqn:Hn; [|discriminate]. cbn [fst] in Hh. injection Hh as <-.
      destruct (Nat.eq_dec (h - NT) k) as [Heq|Hne].
      + (* [comment removed for export] *)
        destruct (CUTS_ok (h - NT)%nat Tc kc Hn) as (sc & Hgp & Hho & [Hck | (HS' & Hsub & Hck)]).
        { pose proof (GPS.check_soundA SEGS IT IT_ok A (ce_nxf ce) LIMIT (HScut (S (h - NT))) XN XE0 XB AP.XA0 AP.XT0 KC (nil_of SWIN) PERMf TOPf FS0 SHC (VSHf HID HIDF)
                      (AINVf PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf
                      (AINV_f_frame (nil_of SWIN) G SHC AINVH HPn G_ro_img G_img_al G_img_shlo PERMf TOPf HID HIDF M0 B0 C0)
                      (AINV_f_lazy (nil_of SWIN) G SHC AINVH HPn PERMf TOPf HID HIDF M0 B0 C0)
                      ltac:(intros; rewrite A_img_hi, A_img_lo; eapply (AINV_f_facts (nil_of SWIN) G SHC AINVH HPn); eassumption)
                      FXOK UINV UINV_agree (fun _ _ _ => T) (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => HT) (fun _ _ _ => eq_refl)
                      RZ RZ_silent1 RZ_exit RZ_conseq RUN SEGS_in_hull HULL_ok SEGS_wx
                      (XN_sound PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB UINV_agree UINV_Q)
                      ltac:(intros id args cs fd ps cs' E2 fx2 R2 M2 m2 T2 _ Hnn; discriminate Hnn)
                      (XB_sound PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB UINV_agree UINV_Q)
                      ltac:(intros id args cs0 csa csb E2 fx2 R2 M2 m2 Ta Tb _ Hnn; discriminate Hnn)
                ltac:(intros id args cs0 fd0 ps0 code0 E2 fx2 R2 M2 m2 _ Hnn; discriminate Hnn)
                      (IHd (S (h - NT)) ltac:(lia)) fuel bfuel None kc Tc sc Hgp Hck E1 fx1 R1 M1 mdl1 T) as X.
        eapply RZ_conseq; [apply X; [exact HC1 | exact I | exact HT] | exact (sd_holes_only T E1 (m_fs mdl1) sc Hho)]. }
        pose proof (GPS.check_soundA SEGS IT IT_ok A (ce_nxf ce) LIMIT HS' XNs XE0 XBs AP.XA0 AP.XT0 KC (nil_of SWIN) PERMf TOPf FS0 SHC (VSHf HID HIDF)
                      (AINVf PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf
                      (AINV_f_frame (nil_of SWIN) G SHC AINVH HPn G_ro_img G_img_al G_img_shlo PERMf TOPf HID HIDF M0 B0 C0)
                      (AINV_f_lazy (nil_of SWIN) G SHC AINVH HPn PERMf TOPf HID HIDF M0 B0 C0)
                      ltac:(intros; rewrite A_img_hi, A_img_lo; eapply (AINV_f_facts (nil_of SWIN) G SHC AINVH HPn); eassumption)
                      FXOK UINV UINV_agree (fun _ _ _ => T) (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => HT) (fun _ _ _ => eq_refl)
                      RZ RZ_silent1 RZ_exit RZ_conseq RUN SEGS_in_hull HULL_ok SEGS_wx
                      (XNs_sound PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB UINV_agree UINV_Q)
                      ltac:(intros id args cs fd ps cs' E2 fx2 R2 M2 m2 T2 _ Hnn; discriminate Hnn)
                      (XBs_sound PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB UINV_agree UINV_Q)
                      ltac:(intros id args cs0 csa csb E2 fx2 R2 M2 m2 Ta Tb _ Hnn; discriminate Hnn)
                ltac:(intros id args cs0 fd0 ps0 code0 E2 fx2 R2 M2 m2 _ Hnn; discriminate Hnn)
                      (holes_stmt_sub SEGS _ _ PERMf TOPf FS0 SHC (VSHf HID HIDF) _ KCAP FTOPf FXOK UINV T RZ Hsub (IHd (S (h - NT)) ltac:(lia))) fuel bfuel None kc Tc sc Hgp Hck E1 fx1 R1 M1 mdl1 T) as X.
        eapply RZ_conseq; [apply X; [exact HC1 | exact I | exact HT] | exact (sd_holes_only T E1 (m_fs mdl1) sc Hho)].
      + (* [comment removed for export] *)
        refine (IHd (S k) ltac:(lia) h Tc _ E1 fx1 R1 M1 mdl1 HC1).
        unfold AzCallCert.HScut. rewrite Hlt. replace (Nat.leb (S k) (h - NT)) with true by (symmetry; apply Nat.leb_le; lia).
        rewrite Hn. reflexivity. }
  pose proof (GPS.check_soundA SEGS IT IT_ok A (ce_nxf ce) LIMIT (HScut 0) XN XE0 XB AP.XA0 AP.XT0 KC (nil_of SWIN) PERMf TOPf FS0 SHC (VSHf HID HIDF)
                (AINVf PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf
                (AINV_f_frame (nil_of SWIN) G SHC AINVH HPn G_ro_img G_img_al G_img_shlo PERMf TOPf HID HIDF M0 B0 C0)
                (AINV_f_lazy (nil_of SWIN) G SHC AINVH HPn PERMf TOPf HID HIDF M0 B0 C0)
                ltac:(intros; rewrite A_img_hi, A_img_lo; eapply (AINV_f_facts (nil_of SWIN) G SHC AINVH HPn); eassumption)
                FXOK UINV UINV_agree (fun _ _ _ => T) (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => HT) (fun _ _ _ => eq_refl)
                RZ RZ_silent1 RZ_exit RZ_conseq RUN SEGS_in_hull HULL_ok SEGS_wx
                (XN_sound PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB UINV_agree UINV_Q)
                ltac:(intros id args cs fd ps cs' E1 fx1 R1 M1 m1 T1 _ Hn; discriminate Hn)
                (XB_sound PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB UINV_agree UINV_Q)
                ltac:(intros id args cs0 csa csb E2 fx2 R2 M2 m2 Ta Tb _ Hnn; discriminate Hnn)
                ltac:(intros id args cs0 fd0 ps0 code0 E2 fx2 R2 M2 m2 _ Hnn; discriminate Hnn)
                (HSall (length CUTS) 0%nat ltac:(lia)) fuel bfuel None p (ce_tin ce) s p_ok CERT E fx R M mdl T) as X.
  eapply RZ_conseq; [apply X | exact (sd_holes_only T E (m_fs mdl) s s_ok)].
  - destruct HC; constructor; try assumption. unfold UINV. apply env_agree_refl.
  - exact I.
  - exact HT.
Qed.
End CertCutX.

(* [comment removed for export] *)
Section RecX.
Variable SEGS : list Segment.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable IT : itab.
Variable A : atable.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable SWIN : list (Z * Z).
Variable G : gtable.
Variable FXOK : FX -> Prop.
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 SEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT SEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HP : hprops SWIN G SHC AINVH.
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_al : 0 <= g_img_lo G /\ g_img_lo G mod 8 = 0 /\ g_img_hi G mod 8 = 0.
Hypothesis G_img_shlo : g_img_hi G <= SHMAPLO.
Hypothesis G_priv : forall lo hi, In (lo, hi) (g_priv G) -> g_ro_hi G <= lo /\ hi <= g_img_hi G.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi G <= lo /\ hi <= g_img_hi G /\ (forall plo phi, In (plo, phi) (g_priv G) -> hi <= plo \/ phi <= lo).
Hypothesis SEGS_out : forall a : word, ~ (g_img_lo G <= bv_unsigned a < g_img_hi G) -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis A_img_hi : img_hi A = g_img_hi G.
Hypothesis A_img_lo : img_lo A = g_img_lo G.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
#[local] Notation AINVf := (AINV_f SWIN G AINVH).
#[local] Notation AINV0 := (AINV_f (nil_of SWIN) G AINVH).
#[local] Notation callee_contract_upto := (callee_contract_upto SEGS SWIN G FXOK RZ SHC KCAP AINVH).
#[local] Notation callee_contract_of_upto := (callee_contract_of_upto SEGS SWIN G FXOK RZ SHC KCAP AINVH).
Section CertCutRecX.
Variable ce : gcallee.
Variable idepth : nat.
Hypothesis idepth_lt : (idepth < ce_nxf ce)%nat.
Hypothesis RUN : GPS.RUN_SOUND SEGS FXOK.
Variable LIMIT : Z.
Variable KC bfuel fuel : nat.
Variable XN : nat -> list expr -> acs -> option acs.
(* [comment removed for export] *)
Hypothesis XN_sound_rec : forall n PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 (UINV : env -> Prop),
  0 <= n ->
  0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> DMEAS idepth E <= n + 1) ->
  callee_contract_upto idepth n ce ->
  GPS.ext_stmt SEGS (ce_nxf ce) XN PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV0 PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf FXOK UINV RZ.
Variable p : plan.
Variable s : shape.
Hypothesis p_ok : gplan_ok p = true.
Hypothesis s_ok : holes_only s = true.
(* [comment removed for export] *)
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Hypothesis XB_sound_rec : forall n PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 (UINV : env -> Prop),
  0 <= n -> 0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> DMEAS idepth E <= n + 1) ->
  callee_contract_upto idepth n ce ->
  GPS.ext2_stmt SEGS (ce_nxf ce) XB PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV0 PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf FXOK UINV RZ.
Variable XNs : nat -> list expr -> acs -> option acs.
Hypothesis XNs_sound_rec : forall n PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 (UINV : env -> Prop),
  0 <= n ->
  0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> DMEAS idepth E <= n + 1) ->
  callee_contract_upto idepth n ce ->
  GPS.ext_stmt SEGS (ce_nxf ce) XNs PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV0 PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf FXOK UINV RZ.
Variable XBs : nat -> list expr -> acs -> option (acs * acs).
Hypothesis XBs_sound_rec : forall n PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 (UINV : env -> Prop),
  0 <= n -> 0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> DMEAS idepth E <= n + 1) ->
  callee_contract_upto idepth n ce ->
  GPS.ext2_stmt SEGS (ce_nxf ce) XBs PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV0 PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf FXOK UINV RZ.
Variable CUTS : list (acs * plan).
Hypothesis CUTS_ok : forall i T k, nth_error CUTS i = Some (T, k) -> exists sh,
  gplan_ok k = true /\ holes_only sh = true /\
  (AP.check SEGS IT A (ce_nxf ce) LIMIT GPS.ISP0 XN XE0 XB (HScut ce CUTS (S i)) KC bfuel fuel None T k = COk sh \/
   exists HS', hs_sub HS' (HScut ce CUTS (S i)) /\ AP.check SEGS IT A (ce_nxf ce) LIMIT GPS.ISP0 XNs XE0 XBs HS' KC bfuel fuel None T k = COk sh).
Hypothesis CERT : AP.check SEGS IT A (ce_nxf ce) LIMIT GPS.ISP0 XN XE0 XB (HScut ce CUTS 0) KC bfuel fuel None (ce_tin ce) p = COk s.

Theorem contract_of_cert_rec_cutX : forall n, 0 <= n -> callee_contract_upto idepth n ce.
Proof.
  intros n Hn. revert n Hn. refine (Wf_Z.Zlt_0_ind _ _). intros n IH Hn.
  destruct (Z.eq_dec n 0) as [->|Hnz].
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 E fx R M mdl T _ _ _ _ _ HQ. exfalso.
    unfold Qd, DMEAS in HQ. pose proof (u64_range (ev E idepth)). lia.
  - unfold callee_contract_upto.
    refine (contract_of_cert_when_cutX SEGS A SEGS_in_hull HULL_ok SWIN G FXOK RUN RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP G_ro_img G_img_al G_img_shlo A_img_hi A_img_lo SEGS_wx
             ce IT IT_ok LIMIT KC bfuel fuel XN (Qd idepth n) _ _ XB _ XNs _ XBs _ CUTS CUTS_ok p s p_ok s_ok CERT).
    + intros E E' Hag HQ. eapply Qd_agree; [exact idepth_lt | exact Hag | exact HQ].
    + intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa HUQ.
      apply (XN_sound_rec (n - 1) PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV ltac:(lia) HB0 HC0 HBc HCc HFB HUa).
      * intros E HE. pose proof (HUQ E HE) as X. unfold Qd in X. lia.
      * apply IH. lia.
    + intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa HUQ.
      apply (XB_sound_rec (n - 1) PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV ltac:(lia) HB0 HC0 HBc HCc HFB HUa).
      * intros E HE. pose proof (HUQ E HE) as X. unfold Qd in X. lia.
      * apply IH. lia.
    + intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa HUQ.
      apply (XNs_sound_rec (n - 1) PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV ltac:(lia) HB0 HC0 HBc HCc HFB HUa).
      * intros E HE. pose proof (HUQ E HE) as X. unfold Qd in X. lia.
      * apply IH. lia.
    + intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa HUQ.
      apply (XBs_sound_rec (n - 1) PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV ltac:(lia) HB0 HC0 HBc HCc HFB HUa).
      * intros E HE. pose proof (HUQ E HE) as X. unfold Qd in X. lia.
      * apply IH. lia.
Qed.

Corollary contract_of_cert_rec_cut_allX : callee_contract SEGS SWIN G FXOK RZ SHC KCAP AINVH ce.
Proof. exact (callee_contract_of_upto idepth ce contract_of_cert_rec_cutX). Qed.
End CertCutRecX.
End RecX.
End BgCutShare.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgAAX.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.BgPsub BgCutShare.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section X.
  Variable c : acfg.
  Variable INVT JS1T : smode -> acs.
  Variable elem : smode -> plan -> plan.
Definition XJ0 : expr := EVar 79.








Definition XTL : acs := add_kn (inst (INVT ML) JV XJ0) [KRange XJ0 0 NVHI].


(* [comment removed for export] *)
Definition XPINS : list nat := [].
Fixpoint xbump (k i : nat) : nat := match k with O => i | Datatypes.S k' => if existsb (Nat.eqb i) XPINS then xbump k' (Datatypes.S i) else i end.
Fixpoint xnumber (i : nat) (l : list nat) : list (nat * nat) :=
  match l with
  | [] => []
  | v :: rest => if existsb (Nat.eqb v) XPINS then xnumber i rest
                 else let i' := xbump (Datatypes.S (length XPINS)) i in (v, i') :: xnumber (Datatypes.S i') rest
  end.
Definition XRN : list (nat * nat) := xnumber NXF (csvars_fo NXF XTL).
Definition XR0 : nat := match find (fun q => Nat.eqb (fst q) 79) XRN with Some q => snd q | None => 79%nat end.
Definition XLOOPC : plan := PRename XRN (PLoopM JV NV [(INVT ML, body c JS1T elem ML, PContraH 1)] [(JV, EVar XR0)]).
Definition XCUTS : list (acs * plan) := [(XTL, XLOOPC)].
(* [comment removed for export] *)
Definition xafter_elem (m : smode) (nk : plan) : plan :=
  chainA c m (c_ixreg c)
    (PCase2 (esub NV J) 1
       (PRun [] (PHandoffW (hole m) [(DISLOT, escale (c_K c) (eaddz J 1))]))
       (PRun [c_ix2pc c] (chainB c m (c_ix2reg c) (PRun [c_head c] nk)))).
Definition xafter1 (m : smode) (nk : plan) : plan :=
  match m with
  | ML => PFactVia (esub (escale 8 A1) IXv) (esub S1 IXv) (c_hr c + 1) (2 ^ 40) (elem ML (xafter_elem ML nk))
  | MS => elem MS (xafter_elem MS nk)
  end.
Definition XHO : plan := PHandoffW 2 [(79%nat, eaddz J 1)].
Definition xalts1S : list (acs * plan) :=
  if Z.leb 23 (c_hr c) then [(JS1T ML, xafter1 ML XHO)] else [(JS1T MS, xafter1 MS PNext); (JS1T ML, xafter1 ML XHO)].
Definition xbodyS : plan := PCase2 (remK c J) (c_K c - 1) (errJ c MS) (PRun [] (PViaM 1 xalts1S LO1 (diamondS c))).
Definition XPLAN_S : plan := PCase2 NV 0 (EXIT0 MS) (PRun [c_head c] (PLoopM JV NV [(INVT MS, xbodyS, PContraH 0)] [])).
Definition XPLAN_L1 : plan := PCase2 NV 0 (EXIT0 ML) (PRun [c_head c] (PHandoffW 2 [(79%nat, ELit 0)])).
End X.

(* [comment removed for export] *)
Lemma xhs_sub : forall (c : acfg) (CUTS : list (acs * plan)), length CUTS = 1%nat ->
  hs_sub (HScut (BgAA.ceL1 c) CUTS 1) (HScut (BgAA.ce c MS) CUTS 1).
Proof.
  intros c CUTS HL h ch H. left. exists 1%nat.
  assert (E1 : HScut (BgAA.ce c MS) CUTS 1 1 = Some (tout c ML)) by reflexivity. rewrite E1.
  destruct h as [|[|h]].
  - assert (E : HScut (BgAA.ceL1 c) CUTS 1 0 = Some (tout c ML)) by reflexivity. rewrite E in H. exact H.
  - assert (E : HScut (BgAA.ceL1 c) CUTS 1 1 = Some (tout c ML)) by reflexivity. rewrite E in H. exact H.
  - exfalso. destruct CUTS as [|x [|y r]]; try discriminate HL.
    assert (E : HScut (BgAA.ceL1 c) [x] 1 (Datatypes.S (Datatypes.S h)) = None) by (destruct h as [|[|h]]; reflexivity).
    rewrite E in H. discriminate H.
Qed.
End BgAAX.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWFT OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAu8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgAAf32CertS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWFT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.
Import BgAAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAu8.BgAAf32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_SX : CHKX (BgAA.ce cfg MS) 0 (BgAA.tin cfg MS) (XPLAN_S cfg INVm JS1m elem) = COk (SHole 0).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End BgAAf32CertS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgTc32 OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAi8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgAAi16CertL1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgTc32.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.
Import BgAAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAi8.BgAAi16.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_L1X : CHKX (BgAA.ceL1 cfg) 0 (BgAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (BgAA.ceL1 cfg) 1 (XTL INVm) (XLOOPC cfg INVm JS1m elem) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
(* [comment removed for export] *)
End BgAAi16CertL1.
Module BgAAi16CertS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgTc32.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.
Import BgAAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAi8.BgAAi16.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_SX : CHKX (BgAA.ce cfg MS) 0 (BgAA.tin cfg MS) (XPLAN_S cfg INVm JS1m elem) = COk (SHole 0).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End BgAAi16CertS.
Module BgAAi8CertL1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgTc32.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.
Import BgAAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAi8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_L1X : CHKX (BgAA.ceL1 cfg) 0 (BgAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (BgAA.ceL1 cfg) 1 (XTL INVm) (XLOOPC cfg INVm JS1m elem) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
(* [comment removed for export] *)
End BgAAi8CertL1.
Module BgAAi8CertS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgTc32.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.
Import BgAAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAi8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_SX : CHKX (BgAA.ce cfg MS) 0 (BgAA.tin cfg MS) (XPLAN_S cfg INVm JS1m elem) = COk (SHole 0).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End BgAAi8CertS.
Module BgAAu8CertL1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.
Import BgAAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAu8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_L1X : CHKX (BgAA.ceL1 cfg) 0 (BgAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (BgAA.ceL1 cfg) 1 (XTL INVm) (XLOOPC cfg INVm JS1m elem) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
(* [comment removed for export] *)
End BgAAu8CertL1.
Module BgAAu8CertS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.
Import BgAAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAu8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_SX : CHKX (BgAA.ce cfg MS) 0 (BgAA.tin cfg MS) (XPLAN_S cfg INVm JS1m elem) = COk (SHole 0).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End BgAAu8CertS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgWAX.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.BgPsub BgCutShare.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section X.
  Variable c : acfg.
  Variable JS0T INVT JS1T : smode -> acs.
  Variable elem : smode -> plan -> plan.
Definition XJ0 : expr := EVar 99.








Definition XTL : acs := add_kn (inst (INVT ML) JV XJ0) [KRange XJ0 0 NVHI].


(* [comment removed for export] *)
Definition XPINS : list nat := [HLSLOT; 61%nat].
Fixpoint xbump (k i : nat) : nat := match k with O => i | Datatypes.S k' => if existsb (Nat.eqb i) XPINS then xbump k' (Datatypes.S i) else i end.
Fixpoint xnumber (i : nat) (l : list nat) : list (nat * nat) :=
  match l with
  | [] => []
  | v :: rest => if existsb (Nat.eqb v) XPINS then xnumber i rest
                 else let i' := xbump (Datatypes.S (length XPINS)) i in (v, i') :: xnumber (Datatypes.S i') rest
  end.
Definition XRN : list (nat * nat) := xnumber NXF (csvars_fo NXF XTL).
Definition XR0 : nat := match find (fun q => Nat.eqb (fst q) 99) XRN with Some q => snd q | None => 99%nat end.
Definition XLOOPC : plan := PRename XRN (PLoopM JV NV [(INVT ML, body c JS1T elem ML, PContraH 1)] [(JV, EVar XR0)]).
Definition XCUTS : list (acs * plan) := [(XTL, XLOOPC)].
Definition xafter_elem (m : smode) (nk : plan) : plan :=
  chainA c m (c_ixreg c)
    (PCase2 (esub NV J) 1
       (PRun [] (PHandoffW (hole m) [(DISLOT, eadd HLv (escale (c_K c) (eaddz J 1)))]))
       (PRun [c_ix2pc c] (chainB c m (c_ix2reg c) (PRun [c_head c] nk)))).
Definition xafter1 (m : smode) (nk : plan) : plan :=
  match m with
  | ML => PFactVia (esub (escale 8 A1) IXv) (esub S1 IXv) (c_hr c + 1) (2 ^ 40) (elem ML (xafter_elem ML nk))
  | MS => elem MS (xafter_elem MS nk)
  end.
Definition XHO : plan := PHandoffW 2 [(99%nat, eaddz J 1); (HLSLOT, HLv); (61%nat, NV)].
Definition xalts1S : list (acs * plan) :=
  if Z.leb 23 (c_hr c) then [(JS1T ML, xafter1 ML XHO)] else [(JS1T MS, xafter1 MS PNext); (JS1T ML, xafter1 ML XHO)].
Definition xbodyS : plan := PCase2 (remK c J) (c_K c - 1) (errJ c MS) (PRun [] (PViaM 1 xalts1S LO1 (diamondS c))).
Definition XPLAN_S : plan :=
  PVia 0 (JS0T MS) HLSLOT (hdr_arms c MS)
    (PRun [] (PCaseReg (c_jreg c) 0 (EXITH MS) (PRun [c_head c] (PLoopM JV NV [(INVT MS, xbodyS, PContraH 0)] [])))).
Definition XPLAN_L1 : plan :=
  PVia 0 (JS0T ML) HLSLOT (hdr_arms c ML)
    (PRun [] (PCaseReg (c_jreg c) 0 (EXITH ML) (PRun [c_head c] (PHandoffW 2 [(99%nat, ELit 0); (HLSLOT, HLv); (61%nat, NV)])))).
End X.

(* [comment removed for export] *)
Lemma xhs_sub : forall (c : acfg) (CUTS : list (acs * plan)), length CUTS = 1%nat ->
  hs_sub (HScut (BgWA.ceL1 c) CUTS 1) (HScut (BgWA.ce c MS) CUTS 1).
Proof.
  intros c CUTS HL h ch H. left. exists 1%nat.
  assert (E1 : HScut (BgWA.ce c MS) CUTS 1 1 = Some (tout c ML)) by reflexivity. rewrite E1.
  destruct h as [|[|h]].
  - assert (E : HScut (BgWA.ceL1 c) CUTS 1 0 = Some (tout c ML)) by reflexivity. rewrite E in H. exact H.
  - assert (E : HScut (BgWA.ceL1 c) CUTS 1 1 = Some (tout c ML)) by reflexivity. rewrite E in H. exact H.
  - exfalso. destruct CUTS as [|x [|y r]]; try discriminate HL.
    assert (E : HScut (BgWA.ceL1 c) [x] 1 (Datatypes.S (Datatypes.S h)) = None) by (destruct h as [|[|h]]; reflexivity).
    rewrite E in H. discriminate H.
Qed.
End BgWAX.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAu8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgWAf32CertL1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWFT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA.
Import BgWAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAu8.BgWAf32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg JS0m) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_L1X : CHKX (BgWA.ceL1 cfg) 0 (BgWA.tin cfg ML) (XPLAN_L1 cfg JS0m) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (BgWA.ceL1 cfg) 1 (XTL INVm) (XLOOPC cfg INVm JS1m elem) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
(* [comment removed for export] *)
End BgWAf32CertL1.
Module BgWAf32CertS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWFT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA.
Import BgWAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAu8.BgWAf32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg JS0m INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_SX : CHKX (BgWA.ce cfg MS) 0 (BgWA.tin cfg MS) (XPLAN_S cfg JS0m INVm JS1m elem) = COk (SHole 0).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End BgWAf32CertS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi16.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgWAi16CertL1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgTc32.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA.
Import BgWAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi16.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg JS0m) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_L1X : CHKX (BgWA.ceL1 cfg) 0 (BgWA.tin cfg ML) (XPLAN_L1 cfg JS0m) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (BgWA.ceL1 cfg) 1 (XTL INVm) (XLOOPC cfg INVm JS1m elem) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
(* [comment removed for export] *)
End BgWAi16CertL1.
Module BgWAi16CertS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgTc32.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA.
Import BgWAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi16.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg JS0m INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_SX : CHKX (BgWA.ce cfg MS) 0 (BgWA.tin cfg MS) (XPLAN_S cfg JS0m INVm JS1m elem) = COk (SHole 0).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End BgWAi16CertS.
Module BgWAi8CertL1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgTc32.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA.
Import BgWAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi16.BgWAi8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg JS0m) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_L1X : CHKX (BgWA.ceL1 cfg) 0 (BgWA.tin cfg ML) (XPLAN_L1 cfg JS0m) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (BgWA.ceL1 cfg) 1 (XTL INVm) (XLOOPC cfg INVm JS1m elem) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
(* [comment removed for export] *)
End BgWAi8CertL1.
Module BgWAu8CertL1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA.
Import BgWAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAu8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg JS0m) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_L1X : CHKX (BgWA.ceL1 cfg) 0 (BgWA.tin cfg ML) (XPLAN_L1 cfg JS0m) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (BgWA.ceL1 cfg) 1 (XTL INVm) (XLOOPC cfg INVm JS1m elem) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
(* [comment removed for export] *)
End BgWAu8CertL1.
Module BgWAu8CertS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA.
Import BgWAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAu8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg JS0m INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_SX : CHKX (BgWA.ce cfg MS) 0 (BgWA.tin cfg MS) (XPLAN_S cfg JS0m INVm JS1m elem) = COk (SHole 0).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End BgWAu8CertS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgTc32. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgTc32.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import BgWA.
Import BgWAX.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi16. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi16.BgWAi8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg JS0m INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_SX : CHKX (BgWA.ce cfg MS) 0 (BgWA.tin cfg MS) (XPLAN_S cfg JS0m INVm JS1m elem) = COk (SHole 0).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
