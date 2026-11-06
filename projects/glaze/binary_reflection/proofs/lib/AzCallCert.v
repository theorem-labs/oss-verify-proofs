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
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)

Section Cert.
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

(* [comment removed for export] *)
Variable ce : gcallee.
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable LIMIT : Z.
Variable KC bfuel fuel : nat.
Variable XN : nat -> list expr -> acs -> option acs.
(* [comment removed for export] *)
Variable Q : env -> Prop.
Hypothesis Q_agree : forall E E', env_agree (ce_nxf ce) E E' -> Q E -> Q E'.
(* [comment removed for export] *)
Hypothesis XN_sound : forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 (UINV : env -> Prop),
  0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> Q E) ->
  GPS.ext_stmt SEGS (ce_nxf ce) XN PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINVf PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf FXOK UINV RZ.
(* [comment removed for export] *)
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Hypothesis XB_sound : forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 (UINV : env -> Prop),
  0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> Q E) ->
  GPS.ext2_stmt SEGS (ce_nxf ce) XB PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINVf PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf FXOK UINV RZ.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.
Definition HSce (h : nat) : option acs := nth_error (ce_touts ce) h.

Variable p : plan.
Variable s : shape.
Hypothesis p_ok : gplan_ok p = true.
Hypothesis s_ok : holes_only s = true.
Hypothesis CERT : AP.check SEGS IT A (ce_nxf ce) LIMIT GPS.ISP0 XN XE0 XB HSce KC bfuel fuel None (ce_tin ce) p = COk s.

(* [comment removed for export] *)
Lemma sd_holes_only : forall (T : TSet) E fs sh, holes_only sh = true -> t_eq (sd (fun _ _ _ => T) T E fs sh) T.
Proof.
  intros T E fs sh. induction sh; cbn [holes_only sd]; intros H tr; try discriminate; try apply iff_refl.
  - apply andb_prop in H as [H1 H2]. unfold t_alt2. split.
    + intros [X|X]; [exact (proj1 (IHsh1 H1 tr) X) | exact (proj1 (IHsh2 H2 tr) X)].
    + intros X. left. exact (proj2 (IHsh1 H1 tr) X).
  - apply andb_prop in H as [H1 H2]. destruct (Z.leb _ _); [exact (IHsh1 H1 tr) | exact (IHsh2 H2 tr)].
Qed.

Theorem contract_of_cert_when : callee_contract_when SEGS SWIN G FXOK RZ SHC KCAP AINVH Q ce.
Proof.
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 E fx R M mdl T HB0 HC0 HBc HCc HFB HQ HC HT Hexits.
  pose proof (hprops_nil SWIN G SHC AINVH HP) as HPn.
  set (UINV := fun E' => env_agree (ce_nxf ce) E E').
  assert (UINV_agree : forall E1 E2, env_agree (ce_nxf ce) E1 E2 -> UINV E1 -> UINV E2).
  { intros E1 E2 H12 H1. unfold UINV in *. eapply env_agree_trans; [exact H1 | exact H12]. }
  assert (UINV_Q : forall E1, UINV E1 -> Q E1).
  { intros E1 H1. eapply Q_agree; [exact H1 | exact HQ]. }
  assert (HSs : GPS.holes_stmt SEGS HSce PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINVf PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf FXOK UINV (fun _ _ _ => T) RZ).
  { intros h ch Hh E1 fx1 R1 M1 mdl1 HC1. unfold HSce in Hh.
    apply (Hexits ch E1 fx1 R1 M1 mdl1).
    - eapply nth_error_In. exact Hh.
    - exact (co_uinv HC1).
    - destruct HC1; constructor; try assumption. exact I.
    - rewrite (co_fs HC1). symmetry. exact (co_fs HC). }
  pose proof (GPS.check_soundA SEGS IT IT_ok A (ce_nxf ce) LIMIT HSce XN XE0 XB AP.XA0 AP.XT0 KC (nil_of SWIN) PERMf TOPf FS0 SHC (VSHf HID HIDF)
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
                HSs fuel bfuel None p (ce_tin ce) s p_ok CERT E fx R M mdl T) as X.
  eapply RZ_conseq; [apply X | exact (sd_holes_only T E (m_fs mdl) s s_ok)].
  - destruct HC; constructor; try assumption. unfold UINV. apply env_agree_refl.
  - exact I.
  - exact HT.
Qed.

End Cert.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CertCut.
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
Variable CUTS : list (acs * plan).
Definition NT : nat := length (ce_touts ce).
Definition HScut (k : nat) (h : nat) : option acs :=
  if Nat.ltb h NT then nth_error (ce_touts ce) h
  else let i := (h - NT)%nat in
       if Nat.leb k i then match nth_error CUTS i with Some c => Some (fst c) | None => None end else None.
Hypothesis CUTS_ok : forall i T k, nth_error CUTS i = Some (T, k) -> exists sh,
  gplan_ok k = true /\ holes_only sh = true /\
  AP.check SEGS IT A (ce_nxf ce) LIMIT GPS.ISP0 XN XE0 XB (HScut (S i)) KC bfuel fuel None T k = COk sh.
Variable p : plan.
Variable s : shape.
Hypothesis p_ok : gplan_ok p = true.
Hypothesis s_ok : holes_only s = true.
Hypothesis CERT : AP.check SEGS IT A (ce_nxf ce) LIMIT GPS.ISP0 XN XE0 XB (HScut 0) KC bfuel fuel None (ce_tin ce) p = COk s.

Theorem contract_of_cert_when_cut : callee_contract_when SEGS SWIN G FXOK RZ SHC KCAP AINVH Q ce.
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
  { induction d as [|d IHd]; intros k Hk h ch Hh E1 fx1 R1 M1 mdl1 HC1; unfold HScut in Hh.
    - destruct (Nat.ltb h NT) eqn:Hlt; [exit_hole Hexits Hh HC1 HC|].
      destruct (Nat.leb k (h - NT)) eqn:Hle; [|discriminate]. apply Nat.leb_le in Hle.
      destruct (nth_error CUTS (h - NT)) as [c|] eqn:Hn; [|discriminate].
      exfalso. assert (Hl : (h - NT < length CUTS)%nat) by (apply nth_error_Some; rewrite Hn; discriminate). lia.
    - destruct (Nat.ltb h NT) eqn:Hlt; [exit_hole Hexits Hh HC1 HC|].
      destruct (Nat.leb k (h - NT)) eqn:Hle; [|discriminate]. apply Nat.leb_le in Hle.
      destruct (nth_error CUTS (h - NT)) as [[Tc kc]|] eqn:Hn; [|discriminate]. cbn [fst] in Hh. injection Hh as <-.
      destruct (Nat.eq_dec (h - NT) k) as [Heq|Hne].
      + (* [comment removed for export] *)
        destruct (CUTS_ok (h - NT)%nat Tc kc Hn) as (sc & Hgp & Hho & Hck).
        pose proof (GPS.check_soundA SEGS IT IT_ok A (ce_nxf ce) LIMIT (HScut (S (h - NT))) XN XE0 XB AP.XA0 AP.XT0 KC (nil_of SWIN) PERMf TOPf FS0 SHC (VSHf HID HIDF)
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
        eapply RZ_conseq; [apply X; [exact HC1 | exact I | exact HT] | exact (sd_holes_only T E1 (m_fs mdl1) sc Hho)].
      + (* [comment removed for export] *)
        refine (IHd (S k) ltac:(lia) h Tc _ E1 fx1 R1 M1 mdl1 HC1).
        unfold HScut. rewrite Hlt. replace (Nat.leb (S k) (h - NT)) with true by (symmetry; apply Nat.leb_le; lia).
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
End CertCut.

(* [comment removed for export] *)
Theorem contract_of_cert :
  forall SEGS {RC : run_ceil} A, (forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None) ->
  APS.hull_ok A -> forall SWIN G FXOK, GPS.RUN_SOUND SEGS FXOK ->
  forall RZ : GPS.rz_t, GPS.RZ_SILENT1 SEGS RZ -> GPS.RZ_EXIT SEGS RZ -> GPS.RZ_CONSEQ RZ ->
  forall SHC KCAP AINVH, hprops SWIN G SHC AINVH ->
  g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G ->
  0 <= g_img_lo G /\ g_img_lo G mod 8 = 0 /\ g_img_hi G mod 8 = 0 -> g_img_hi G <= SHMAPLO ->
  img_hi A = g_img_hi G -> img_lo A = g_img_lo G -> wx_segs_nowrap SEGS ->
  forall ce IT, itab_sound SEGS IT -> forall LIMIT KC bfuel fuel XN,
  (forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 (UINV : env -> Prop),
     0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
     (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
     GPS.ext_stmt SEGS (ce_nxf ce) XN PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f (nil_of SWIN) G AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf FXOK UINV RZ) ->
  forall p s, gplan_ok p = true -> holes_only s = true ->
  AP.check SEGS IT A (ce_nxf ce) LIMIT GPS.ISP0 XN XE0 XB0 (HSce ce) KC bfuel fuel None (ce_tin ce) p = COk s ->
  callee_contract SEGS SWIN G FXOK RZ SHC KCAP AINVH ce.
Proof.
  intros SEGS RC A Hh Hk SWIN G FXOK RUN RZ RZs RZe RZc SHC KCAP AINVH HP G1 G2 G3 G4 G5 G6 ce IT ITok LIMIT KC bfuel fuel XN XNs p s Hp Hs CERT.
  unfold callee_contract.
  unshelve (eapply (contract_of_cert_when SEGS A Hh Hk SWIN G FXOK RUN RZ RZs RZe RZc SHC KCAP AINVH HP G1 G2 G3 G4 G5 G6 ce IT ITok LIMIT KC bfuel fuel XN QTRUE _ _ XB0 _ p s Hp Hs CERT)).
  all: first [ exact Hp | exact Hs | exact CERT | (intros; exact I) | (intros; eapply XNs; eassumption)
             | (intros; intros id args cs csa csb E1 fx1 R1 M1 m1 T1 HC1 Hn; discriminate Hn) ].
Qed.

(* [comment removed for export] *)
Theorem contract_of_cert_xb :
  forall SEGS {RC : run_ceil} A, (forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None) ->
  APS.hull_ok A -> forall SWIN G FXOK, GPS.RUN_SOUND SEGS FXOK ->
  forall RZ : GPS.rz_t, GPS.RZ_SILENT1 SEGS RZ -> GPS.RZ_EXIT SEGS RZ -> GPS.RZ_CONSEQ RZ ->
  forall SHC KCAP AINVH, hprops SWIN G SHC AINVH ->
  g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G ->
  0 <= g_img_lo G /\ g_img_lo G mod 8 = 0 /\ g_img_hi G mod 8 = 0 -> g_img_hi G <= SHMAPLO ->
  img_hi A = g_img_hi G -> img_lo A = g_img_lo G -> wx_segs_nowrap SEGS ->
  forall ce IT, itab_sound SEGS IT -> forall LIMIT KC bfuel fuel XN,
  (forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 (UINV : env -> Prop),
     0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
     (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
     GPS.ext_stmt SEGS (ce_nxf ce) XN PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f (nil_of SWIN) G AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf FXOK UINV RZ) ->
  forall XB,
  (forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 (UINV : env -> Prop),
     0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
     (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
     GPS.ext2_stmt SEGS (ce_nxf ce) XB PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f (nil_of SWIN) G AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf FXOK UINV RZ) ->
  forall p s, gplan_ok p = true -> holes_only s = true ->
  AP.check SEGS IT A (ce_nxf ce) LIMIT GPS.ISP0 XN XE0 XB (HSce ce) KC bfuel fuel None (ce_tin ce) p = COk s ->
  callee_contract SEGS SWIN G FXOK RZ SHC KCAP AINVH ce.
Proof.
  intros SEGS RC A Hh Hk SWIN G FXOK RUN RZ RZs RZe RZc SHC KCAP AINVH HP G1 G2 G3 G4 G5 G6 ce IT ITok LIMIT KC bfuel fuel XN XNs XB XBs p s Hp Hs CERT.
  unfold callee_contract.
  unshelve (eapply (contract_of_cert_when SEGS A Hh Hk SWIN G FXOK RUN RZ RZs RZe RZc SHC KCAP AINVH HP G1 G2 G3 G4 G5 G6 ce IT ITok LIMIT KC bfuel fuel XN QTRUE _ _ XB _ p s Hp Hs CERT)).
  all: first [ exact Hp | exact Hs | exact CERT | (intros; exact I) | (intros; eapply XNs; eassumption) | (intros; eapply XBs; eassumption) ].
Qed.

(* [comment removed for export] *)
Theorem contract_of_cert_xb_cut :
  forall SEGS {RC : run_ceil} A, (forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None) ->
  APS.hull_ok A -> forall SWIN G FXOK, GPS.RUN_SOUND SEGS FXOK ->
  forall RZ : GPS.rz_t, GPS.RZ_SILENT1 SEGS RZ -> GPS.RZ_EXIT SEGS RZ -> GPS.RZ_CONSEQ RZ ->
  forall SHC KCAP AINVH, hprops SWIN G SHC AINVH ->
  g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G ->
  0 <= g_img_lo G /\ g_img_lo G mod 8 = 0 /\ g_img_hi G mod 8 = 0 -> g_img_hi G <= SHMAPLO ->
  img_hi A = g_img_hi G -> img_lo A = g_img_lo G -> wx_segs_nowrap SEGS ->
  forall ce IT, itab_sound SEGS IT -> forall LIMIT KC bfuel fuel XN,
  (forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 (UINV : env -> Prop),
     0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
     (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
     GPS.ext_stmt SEGS (ce_nxf ce) XN PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f (nil_of SWIN) G AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf FXOK UINV RZ) ->
  forall XB,
  (forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 (UINV : env -> Prop),
     0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
     (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
     GPS.ext2_stmt SEGS (ce_nxf ce) XB PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f (nil_of SWIN) G AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf FXOK UINV RZ) ->
  forall (CUTS : list (acs * plan)),
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh,
     gplan_ok k = true /\ holes_only sh = true /\
     AP.check SEGS IT A (ce_nxf ce) LIMIT GPS.ISP0 XN XE0 XB (HScut ce CUTS (S i)) KC bfuel fuel None T k = COk sh) ->
  forall p s, gplan_ok p = true -> holes_only s = true ->
  AP.check SEGS IT A (ce_nxf ce) LIMIT GPS.ISP0 XN XE0 XB (HScut ce CUTS 0) KC bfuel fuel None (ce_tin ce) p = COk s ->
  callee_contract SEGS SWIN G FXOK RZ SHC KCAP AINVH ce.
Proof.
  intros SEGS RC A Hh Hk SWIN G FXOK RUN RZ RZs RZe RZc SHC KCAP AINVH HP G1 G2 G3 G4 G5 G6 ce IT ITok LIMIT KC bfuel fuel XN XNs XB XBs CUTS Hcuts p s Hp Hs CERT.
  unfold callee_contract.
  unshelve (eapply (contract_of_cert_when_cut SEGS A Hh Hk SWIN G FXOK RUN RZ RZs RZe RZc SHC KCAP AINVH HP G1 G2 G3 G4 G5 G6 ce IT ITok LIMIT KC bfuel fuel XN QTRUE _ _ XB _ CUTS Hcuts p s Hp Hs CERT)).
  all: first [ exact Hp | exact Hs | exact CERT | (intros; exact I) | (intros; eapply XNs; eassumption) | (intros; eapply XBs; eassumption) ].
Qed.

Section Hooks.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable IT : itab.
Variable A : atable.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis IT_ok : itab_sound SEGS IT.       (* [comment removed for export] *)
Variable nx0 : nat.
Variable SWIN : list (Z * Z).
Variable G : gtable.
Variable bcap ccap : Z.
Variable FXOK : FX -> Prop.
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
(* [comment removed for export] *)
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable HIDc : list (Z * Z).
Variable HIDFc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Hypothesis B0c_nonneg : 0 <= B0c.
Hypothesis C0c_nonneg : 0 <= C0c.
Hypothesis bcap_ok : B0c + bcap <= GBUDGET.
Hypothesis ccap_ok : C0c + ccap <= GCOUNT.
Variable FTOPc : Z.                                                (* [comment removed for export] *)
Hypothesis FTOPc_ok : Z.of_nat (length HIDFc) + FTOPc <= FMIN.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 SEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT SEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
#[local] Notation AINVc := (AINV_f SWIN G AINVH PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation VSHc := (VSHf HIDc HIDFc).

(* [comment removed for export] *)
Variable CT : nat -> option gcallee.
Hypothesis CT_sound : forall id ce, CT id = Some ce -> callee_contract SEGS SWIN G FXOK RZ SHC KCAP AINVH ce.

Definition XNc (id : nat) (args : list expr) (cs : acs) : option acs :=
  match CT id with
  | Some ce => node_call SEGS A nx0 bcap ccap G ce args cs
  | None =>
      match id with      (* [comment removed for export] *)
      | 42%nat => node_enumload SEGS IT nx0 cs
      | 43%nat => node_popcnt args cs
      | 44%nat => node_havoc64 nx0 args cs
      | 45%nat => node_enumreg args cs
      | _ => XNg SEGS IT A nx0 G bcap ccap id args cs
      end
  end.

Theorem XNc_sound :
  gcontracts SEGS IT A nx0 PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc FXOK UINV RZ G bcap ccap ->
  GPS.ext_stmt SEGS nx0 XNc PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc FXOK UINV RZ.
Proof.
  intros GCs id args. unfold XNc. destruct (CT id) as [ce|] eqn:Hct.
  - exact (node_call_sound SEGS A SEGS_in_hull HULL_ok SEGS_wx SWIN G FXOK RZ RZ_silent1 SHC KCAP AINVH HP G_ro_img G_img_al G_img_shlo SWIN_img SEGS_out A_img_hi A_img_lo nx0 PERMc SPTOPc FS0 HIDc HIDFc M0c B0c C0c B0c_nonneg C0c_nonneg FTOPc FTOPc_ok bcap ccap bcap_ok ccap_ok UINV UINV_agree ce args (CT_sound id ce Hct)).
  - pose proof (AINV_f_frame SWIN G SHC AINVH HP G_ro_img G_img_al G_img_shlo PERMc SPTOPc HIDc HIDFc M0c B0c C0c) as AF.
    pose proof (AINV_f_lazy SWIN G SHC AINVH HP PERMc SPTOPc HIDc HIDFc M0c B0c C0c) as AL.
    assert (AFa : forall Lc Lf B C K M mdl, AINVc Lc Lf B C K M mdl ->
              Forall (fun iv => 0 < bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL_run
                                /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_lo A \/ img_hi A <= bv_unsigned (fst iv))) (m_vm_lazy mdl)).
    { intros. rewrite A_img_hi, A_img_lo. eapply (AINV_f_facts SWIN G SHC AINVH HP); eassumption. }
    do 42 (destruct id as [|id]; [exact (XNg_sound SEGS IT A nx0 PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc FXOK UINV RZ G bcap ccap GCs _ args)|]).
    destruct id as [|id]; [apply GPS.node1_stmt_N; exact (node_enumload_sound SEGS IT IT_ok nx0 SWIN PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc AF AL A AFa SEGS_in_hull SEGS_wx FXOK UINV UINV_agree RZ RZ_silent1)|].
    destruct id as [|id]; [apply GPS.node1_stmt_N; exact (node_popcnt_sound SEGS nx0 PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc FXOK UINV RZ args)|].
    destruct id as [|id]; [apply GPS.node1_stmt_N; exact (node_havoc64_sound SEGS nx0 SWIN PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc AF FXOK UINV UINV_agree RZ args)|].
    destruct id as [|id]; [apply GPS.node1_stmt_N; exact (node_enumreg_sound SEGS nx0 PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc FXOK UINV RZ args)|].
    exact (XNg_sound SEGS IT A nx0 PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc FXOK UINV RZ G bcap ccap GCs _ args).
Qed.

(* [comment removed for export] *)
Variable CT2 : nat -> option gcallee2.
Hypothesis CT2_sound : forall id c, CT2 id = Some c -> callee_contract SEGS SWIN G FXOK RZ SHC KCAP AINVH (c2_merged c).
Definition XBc (id : nat) (args : list expr) (cs : acs) : option (acs * acs) :=
  match CT2 id with
  | Some c => node_call2F SEGS A nx0 bcap ccap G c args cs   (* [comment removed for export] *)
  | None => XBg SEGS nx0 G bcap ccap id args cs
  end.
(* [comment removed for export] *)
Theorem XBc_sound0 :
  GPS.ext2_stmt SEGS nx0 XBc PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc FXOK UINV RZ.
Proof.
  intros id args. unfold XBc. destruct (CT2 id) as [c|] eqn:Hct.
  - intros cs csa csb E fx R M model T HC Hn. rewrite node_call2F_eq in Hn.
    exact (node_call2_sound SEGS A SEGS_in_hull HULL_ok SEGS_wx SWIN G FXOK RZ RZ_silent1 SHC KCAP AINVH HP G_ro_img G_img_al G_img_shlo SWIN_img SEGS_out A_img_hi A_img_lo nx0 PERMc SPTOPc FS0 HIDc HIDFc M0c B0c C0c B0c_nonneg C0c_nonneg FTOPc FTOPc_ok bcap ccap bcap_ok ccap_ok UINV UINV_agree c args (CT2_sound id c Hct) cs csa csb E fx R M model T HC Hn).
  - exact (XBg_sound0 SEGS nx0 PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc FXOK UINV RZ G bcap ccap id args).
Qed.
End Hooks.
