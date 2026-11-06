(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition DMEAS (i : nat) (E : env) : Z := 2 ^ 64 - bv_unsigned (ev E i).
Definition Qd (i : nat) (n : Z) (E : env) : Prop := DMEAS i E <= n.

Lemma Qd_agree : forall i nxf n E E', (i < nxf)%nat -> env_agree nxf E E' -> Qd i n E -> Qd i n E'.
Proof. intros i nxf n E E' Hi [Hag _] H. unfold Qd, DMEAS in *. rewrite <- (Hag i Hi). exact H. Qed.

(* [comment removed for export] *)
Definition rec_cond (i nxf : nat) (cs : acs) (th : list expr) : bool :=
  (Nat.eqb (length th) nxf && Nat.ltb i nxf &&
   let '(b, c) := split_lit (nth i th (ELit 0)) in
   expr_eqb b (EVar i) && Z.leb 1 c
   && match xhi (kn cs) (EVar i) with Some h => Z.ltb (h + c) two64 | None => false end)%bool.

Section Rec.
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
#[local] Notation AINV0 := (AINV_f (nil_of SWIN) G AINVH).   (* [comment removed for export] *)

Definition callee_contract_upto (i : nat) (n : Z) (ce : gcallee) : Prop :=
  callee_contract_when SEGS SWIN G FXOK RZ SHC KCAP AINVH (Qd i n) ce.

Lemma callee_contract_of_upto : forall i ce,
  (forall n, 0 <= n -> callee_contract_upto i n ce) -> callee_contract SEGS SWIN G FXOK RZ SHC KCAP AINVH ce.
Proof.
  intros i ce H. unfold callee_contract.
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 E fx R M mdl T HB0 HC0 HBc HCc HFB _ HC HT Hex.
  apply (H (2 ^ 64) ltac:(lia) PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 E fx R M mdl T HB0 HC0 HBc HCc HFB); try assumption.
  unfold Qd, DMEAS. pose proof (u64_range (ev E i)). lia.
Qed.

(* [comment removed for export] *)
Section Caller.
Variable nx0 : nat.
Variable bcap ccap : Z.
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
#[local] Notation AINVc := (AINVf PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation VSHc := (VSHf HIDc HIDFc).

Definition node_callrec (i : nat) (ce : gcallee) (args : list expr) (cs : acs) : option acs :=
  node_call_cond SEGS A G nx0 bcap ccap (rec_cond i (ce_nxf ce)) ce args cs.

Theorem node_callrec_sound : forall i n ce args,
  callee_contract_upto i n ce ->
  (forall E, UINV E -> DMEAS i E <= n + 1) ->
  GPS.node1_stmtN SEGS nx0 PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc FXOK UINV RZ always (node_callrec i ce args).
Proof.
  intros i n ce args CC HU. unfold node_callrec.
  apply (node_call_cond_sound SEGS A SEGS_in_hull HULL_ok SEGS_wx SWIN G FXOK RZ RZ_silent1 SHC KCAP AINVH HP G_ro_img G_img_al G_img_shlo SWIN_img SEGS_out A_img_hi A_img_lo
           nx0 PERMc SPTOPc FS0 HIDc HIDFc M0c B0c C0c B0c_nonneg C0c_nonneg FTOPc FTOPc_ok bcap ccap bcap_ok ccap_ok UINV UINV_agree
           (Qd i n) (rec_cond i (ce_nxf ce)) ce args CC).
  intros cs th E fx R M model Hbind Hc HC. unfold rec_cond in Hc.
  apply andb_prop in Hc as [H12 Hlet]. apply andb_prop in H12 as [Hlen Hi].
  destruct (split_lit (nth i th (ELit 0))) as [b c] eqn:Hsp.
  apply andb_prop in Hlet as [Hlet Hx]. apply andb_prop in Hlet as [Hb H1].
  apply Nat.eqb_eq in Hlen. apply Nat.ltb_lt in Hi. apply expr_eqb_eq in Hb. subst b. apply Z.leb_le in H1.
  destruct (xhi (kn cs) (EVar i)) as [h|] eqn:Hh; [|discriminate]. apply Z.ltb_lt in Hx.
  pose proof (xhi_sound SEGS E _ (kn cs) (EVar i) h (co_know HC) Hh) as Hhi. cbn [edenot] in Hhi.
  pose proof (HU E (co_uinv HC)) as HD.
  unfold Qd, DMEAS in *. cbn [tenv ev]. rewrite Hlen.
  replace (Nat.ltb i (ce_nxf ce)) with true by (symmetry; apply Nat.ltb_lt; exact Hi).
  rewrite (split_lit_denot E (nth i th (ELit 0)) (EVar i) c Hsp). cbn [edenot].
  pose proof (u64_range (ev E i)). unfold two64 in Hx. rewrite u64_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Definition node_callrec2 (i : nat) (c : gcallee2) (args : list expr) (cs : acs) : option (acs * acs) :=
  node_call2_cond SEGS A nx0 bcap ccap G (rec_cond i (c2_nxf c)) c args cs.

Theorem node_callrec2_sound : forall i n c args,
  callee_contract_upto i n (c2_merged c) ->
  (forall E, UINV E -> DMEAS i E <= n + 1) ->
  node2_stmt SEGS nx0 PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc FXOK UINV RZ (node_callrec2 i c args).
Proof.
  intros i n c args CC HU. unfold node_callrec2.
  apply (node_call2_cond_sound SEGS A SEGS_in_hull HULL_ok SEGS_wx SWIN G FXOK RZ RZ_silent1 SHC KCAP AINVH HP G_ro_img G_img_al G_img_shlo SWIN_img SEGS_out A_img_hi A_img_lo
           nx0 PERMc SPTOPc FS0 HIDc HIDFc M0c B0c C0c B0c_nonneg C0c_nonneg FTOPc FTOPc_ok bcap ccap bcap_ok ccap_ok UINV UINV_agree
           (Qd i n) (rec_cond i (c2_nxf c)) c args CC).
  intros cs th E fx R M model Hbind Hc HC. unfold rec_cond in Hc.
  apply andb_prop in Hc as [H12 Hlet]. apply andb_prop in H12 as [Hlen Hi].
  destruct (split_lit (nth i th (ELit 0))) as [b c'] eqn:Hsp.
  apply andb_prop in Hlet as [Hlet Hx]. apply andb_prop in Hlet as [Hb H1].
  apply Nat.eqb_eq in Hlen. apply Nat.ltb_lt in Hi. apply expr_eqb_eq in Hb. subst b. apply Z.leb_le in H1.
  destruct (xhi (kn cs) (EVar i)) as [h|] eqn:Hh; [|discriminate]. apply Z.ltb_lt in Hx.
  pose proof (xhi_sound SEGS E _ (kn cs) (EVar i) h (co_know HC) Hh) as Hhi. cbn [edenot] in Hhi.
  pose proof (HU E (co_uinv HC)) as HD.
  unfold Qd, DMEAS in *. cbn [tenv ev]. cbn [c2_nxf c2_class0 ce_nxf] in Hlen. rewrite Hlen.
  replace (Nat.ltb i (c2_nxf c)) with true by (symmetry; apply Nat.ltb_lt; exact Hi).
  rewrite (split_lit_denot E (nth i th (ELit 0)) (EVar i) c' Hsp). cbn [edenot].
  pose proof (u64_range (ev E i)). unfold two64 in Hx. rewrite u64_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Variable self_id : nat.
Variable idepth : nat.
Variable ce_self : gcallee.
Variable CT : nat -> option gcallee.
Hypothesis CT_sound : forall id ce, CT id = Some ce -> callee_contract SEGS SWIN G FXOK RZ SHC KCAP AINVH ce.



(* [comment removed for export] *)
Variable self2_id : nat.
Variable c2_self : gcallee2.
Variable CT2 : nat -> option gcallee2.
Hypothesis CT2_sound : forall id c, CT2 id = Some c -> callee_contract SEGS SWIN G FXOK RZ SHC KCAP AINVH (c2_merged c).


(* [comment removed for export] *)
Definition XNr_gen (XN0 : nat -> list expr -> acs -> option acs) (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id self_id then node_callrec idepth ce_self args cs else XN0 id args cs.
Theorem XNr_gen_sound : forall XN0 n,
  GPS.ext_stmt SEGS nx0 XN0 PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc FXOK UINV RZ ->
  callee_contract_upto idepth n ce_self ->
  (forall E, UINV E -> DMEAS idepth E <= n + 1) ->
  GPS.ext_stmt SEGS nx0 (XNr_gen XN0) PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc FXOK UINV RZ.
Proof.
  intros XN0 n H0 CC HU id args. unfold XNr_gen. destruct (Nat.eqb id self_id).
  - exact (node_callrec_sound idepth n ce_self args CC HU).
  - exact (H0 id args).
Qed.
Definition XBr_gen (XB0 : nat -> list expr -> acs -> option (acs * acs)) (id : nat) (args : list expr) (cs : acs) : option (acs * acs) :=
  if Nat.eqb id self2_id then node_callrec2 idepth c2_self args cs else XB0 id args cs.
Theorem XBr_gen_sound : forall XB0 n,
  GPS.ext2_stmt SEGS nx0 XB0 PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc FXOK UINV RZ ->
  callee_contract_upto idepth n (c2_merged c2_self) ->
  (forall E, UINV E -> DMEAS idepth E <= n + 1) ->
  GPS.ext2_stmt SEGS nx0 (XBr_gen XB0) PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc FXOK UINV RZ.
Proof.
  intros XB0 n H0 CC HU id args. unfold XBr_gen. destruct (Nat.eqb id self2_id).
  - exact (node_callrec2_sound idepth n c2_self args CC HU).
  - exact (H0 id args).
Qed.
End Caller.

(* [comment removed for export] *)
Section Cert.
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
Hypothesis CERT : AP.check SEGS IT A (ce_nxf ce) LIMIT GPS.ISP0 XN XE0 XB (HSce ce) KC bfuel fuel None (ce_tin ce) p = COk s.


End Cert.

(* [comment removed for export] *)
Section CertCut.
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
Variable CUTS : list (acs * plan).
Hypothesis CUTS_ok : forall i T k, nth_error CUTS i = Some (T, k) -> exists sh,
  gplan_ok k = true /\ holes_only sh = true /\
  AP.check SEGS IT A (ce_nxf ce) LIMIT GPS.ISP0 XN XE0 XB (HScut ce CUTS (S i)) KC bfuel fuel None T k = COk sh.
Hypothesis CERT : AP.check SEGS IT A (ce_nxf ce) LIMIT GPS.ISP0 XN XE0 XB (HScut ce CUTS 0) KC bfuel fuel None (ce_tin ce) p = COk s.

Theorem contract_of_cert_rec_cut : forall n, 0 <= n -> callee_contract_upto idepth n ce.
Proof.
  intros n Hn. revert n Hn. refine (Wf_Z.Zlt_0_ind _ _). intros n IH Hn.
  destruct (Z.eq_dec n 0) as [->|Hnz].
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 E fx R M mdl T _ _ _ _ _ HQ. exfalso.
    unfold Qd, DMEAS in HQ. pose proof (u64_range (ev E idepth)). lia.
  - unfold callee_contract_upto.
    refine (contract_of_cert_when_cut SEGS A SEGS_in_hull HULL_ok SWIN G FXOK RUN RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP G_ro_img G_img_al G_img_shlo A_img_hi A_img_lo SEGS_wx
             ce IT IT_ok LIMIT KC bfuel fuel XN (Qd idepth n) _ _ XB _ CUTS CUTS_ok p s p_ok s_ok CERT).
    + intros E E' Hag HQ. eapply Qd_agree; [exact idepth_lt | exact Hag | exact HQ].
    + intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa HUQ.
      apply (XN_sound_rec (n - 1) PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV ltac:(lia) HB0 HC0 HBc HCc HFB HUa).
      * intros E HE. pose proof (HUQ E HE) as X. unfold Qd in X. lia.
      * apply IH. lia.
    + intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa HUQ.
      apply (XB_sound_rec (n - 1) PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV ltac:(lia) HB0 HC0 HBc HCc HFB HUa).
      * intros E HE. pose proof (HUQ E HE) as X. unfold Qd in X. lia.
      * apply IH. lia.
Qed.

Corollary contract_of_cert_rec_cut_all : callee_contract SEGS SWIN G FXOK RZ SHC KCAP AINVH ce.
Proof. exact (callee_contract_of_upto idepth ce contract_of_cert_rec_cut). Qed.
End CertCut.
End Rec.

