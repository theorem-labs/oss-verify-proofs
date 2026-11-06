(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS2A OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS0SoundA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvCertSoundZ. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A.BoDrvS0A OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS2A.BoDrvS1A OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvGSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS0SoundA.BoDrvNodesSoundA11 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS0SoundA.BoDrvNodesAllA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A.BoDrvInstFactsA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS0SoundA.BoDrvUinvA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS0SoundA.BoDrvCertSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS0SoundA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvCertSoundZ.BoDrvS0SpecA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvCertSoundZ OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvGlueLibA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.
#[local] Notation RZ := (realizes BSEGS).

Record dinst : Type := DI {
  di_SHC : list (Z * Z);
  di_KCAP : Z;
  di_AINVH1 : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop;        (* [comment removed for export] *)
  di_AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop;         (* [comment removed for export] *)
  di_SWIN : list (Z * Z);
  di_SPTOP : Z;
  di_HID : list (Z * Z);
  di_HIDF : list (Z * Z);
  di_M0 : word -> option byte;
  di_B0 : Z;
  di_C0 : Z;
  di_FTOP : Z
}.

(* [comment removed for export] *)
Definition uxa (UX : env -> Prop) : Prop := forall E E', env_agree NXD E E' -> UX E -> UX E'.

(* [comment removed for export] *)
Definition UXf (data : list byte) (E : env) : Prop := bv_unsigned (ev E 4%nat) = APS.flen data.
Definition UXc (data : list byte) (E : env) : Prop :=
  UXf data E /\ uE E (EVar 3) = Z.of_nat (length data) /\ (Z.of_nat (length data) < 65536 -> uE E (EVar 5) <= EVT).   (* [comment removed for export] *)
Lemma UXf_a : forall data, uxa (UXf data).
Proof. intros data E E' [Hev _] H. unfold UXf in *. rewrite <- (Hev 4%nat) by (unfold NXD; lia). exact H. Qed.
Lemma UXc_a : forall data, uxa (UXc data).
Proof.
  intros data E E' Hag (H1 & H2 & H3). split; [exact (UXf_a data E E' Hag H1)|]. destruct Hag as [Hev _]. unfold uE in *. cbn [edenot] in *.
  rewrite <- (Hev 3%nat), <- (Hev 5%nat) by (unfold NXD; lia). split; assumption.
Qed.
Lemma flen_le : forall data, APS.flen data <= DNA.FCAP. Proof. intros data. unfold APS.flen, DNA.FCAP. lia. Qed.
(* [comment removed for export] *)
Lemma blob3 : forall a0 p fs data E, U_drv a0 p fs data E -> UXf data E -> eb E 3%nat = APS.chunk 0 data.
Proof.
  intros a0 p fs data E (_ & _ & _ & _ & _ & H6 & _) HX. unfold UXf in HX.
  destruct (H6 ltac:(rewrite HX; apply flen_le)) as (_ & _ & _ & _ & Hch). exact (Hch 0%nat ltac:(lia)).
Qed.

(* [comment removed for export] *)
Definition UXr (data : list byte) (len cap : Z) (E : env) : Prop := UXf data E /\ uE E (EVar 3) = len /\ uE E (EVar 2) = cap.
Lemma UXr_a : forall data len cap, uxa (UXr data len cap).
Proof.
  intros data len cap E E' Hag (H1 & H2 & H3). split; [exact (UXf_a data E E' Hag H1)|]. destruct Hag as [Hev _]. unfold uE in *. cbn [edenot] in *.
  rewrite <- (Hev 3%nat), <- (Hev 2%nat) by (unfold NXD; lia). split; assumption.
Qed.

Section Glue.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable I : dinst.
Variables (a0 p : list byte) (fs : Fs.Fs) (data : list byte).

Definition AINVg (AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop) (M0 : word -> option byte) :=
  AINV_f (di_SWIN I) GBOTH AINVH PERM_A_lit (di_SPTOP I) (di_HID I) (di_HIDF I) M0 (di_B0 I) (di_C0 I).
(* [comment removed for export] *)
Definition csG (AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop) (UX : env -> Prop)
  : env -> acs -> GPS.FX -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  GPS.cs_ok BSEGS PERM_A_lit (di_SPTOP I) fs (di_SHC I) (VSHf (di_HID I) (di_HIDF I)) (AINVg AINVH (di_M0 I)) (di_KCAP I) (di_FTOP I) fx_ok (UINVd a0 p fs data UX).
Definition cs1 := csG (di_AINVH1 I).                       (* [comment removed for export] *)
Definition csA := csG (di_AINVH I).                        (* [comment removed for export] *)
#[local] Notation GCg AINVH UX M0 := (gcontracts_core BSEGS ITA ABOTH NXD PERM_A_lit (di_SPTOP I) fs (di_SHC I) (VSHf (di_HID I) (di_HIDF I)) (AINVg AINVH M0) (di_KCAP I) (di_FTOP I) fx_ok
       (UINVd a0 p fs data UX) RZ GBOTH).

Definition M2S_stmt (X : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop) : Prop :=
  forall L LF B C K M mdl, X L LF B C K M mdl ->
  rdn BSEGS M (Z_to_bv 64 0x10eea8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn BSEGS M (Z_to_bv 64 0x10eea0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))
  /\ exists me : Z, rdn BSEGS M (Z_to_bv 64 0x10eeb0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 me)).
Definition DTH_stmt (X : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop) : Prop :=
  forall L LF B C K M mdl, X L LF B C K M mdl ->
  rdn BSEGS M (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ exists cpm : byte, rdn BSEGS M (Z_to_bv 64 0x10da1c) 1 = Some [cpm] /\ bv_unsigned cpm <> 0.
Definition DTF_stmt (X : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop) : Prop :=
  forall L LF B C K M M' mdl, X L LF B C K M mdl ->
  (forall a : word, M' a <> M a -> (in_lsb (bv_unsigned a) = true \/ in_mub (bv_unsigned a) = true) /\ M' a <> None) ->
  rdn BSEGS M' (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  X L LF B C K M' mdl.
(* [comment removed for export] *)
Definition cells_stmt X : Prop := M2S_stmt X /\ DTH_stmt X /\ DTF_stmt X.

Record file_hyps : Prop := FH {
  fh_HP1 : hprops (di_SWIN I) GBOTH (di_SHC I) (di_AINVH1 I);
  fh_HP : hprops (di_SWIN I) GBOTH (di_SHC I) (di_AINVH I);
  fh_SWIN_img : forall lo hi, In (lo, hi) (di_SWIN I) ->
     g_ro_hi GBOTH <= lo /\ hi <= g_img_hi GBOTH /\ (forall plo phi, In (plo, phi) (g_priv GBOTH) -> hi <= plo \/ phi <= lo);
  fh_B0 : 0 <= di_B0 I;
  fh_C0 : 0 <= di_C0 I;
  fh_bcap : di_B0 I + BCAP <= GBUDGET;
  fh_ccap : di_C0 I + CCAP <= GCOUNT;
  fh_FTOP : Z.of_nat (length (di_HIDF I)) + di_FTOP I <= FMIN;
  (* [comment removed for export] *)
  fh_GC : forall UX, uxa UX -> forall M0 : word -> option byte,
     gcontracts BSEGS ITA ABOTH NXD PERM_A_lit (di_SPTOP I) fs (di_SHC I) (VSHf (di_HID I) (di_HIDF I)) (AINVg (di_AINVH I) M0) (di_KCAP I) (di_FTOP I) fx_ok
       (UINVd a0 p fs data UX) RZ GBOTH BCAP CCAP;
  fh_FZN : callee_contract BSEGS (di_SWIN I) GBOTH fx_ok RZ (di_SHC I) (di_KCAP I) (di_AINVH I) BoDrvHooksA.BoFZ.ceN;
  fh_FZE : callee_contract BSEGS (di_SWIN I) GBOTH fx_ok RZ (di_SHC I) (di_KCAP I) (di_AINVH I) BoDrvHooksA.BoFZ.ceE;
  (* [comment removed for export] *)
  fh_GCC1 : forall UX, uxa UX -> forall M0 : word -> option byte, GCg (di_AINVH1 I) UX M0;
  fh_cells1 : cells_stmt (di_AINVH1 I);
  fh_cells : cells_stmt (di_AINVH I);
  (* [comment removed for export] *)
  fh_W1 : forall UX E cs fx R M model, cs1 UX E cs fx R M model -> csA UX E cs fx R M model;
  (* [comment removed for export] *)
  fh_M1G1 : forall UX, uxa UX -> forall (tm csa csb : acs) E fx R M model (Tb : TSet),
     cs1 UX E tm fx R M model -> M12 tm = Some (csa, csb) -> 64512 < uE E (reg tm 10) -> Tb [] ->
     (forall E' fx' R' M' model',
         env_agree NXD E E' /\ env_agree (nxt tm) E E' -> cs1 UX E' csb fx' R' M' model' -> m_fs model' = m_fs model ->
         RZ (cfgF BSEGS fx' R' (pc csb) M' model') Tb) ->
     RZ (cfgF BSEGS fx R (pc tm) M model) Tb;
  (* [comment removed for export] *)
  fh_M1GP : forall UX, uxa UX -> forall (tm csa csb : acs) E fx R M model (Tb : TSet),
     cs1 UX E tm fx R M model -> M12 tm = Some (csa, csb) -> a_fake tm = [] ->
     1 <= uE E (reg tm 10) -> (uE E (a_meter tm) <= EVT \/ 8193 <= uE E (reg tm 10)) -> Tb [] ->
     (forall E' fx' R' M' model',
         env_agree NXD E E' /\ env_agree (nxt tm) E E' -> csA UX E' csb fx' R' M' model' -> m_fs model' = m_fs model ->
         RZ (cfgF BSEGS fx' R' (pc csb) M' model') Tb) ->
     RZ (cfgF BSEGS fx R (pc tm) M model) Tb
}.

Hypothesis FHY : file_hyps.

(* [comment removed for export] *)
Theorem run_a : forall (UX : env -> Prop) (UXa : uxa UX) (D : env -> Fs.Fs -> TSet),
  (forall E E' fs', env_agree NXD E E' -> D E fs' = D E' fs') -> (forall E fs', D E fs' []) ->
  forall hs pl cs s, gplan_ok pl = true -> CHKa hs BF FUEL cs pl = COk s ->
  (forall h ch, hs h = Some ch -> forall E fx R M model, csA UX E ch fx R M model -> RZ (cfgF BSEGS fx R (pc ch) M model) (D E fs)) ->
  forall E fx R M model, csA UX E cs fx R M model ->
  RZ (cfgF BSEGS fx R (pc cs) M model) (sd (fun (_ : nat) E0 fs' => D E0 fs') (D E fs) E fs s).
Proof.
  intros UX UXa D Dag Dnil hs pl cs s Hgp Hc HH E fx R M model HC. destruct FHY. destruct fh_cells0 as (c1 & c2 & c3).
  pose proof (drvA_cert_sound_rz (di_SHC I) (di_KCAP I) (di_AINVH I) (di_SWIN I) fh_HP0 fh_SWIN_img0 (di_SPTOP I) (di_HID I) (di_HIDF I) (di_M0 I)
                (di_B0 I) (di_C0 I) fh_B1 fh_C1 fh_bcap0 fh_ccap0 (di_FTOP I) fh_FTOP0 a0 p fs data UX UXa (fh_GC0 UX UXa) fh_FZN0 fh_FZE0
                c1 c2 c3 D Dag Dnil hs BF FUEL pl cs s Hgp Hc) as H.
  assert (HS : GPS.holes_stmt BSEGS hs PERM_A_lit (di_SPTOP I) fs (di_SHC I) (VSHf (di_HID I) (di_HIDF I)) (AINVg (di_AINVH I) (di_M0 I)) (di_KCAP I) (di_FTOP I) fx_ok
                 (UINVd a0 p fs data UX) (fun (_ : nat) E0 fs' => D E0 fs') RZ).
  { intros h ch Hh E0 fx0 R0 M1 model0 HC0. rewrite (co_fs HC0). exact (HH h ch Hh E0 fx0 R0 M1 model0 HC0). }
  specialize (H HS E fx R M model HC). rewrite (co_fs HC) in H. exact H.
Qed.

(* [comment removed for export] *)
Theorem run_1 : forall (UX : env -> Prop) (UXa : uxa UX) (D : env -> Fs.Fs -> TSet),
  (forall E E' fs', env_agree NXD E E' -> D E fs' = D E' fs') -> (forall E fs', D E fs' []) ->
  forall hs pl cs s, gplan_ok pl = true -> CHKz hs BF FUEL cs pl = COk s ->
  (forall h ch, hs h = Some ch -> forall E fx R M model, cs1 UX E ch fx R M model -> RZ (cfgF BSEGS fx R (pc ch) M model) (D E fs)) ->
  forall E fx R M model, cs1 UX E cs fx R M model ->
  RZ (cfgF BSEGS fx R (pc cs) M model) (sd (fun (_ : nat) E0 fs' => D E0 fs') (D E fs) E fs s).
Proof.
  intros UX UXa D Dag Dnil hs pl cs s Hgp Hc HH E fx R M model HC. destruct FHY. destruct fh_cells2 as (c1 & c2 & c3).
  pose proof (drvA_cert_sound_zh (di_SHC I) (di_KCAP I) (di_AINVH1 I) (di_SWIN I) fh_HP2 (di_SPTOP I) (di_HID I) (di_HIDF I) (di_M0 I)
                (di_B0 I) (di_C0 I) (di_FTOP I) a0 p fs data UX UXa (fh_GCC2 UX UXa) c1 c2 c3 D Dag Dnil hs BF FUEL pl cs s Hgp Hc) as H.
  assert (HS : GPS.holes_stmt BSEGS hs PERM_A_lit (di_SPTOP I) fs (di_SHC I) (VSHf (di_HID I) (di_HIDF I)) (AINVg (di_AINVH1 I) (di_M0 I)) (di_KCAP I) (di_FTOP I) fx_ok
                 (UINVd a0 p fs data UX) (fun (_ : nat) E0 fs' => D E0 fs') RZ).
  { intros h ch Hh E0 fx0 R0 M1 model0 HC0. rewrite (co_fs HC0). exact (HH h ch Hh E0 fx0 R0 M1 model0 HC0). }
  specialize (H HS E fx R M model HC). rewrite (co_fs HC) in H. exact H.
Qed.

(* [comment removed for export] *)
Theorem m1g1 : forall (UX : env -> Prop) (UXa : uxa UX) (tm csa csb : acs) (Tb : TSet), M12 tm = Some (csa, csb) -> Tb [] ->
  (forall E fx R M model, cs1 UX E csb fx R M model -> RZ (cfgF BSEGS fx R (pc csb) M model) Tb) ->
  forall E fx R M model, cs1 UX E tm fx R M model -> 64512 < uE E (reg tm 10) -> RZ (cfgF BSEGS fx R (pc tm) M model) Tb.
Proof.
  intros UX UXa tm csa csb Tb HM Htb HB E fx R M model HC Hn.
  apply (fh_M1G1 FHY UX UXa tm csa csb E fx R M model Tb HC HM Hn Htb).
  intros E' fx' R' M' model' _ HC' _. exact (HB E' fx' R' M' model' HC').
Qed.
(* [comment removed for export] *)
Theorem m1gp : forall (UX : env -> Prop) (UXa : uxa UX) (tm csa csb : acs) (Tb : TSet), M12 tm = Some (csa, csb) -> a_fake tm = [] -> Tb [] ->
  (forall E fx R M model, csA UX E csb fx R M model -> RZ (cfgF BSEGS fx R (pc csb) M model) Tb) ->
  forall E fx R M model, cs1 UX E tm fx R M model -> 1 <= uE E (reg tm 10) -> (uE E (a_meter tm) <= EVT \/ 8193 <= uE E (reg tm 10)) ->
  RZ (cfgF BSEGS fx R (pc tm) M model) Tb.
Proof.
  intros UX UXa tm csa csb Tb HM HF Htb HB E fx R M model HC Hn Hk.
  apply (fh_M1GP FHY UX UXa tm csa csb E fx R M model Tb HC HM HF Hn Hk Htb).
  intros E' fx' R' M' model' _ HC' _. exact (HB E' fx' R' M' model' HC').
Qed.


(* [comment removed for export] *)
Lemma U_drv_tenv : forall E th, nth_error th 4%nat = Some (EVar 4) -> U_drv a0 p fs data E -> U_drv a0 p fs data (tenv E th).
Proof.
  intros E th H4 (H1 & H2 & H3 & H4' & H5 & H6 & H7).
  assert (E4 : ev (tenv E th) 4%nat = ev E 4%nat) by (rewrite (tenv_ev E th 4%nat (EVar 4) H4); reflexivity).
  unfold U_drv, uE. cbn [edenot]. rewrite tenv_eb, E4. unfold uE in H6. cbn [edenot] in H6.
  repeat split; try assumption; try (apply H5; assumption); try (apply H6; assumption); try (apply H7; assumption).
Qed.

(* [comment removed for export] *)
Theorem rebase : forall AINVH (UX UX' : env -> Prop) (hi : nat) (w : tbind) (h T : acs) E fx R M model,
  csG AINVH UX E h fx R M model -> entails_tw ABOTH 0 hi w h T = true ->
  nth_error (infer_th 0 hi w h T) 4%nat = Some (EVar 4) ->
  UX' (tenv E (infer_th 0 hi w h T)) ->
  csG AINVH UX' (tenv E (infer_th 0 hi w h T)) T fx R M model /\ pc T = pc h.
Proof.
  intros AINVH UX UX' hi w h T E fx R M model HC H H4 HU'. rewrite APC.entails_tw_eq in H. apply andb_prop in H as [_ H].
  apply (entails_t_tenv PERM_A_lit (di_SPTOP I) fs (di_SHC I) (VSHf (di_HID I) (di_HIDF I)) (AINVg AINVH (di_M0 I)) (di_KCAP I) (di_FTOP I)
           (UINVd a0 p fs data UX) (UINVd a0 p fs data UX') E h T _ fx R M model HC H).
  split; [apply U_drv_tenv; [exact H4 | exact (proj1 (co_uinv HC))] | exact HU'].
Qed.

(* [comment removed for export] *)
Lemma add_facts : forall AINVH (UX : env -> Prop) E cs fx R M model (ks : list kentry),
  csG AINVH UX E cs fx R M model -> Forall (kentry_ok BSEGS E (Mr (di_SHC I) (VSHf (di_HID I) (di_HIDF I)) E cs model M)) ks ->
  csG AINVH UX E (add_kn cs ks) fx R M model.
Proof.
  intros AINVH UX E cs fx R M model ks HC HK. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. apply Forall_app. split; [exact HK | exact (co_know HC)].
Qed.
End Glue.
