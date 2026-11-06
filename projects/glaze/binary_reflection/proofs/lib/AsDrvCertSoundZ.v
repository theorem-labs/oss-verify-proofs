(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.glaze.binary_reflection.images.Asan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA11.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDrvNodesAllZ.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.AsDrvGSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.AsDrvNodesSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.AsDrvNodesSoundA2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvNodesSoundA4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvNodesSoundA5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA11.AsDrvNodesSoundA6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA11.AsDrvNodesSoundA7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA11.AsDrvNodesSoundA9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvNodesAllA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

Section AllZ.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable SWIN : list (Z * Z).
Hypothesis HP : hprops SWIN GASAN SHC AINVH.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN ->
  g_ro_hi GASAN <= lo /\ hi <= g_img_hi GASAN /\ (forall plo phi, In (plo, phi) (g_priv GASAN) -> hi <= plo \/ phi <= lo).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable HIDc HIDFc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Hypothesis B0c_nonneg : 0 <= B0c.
Hypothesis C0c_nonneg : 0 <= C0c.
Variable FTOPc : Z.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree NXD E E' -> UINV E -> UINV E'.
#[local] Notation AINVc := (AINV_f SWIN GASAN AINVH PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation VSHc := (VSHf HIDc HIDFc).
#[local] Notation RZ := (realizes ASEGS).
#[local] Notation N1 := (fun nd => GPS.node1_stmtN ASEGS NXD PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ always nd).

Hypothesis GCC : gcontracts_core ASEGS ITA AASAN NXD PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ GASAN.
Hypothesis M2S_H : forall L LF B C K M mdl, AINVH L LF B C K M mdl ->
  rdn ASEGS M (Z_to_bv 64 0x108268) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn ASEGS M (Z_to_bv 64 0x108260) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))
  /\ exists me : Z, rdn ASEGS M (Z_to_bv 64 0x108270) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 me)).
Hypothesis NONUL12 : forall E, UINV E -> forall j, (j = 1 \/ j = 2)%nat -> ~ In (Z_to_bv 8 0) (eb E j).
Hypothesis ABSENT2 : forall E, UINV E -> bv_unsigned (ev E 4%nat) = DNA.CLS_ABSENT ->
  eb E 2%nat <> [] -> openat_plain_name (eb E 2%nat) = true /\ fs_lookup FS0 (eb E 2%nat) = None.

(* [comment removed for export] *)
Lemma XNc_core_sound : forall id args, id <> 20%nat -> N1 (XNc ASEGS ITA AASAN NXD GASAN BCAP CCAP CT0 id args).
Proof.
  intros id args Hne. unfold XNc. change (CT0 id) with (@None gcallee).
  pose proof (AINV_f_frame SWIN GASAN SHC AINVH HP asan_G_ro_img2 drvA_G_img_al drvA_G_img_shlo PERMc SPTOPc HIDc HIDFc M0c B0c C0c) as AF.
  pose proof (AINV_f_lazy SWIN GASAN SHC AINVH HP PERMc SPTOPc HIDc HIDFc M0c B0c C0c) as AL.
  assert (AFa : forall Lc Lf B C K M mdl, AINVc Lc Lf B C K M mdl ->
            Forall (fun iv => 0 < bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= GlzConst.RunCeil.CEIL
                              /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_lo AASAN \/ img_hi AASAN <= bv_unsigned (fst iv))) (m_vm_lazy mdl)).
  { intros. rewrite asan_A_img_hi, asan_A_img_lo. eapply (AINV_f_facts SWIN GASAN SHC AINVH HP); eassumption. }
  assert (HG : forall id', id' <> 20%nat -> N1 (XNg ASEGS ITA AASAN NXD GASAN BCAP CCAP id' args)).
  { intros id' Hn' cs cs' E fx R M model T HT HC Hp Hn Hk.
    refine (XNg_core_sound ASEGS ITA AASAN NXD PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ GASAN BCAP CCAP GCC id' args cs cs' E fx R M model T HT HC Hp _ Hk).
    rewrite <- Hn. unfold XNg_core. clear - Hn'.
    do 21 (destruct id' as [|id']; [first [exfalso; apply Hn'; reflexivity | reflexivity]|]). reflexivity. }
  do 20 (destruct id as [|id]; [refine (HG _ _); discriminate|]).
  destruct id as [|id]; [exfalso; apply Hne; reflexivity|].
  do 21 (destruct id as [|id]; [refine (HG _ _); discriminate|]).
  destruct id as [|id]; [apply GPS.node1_stmt_N; exact (node_enumload_sound ASEGS ITA ITA_ok NXD SWIN PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc AF AL AASAN AFa asan_in_hull asan_segs_wx fx_ok UINV UINV_agree RZ RZ_silent1_rz)|].
  destruct id as [|id]; [apply GPS.node1_stmt_N; exact (node_popcnt_sound ASEGS NXD PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ args)|].
  destruct id as [|id]; [apply GPS.node1_stmt_N; exact (node_havoc64_sound ASEGS NXD SWIN PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc AF fx_ok UINV UINV_agree RZ args)|].
  destruct id as [|id]; [apply GPS.node1_stmt_N; exact (node_enumreg_sound ASEGS NXD PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ args)|].
  refine (HG _ _); discriminate.
Qed.

Lemma NONUL2z : forall E, UINV E -> ~ In (Z_to_bv 8 0) (eb E 2%nat).
Proof. intros E HU. exact (NONUL12 E HU 2%nat (or_intror eq_refl)). Qed.

Theorem XNz_sound_all : GPS.ext_stmt ASEGS NXD XNz PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ.
Proof.
  intros id args. unfold XNz.
  destruct (Nat.eqb id 20 || Nat.eqb id 120 || Nat.eqb id 121)%bool eqn:Hz; [intros cs cs' E fx R M model T _ _ _ Hn; discriminate Hn|].
  apply orb_false_iff in Hz as [Hz H121]. apply orb_false_iff in Hz as [H20 H120].
  apply Nat.eqb_neq in H20. apply Nat.eqb_neq in H120. apply Nat.eqb_neq in H121.
  unfold XNa. rewrite (proj2 (Nat.eqb_neq id 120) H120), (proj2 (Nat.eqb_neq id 121) H121). unfold DNA.XNP.
  repeat match goal with |- context [Nat.eqb id ?n] => destruct (Nat.eqb_spec id n); [cbn [orb]|cbn [orb]] end.
  - apply node_read_sound; assumption || exact RZ_silent1_rz.
  - apply node_close_sound; assumption || exact RZ_silent1_rz.
  - apply node_ioctl_sound; assumption || exact RZ_silent1_rz.
  - apply node_blobmemchr_sound; first [assumption | exact RZ_silent1_rz | exact NONUL12].
  - apply node_blobstrlen_sound; first [assumption | exact RZ_silent1_rz | exact NONUL12].
  - apply node_region_sound; assumption || exact RZ_silent1_rz.
  - apply node_qctail_printf_sound; assumption || exact RZ_silent1_rz.
  - apply node_qctail_strnlen_sound; assumption || exact RZ_silent1_rz.
  - apply node_qctail_memchr_sound; assumption || exact RZ_silent1_rz.
  - apply node_openat_toolong_sound; first [assumption | exact RZ_silent1_rz | exact NONUL2z].
  - apply node_openat_absent_sound; first [assumption | exact RZ_silent1_rz | exact NONUL2z].
  - exact (XNc_core_sound id args H20).
Qed.
End AllZ.
End AsDrvNodesAllZ.
Require Stdlib.Strings.String OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDrvS0SpecA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvS0A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.AsDrvGSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvNodesAllA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvInstFactsA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvUinvA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvCertSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition shS3A (L : expr) (a b : Z) (pre : list Z) (j : nat) (suf : list Z) : shape :=
  SCase L a (SEmitP 2 [SPLit pre; SPBlob j; SPLit suf] (SEmitP 1 [] (SExit 2)))
    (SCase L b (SEmitP 2 [SPLit pre; SPBlob j; SPLit suf] (SEmitP 2 [] (SEmitP 1 [] (SExit 2))))
               (SEmitP 2 [SPLit pre; SPBlob j] (SEmitP 2 [SPLit suf] (SEmitP 1 [] (SExit 2))))).

Lemma emit1_nilA : forall fs, t_eq (t_emit (map (WriteEv (Z_to_bv 64 1)) []) (t_exit (Z_to_bv 64 2) fs)) (t_exit (exit_code 2) fs).
Proof. intros fs. cbn [map]. unfold exit_code. apply t_emit_nil_eq. apply Spec4.t_exit_has_nil. Qed.

Lemma sd_long : forall HOLES D E fs pre j suf,
  t_eq (GPS.sd HOLES D E fs (SEmitP 2 [SPLit pre; SPBlob j] (SEmitP 2 [SPLit suf] (SEmitP 1 [] (SExit 2)))))
       (t_die (map (Z_to_bv 8) pre ++ eb E j ++ map (Z_to_bv 8) suf) fs).
Proof.
  intros HOLES D E fs pre j suf. unfold t_die. cbn [GPS.sd]. unfold GPS.Wp, Spec4.W. cbn [flat_map GPS.piece_den]. rewrite !app_nil_r.
  eapply t_eq_trans; [| apply Spec4.AgentLib.t_emit_congr; apply emit1_nilA].
  eapply t_eq_trans; [| apply t_eq_sym; rewrite app_assoc, map_app; apply Spec4.AgentLib.t_emit_app].
  apply Spec4.AgentLib.t_emit_congr. apply Spec4.AgentLib.t_emit_congr. apply t_eq_refl.
Qed.

Lemma sd_shS3A : forall HOLES D E fs L a b pre j suf,
  t_eq (GPS.sd HOLES D E fs (shS3A L a b pre j suf)) (t_die (map (Z_to_bv 8) pre ++ eb E j ++ map (Z_to_bv 8) suf) fs).
Proof.
  intros HOLES D E fs L a b pre j suf. unfold shS3A. cbn [GPS.sd].
  destruct (Z.leb (bv_unsigned (edenot E L)) a); [| destruct (Z.leb (bv_unsigned (edenot E L)) b)].
  - unfold t_die. unfold GPS.Wp, Spec4.W. cbn [flat_map GPS.piece_den]. rewrite !app_nil_r.
    apply Spec4.AgentLib.t_emit_congr. apply emit1_nilA.
  - unfold t_die. unfold GPS.Wp, Spec4.W. cbn [flat_map GPS.piece_den]. rewrite !app_nil_r.
    apply Spec4.AgentLib.t_emit_congr. cbn [map]. eapply t_eq_trans; [apply t_emit_nil_eq; apply t_emit_has_nil | apply emit1_nilA].
  - exact (sd_long HOLES D E fs pre j suf).
Qed.

Lemma sd_lit1A : forall HOLES D E fs z,
  t_eq (GPS.sd HOLES D E fs (SEmitP 2 [SPLit z] (SEmitP 1 [] (SExit 2)))) (t_die (map (Z_to_bv 8) z) fs).
Proof.
  intros HOLES D E fs z. unfold t_die. cbn [GPS.sd]. unfold GPS.Wp, Spec4.W. cbn [flat_map GPS.piece_den]. rewrite !app_nil_r.
  apply Spec4.AgentLib.t_emit_congr. apply emit1_nilA.
Qed.

(* [comment removed for export] *)
Definition zU1 : list Z := [117; 115; 97; 103; 101; 58; 32].
Definition zU2 : list Z := [32; 73; 78; 80; 85; 84; 10].
Lemma zU1_ok : map (Z_to_bv 8) zU1 = s2b "usage: "%string. Proof. vm_compute. reflexivity. Qed.
Lemma zU2_ok : map (Z_to_bv 8) zU2 = s2b " INPUT"%string ++ [LF]. Proof. vm_compute. reflexivity. Qed.
Lemma zCO_okA : map (Z_to_bv 8) MSG_CO = s2b "cli: cannot open "%string. Proof. vm_compute. reflexivity. Qed.
Lemma zRE_okA : map (Z_to_bv 8) MSG_RE = s2b "cli: read error on "%string. Proof. vm_compute. reflexivity. Qed.
Lemma zNL_okA : map (Z_to_bv 8) [10] = [LF]. Proof. vm_compute. reflexivity. Qed.

Lemma shapeU_eq : shapeU = shS3A L0 66 73 zU1 1 zU2. Proof. reflexivity. Qed.
Lemma shapeCOa_eq : shapeCOa = shS3A L1 62 63 MSG_CO 2 [10]. Proof. reflexivity. Qed.
Lemma shapeD2_eq : shapeD2 = shS3A L1 60 61 MSG_RE 2 [10]. Proof. reflexivity. Qed.

Lemma sd_shapeU : forall HOLES D E fs, t_eq (GPS.sd HOLES D E fs shapeU) (t_die (msg_usage (eb E 1%nat)) fs).
Proof. intros. rewrite shapeU_eq. eapply t_eq_trans; [apply (sd_shS3A HOLES D)|]. rewrite zU1_ok, zU2_ok. unfold msg_usage. apply t_eq_refl. Qed.
Lemma sd_shapeCOa : forall HOLES D E fs, t_eq (GPS.sd HOLES D E fs shapeCOa) (t_die (msg_cannot_open (eb E 2%nat)) fs).
Proof. intros. rewrite shapeCOa_eq. eapply t_eq_trans; [apply (sd_shS3A HOLES D)|]. rewrite zCO_okA, zNL_okA. unfold msg_cannot_open. apply t_eq_refl. Qed.
Lemma sd_shapeD2 : forall HOLES D E fs, t_eq (GPS.sd HOLES D E fs shapeD2) (t_die (msg_read_error (eb E 2%nat)) fs).
Proof. intros. rewrite shapeD2_eq. eapply t_eq_trans; [apply (sd_shS3A HOLES D)|]. rewrite zRE_okA, zNL_okA. unfold msg_read_error. apply t_eq_refl. Qed.
Lemma sd_shapeCOt : forall HOLES D E fs, t_eq (GPS.sd HOLES D E fs shapeCOt) (t_die (msg_cannot_open (eb E 2%nat)) fs).
Proof. intros. unfold shapeCOt. eapply t_eq_trans; [apply (sd_long HOLES D)|]. rewrite zCO_okA, zNL_okA. unfold msg_cannot_open. apply t_eq_refl. Qed.
Lemma sd_shapeUz : forall HOLES D E fs, t_eq (GPS.sd HOLES D E fs shapeUz) (t_die (msg_usage []) fs).
Proof. intros. unfold shapeUz. eapply t_eq_trans; [apply (sd_lit1A HOLES D)|]. replace (msg_usage []) with (map (Z_to_bv 8) [117; 115; 97; 103; 101; 58; 32; 32; 73; 78; 80; 85; 84; 10]) by (vm_compute; reflexivity). apply t_eq_refl. Qed.
Lemma sd_shapeCOz : forall HOLES D E fs, t_eq (GPS.sd HOLES D E fs shapeCOz) (t_die (msg_cannot_open []) fs).
Proof. intros. unfold shapeCOz. eapply t_eq_trans; [apply (sd_lit1A HOLES D)|]. replace (msg_cannot_open []) with (map (Z_to_bv 8) [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 10]) by (vm_compute; reflexivity). apply t_eq_refl. Qed.

(* [comment removed for export] *)
Section S0SpecA.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable SWIN : list (Z * Z).
Hypothesis HP : hprops SWIN GASAN SHC AINVH.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN ->
  g_ro_hi GASAN <= lo /\ hi <= g_img_hi GASAN /\ (forall plo phi, In (plo, phi) (g_priv GASAN) -> hi <= plo \/ phi <= lo).
Variable SPTOPc : Z.
Variable HIDc HIDFc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Hypothesis B0c_nonneg : 0 <= B0c.
Hypothesis C0c_nonneg : 0 <= C0c.
Hypothesis bcap_ok : B0c + BCAP <= GBUDGET.
Hypothesis ccap_ok : C0c + CCAP <= GCOUNT.
Variable FTOPc : Z.
Hypothesis FTOPc_ok : Z.of_nat (length HIDFc) + FTOPc <= FMIN.
Variables (a0 p : list byte) (fs : Fs.Fs) (data : list byte).
#[local] Notation UINVd := (UINVd a0 p fs data UX0).
#[local] Notation PERMc := PERM_A_lit.
#[local] Notation AINVc := (AINV_f SWIN GASAN AINVH PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation VSHc := (VSHf HIDc HIDFc).
#[local] Notation RZ := (realizes ASEGS).
#[local] Notation cs_okA := (GPS.cs_ok ASEGS PERMc SPTOPc fs SHC VSHc AINVc KCAP FTOPc fx_ok UINVd).
Hypothesis GC_all : forall M0 : word -> option byte,
  gcontracts ASEGS ITA AASAN NXD PERMc SPTOPc fs SHC VSHc (AINV_f SWIN GASAN AINVH PERMc SPTOPc HIDc HIDFc M0 B0c C0c) KCAP FTOPc fx_ok UINVd RZ GASAN BCAP CCAP.
Hypothesis FZN_contract : callee_contract ASEGS SWIN GASAN fx_ok RZ SHC KCAP AINVH AsDrvHooksA.AsFZ.ceN.
Hypothesis FZE_contract : callee_contract ASEGS SWIN GASAN fx_ok RZ SHC KCAP AINVH AsDrvHooksA.AsFZ.ceE.
Hypothesis M2S_H : forall L LF B C K M mdl, AINVH L LF B C K M mdl ->
  rdn ASEGS M (Z_to_bv 64 0x108268) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn ASEGS M (Z_to_bv 64 0x108260) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))
  /\ exists me : Z, rdn ASEGS M (Z_to_bv 64 0x108270) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 me)).
Hypothesis DTOR_H : forall L LF B C K M mdl, AINVH L LF B C K M mdl ->
  rdn ASEGS M (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ exists cpm : byte, rdn ASEGS M (Z_to_bv 64 0x106ddc) 1 = Some [cpm] /\ bv_unsigned cpm <> 0.
Hypothesis DTOR_FRAME : forall L LF B C K M M' mdl, AINVH L LF B C K M mdl ->
  (forall a : word, M' a <> M a -> (in_lsb (bv_unsigned a) = true \/ in_mub (bv_unsigned a) = true) /\ M' a <> None) ->
  rdn ASEGS M' (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  AINVH L LF B C K M' mdl.

#[local] Notation ARGS thm := (thm RC SFL SHC KCAP AINVH SWIN HP SWIN_img SPTOPc HIDc HIDFc M0c B0c C0c B0c_nonneg C0c_nonneg bcap_ok ccap_ok FTOPc FTOPc_ok
                                   a0 p fs data GC_all FZN_contract FZE_contract M2S_H DTOR_H DTOR_FRAME).

(* [comment removed for export] *)
Lemma to_die : forall (cs : acs) (sh : shape) (msg : env -> list byte) (m : list byte),
  (forall E fx R M model, cs_okA E cs fx R M model -> RZ (cfgF ASEGS fx R (pc cs) M model) (GPS.sd (fun _ E' fs' => D0 E' fs') (D0 E (m_fs model)) E (m_fs model) sh)) ->
  (forall HOLES D E fs', t_eq (GPS.sd HOLES D E fs' sh) (t_die (msg E) fs')) ->
  (forall E, UINVd E -> msg E = m) ->
  forall E fx R M model, cs_okA E cs fx R M model -> RZ (cfgF ASEGS fx R (pc cs) M model) (t_die m fs).
Proof.
  intros cs sh msg m HS Hsd Hm E fx R M model HC.
  pose proof (HS E fx R M model HC) as H. rewrite (co_fs HC) in H.
  eapply RZ_conseq_rz; [exact H|]. rewrite <- (Hm E (co_uinv HC)). apply Hsd.
Qed.

Theorem usage1_spec : forall E fx R M model, cs_okA E tMu1n fx R M model -> RZ (cfgF ASEGS fx R (pc tMu1n) M model) (t_die (msg_usage a0) fs).
Proof. apply (to_die tMu1n shapeU (fun E => msg_usage (eb E 1%nat)) _ (ARGS (@usage1_sound)) sd_shapeU). intros E [HU _]. rewrite (proj1 HU). reflexivity. Qed.
Theorem usage3_spec : forall E fx R M model, cs_okA E tMu3n fx R M model -> RZ (cfgF ASEGS fx R (pc tMu3n) M model) (t_die (msg_usage a0) fs).
Proof. apply (to_die tMu3n shapeU (fun E => msg_usage (eb E 1%nat)) _ (ARGS (@usage3_sound)) sd_shapeU). intros E [HU _]. rewrite (proj1 HU). reflexivity. Qed.
Theorem usage1z_spec : forall E fx R M model, cs_okA E tMu1z fx R M model -> RZ (cfgF ASEGS fx R (pc tMu1z) M model) (t_die (msg_usage []) fs).
Proof. apply (to_die tMu1z shapeUz (fun _ => msg_usage []) _ (ARGS (@usage1z_sound)) sd_shapeUz). reflexivity. Qed.
Theorem usage3z_spec : forall E fx R M model, cs_okA E tMu3z fx R M model -> RZ (cfgF ASEGS fx R (pc tMu3z) M model) (t_die (msg_usage []) fs).
Proof. apply (to_die tMu3z shapeUz (fun _ => msg_usage []) _ (ARGS (@usage3z_sound)) sd_shapeUz). reflexivity. Qed.
Theorem cantopen_absent_spec : forall E fx R M model, cs_okA E tMoa fx R M model -> RZ (cfgF ASEGS fx R (pc tMoa) M model) (t_die (msg_cannot_open p) fs).
Proof. apply (to_die tMoa shapeCOa (fun E => msg_cannot_open (eb E 2%nat)) _ (ARGS (@cantopen_absent_sound)) sd_shapeCOa). intros E [HU _]. rewrite (proj1 (proj2 HU)). reflexivity. Qed.
Theorem cantopen_empty_spec : forall E fx R M model, cs_okA E tMoz fx R M model -> RZ (cfgF ASEGS fx R (pc tMoz) M model) (t_die (msg_cannot_open []) fs).
Proof. apply (to_die tMoz shapeCOz (fun _ => msg_cannot_open []) _ (ARGS (@cantopen_empty_sound)) sd_shapeCOz). reflexivity. Qed.
Theorem cantopen_toolong_spec : forall E fx R M model, cs_okA E tMot fx R M model -> RZ (cfgF ASEGS fx R (pc tMot) M model) (t_die (msg_cannot_open p) fs).
Proof. apply (to_die tMot shapeCOt (fun E => msg_cannot_open (eb E 2%nat)) _ (ARGS (@cantopen_toolong_sound)) sd_shapeCOt). intros E [HU _]. rewrite (proj1 (proj2 HU)). reflexivity. Qed.
(* [comment removed for export] *)
End S0SpecA.
End AsDrvS0SpecA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvS0A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvS1A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.AsDrvGSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvNodesAllA AsDrvNodesAllZ OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvInstFactsA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvUinvA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvCertSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA AsDrvS0SpecA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

Lemma CHK0z_eq : CHK0z = fun cs p => checkA ASEGS ITA AASAN NXD LIMIT ISP0 XNz XEa XB0 XAa AP.XT0 (fun _ => None) 0%nat false BF0 FUEL0 None cs p.
Proof. reflexivity. Qed.

Section CertSoundZ.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable SWIN : list (Z * Z).
Hypothesis HP : hprops SWIN GASAN SHC AINVH.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN ->
  g_ro_hi GASAN <= lo /\ hi <= g_img_hi GASAN /\ (forall plo phi, In (plo, phi) (g_priv GASAN) -> hi <= plo \/ phi <= lo).
Variable SPTOPc : Z.
Variable HIDc HIDFc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Hypothesis B0c_nonneg : 0 <= B0c.
Hypothesis C0c_nonneg : 0 <= C0c.
Variable FTOPc : Z.
Variables (a0 p : list byte) (fs : Fs.Fs) (data : list byte).
(* [comment removed for export] *)
Variable UX : env -> Prop.
Hypothesis UX_agree : forall E E', env_agree NXD E E' -> UX E -> UX E'.
#[local] Notation UINVd := (UINVd a0 p fs data UX).
#[local] Notation PERMc := PERM_A_lit.
#[local] Notation AINVat M0 := (AINV_f SWIN GASAN AINVH PERMc SPTOPc HIDc HIDFc M0 B0c C0c).
#[local] Notation AINVc := (AINVat M0c).
#[local] Notation VSHc := (VSHf HIDc HIDFc).
#[local] Notation RZ := (realizes ASEGS).
#[local] Notation cs_okat M0 := (GPS.cs_ok ASEGS PERMc SPTOPc fs SHC VSHc (AINVat M0) KCAP FTOPc fx_ok UINVd).
#[local] Notation cs_okA := (cs_okat M0c).

Hypothesis GCC_all : forall M0 : word -> option byte,
  gcontracts_core ASEGS ITA AASAN NXD PERMc SPTOPc fs SHC VSHc (AINVat M0) KCAP FTOPc fx_ok UINVd RZ GASAN.
Hypothesis M2S_H : forall L LF B C K M mdl, AINVH L LF B C K M mdl ->
  rdn ASEGS M (Z_to_bv 64 0x108268) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn ASEGS M (Z_to_bv 64 0x108260) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))
  /\ exists me : Z, rdn ASEGS M (Z_to_bv 64 0x108270) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 me)).
Hypothesis DTOR_H : forall L LF B C K M mdl, AINVH L LF B C K M mdl ->
  rdn ASEGS M (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ exists cpm : byte, rdn ASEGS M (Z_to_bv 64 0x106ddc) 1 = Some [cpm] /\ bv_unsigned cpm <> 0.
Hypothesis DTOR_FRAME : forall L LF B C K M M' mdl, AINVH L LF B C K M mdl ->
  (forall a : word, M' a <> M a -> (in_lsb (bv_unsigned a) = true \/ in_mub (bv_unsigned a) = true) /\ M' a <> None) ->
  rdn ASEGS M' (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  AINVH L LF B C K M' mdl.

Lemma UXa : forall E E', env_agree NXD E E' -> UINVd E -> UINVd E'.
Proof. exact (UINVd_agree a0 p fs data UX UX_agree). Qed.

Lemma XNz_at : forall M0, GPS.ext_stmt ASEGS NXD XNz PERMc SPTOPc fs SHC VSHc (AINVat M0) KCAP FTOPc fx_ok UINVd RZ.
Proof.
  intros M0.
  apply (XNz_sound_all SHC KCAP AINVH SWIN HP PERMc SPTOPc fs HIDc HIDFc M0 B0c C0c FTOPc UINVd UXa (GCC_all M0) M2S_H).
  - intros E [HU _]. exact (U_drv_NONUL12 a0 p fs data E HU).
  - intros E [HU _]. exact (U_drv_ABSENT2 a0 p fs data E HU).
Qed.
Lemma XEz_at : forall M0, GPS.emit_stmt ASEGS NXD XEa PERMc SPTOPc fs SHC VSHc (AINVat M0) KCAP FTOPc fx_ok UINVd RZ.
Proof.
  intros M0. apply (XEa_sound_all SHC KCAP AINVH SWIN HP PERMc SPTOPc fs HIDc HIDFc M0 B0c C0c FTOPc UINVd UXa).
  intros a Ha. rewrite <- (PERM_A_den (Env (fun _ => Z_to_bv 64 0) (fun _ => []))). exact (PERM_files_A _ a Ha).
Qed.
Lemma XAz_at : forall M0, GPS.alt2_stmt ASEGS NXD XAa PERMc SPTOPc fs SHC VSHc (AINVat M0) KCAP FTOPc fx_ok UINVd RZ.
Proof.
  intros M0.
  exact (XAa_sound_all SHC KCAP AINVH SWIN HP PERMc SPTOPc fs HIDc HIDFc M0 B0c C0c FTOPc UINVd UXa
           (fun E HU => U_drv_NONUL12 a0 p fs data E (proj1 HU)) data
           (fun E HU => U_drv_FILE2 a0 p fs data E (proj1 HU)) (fun E HU => U_drv_DIR2 a0 p fs data E (proj1 HU))).
Qed.

Lemma tail_sound_z : forall (M0' : word -> option byte) pl cs s,
  gplan_ok pl = true -> CHK0z cs pl = COk s ->
  forall E fx R M model, cs_okat M0' E cs fx R M model ->
  RZ (cfgF ASEGS fx R (pc cs) M model) (GPS.sd (fun _ _ _ => t_nil) t_nil E (m_fs model) s).
Proof.
  intros M0' pl cs s Hgp Hc E fx R M model HC.
  rewrite CHK0z_eq in Hc.
  exact (GPS.check_soundA ASEGS ITA ITA_ok AASAN NXD LIMIT (fun _ => None) XNz XEa XB0 XAa AP.XT0 0%nat SWIN PERMc SPTOPc fs SHC VSHc (AINVat M0') KCAP FTOPc
           (AINV_f_frame SWIN GASAN SHC AINVH HP asan_G_ro_img2 drvA_G_img_al drvA_G_img_shlo PERMc SPTOPc HIDc HIDFc M0' B0c C0c)
           (AINV_f_lazy SWIN GASAN SHC AINVH HP PERMc SPTOPc HIDc HIDFc M0' B0c C0c)
           ltac:(intros; rewrite asan_A_img_hi, asan_A_img_lo; eapply (AINV_f_facts SWIN GASAN SHC AINVH HP); eassumption)
           fx_ok UINVd UXa (fun _ _ _ => t_nil) (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun _ _ _ => eq_refl)
           RZ RZ_silent1_rz RZ_exit_rz RZ_conseq_rz (RUN_sound_fx ASEGS) asan_in_hull asan_hull_ok asan_segs_wx
           (XNz_at M0') (XEz_at M0')
           (fun id args cs0 csa csb E0 fx0 R0 Mx mdl T _ Hn => ltac:(discriminate Hn))
           (XAz_at M0')
           (fun id args cs0 fd ps code E0 fx0 R0 Mx mdl _ Hn => ltac:(discriminate Hn))
           (fun h ch Hh => ltac:(discriminate Hh)) FUEL0 BF0 None pl cs s Hgp Hc E fx R M model t_nil HC
           ltac:(exact I) eq_refl).
Qed.

Theorem XTz_sound : GPS.term_stmt ASEGS XTz PERMc SPTOPc fs SHC VSHc AINVc KCAP FTOPc fx_ok UINVd RZ.
Proof.
  exact (XT70_sound RZ RZ_silent1_rz SHC KCAP AINVH SWIN HP PERMc SPTOPc fs HIDc HIDFc M0c B0c C0c FTOPc UINVd UXa
           M2S_H DTOR_H DTOR_FRAME PERM_flag_A CHK0z tail_sound_z RZ_conseq_rz).
Qed.


(* [comment removed for export] *)
Section Holes.
Variable D : env -> Fs.Fs -> TSet.
Hypothesis D_agree : forall E E' fs', env_agree NXD E E' -> D E fs' = D E' fs'.
Hypothesis D_nil : forall E fs', D E fs' [].
#[local] Notation HOLES := (fun (_ : nat) E fs' => D E fs').
Theorem drvA_cert_sound_zh : forall hs bf fuel pl cs s,
  gplan_ok pl = true -> CHKz hs bf fuel cs pl = COk s ->
  GPS.holes_stmt ASEGS hs PERMc SPTOPc fs SHC VSHc AINVc KCAP FTOPc fx_ok UINVd HOLES RZ ->
  forall E fx R M model, cs_okA E cs fx R M model ->
  RZ (cfgF ASEGS fx R (pc cs) M model) (GPS.sd HOLES (D E (m_fs model)) E (m_fs model) s).
Proof.
  intros hs bf fuel pl cs s Hgp Hc HSs E fx R M model HC.
  exact (GPS.check_soundA ASEGS ITA ITA_ok AASAN NXD LIMIT hs XNz XEa XB0 XAa XTz 0%nat SWIN PERMc SPTOPc fs SHC VSHc AINVc KCAP FTOPc
           (AINV_f_frame SWIN GASAN SHC AINVH HP asan_G_ro_img2 drvA_G_img_al drvA_G_img_shlo PERMc SPTOPc HIDc HIDFc M0c B0c C0c)
           (AINV_f_lazy SWIN GASAN SHC AINVH HP PERMc SPTOPc HIDc HIDFc M0c B0c C0c)
           ltac:(intros; rewrite asan_A_img_hi, asan_A_img_lo; eapply (AINV_f_facts SWIN GASAN SHC AINVH HP); eassumption)
           fx_ok UINVd UXa HOLES (fun _ E1 E2 fs' Hag => D_agree E1 E2 fs' Hag) (fun _ => D_nil) (fun _ _ _ => eq_refl)
           RZ RZ_silent1_rz RZ_exit_rz RZ_conseq_rz (RUN_sound_fx ASEGS) asan_in_hull asan_hull_ok asan_segs_wx
           (XNz_at M0c) (XEz_at M0c)
           (fun id args cs0 csa csb E0 fx0 R0 Mx mdl T _ Hn => ltac:(discriminate Hn))
           (XAz_at M0c) XTz_sound
           HSs fuel bf None pl cs s Hgp Hc E fx R M model (D E (m_fs model)) HC
           ltac:(exact I) (D_nil E (m_fs model))).
Qed.
End Holes.

End CertSoundZ.
