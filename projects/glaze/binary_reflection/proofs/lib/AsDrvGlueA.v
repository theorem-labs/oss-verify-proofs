(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.glaze.binary_reflection.images.Asan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS3A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDrvGlueLibA.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS3A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.AsDrvGSoundA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
Section EntTenv.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variables (PERMc : list (Z * Z)) (SPTOPc : Z) (FS0 : Fs.Fs) (SHC VSH : list (Z * Z)).
Variable AINV : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variables (KCAP FTOPc : Z).
#[local] Notation cs_okU U := (GPS.cs_ok ASEGS PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc fx_ok U).

(* [comment removed for export] *)
Lemma entails_t_tenv : forall (U U' : env -> Prop) E cs T th fx R M model,
  cs_okU U E cs fx R M model -> entails_t AASAN 0 cs T th = true -> U' (tenv E th) ->
  cs_okU U' (tenv E th) T fx R M model /\ pc T = pc cs.
Proof.
  intros U U' E cs T th fx R M model HC H HU'. apply APC.entails_t_imp in H. unfold APC.entails_t_ref in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  rename H into Hpc. apply Z.eqb_eq in Hpc.
  match goal with Hl : match s_log (a_ss T) with _ => _ end = true |- _ => rename Hl into HL; destruct (s_log (a_ss T)) eqn:HL'; [clear HL; rename HL' into HL|discriminate] end.
  match goal with Hl : match s_resv (a_ss T) with _ => _ end = true |- _ => clear Hl end.
  match goal with Hl : th_id_below 0 th = true |- _ => rename Hl into Hid end.
  match goal with Hl : regs_ent _ _ _ _ = true |- _ => rename Hl into Hregs end.
  match goal with Hl : kn_ent _ _ _ = true |- _ => rename Hl into Hkn end.
  match goal with Hl : list_eqb pair_eqb (map (ptsubst th) (a_vis T)) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hl; rename Hl into Hvis end.
  match goal with Hl : list_eqb pair_eqb (map (ptsubst th) (a_ghost T)) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hl; rename Hl into Hgh end.
  match goal with Hl : expr_eqb (tsubst th (a_brk T)) _ = true |- _ => apply expr_eqb_eq in Hl; rename Hl into Hbrk end.
  match goal with Hl : list_eqb pair_eqb (map (ptsubst th) (a_fake T)) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hl; rename Hl into Hfake end.
  match goal with Hl : expr_eqb (tsubst th (a_meter T)) _ = true |- _ => apply expr_eqb_eq in Hl; rename Hl into Hmeter end.
  match goal with Hl : expr_eqb (tsubst th (a_fbud T)) _ = true |- _ => apply expr_eqb_eq in Hl; rename Hl into Hfbud end.
  match goal with Hl : afd_eqb (ftsubst th (a_fd T)) _ = true |- _ => apply afd_eqb_eq in Hl; rename Hl into Hfd end.
  match goal with Hl : Z.leb (a_ylo T) (a_ylo cs) = true |- _ => apply Z.leb_le in Hl; rename Hl into Hylo end.
  match goal with Hl : list_eqb amap_eqb (a_maps cs) (a_maps T) = true |- _ => apply (list_eqb_eq amap_eqb amap_eqb_eq) in Hl; rename Hl into Hmaps end.
  match goal with Hl : AP.maps_vars_lt 0 (a_maps T) = true |- _ => rename Hl into Hmv end.
  set (E' := tenv E th).
  assert (Hag : env_agree 0 E E') by (apply th_id_below_agree; exact Hid).
  assert (HMR : Mr SHC VSH E' T model M = Mr SHC VSH E cs model M).
  { unfold Mr. f_equal. apply functional_extensionality. intros a. unfold hid, vlz. unfold E'.
    rewrite <- in_shb_ptsubst, !map_app, Hvis, Hfake. reflexivity. }
  split; [|symmetry; exact Hpc].
  destruct HC as [CR CL CK CH CF CD CA CU CX CP CT CK2 CFB CFL]; constructor; try assumption.
  - apply (proj1 (regs_ok_tsubst E th (s_regs (a_ss T)) R)).
    destruct (regs_ent_sound ASEGS E _ (kn cs) _ _ 0%nat CK Hregs) as [Hlen Hn].
    intros r. rewrite (CR r). unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0; [reflexivity|]. symmetry. apply Hn.
    intros Hz. cbn in Hz. unfold ridx in Hz. unfold bv_eqb in Hr0. apply Z.eqb_neq in Hr0. apply Hr0.
    change (bv_unsigned r = 0). pose proof (u5_range r). lia.
  - rewrite HMR. apply (proj1 (know_ok_ktsubst ASEGS E th _ (kn T))). eapply (kn_ent_sound ASEGS AASAN asan_in_hull asan_hull_ok); [exact CK | exact Hkn].
  - unfold E'. apply fds_ok_ftsubst. rewrite Hfd. exact CD.
  - unfold E'. rewrite <- !blocks_den_ptsubst, <- bcost_ptsubst, <- uE_tsubst, Hvis, Hfake, Hmeter. unfold bcount in *.
    rewrite <- (length_map (ptsubst th)), Hvis. exact CA.
  - unfold E'. rewrite <- wins_den_ptsubst, Hgh. exact CP.
  - unfold E'. rewrite <- sptop_den_tsubst, Hbrk. exact CT.
  - unfold E'. rewrite <- uE_tsubst, Hmeter. exact CK2.
  - unfold E'. rewrite <- uE_tsubst, Hfbud, <- (length_map (ptsubst th)), Hfake. exact CFB.
  - rewrite <- Hmaps. eapply (floor_sem_xfer E E' (a_maps cs) (a_brk cs) (a_brk T) (a_ylo cs) (a_ylo T)); [| | exact Hylo | exact CFL].
    + intros f l kd r Hm. unfold uE. rewrite <- Hmaps, Hm in Hmv. cbn [AP.maps_vars_lt forallb am_base am_len] in Hmv.
      apply andb_prop in Hmv as [Hmv _]. apply andb_prop in Hmv as [Hf _].
      rewrite <- (edenot_agree' 0 E E' f Hag Hf). reflexivity.
    + unfold E'. rewrite <- sptop_den_tsubst, Hbrk. reflexivity.
Qed.
End EntTenv.

(* [comment removed for export] *)
#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)
Lemma uE_lit : forall E z, 0 <= z < 2 ^ 64 -> uE E (ELit z) = z.
Proof. intros E z H. unfold uE. cbn [edenot]. apply u64_lit. exact H. Qed.
Lemma uE_esub : forall E a b, uE E (esub a b) = (uE E a - uE E b) mod 2 ^ 64.
Proof. intros E a b. unfold uE, esub. rewrite mkAlu_denot. unfold Sem.alu64, Sem.alu. rewrite bv_sub_unsigned, bv_wrap64_mod. reflexivity. Qed.
Lemma uE_eadd : forall E a b, uE E (eadd a b) = (uE E a + uE E b) mod 2 ^ 64.
Proof. intros E a b. unfold uE, eadd. rewrite mkAlu_denot. unfold Sem.alu64, Sem.alu. rewrite bv_add_unsigned, bv_wrap64_mod. reflexivity. Qed.


Lemma uE_eaddz_w : forall E e z, edenot E (eaddz e z) = bv_add (edenot E e) (Z_to_bv 64 z).
Proof. intros E e z. unfold eaddz. rewrite mkAlu_denot. reflexivity. Qed.

(* [comment removed for export] *)
Lemma tenv_ev : forall E th i e, nth_error th i = Some e -> ev (tenv E th) i = edenot E e.
Proof.
  intros E th i e H. unfold tenv. cbn [ev]. pose proof (nth_error_Some th i) as [H1 _]. rewrite H in H1.
  specialize (H1 ltac:(discriminate)). apply Nat.ltb_lt in H1. rewrite H1. rewrite (nth_error_nth th i (ELit 0) H). reflexivity.
Qed.
Lemma tenv_uE : forall E th i e, nth_error th i = Some e -> uE (tenv E th) (EVar i) = uE E e.
Proof. intros E th i e H. unfold uE. cbn [edenot]. rewrite (tenv_ev E th i e H). reflexivity. Qed.
Lemma tenv_eb : forall E th, eb (tenv E th) = eb E. Proof. reflexivity. Qed.

Lemma blob1_hdr : forall bs i, bytes_le_to_Z (blob_bytes bs (Z.of_nat i) 1) = hdr_byte bs i.
Proof.
  intros bs i. unfold blob_bytes, hdr_byte. rewrite Nat2Z.id.
  destruct (nth_error bs i) as [b|] eqn:Hn.
  - pose proof (nth_error_split bs i Hn) as (l1 & l2 & -> & Hl). rewrite <- Hl.
    rewrite skipn_app, skipn_all, Nat.sub_diag. cbn [skipn app firstn]. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
    apply bytes_le_single.
  - apply nth_error_None in Hn. rewrite skipn_all2 by exact Hn. rewrite nth_overflow by exact Hn. cbn. reflexivity.
Qed.
Definition envB (b0 b1 b2 : Z) : env := Env (fun _ => Z_to_bv 64 0) (fun k => if Nat.eqb k 3 then [Z_to_bv 8 b0; Z_to_bv 8 b1; Z_to_bv 8 b2] else []).
Definition cfgxF (b0 b1 : Z) : Z := uE (envB b0 b1 0) CFGX.

Definition callsbF (b2 : Z) : Z := uE (envB 0 0 b2) CALLSB.
Lemma blobval_hdr : forall sx bs bs' i z, z = Z.of_nat i -> hdr_byte bs i = hdr_byte bs' i -> blob_val sx bs z 1 = blob_val sx bs' z 1.
Proof. intros sx bs bs' i z -> H. unfold blob_val. rewrite !blob1_hdr, H. reflexivity. Qed.
Lemma hdr_envB : forall b0 b1 b2 i, (i < 3)%nat -> 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  hdr_byte [Z_to_bv 8 b0; Z_to_bv 8 b1; Z_to_bv 8 b2] i = nth i [b0; b1; b2] 0.
Proof.
  intros b0 b1 b2 i Hi H0 H1 H2. unfold hdr_byte. destruct i as [|[|[|i]]]; cbn [nth]; try lia; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; apply Z.mod_small; cbn; lia.
Qed.
Lemma uE_CFGX_env : forall E, uE E CFGX = cfgxF (hdr_byte (eb E 3%nat) 0) (hdr_byte (eb E 3%nat) 1).
Proof.
  intros E. unfold cfgxF, uE, CFGX, B0, B1sx. cbn [edenot envB eb Nat.eqb].
  pose proof (hdr_byte_range (eb E 3%nat) 0) as R0. pose proof (hdr_byte_range (eb E 3%nat) 1) as R1.
  rewrite (blobval_hdr true (eb E 3%nat) [Z_to_bv 8 (hdr_byte (eb E 3%nat) 0); Z_to_bv 8 (hdr_byte (eb E 3%nat) 1); Z_to_bv 8 0] 1%nat 1 eq_refl)
    by (rewrite hdr_envB by lia; reflexivity).
  rewrite (blobval_hdr false (eb E 3%nat) [Z_to_bv 8 (hdr_byte (eb E 3%nat) 0); Z_to_bv 8 (hdr_byte (eb E 3%nat) 1); Z_to_bv 8 0] 0%nat 0 eq_refl)
    by (rewrite hdr_envB by lia; reflexivity).
  reflexivity.
Qed.

Lemma blobval_envB0 : forall b0 b1 b2, 0 <= b0 < 256 -> blob_val false [Z_to_bv 8 b0; Z_to_bv 8 b1; Z_to_bv 8 b2] 0 1 = Z_to_bv 64 b0.
Proof.
  intros b0 b1 b2 H. unfold blob_val. change (blob_bytes [Z_to_bv 8 b0; Z_to_bv 8 b1; Z_to_bv 8 b2] 0 1) with [Z_to_bv 8 b0]. rewrite bytes_le_single, Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. rewrite Z.mod_small by (cbn; lia). reflexivity.
Qed.
Fixpoint zseq (a : Z) (n : nat) : list Z := match n with O => [] | Datatypes.S n' => a :: zseq (a + 1) n' end.
Lemma zseq_In : forall n a z, a <= z < a + Z.of_nat n -> In z (zseq a n).
Proof. induction n as [|n IH]; intros a z Hz; [lia|]. cbn [zseq]. destruct (Z.eq_dec a z); [left; exact e | right; apply IH; lia]. Qed.

Lemma cfgx_split : forall b0 b1, 0 <= b0 < 256 -> cfgxF b0 b1 = Z.lor (cfgxF 0 b1) b0.
Proof.
  intros b0 b1 Hb0. unfold cfgxF, uE, CFGX, B0. cbn [edenot envB eb Nat.eqb].
  rewrite !blobval_envB0 by lia. unfold Sem.alu64, Sem.alu. rewrite !bv_or_unsigned, !u64_lit by lia. rewrite Z.lor_0_r. reflexivity.
Qed.
Lemma cfgx_chk : forallb (fun b1 => Z.eqb (cfgxF 0 b1) (256 * (b1 mod 128))) (zseq 0 256) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma land_high_low : forall m b0, 0 <= m -> 0 <= b0 < 256 -> Z.land (256 * m) b0 = 0.
Proof.
  intros m b0 Hm Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_ge_dec i 8).
  - replace (256 * m) with (m * 2 ^ 8) by lia. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - destruct (Z.eq_dec b0 0) as [->|Hnz]; [rewrite Z.bits_0; apply andb_false_r|].
    rewrite (Z.bits_above_log2 b0 i); [apply andb_false_r | lia |].
    apply (Z.lt_le_trans _ 8); [|lia]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma lor_high_low : forall m b0, 0 <= m -> 0 <= b0 < 256 -> Z.lor (256 * m) b0 = 256 * m + b0.
Proof.
  intros m b0 Hm Hb. rewrite <- Z.lxor_lor by (apply land_high_low; lia). symmetry. apply Z.add_nocarry_lxor. apply land_high_low; lia.
Qed.

Lemma callsb_chk : forallb (fun b2 => Z.eqb (callsbF b2) (b2 mod 4 + 1)) (zseq 0 256) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cfgx_bytes : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 -> cfgxF b0 b1 = (b0 + 256 * b1) mod 32768.
Proof.
  intros b0 b1 H0 H1. rewrite cfgx_split by lia.
  pose proof (proj1 (forallb_forall _ _) cfgx_chk b1 (zseq_In 256 0 b1 ltac:(lia))) as X. apply Z.eqb_eq in X. rewrite X.
  pose proof (Z.mod_pos_bound b1 128 ltac:(lia)) as Hr. pose proof (Z.div_mod b1 128 ltac:(lia)) as Hd.
  rewrite lor_high_low by lia.
  apply (Z.mod_unique_pos _ 32768 (b1 / 128)); lia.
Qed.

Lemma callsb_bytes : forall b2, 0 <= b2 < 256 -> callsbF b2 = b2 mod 4 + 1.
Proof.
  intros b2 H2. pose proof (proj1 (forallb_forall _ _) callsb_chk b2 (zseq_In 256 0 b2 ltac:(lia))) as X. apply Z.eqb_eq in X. exact X.
Qed.

Lemma uE_CALLSB_env : forall E, uE E CALLSB = callsbF (hdr_byte (eb E 3%nat) 2).
Proof.
  intros E. unfold callsbF, uE, CALLSB, B2. pose proof (hdr_byte_range (eb E 3%nat) 2) as R2.
  rewrite !uE_eaddz_w. cbn [edenot envB eb Nat.eqb].
  rewrite (blobval_hdr false (eb E 3%nat) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 (hdr_byte (eb E 3%nat) 2)] 2%nat 2 eq_refl)
    by (rewrite hdr_envB by lia; reflexivity). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nth_firstn_lt : forall (A : Type) (l : list A) (n i : nat) (d : A), (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  intros A l. induction l as [|x l IH]; intros n i d H; [rewrite firstn_nil; reflexivity|].
  destruct n as [|n]; [lia|]. cbn [firstn]. destruct i as [|i]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.
Lemma CH_Z : Z.of_nat APS.CH = 65536. Proof. unfold APS.CH. apply Z2Nat.id. lia. Qed.
Lemma hdr_chunk0 : forall data i, (i < 3)%nat -> hdr_byte (APS.chunk 0 data) i = hdr_byte data i.
Proof.
  intros data i Hi. unfold hdr_byte, APS.chunk. rewrite Nat.mul_0_r. cbn [skipn]. rewrite nth_firstn_lt; [reflexivity|].
  pose proof CH_Z. lia.
Qed.

Section HdrData.
Variable data : list byte.
Variable E : env.
Hypothesis HB : eb E 3%nat = APS.chunk 0 data.

Lemma cfgx_hdr : uE E CFGX = hdr_cfglen data.
Proof.
  rewrite uE_CFGX_env, HB, !hdr_chunk0 by lia. unfold hdr_cfglen, hdr_cfg. apply cfgx_bytes; apply hdr_byte_range.
Qed.

Lemma callsb_val : uE E CALLSB = hdr_byte data 2 mod 4 + 1.
Proof. rewrite uE_CALLSB_env, HB, hdr_chunk0 by lia. apply callsb_bytes. apply hdr_byte_range. Qed.
Lemma callsb_hdr : hdr_cfglen data <> 0 -> uE E CALLSB = Z.of_nat (hdr_calls data).
Proof.
  intros Hc. rewrite callsb_val. unfold hdr_calls. destruct (Z.eqb_spec (hdr_cfglen data) 0) as [X|_]; [contradiction|].
  pose proof (Z.mod_pos_bound (hdr_byte data 2) 4 ltac:(lia)). rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia.
Qed.
Lemma calls1_hdr : hdr_cfglen data = 0 -> hdr_calls data = 1%nat.
Proof. intros Hc. unfold hdr_calls. rewrite Hc. reflexivity. Qed.
Lemma b0_val : uE E B0 = hdr_byte data 0.
Proof.
  unfold uE, B0. cbn [edenot]. pose proof (hdr_byte_range (eb E 3%nat) 0) as R0.
  rewrite (blobval_hdr false (eb E 3%nat) [Z_to_bv 8 (hdr_byte (eb E 3%nat) 0); Z_to_bv 8 0; Z_to_bv 8 0] 0%nat 0 eq_refl) by (rewrite hdr_envB by lia; reflexivity).
  rewrite blobval_envB0 by lia. rewrite u64_lit by lia. rewrite HB, hdr_chunk0 by lia. reflexivity.
Qed.
Lemma b2_rng : 0 <= uE E B2 <= 255.
Proof.
  unfold uE, B2. cbn [edenot]. pose proof (hdr_byte_range (eb E 3%nat) 2) as R2.
  unfold blob_val. change 2 with (Z.of_nat 2). rewrite (blob1_hdr (eb E 3%nat) 2). rewrite u64_lit by lia. lia.
Qed.
End HdrData.
End AsDrvGlueLibA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvCertSoundZ. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvS0A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvS1A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.AsDrvGSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvNodesAllA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvInstFactsA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvUinvA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvCertSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvCertSoundZ.AsDrvS0SpecA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvCertSoundZ AsDrvGlueLibA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.
#[local] Notation RZ := (realizes ASEGS).

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
  AINV_f (di_SWIN I) GASAN AINVH PERM_A_lit (di_SPTOP I) (di_HID I) (di_HIDF I) M0 (di_B0 I) (di_C0 I).
(* [comment removed for export] *)
Definition csG (AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop) (UX : env -> Prop)
  : env -> acs -> GPS.FX -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  GPS.cs_ok ASEGS PERM_A_lit (di_SPTOP I) fs (di_SHC I) (VSHf (di_HID I) (di_HIDF I)) (AINVg AINVH (di_M0 I)) (di_KCAP I) (di_FTOP I) fx_ok (UINVd a0 p fs data UX).
Definition cs1 := csG (di_AINVH1 I).                       (* [comment removed for export] *)
Definition csA := csG (di_AINVH I).                        (* [comment removed for export] *)
#[local] Notation GCg AINVH UX M0 := (gcontracts_core ASEGS ITA AASAN NXD PERM_A_lit (di_SPTOP I) fs (di_SHC I) (VSHf (di_HID I) (di_HIDF I)) (AINVg AINVH M0) (di_KCAP I) (di_FTOP I) fx_ok
       (UINVd a0 p fs data UX) RZ GASAN).

Definition M2S_stmt (X : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop) : Prop :=
  forall L LF B C K M mdl, X L LF B C K M mdl ->
  rdn ASEGS M (Z_to_bv 64 0x108268) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn ASEGS M (Z_to_bv 64 0x108260) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))
  /\ exists me : Z, rdn ASEGS M (Z_to_bv 64 0x108270) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 me)).
Definition DTH_stmt (X : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop) : Prop :=
  forall L LF B C K M mdl, X L LF B C K M mdl ->
  rdn ASEGS M (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ exists cpm : byte, rdn ASEGS M (Z_to_bv 64 0x106ddc) 1 = Some [cpm] /\ bv_unsigned cpm <> 0.
Definition DTF_stmt (X : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop) : Prop :=
  forall L LF B C K M M' mdl, X L LF B C K M mdl ->
  (forall a : word, M' a <> M a -> (in_lsb (bv_unsigned a) = true \/ in_mub (bv_unsigned a) = true) /\ M' a <> None) ->
  rdn ASEGS M' (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  X L LF B C K M' mdl.
(* [comment removed for export] *)
Definition cells_stmt X : Prop := M2S_stmt X /\ DTH_stmt X /\ DTF_stmt X.

Record file_hyps : Prop := FH {
  fh_HP1 : hprops (di_SWIN I) GASAN (di_SHC I) (di_AINVH1 I);
  fh_HP : hprops (di_SWIN I) GASAN (di_SHC I) (di_AINVH I);
  fh_SWIN_img : forall lo hi, In (lo, hi) (di_SWIN I) ->
     g_ro_hi GASAN <= lo /\ hi <= g_img_hi GASAN /\ (forall plo phi, In (plo, phi) (g_priv GASAN) -> hi <= plo \/ phi <= lo);
  fh_B0 : 0 <= di_B0 I;
  fh_C0 : 0 <= di_C0 I;
  fh_bcap : di_B0 I + BCAP <= GBUDGET;
  fh_ccap : di_C0 I + CCAP <= GCOUNT;
  fh_FTOP : Z.of_nat (length (di_HIDF I)) + di_FTOP I <= FMIN;
  (* [comment removed for export] *)
  fh_GC : forall UX, uxa UX -> forall M0 : word -> option byte,
     gcontracts ASEGS ITA AASAN NXD PERM_A_lit (di_SPTOP I) fs (di_SHC I) (VSHf (di_HID I) (di_HIDF I)) (AINVg (di_AINVH I) M0) (di_KCAP I) (di_FTOP I) fx_ok
       (UINVd a0 p fs data UX) RZ GASAN BCAP CCAP;
  fh_FZN : callee_contract ASEGS (di_SWIN I) GASAN fx_ok RZ (di_SHC I) (di_KCAP I) (di_AINVH I) AsDrvHooksA.AsFZ.ceN;
  fh_FZE : callee_contract ASEGS (di_SWIN I) GASAN fx_ok RZ (di_SHC I) (di_KCAP I) (di_AINVH I) AsDrvHooksA.AsFZ.ceE;
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
         RZ (cfgF ASEGS fx' R' (pc csb) M' model') Tb) ->
     RZ (cfgF ASEGS fx R (pc tm) M model) Tb;
  (* [comment removed for export] *)
  fh_M1GP : forall UX, uxa UX -> forall (tm csa csb : acs) E fx R M model (Tb : TSet),
     cs1 UX E tm fx R M model -> M12 tm = Some (csa, csb) -> a_fake tm = [] ->
     1 <= uE E (reg tm 10) -> (uE E (a_meter tm) <= EVT \/ 8193 <= uE E (reg tm 10)) -> Tb [] ->
     (forall E' fx' R' M' model',
         env_agree NXD E E' /\ env_agree (nxt tm) E E' -> csA UX E' csb fx' R' M' model' -> m_fs model' = m_fs model ->
         RZ (cfgF ASEGS fx' R' (pc csb) M' model') Tb) ->
     RZ (cfgF ASEGS fx R (pc tm) M model) Tb
}.

Hypothesis FHY : file_hyps.

(* [comment removed for export] *)
Theorem run_a : forall (UX : env -> Prop) (UXa : uxa UX) (D : env -> Fs.Fs -> TSet),
  (forall E E' fs', env_agree NXD E E' -> D E fs' = D E' fs') -> (forall E fs', D E fs' []) ->
  forall hs pl cs s, gplan_ok pl = true -> CHKa hs BF FUEL cs pl = COk s ->
  (forall h ch, hs h = Some ch -> forall E fx R M model, csA UX E ch fx R M model -> RZ (cfgF ASEGS fx R (pc ch) M model) (D E fs)) ->
  forall E fx R M model, csA UX E cs fx R M model ->
  RZ (cfgF ASEGS fx R (pc cs) M model) (sd (fun (_ : nat) E0 fs' => D E0 fs') (D E fs) E fs s).
Proof.
  intros UX UXa D Dag Dnil hs pl cs s Hgp Hc HH E fx R M model HC. destruct FHY. destruct fh_cells0 as (c1 & c2 & c3).
  pose proof (drvA_cert_sound_rz (di_SHC I) (di_KCAP I) (di_AINVH I) (di_SWIN I) fh_HP0 fh_SWIN_img0 (di_SPTOP I) (di_HID I) (di_HIDF I) (di_M0 I)
                (di_B0 I) (di_C0 I) fh_B1 fh_C1 fh_bcap0 fh_ccap0 (di_FTOP I) fh_FTOP0 a0 p fs data UX UXa (fh_GC0 UX UXa) fh_FZN0 fh_FZE0
                c1 c2 c3 D Dag Dnil hs BF FUEL pl cs s Hgp Hc) as H.
  assert (HS : GPS.holes_stmt ASEGS hs PERM_A_lit (di_SPTOP I) fs (di_SHC I) (VSHf (di_HID I) (di_HIDF I)) (AINVg (di_AINVH I) (di_M0 I)) (di_KCAP I) (di_FTOP I) fx_ok
                 (UINVd a0 p fs data UX) (fun (_ : nat) E0 fs' => D E0 fs') RZ).
  { intros h ch Hh E0 fx0 R0 M1 model0 HC0. rewrite (co_fs HC0). exact (HH h ch Hh E0 fx0 R0 M1 model0 HC0). }
  specialize (H HS E fx R M model HC). rewrite (co_fs HC) in H. exact H.
Qed.

(* [comment removed for export] *)
Theorem run_1 : forall (UX : env -> Prop) (UXa : uxa UX) (D : env -> Fs.Fs -> TSet),
  (forall E E' fs', env_agree NXD E E' -> D E fs' = D E' fs') -> (forall E fs', D E fs' []) ->
  forall hs pl cs s, gplan_ok pl = true -> CHKz hs BF FUEL cs pl = COk s ->
  (forall h ch, hs h = Some ch -> forall E fx R M model, cs1 UX E ch fx R M model -> RZ (cfgF ASEGS fx R (pc ch) M model) (D E fs)) ->
  forall E fx R M model, cs1 UX E cs fx R M model ->
  RZ (cfgF ASEGS fx R (pc cs) M model) (sd (fun (_ : nat) E0 fs' => D E0 fs') (D E fs) E fs s).
Proof.
  intros UX UXa D Dag Dnil hs pl cs s Hgp Hc HH E fx R M model HC. destruct FHY. destruct fh_cells2 as (c1 & c2 & c3).
  pose proof (drvA_cert_sound_zh (di_SHC I) (di_KCAP I) (di_AINVH1 I) (di_SWIN I) fh_HP2 (di_SPTOP I) (di_HID I) (di_HIDF I) (di_M0 I)
                (di_B0 I) (di_C0 I) (di_FTOP I) a0 p fs data UX UXa (fh_GCC2 UX UXa) c1 c2 c3 D Dag Dnil hs BF FUEL pl cs s Hgp Hc) as H.
  assert (HS : GPS.holes_stmt ASEGS hs PERM_A_lit (di_SPTOP I) fs (di_SHC I) (VSHf (di_HID I) (di_HIDF I)) (AINVg (di_AINVH1 I) (di_M0 I)) (di_KCAP I) (di_FTOP I) fx_ok
                 (UINVd a0 p fs data UX) (fun (_ : nat) E0 fs' => D E0 fs') RZ).
  { intros h ch Hh E0 fx0 R0 M1 model0 HC0. rewrite (co_fs HC0). exact (HH h ch Hh E0 fx0 R0 M1 model0 HC0). }
  specialize (H HS E fx R M model HC). rewrite (co_fs HC) in H. exact H.
Qed.

(* [comment removed for export] *)
Theorem m1g1 : forall (UX : env -> Prop) (UXa : uxa UX) (tm csa csb : acs) (Tb : TSet), M12 tm = Some (csa, csb) -> Tb [] ->
  (forall E fx R M model, cs1 UX E csb fx R M model -> RZ (cfgF ASEGS fx R (pc csb) M model) Tb) ->
  forall E fx R M model, cs1 UX E tm fx R M model -> 64512 < uE E (reg tm 10) -> RZ (cfgF ASEGS fx R (pc tm) M model) Tb.
Proof.
  intros UX UXa tm csa csb Tb HM Htb HB E fx R M model HC Hn.
  apply (fh_M1G1 FHY UX UXa tm csa csb E fx R M model Tb HC HM Hn Htb).
  intros E' fx' R' M' model' _ HC' _. exact (HB E' fx' R' M' model' HC').
Qed.
(* [comment removed for export] *)
Theorem m1gp : forall (UX : env -> Prop) (UXa : uxa UX) (tm csa csb : acs) (Tb : TSet), M12 tm = Some (csa, csb) -> a_fake tm = [] -> Tb [] ->
  (forall E fx R M model, csA UX E csb fx R M model -> RZ (cfgF ASEGS fx R (pc csb) M model) Tb) ->
  forall E fx R M model, cs1 UX E tm fx R M model -> 1 <= uE E (reg tm 10) -> (uE E (a_meter tm) <= EVT \/ 8193 <= uE E (reg tm 10)) ->
  RZ (cfgF ASEGS fx R (pc tm) M model) Tb.
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
  csG AINVH UX E h fx R M model -> entails_tw AASAN 0 hi w h T = true ->
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
  csG AINVH UX E cs fx R M model -> Forall (kentry_ok ASEGS E (Mr (di_SHC I) (VSHf (di_HID I) (di_HIDF I)) E cs model M)) ks ->
  csG AINVH UX E (add_kn cs ks) fx R M model.
Proof.
  intros AINVH UX E cs fx R M model ks HC HK. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. apply Forall_app. split; [exact HK | exact (co_know HC)].
Qed.
End Glue.
