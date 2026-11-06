(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Bridge.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable IA : AsVocab.AsCells.as_addrs.
Variable AAINV : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable fsbase : Z.
Variable SEGS : list Segment.
Hypothesis AAP : AsVocab.AAINV_props IA AAINV fsbase SEGS.
Variable SWIN : list (Z * Z).
Variable G : gtable.
(* [comment removed for export] *)
Hypothesis G_imglo : g_img_lo G = AsVocab.AsCells.ia_img_lo IA.
Hypothesis G_hi : g_img_hi G = AsVocab.AsCells.ia_img_hi IA.
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_al : 0 <= g_img_lo G /\ g_img_lo G mod 8 = 0 /\ g_img_hi G mod 8 = 0.
Hypothesis G_errno : g_ro_hi G <= g_errno G /\ g_errno G + 4 <= g_img_hi G.   (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis SWIN_ok : AsVocab.as_wins_ok IA SWIN.

(* [comment removed for export] *)
Definition wfr (fk : Z * Z) : Z * Z := (fst fk, AsVocab.FS (snd fk)).
Definition AINVw (Lc Lf : list (Z * Z)) (B C K : Z) (M : word -> option byte) (mdl : Model) : Prop :=
  exists FF, Lf = map wfr FF /\ AAINV Lc FF B C K M mdl.
Definition SHCw : list (Z * Z) := AsVocab.SHC IA fsbase.

#[local] Notation u := bv_unsigned.

Lemma FS_pos8 : forall k, 0 <= k -> 8 <= AsVocab.FS k /\ AsVocab.FS k mod 8 = 0.
Proof.
  intros k Hk. unfold AsVocab.FS. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk) as Hp. split; [lia|].
  replace (64 * 2 ^ k) with ((8 * 2 ^ k) * 8) by lia. apply Z_mod_mult.
Qed.

Lemma in_map_wfr : forall f m FF, In (f, m) (map wfr FF) -> exists k, In (f, k) FF /\ m = AsVocab.FS k.
Proof.
  intros f m FF H. apply in_map_iff in H as [[f0 k] [Heq Hin]]. unfold wfr in Heq. cbn in Heq. injection Heq as <- <-.
  exists k. split; [exact Hin | reflexivity].
Qed.

Lemma map_wfr_split : forall FF F1 f m F2, map wfr FF = F1 ++ (f, m) :: F2 ->
  exists G1 k G2, FF = G1 ++ (f, k) :: G2 /\ map wfr G1 = F1 /\ map wfr G2 = F2 /\ m = AsVocab.FS k.
Proof.
  intros FF. induction FF as [|[f0 k0] r IH]; intros F1 f m F2 H.
  - destruct F1; discriminate.
  - destruct F1 as [|x F1'].
    + cbn in H. injection H as E1 E2 E3. subst. exists [], k0, r. repeat split; reflexivity.
    + cbn in H. injection H as E1 E2. destruct (IH F1' f m F2 E2) as (G1 & k & G2 & -> & M1 & M2 & Hm).
      exists ((f0, k0) :: G1), k, G2. subst. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma in_shadow_sh : forall b n z, in_shadow SB b n z <-> AsVocab.sh_lo b <= z < AsVocab.sh_hi b n.
Proof. intros. unfold in_shadow, AsVocab.sh_lo, AsVocab.sh_hi, AsVocab.SB, SB. tauto. Qed.

Lemma ablk_ok_of : forall p n, AsVocab.ablk_ok IA p n -> ablk_ok G p n.
Proof.
  intros p n (A1 & A2 & A3 & A4). unfold ablk_ok. rewrite G_imglo, G_hi.
  unfold AsVocab.PTRLO, AsVocab.AS_LO, AsVocab.AS_HEAPLO in *. unfold PTRLO, SHMAPLO, KHI. repeat split; try lia.
Qed.

Theorem hprops_of_AAINV_props : hprops SWIN G SHCw AINVw.
Proof.
  destruct AAP as [Hframe Hmodel Hmono Hlazy Hzone Hdisj Hperm Hfzone Hfdisj Hbfdisj Hbounds Hlazyzone Hcells Hnolazy Hshdef].
  constructor.
  - (* [comment removed for export] *)
    intros L LF B C K M M' mdl (FF & -> & HA) Hch. exists FF. split; [reflexivity|].
    eapply (Hframe SWIN); [exact SWIN_ok | exact HA |]. intros a Ha. destruct (Hch a Ha) as [Ho Hd]. split; [|exact Hd].
    unfold AsVocab.as_app_owned. destruct Ho as [Hb|[Hf|[Hc|[Hw|[Hl|[Hs|Hi]]]]]].
    + left. exact Hb.
    + right. left. apply in_blocks_fusable in Hf as (f & m & Hin & Hz). apply in_map_wfr in Hin as (k & Hin & ->).
      exists f, k. split; [exact Hin | lia].
    + right. right. left. exact Hc.
    + right. right. right. left. exact Hw.
    + (* [comment removed for export] *)
      destruct Hl as (b & n & Hin & Hz); apply in_shadow_sh in Hz.
      right. right. right. right. right. left. apply in_map_wfr in Hin as (k & Hin & ->). exists b, k. split; assumption.
    + do 6 right. left. unfold AsVocab.in_stack_shadow, AsVocab.sh_lo, AsVocab.SB. unfold in_sshadow, SB, HEAPLO in Hs. lia.
    + do 7 right. unfold AsVocab.in_image_shadow, AsVocab.sh_lo, AsVocab.sh_hi, AsVocab.SB. unfold in_ishadow, SB in Hi.
      rewrite <- G_imglo, <- G_hi. pose proof G_ro_img as (R0 & R1 & R2). pose proof G_img_al as (GA0 & GA1 & GA2).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      replace (g_img_lo G + (g_img_hi G - g_img_lo G) + 7) with (g_img_hi G + 7) by lia. lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - (* [comment removed for export] *) intros L LF B C K M mdl mdl' (FF & -> & HA) Hvm. exists FF. split; [reflexivity | eapply Hmodel; eassumption].
  - (* [comment removed for export] *) intros L LF B C K B' C' K' M mdl (FF & -> & HA) HB HC HK. exists FF. split; [reflexivity | eapply Hmono; eassumption].
  - (* [comment removed for export] *)
    intros L LF B C K M mdl (FF & -> & HA).
    destruct (Hlazy _ _ _ _ _ _ _ HA) as (AA & Hwf & Hminv & Hshc & Hblk & Hmat).
    exists AA. split; [exact Hwf|]. split; [exact Hminv|]. split; [|split].
    + intros a Hc. unfold in_shc, SHCw in Hc. apply existsb_exists in Hc as [[lo hi] [Hin Hb]]. cbn [fst snd] in Hb.
      apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
      pose proof (Hshc lo hi Hin (u a) ltac:(lia)) as X. rewrite Z_to_bv_bv_unsigned in X. exact X.
    + intros a b n Hin Hsh. apply in_app_iff in Hin as [Hin|Hin].
      * pose proof (Hblk b n Hin (u a)) as X. rewrite Z_to_bv_bv_unsigned in X. apply X. apply in_shadow_sh. exact Hsh.
      * (* [comment removed for export] *)
        apply in_map_wfr in Hin as (k & Hin & ->).
        destruct (Hfzone _ _ _ _ _ _ _ b k HA Hin) as (K1 & K2 & K3 & K4 & K5).
        assert (HinS : In (AsVocab.sh_lo fsbase, AsVocab.sh_hi fsbase AsVocab.FAKE_SIZE) SHCw) by (unfold SHCw, AsVocab.SHC; cbn; tauto).
        pose proof (Hshc _ _ HinS (u a)) as X. rewrite Z_to_bv_bv_unsigned in X. apply X.
        unfold in_shadow, SB in Hsh. unfold AsVocab.sh_lo, AsVocab.sh_hi, AsVocab.SB.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    + intros mdl' Hm Hs. exists FF. split; [reflexivity|]. apply Hmat; assumption.
  - (* [comment removed for export] *)
    intros L LF B C K M mdl (FF & -> & HA). pose proof (Hlazyzone _ _ _ _ _ _ _ HA) as X.
    apply Forall_forall. intros iv Hin. pose proof (proj1 (Forall_forall _ _) X iv Hin) as (X1 & X2 & X3).
    rewrite G_imglo, G_hi. repeat split; assumption.
  - (* [comment removed for export] *)
    intros L LF B C K M mdl b m (FF & -> & HA) Hin. destruct (Hzone _ _ _ _ _ _ _ b m HA Hin) as (Z1 & Z2 & Z3).
    split; [exact (ablk_ok_of b m Z1)|].
    apply Z.mod_divide in Z3; [|lia]. apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact Z3]. exists 2. reflexivity.
  - (* [comment removed for export] *)
    intros L LF B C K M mdl f m (FF & -> & HA) Hin. apply in_map_wfr in Hin as (k & Hin & ->).
    destruct (Hfzone _ _ _ _ _ _ _ f k HA Hin) as (K1 & K2 & K3 & K4 & K5).
    destruct (FS_pos8 k ltac:(lia)) as [P1 P2].
    split; [exact (ablk_ok_of f _ K2)|]. repeat split; try lia.
    (* [comment removed for export] *)
    apply Z.mod_divide in K3; [|lia]. apply Z.mod_divide in P2; [|lia]. apply Z.mod_divide; [lia|].
    eapply Z.divide_trans; [exact P2 | exact K3].
  - (* [comment removed for export] *)
    intros L LF B C K M mdl L1 L2 b m b' m' (FF & -> & HA) HL Hin. eapply Hdisj; eassumption.
  - (* [comment removed for export] *)
    intros L LF B C K M mdl F1 F2 f m f' m' (FF & Hmap & HA) HL Hin. rewrite HL in Hmap. symmetry in Hmap.
    destruct (map_wfr_split FF F1 f m F2 Hmap) as (G1 & k & G2 & -> & M1 & M2 & ->).
    assert (Hin' : In (f', m') (map wfr (G1 ++ G2))) by (rewrite map_app, M1, M2; exact Hin).
    apply in_map_wfr in Hin' as (k' & Hin' & ->).
    eapply Hfdisj; [exact HA | reflexivity | exact Hin'].
  - (* [comment removed for export] *)
    intros L LF B C K M mdl b m f n (FF & -> & HA) Hin Hinf. apply in_map_wfr in Hinf as (k & Hinf & ->).
    eapply Hbfdisj; eassumption.
  - (* [comment removed for export] *)
    intros L L' LF LF' B C K M mdl P1 P2 (FF & -> & HA).
    destruct (Permutation_map_inv wfr FF (Permutation_sym P2)) as [FF' [-> P3]].
    exists FF'. split; [reflexivity|]. eapply Hperm; [exact P1 | exact P3 | exact HA].
  - (* [comment removed for export] *)
    intros z Hs. unfold in_shc, SHCw, AsVocab.SHC. apply existsb_exists.
    exists (AsVocab.sh_lo CEIL_run, AsVocab.SB + 2 ^ 44). split; [cbn; tauto|]. cbn [fst snd].
    unfold in_sshadow, SB, HEAPLO in Hs. unfold AsVocab.sh_lo, AsVocab.SB.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  - (* [comment removed for export] *)
    intros z Hz. unfold in_shc, SHCw, AsVocab.SHC. apply existsb_exists.
    exists (AsVocab.sh_lo (AsVocab.AsCells.ia_img_lo IA), AsVocab.sh_hi (AsVocab.AsCells.ia_img_lo IA) (AsVocab.AsCells.ia_img_hi IA - AsVocab.AsCells.ia_img_lo IA)).
    split; [cbn; tauto|]. cbn [fst snd]. pose proof G_ro_img as (R0 & R1 & R2). rewrite G_hi in Hz, R2. rewrite G_imglo in R0.
    unfold SB in Hz. unfold AsVocab.sh_lo, AsVocab.sh_hi, AsVocab.SB.
    replace (AsVocab.AsCells.ia_img_lo IA + (AsVocab.AsCells.ia_img_hi IA - AsVocab.AsCells.ia_img_lo IA) + 7) with (AsVocab.AsCells.ia_img_hi IA + 7) by lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - (* [comment removed for export] *)
    intros L LF B C K M mdl b n a (FF & -> & HA) Hin Hz.
    pose proof (Hnolazy _ _ _ _ _ _ _ (u a) HA) as X. unfold AsVocab.lzb in X. rewrite Z_to_bv_bv_unsigned in X.
    apply X. apply in_app_iff in Hin as [Hin|Hin].
    + left. exists b, n. split; [exact Hin | lia].
    + right. apply in_map_wfr in Hin as (k & Hin & ->). exists b, k. split; [exact Hin | lia].
  - (* [comment removed for export] *)
    exact G_errno.
Qed.
End Bridge.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section BridgeLG.
Context {RC : run_ceil}.
Variable X : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable SWIN : list (Z * Z).
Variable G : gtable.
Variable SHC : list (Z * Z).
Hypothesis HPX : hprops SWIN G SHC (AINVw X).
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_al : 0 <= g_img_lo G /\ g_img_lo G mod 8 = 0 /\ g_img_hi G mod 8 = 0.
Hypothesis G_img_shlo : g_img_hi G <= SHMAPLO.
Hypothesis SWIN_hi : forall z, in_wins SWIN z -> z < g_img_hi G.
Hypothesis X_pos : forall L LF B C K M mdl b n, AINVw X L LF B C K M mdl -> In (b, n) L -> 1 <= n.
#[local] Notation u := bv_unsigned.
#[local] Notation XL := (AzBridgeLG.AAINV_LG X).

Lemma AINVw_LG_proj : forall L LF B C K M mdl, AINVw XL L LF B C K M mdl -> AINVw X L LF B C K M mdl /\ AzBridgeLG.LG M L.
Proof. intros L LF B C K M mdl (FF & HL & (HA & HG)). split; [exists FF; split; assumption | exact HG]. Qed.
Lemma AINVw_LG_intro : forall L LF B C K M mdl, AINVw X L LF B C K M mdl -> AzBridgeLG.LG M L -> AINVw XL L LF B C K M mdl.
Proof. intros L LF B C K M mdl (FF & HL & HA) HG. exists FF. split; [exact HL | split; assumption]. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma egb_in_shadow_e : forall b n, n mod 8 <> 0 -> b mod 8 = 0 -> 1 <= n -> in_shadow SB b n (AzBridgeLG.egb b n).
Proof. intros b n Hm Hal Hn. unfold in_shadow, AzBridgeLG.egb, AsVocab.SB, SB. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma happ_not_egb : forall L LF B C K M mdl (a : word) b n,
  AINVw X L LF B C K M mdl -> In (b, n) L -> n mod 8 <> 0 -> happ SWIN G L LF a -> u a <> AzBridgeLG.egb b n.
Proof.
  intros L LF B C K M mdl a b n HA Hin Hm Ho He.
  destruct (hp_zone _ _ _ _ HPX _ _ _ _ _ _ _ b n HA Hin) as [Hab Hal].
  pose proof (egb_in_shadow_e b n Hm Hal (X_pos _ _ _ _ _ _ _ b n HA Hin)) as Hsh. rewrite <- He in Hsh.
  destruct (ablk_shadow G G_ro_img G_img_al G_img_shlo b n (u a) Hab Hsh) as (S1 & S2 & S3 & S4).
  pose proof (band_lits G G_img_al) as (BL1 & BL2 & BL3 & BL4 & BL5 & BL6 & BL7).
  destruct Ho as [Hb|[Hf|[Hc|[Hw|[Hl|[Hs|Hi]]]]]].
  - destruct Hb as (b' & n' & Hin' & Hz). destruct (hp_zone _ _ _ _ HPX _ _ _ _ _ _ _ b' n' HA Hin') as [Hab' _].
    exact (proj2 (proj2 (proj2 (ablk_byte G G_ro_img G_img_al G_img_shlo b' n' (u a) Hab' Hz))) ltac:(lia)).
  - apply in_blocks_fusable in Hf as (f & m & Hinf & Hz). destruct (hp_fzone _ _ _ _ HPX _ _ _ _ _ _ _ f m HA Hinf) as (Hab' & _).
    exact (proj2 (proj2 (proj2 (ablk_byte G G_ro_img G_img_al G_img_shlo f m (u a) Hab' ltac:(lia)))) ltac:(lia)).
  - lia.
  - pose proof (SWIN_hi _ Hw). lia.
  - destruct Hl as (f & m & Hinf & Hz). destruct (hp_fzone _ _ _ _ HPX _ _ _ _ _ _ _ f m HA Hinf) as (_ & f8 & _).
    destruct (hp_bfdisj _ _ _ _ HPX _ _ _ _ _ _ _ b n f m HA Hin Hinf) as [D|D].
    + exact (in_shadow_apart b n f m (u a) D f8 Hsh Hz).
    + exact (in_shadow_apart f m b n (u a) D Hal Hz Hsh).
  - unfold in_sshadow in Hs. lia.
  - destruct (ishadow_bounds G G_ro_img G_img_al G_img_shlo _ Hi). lia.
Qed.

Theorem hprops_LG : hprops SWIN G SHC (AINVw XL).
Proof.
  constructor.
  - intros L LF B C K M M' mdl HA Hch. destruct (AINVw_LG_proj _ _ _ _ _ _ _ HA) as [HA0 HG].
    apply AINVw_LG_intro; [exact (hp_frame _ _ _ _ HPX _ _ _ _ _ _ _ _ HA0 Hch)|].
    apply (AzBridgeLG.LG_kept M M' L L HG (fun x H => H)). intros b n Hin Hm.
    destruct (decide (M' (Z_to_bv 64 (AzBridgeLG.egb b n)) = M (Z_to_bv 64 (AzBridgeLG.egb b n)))) as [Heq|Hne]; [exact Heq|]. exfalso.
    destruct (Hch _ Hne) as [Ho _].
    destruct (hp_zone _ _ _ _ HPX _ _ _ _ _ _ _ b n HA0 Hin) as [Hab Hal].
    pose proof (egb_in_shadow_e b n Hm Hal (X_pos _ _ _ _ _ _ _ b n HA0 Hin)) as Hsh.
    destruct (ablk_shadow G G_ro_img G_img_al G_img_shlo b n _ Hab Hsh) as (S1 & _ & S3 & _).
    refine (happ_not_egb L LF B C K M mdl _ b n HA0 Hin Hm Ho _).
    apply u64_lit. unfold SB, KHI, HEAPLO in *. lia.
  - intros L LF B C K M mdl mdl' HA Hvm. destruct (AINVw_LG_proj _ _ _ _ _ _ _ HA) as [HA0 HG].
    exact (AINVw_LG_intro _ _ _ _ _ _ _ (hp_vm _ _ _ _ HPX _ _ _ _ _ _ _ _ HA0 Hvm) HG).
  - intros L LF B C K B' C' K' M mdl HA HB HC HK. destruct (AINVw_LG_proj _ _ _ _ _ _ _ HA) as [HA0 HG].
    exact (AINVw_LG_intro _ _ _ _ _ _ _ (hp_mono _ _ _ _ HPX _ _ _ _ _ _ _ _ _ _ HA0 HB HC HK) HG).
  - intros L LF B C K M mdl HA. destruct (AINVw_LG_proj _ _ _ _ _ _ _ HA) as [HA0 HG].
    destruct (hp_lazy _ _ _ _ HPX _ _ _ _ _ _ _ HA0) as (AA & H1 & H2 & H3 & H4 & H5).
    exists AA. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
    intros mdl' Hm Hs. exact (AINVw_LG_intro _ _ _ _ _ _ _ (H5 mdl' Hm Hs) HG).
  - intros L LF B C K M mdl HA. exact (hp_facts _ _ _ _ HPX _ _ _ _ _ _ _ (proj1 (AINVw_LG_proj _ _ _ _ _ _ _ HA))).
  - intros L LF B C K M mdl b m HA. exact (hp_zone _ _ _ _ HPX _ _ _ _ _ _ _ b m (proj1 (AINVw_LG_proj _ _ _ _ _ _ _ HA))).
  - intros L LF B C K M mdl f m HA. exact (hp_fzone _ _ _ _ HPX _ _ _ _ _ _ _ f m (proj1 (AINVw_LG_proj _ _ _ _ _ _ _ HA))).
  - intros L LF B C K M mdl L1 L2 b m b' m' HA. exact (hp_disj _ _ _ _ HPX _ _ _ _ _ _ _ L1 L2 b m b' m' (proj1 (AINVw_LG_proj _ _ _ _ _ _ _ HA))).
  - intros L LF B C K M mdl F1 F2 f m f' m' HA. exact (hp_fdisj _ _ _ _ HPX _ _ _ _ _ _ _ F1 F2 f m f' m' (proj1 (AINVw_LG_proj _ _ _ _ _ _ _ HA))).
  - intros L LF B C K M mdl b m f n HA. exact (hp_bfdisj _ _ _ _ HPX _ _ _ _ _ _ _ b m f n (proj1 (AINVw_LG_proj _ _ _ _ _ _ _ HA))).
  - intros L L' LF LF' B C K M mdl P1 P2 HA. destruct (AINVw_LG_proj _ _ _ _ _ _ _ HA) as [HA0 HG].
    apply (AINVw_LG_intro _ _ _ _ _ _ _ (hp_perm _ _ _ _ HPX _ _ _ _ _ _ _ _ _ P1 P2 HA0)).
    intros b n Hin. apply HG. exact (Permutation_in _ (Permutation_sym P1) Hin).
  - exact (hp_shc_stack _ _ _ _ HPX).
  - exact (hp_shc_image _ _ _ _ HPX).
  - intros L LF B C K M mdl b n a HA. exact (hp_nolazy _ _ _ _ HPX _ _ _ _ _ _ _ b n a (proj1 (AINVw_LG_proj _ _ _ _ _ _ _ HA))).
  - exact (hp_errno _ _ _ _ HPX).
Qed.
End BridgeLG.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Inst.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable bt : AsAinvDefs3.as_boot.
Variable SWIN : list (Z * Z).
Variable G : gtable.
Hypothesis G_imglo : g_img_lo G = AsVocab.AsCells.ia_img_lo (AsAinvDefs3.bt_ia bt).
Hypothesis G_hi : g_img_hi G = AsVocab.AsCells.ia_img_hi (AsAinvDefs3.bt_ia bt).
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_al : 0 <= g_img_lo G /\ g_img_lo G mod 8 = 0 /\ g_img_hi G mod 8 = 0.
Hypothesis G_errno : g_ro_hi G <= g_errno G /\ g_errno G + 4 <= g_img_hi G.   (* [comment removed for export] *)
Hypothesis SWIN_ok : AsVocab.as_wins_ok (AsAinvDefs3.bt_ia bt) SWIN.

Hypothesis G_img_shlo : g_img_hi G <= SHMAPLO.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AAINV_HL (h : option Z) : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop :=
  AzBridgeLG.AAINV_LG (AsAinvEntry3.AsAinvHole3.AAINV_HS bt h).
Definition AINVH_bt : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop :=
  AINVw (AAINV_HL None).
Definition AINVHN_bt (n : Z) : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop :=
  AINVw (AAINV_HL (Some n)).
Definition SHC_bt : list (Z * Z) := SHCw (AsAinvDefs3.bt_ia bt) (AsAinvDefs3.bt_fs bt).

Lemma SWIN_hi_bt : forall z, in_wins SWIN z -> z < g_img_hi G.
Proof. intros z Hz. rewrite G_hi. exact (proj2 (proj1 (SWIN_ok z Hz))). Qed.
Lemma hprops_h : forall h, hprops SWIN G SHC_bt (AINVw (AAINV_HL h)).
Proof.
  intros h.
  apply (hprops_LG (AsAinvEntry3.AsAinvHole3.AAINV_HS bt h) SWIN G SHC_bt
           (hprops_of_AAINV_props (AsAinvDefs3.bt_ia bt) (AsAinvEntry3.AsAinvHole3.AAINV_HS bt h) (AsAinvDefs3.bt_fs bt) (AsAinvDefs3.bt_segs bt)
              (AsAinvFrame3b.AAINV_props_all bt (AsAinvEntry3.AsAinvHole3.holes_lsopt h)) SWIN G G_imglo G_hi G_ro_img G_img_al G_errno SWIN_ok)
           G_ro_img G_img_al G_img_shlo SWIN_hi_bt).
  intros L LF B C K M mdl b n (FF & _ & HA) Hin.
  exact (proj1 (proj2 (AsVocab.aap_zone _ _ _ _ (AsAinvFrame3b.AAINV_props_all bt (AsAinvEntry3.AsAinvHole3.holes_lsopt h)) _ _ _ _ _ _ _ b n HA Hin))).
Qed.
Theorem hprops_bt : hprops SWIN G SHC_bt AINVH_bt.
Proof. exact (hprops_h None). Qed.
Theorem hpropsN_bt : forall n, hprops SWIN G SHC_bt (AINVHN_bt n).
Proof. intros n. exact (hprops_h (Some n)). Qed.


#[local] Notation u := bv_unsigned.




(* [comment removed for export] *)
Lemma HS_zone : forall h Lc FF B C K M mdl b n, AsAinvEntry3.AsAinvHole3.AAINV_HS bt h Lc FF B C K M mdl -> In (b, n) Lc ->
  AsVocab.ablk_ok (AsAinvDefs3.bt_ia bt) b n /\ 1 <= n /\ b mod 16 = 0.
Proof. intros h Lc FF B C K M mdl b n HA Hin. exact (AsVocab.aap_zone _ _ _ _ (AsAinvFrame3b.AAINV_props_all bt (AsAinvEntry3.AsAinvHole3.holes_lsopt h)) _ _ _ _ _ _ _ b n HA Hin). Qed.
Lemma HS_disj : forall h Lc FF B C K M mdl L1 L2 b n b' n',
  AsAinvEntry3.AsAinvHole3.AAINV_HS bt h Lc FF B C K M mdl -> Lc = L1 ++ (b, n) :: L2 -> In (b', n') (L1 ++ L2) -> b + n <= b' \/ b' + n' <= b.
Proof. intros h Lc FF B C K M mdl L1 L2 b n b' n' HA HL Hin. exact (AsVocab.aap_disj _ _ _ _ (AsAinvFrame3b.AAINV_props_all bt (AsAinvEntry3.AsAinvHole3.holes_lsopt h)) _ _ _ _ _ _ _ L1 L2 b n b' n' HA HL Hin). Qed.
Lemma IMG_LO_bt : AsVocab.AsCells.ia_img_hi (AsAinvDefs3.bt_ia bt) <= AsVocab.AS_LO.
Proof. rewrite <- G_hi. unfold AsVocab.AS_LO. unfold SHMAPLO in G_img_shlo. exact G_img_shlo. Qed.
Theorem as_contracts_HL : forall SEGS FXOK FRESH,   (* [comment removed for export] *)
  (forall z, AsVocab.in_wins (AsVocab.AsCells.ia_priv (AsAinvDefs3.bt_ia bt)) z -> z < AsVocab.AsCells.ia_img_hi (AsAinvDefs3.bt_ia bt)) ->
  AsVocab.ia_errno (AsAinvDefs3.bt_ia bt) + 4 <= AsVocab.AsCells.ia_img_hi (AsAinvDefs3.bt_ia bt) ->
  AsIfaceNM3.as_contracts_n SEGS FXOK (AsAinvDefs3.bt_ia bt) (AsAinvEntry3.AsAinvHole3.AAINV_HS bt) FRESH (AsAinvDefs3.bt_fs bt) ->
  AsIfaceNM3.as_contracts_n SEGS FXOK (AsAinvDefs3.bt_ia bt) AAINV_HL FRESH (AsAinvDefs3.bt_fs bt).
Proof.
  intros SEGS FXOK FRESH HP HE ASC.
  exact (AzBridgeLG.as_contracts_n_LG SEGS FXOK (AsAinvDefs3.bt_ia bt) (AsAinvEntry3.AsAinvHole3.AAINV_HS bt) FRESH (AsAinvDefs3.bt_fs bt) HS_zone IMG_LO_bt HP HE ASC).
Qed.

(* [comment removed for export] *)
Definition AAINV_WL (h : option Z) : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop :=
  AzBridgeLG.AAINV_LG (AsAinvDefs3.AAINV_H bt h).
Definition AINVHW_bt (n : Z) : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop :=
  AINVw (AAINV_WL (Some n)).
Lemma HW_zone : forall h Lc FF B C K M mdl b n, AsAinvDefs3.AAINV_H bt h Lc FF B C K M mdl -> In (b, n) Lc ->
  AsVocab.ablk_ok (AsAinvDefs3.bt_ia bt) b n /\ 1 <= n /\ b mod 16 = 0.
Proof. intros h Lc FF B C K M mdl b n HA Hin. exact (AsVocab.aap_zone _ _ _ _ (AsAinvFrame3b.AAINV_props_all bt (AsAinvDefs3.holes_le h)) _ _ _ _ _ _ _ b n HA Hin). Qed.


Theorem annotate_HL : forall SEGS FXOK entry,
  AsIface3.ANNOTATE_AT SEGS FXOK (AsAinvDefs3.bt_ia bt) (AsAinvEntry3.AsAinvHole3.AAINV_HS bt) entry ->
  AsIface3.ANNOTATE_ATW SEGS FXOK (AsAinvDefs3.bt_ia bt) AAINV_HL entry.
Proof. intros SEGS FXOK entry AN. exact (AzBridgeLG.annotate_LG SEGS FXOK (AsAinvDefs3.bt_ia bt) (AsAinvEntry3.AsAinvHole3.AAINV_HS bt) HS_zone HS_disj entry AN). Qed.
End Inst.
