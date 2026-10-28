(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_SR LbB_MILB LbB_PrsStmt LbB_Own LbB_RtOwn LbB_PmBase LbB_PmOwn LbB_PmCut
  LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmXv LbB_PmVec LbB_PmVup LbB_PmVops LbB_PmDS LbB_WoGen LbB_ContStmt LbB_PmWKit LbB_PmWG
  LbB_HEmpStmt LbB_HEmpR LbB_HRehB LbB_HKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind LbB_HEmp.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition set_m1A (c : pmc) (t : Z * Z * list (Z * (Z * Z))) : pmc :=
  {| c_widx := c_widx c; c_icount := c_icount c; c_endian := c_endian c; c_reqconv := c_reqconv c;
     c_m1 := t; c_m2 := c_m2 c; c_m3 := c_m3 c; c_v1 := c_v1 c; c_v2 := c_v2 c; c_v3 := c_v3 c; c_tr := c_tr c |}.

Definition rest_m1 (c : pmc) : list (Z * Z) :=
  umap_blocks 32 (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c))
  ++ umap_blocks 24 (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c))
  ++ vec_opnd_blocks (t3a (c_v1 c)) (t3c (c_v1 c))
  ++ (if t3a (c_v2 c) =? 0 then [] else [(t3a (c_v2 c), 4 * t3c (c_v2 c))])
  ++ (if t3a (c_v3 c) =? 0 then [] else [(t3a (c_v3 c), 4 * t3c (c_v3 c))])
  ++ c_tr c.
Definition mblk1 (c : pmc) : list (Z * Z) := umap_blocks 24 (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c)).

Lemma cbk_m1 : forall c, Permutation (c_blocks c) (mblk1 c ++ rest_m1 c).
Proof. intros c. unfold c_blocks, mblk1, rest_m1. apply Permutation_refl. Qed.
Lemma cbk_m1' : forall c t, Permutation (c_blocks (set_m1A c t)) (umap_blocks 24 (t3a t) (t3b t) (t3c t) ++ rest_m1 c).
Proof. intros c t. unfold c_blocks, set_m1A, rest_m1. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr]. apply Permutation_refl. Qed.

Lemma pm_phi_blocks_perm : forall l l', Permutation l l' -> pm_phi_blocks l = pm_phi_blocks l'.
Proof.
  intros l l' P. induction P as [|x l1 l2 P IH|x y l1|l1 l2 l3 P1 IH1 P2 IH2].
  - reflexivity.
  - rewrite !pm_phi_blocks_cons, IH. reflexivity.
  - rewrite !pm_phi_blocks_cons. lia.
  - rewrite IH1, IH2. reflexivity.
Qed.
Lemma pm_phi_blocks_nodes : forall (ents : list (Z * (Z * Z))), pm_phi_blocks (map (fun e => (fst e, 24)) ents) = 0.
Proof.
  induction ents as [|e ents IH]; [reflexivity|]. cbn [map]. rewrite pm_phi_blocks_cons, IH. cbn [snd]. unfold ICM_LARGE.
  replace (64512 <? 24) with false by reflexivity. lia.
Qed.
Lemma pm_phi_blocks_umap : forall bl bc (ents : list (Z * (Z * Z))), pm_phi_blocks (umap_blocks 24 bl bc ents) = lg (8 * bc) * (if bc =? 0 then 0 else 1).
Proof.
  intros bl bc ents. unfold umap_blocks. rewrite pm_phi_blocks_app, pm_phi_blocks_nodes.
  destruct (Z.eqb_spec bc 0) as [E|E].
  - rewrite Z.mul_0_r. reflexivity.
  - rewrite pm_phi_blocks_one. lia.
Qed.
Lemma pm_phi_m1 : forall c, pm_phi c = lg (8 * t3b (c_m1 c)) * (if t3b (c_m1 c) =? 0 then 0 else 1) + pm_phi_blocks (rest_m1 c) + pm_prog c.
Proof. intros c. unfold pm_phi. rewrite (pm_phi_blocks_perm _ _ (cbk_m1 c)), pm_phi_blocks_app. unfold mblk1. rewrite pm_phi_blocks_umap. reflexivity. Qed.
Lemma pm_phi_set_m1 : forall c t, pm_phi (set_m1A c t) = lg (8 * t3b t) * (if t3b t =? 0 then 0 else 1) + pm_phi_blocks (rest_m1 c) + pm_prog c.
Proof. intros c t. unfold pm_phi. rewrite (pm_phi_blocks_perm _ _ (cbk_m1' c t)), pm_phi_blocks_app, pm_phi_blocks_umap. reflexivity. Qed.

Lemma bseq_next_ge2 : forall bc, In bc BSEQ -> bc <> BSEQ_LAST -> 2 * bc + 1 <= bseq_next bc.
Proof.
  intros bc Hin Hl. unfold BSEQ in Hin. unfold BSEQ_LAST in Hl.
  repeat (destruct Hin as [<-|Hin];
    [first [lazymatch goal with |- _ <= ?r => let v := eval vm_compute in r in change r with v end; lia | exfalso; apply Hl; reflexivity] |]).
  destruct Hin.
Qed.

Lemma phi_rehash_m1 : forall c bl bc (ents : list (Z * (Z * Z))) bl' (ents' : list (Z * (Z * Z))),
  c_m1 c = (bl, bc, ents) -> In bc BSEQ -> bc <> BSEQ_LAST ->
  pm_phi (set_m1A c (bl', bseq_next bc, ents')) >= pm_phi c + ICM (8 * bseq_next bc).
Proof.
  intros c bl bc ents bl' ents' E Hin Hl.
  pose proof (bseq_next_ge2 bc Hin Hl) as G. pose proof (LbB_HFind.BSEQ_boundA bc Hin) as B.
  rewrite pm_phi_set_m1, pm_phi_m1, E. cbn [t3b fst snd].
  unfold lg, ICM. destruct (Z.eqb_spec (bseq_next bc) 0); [lia|]. destruct (Z.eqb_spec bc 0) as [E0|E0];
    destruct (Z.ltb_spec 64512 (8 * bseq_next bc)); destruct (Z.ltb_spec 64512 (8 * bc)); destruct (Z.leb_spec (8 * bseq_next bc) 64512); lia.
Qed.
Lemma phi_same_m1 : forall c bl bc (ents : list (Z * (Z * Z))) (ents' : list (Z * (Z * Z))),
  c_m1 c = (bl, bc, ents) -> pm_phi (set_m1A c (bl, bc, ents')) = pm_phi c.
Proof. intros c bl bc ents ents' E. rewrite pm_phi_set_m1, pm_phi_m1, E. reflexivity. Qed.

Lemma agree_of_munchW : forall W m m' a k, munch W m m' -> (forall x, a <= x < a + k -> outside W x) ->
  0 <= a -> a + k <= 2 ^ 64 -> HRepFacts.agree_on m m' a k.
Proof. intros W m m' a k MU HO Ha Hak i Hi. apply MU. rewrite u64_of_Z by lia. apply HO. lia. Qed.

Section Keep.
  Context {HCEIL : HeapCeil}.

  Lemma pmc_keep_m1 : forall (p : Z) L L' m m' (c : pmc),
    @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) L m (p + O_M2) (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c)) ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) L m (p + O_M3) (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c)) ->
    @vec_opnd AC_A ASEGS LY_A MI_A L m (p + O_V1) (t3a (c_v1 c)) (t3b (c_v1 c)) (t3c (c_v1 c)) ->
    @vec32 AC_A ASEGS LY_A MI_A L m (p + O_V2) (t3a (c_v2 c)) (t3b (c_v2 c)) (t3c (c_v2 c)) ->
    @vec32 AC_A ASEGS LY_A MI_A L m (p + O_V3) (t3a (c_v3 c)) (t3b (c_v3 c)) (t3c (c_v3 c)) ->
    pmc_sh m c ->
    (forall a, p + O_M2 <= a < p + PARSER_SIZE -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
    (forall A n a, In (A, n) (rest_m1 c) -> A <= a < A + n -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
    (forall A n sbs, In (A, n) (rest_m1 c) -> Z.of_nat (length sbs) <= nsh n -> SHAD m A sbs -> SHAD m' A sbs) ->
    (forall b, In b (rest_m1 c) -> In b L -> In b L') ->
    @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) L' m' (p + O_M2) (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c))
    /\ @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) L' m' (p + O_M3) (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c))
    /\ umap_sh m' 32 (c_m2 c) /\ umap_sh m' 24 (c_m3 c)
    /\ @vec_opnd AC_A ASEGS LY_A MI_A L' m' (p + O_V1) (t3a (c_v1 c)) (t3b (c_v1 c)) (t3c (c_v1 c)) /\ vsh_opnd m' (c_v1 c)
    /\ @vec32 AC_A ASEGS LY_A MI_A L' m' (p + O_V2) (t3a (c_v2 c)) (t3b (c_v2 c)) (t3c (c_v2 c)) /\ vsh32 m' (c_v2 c)
    /\ @vec32 AC_A ASEGS LY_A MI_A L' m' (p + O_V3) (t3a (c_v3 c)) (t3b (c_v3 c)) (t3c (c_v3 c)) /\ vsh32 m' (c_v3 c).
  Proof.
    intros p L L' m m' c U2 U3 V1 V2 V3 SHc HEQ BEQ SEQ LIVE.
    set (P2 := umap_blocks 32 (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c))).
    set (P3 := umap_blocks 24 (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c))).
    set (P4 := vec_opnd_blocks (t3a (c_v1 c)) (t3c (c_v1 c))).
    set (P5 := if t3a (c_v2 c) =? 0 then [] else [(t3a (c_v2 c), 4 * t3c (c_v2 c))]).
    set (P6 := if t3a (c_v3 c) =? 0 then [] else [(t3a (c_v3 c), 4 * t3c (c_v3 c))]).
    set (P7 := c_tr c).
    assert (ER : rest_m1 c = P2 ++ P3 ++ P4 ++ P5 ++ P6 ++ P7) by reflexivity.
    assert (I2 : forall b, In b P2 -> In b (rest_m1 c)) by (intros b Hb; rewrite ER, !in_app_iff; tauto).
    assert (I3 : forall b, In b P3 -> In b (rest_m1 c)) by (intros b Hb; rewrite ER, !in_app_iff; tauto).
    assert (I4 : forall b, In b P4 -> In b (rest_m1 c)) by (intros b Hb; rewrite ER, !in_app_iff; tauto).
    assert (I5 : forall b, In b P5 -> In b (rest_m1 c)) by (intros b Hb; rewrite ER, !in_app_iff; tauto).
    assert (I6 : forall b, In b P6 -> In b (rest_m1 c)) by (intros b Hb; rewrite ER, !in_app_iff; tauto).

    assert (UK : forall NS (V : Type) (nval : mem -> Z -> V -> Prop)
      (nval_agree : forall M M' p v, nval M p v -> HRepFacts.agree_on M M' (p + 20) (NS - 20) -> 0 < p -> p + NS <= 2 ^ 47 -> nval M' p v)
      (HNS : 24 <= NS) off bl bc ents,
      O_M2 <= off -> off + 40 <= PARSER_SIZE ->
      (forall b, In b (umap_blocks NS bl bc ents) -> In b (rest_m1 c)) ->
      @umapx AC_A ASEGS LY_A MI_A NS V nval L m (p + off) bl bc ents ->
      @umapx AC_A ASEGS LY_A MI_A NS V nval L' m' (p + off) bl bc ents).
    { intros NS V nval nval_agree HNS off bl bc ents Ho1 Ho2 IB U.
      eapply (umapx_agree ASEGS LY_A MI_A NS V nval nval_agree HNS); [exact U | |].
      - intros a Ha. unfold umap_foot in Ha. destruct Ha as [Ha|[(Hbc & Ha)|(q & Hq & Ha)]].
        + apply HEQ. lia.
        + assert (Hin : In (bl, 8 * bc) (umap_blocks NS bl bc ents)).
          { unfold umap_blocks. apply in_app_iff. left. destruct (Z.eqb_spec bc 0); [lia | left; reflexivity]. }
          exact (BEQ bl (8 * bc) a (IB _ Hin) Ha).
        + assert (Hin : In (q, NS) (umap_blocks NS bl bc ents)).
          { unfold umap_blocks. apply in_app_iff. right.
            apply in_map_iff in Hq. destruct Hq as ([q' kv] & Eq & Hin). cbn in Eq. subst q'.
            apply in_map_iff. exists (q, kv). split; [reflexivity | exact Hin]. }
          exact (BEQ q NS a (IB _ Hin) Ha).
      - intros b n0 Hb Hl. apply LIVE; [exact (IB _ Hb) | exact Hl]. }
    pose proof SHc as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6).
    split; [apply (UK 32 (Z * Z * Z)%type (nval32 ASEGS) (nval32_agree ASEGS) ltac:(lia) O_M2); [unfold O_M2; lia | unfold O_M2, PARSER_SIZE; lia | exact I2 | exact U2]|].
    split; [apply (UK 24 Z (nval24 ASEGS) (nval24_agree ASEGS) ltac:(lia) O_M3); [unfold O_M2, O_M3; lia | unfold O_M3, PARSER_SIZE; lia | exact I3 | exact U3]|].

    assert (USH : forall NS (V : Type) (t : Z * Z * list (Z * (Z * V))),
      (forall b, In b (umap_blocks NS (t3a t) (t3b t) (t3c t)) -> In b (rest_m1 c)) ->
      umap_sh m NS t -> umap_sh m' NS t).
    { intros NS V [[bl bc] ents] IB [SB SN]. unfold umap_sh. cbn [t3a t3b t3c fst snd] in *. split.
      - intros Hbc. pose proof (SB Hbc) as AD. destruct AD as [Hn SH]. split; [exact Hn|].
        assert (Hin : In (bl, 8 * bc) (umap_blocks NS bl bc ents)).
        { unfold umap_blocks. apply in_app_iff. left. destruct (Z.eqb_spec bc 0); [lia | left; reflexivity]. }
        eapply (SEQ bl (8 * bc)); [exact (IB _ Hin) | rewrite shadow_of_length by lia; lia | exact SH].
      - intros q k v Hin. destruct (SN q k v Hin) as [Hn SH]. split; [exact Hn|].
        assert (Hin' : In (q, NS) (umap_blocks NS bl bc ents)).
        { unfold umap_blocks. apply in_app_iff. right. apply in_map_iff. exists (q, (k, v)). split; [reflexivity | exact Hin]. }
        eapply (SEQ q NS); [exact (IB _ Hin') | rewrite shadow_of_length by lia; lia | exact SH]. }
    split; [exact (USH 32 (Z * Z * Z)%type (c_m2 c) I2 SH2)|].
    split; [exact (USH 24 Z (c_m3 c) I3 SH3)|].

    split; [| split; [| split; [| split; [| split]]]].
    - eapply vec_opnd_live; [eapply vec_opnd_frame; [exact V1|] |].
      + intros a Ha. unfold vec_opnd_fp, zwin in Ha. apply HEQ. unfold O_V1, O_M2, PARSER_SIZE in *. lia.
      + intros Hb Hl. apply LIVE; [| exact Hl]. apply I4. subst P4. unfold vec_opnd_blocks. destruct (Z.eqb_spec (t3a (c_v1 c)) 0); [lia | left; reflexivity].
    - intros Hb. pose proof V1 as (_ & _ & _ & Hlen & _).
      assert (Hin : In (t3a (c_v1 c), OPND_SZ * t3c (c_v1 c)) (rest_m1 c)).
      { apply I4. subst P4. unfold vec_opnd_blocks. destruct (Z.eqb_spec (t3a (c_v1 c)) 0); [lia | left; reflexivity]. }
      eapply (SEQ (t3a (c_v1 c)) (OPND_SZ * t3c (c_v1 c))); [exact Hin | | exact (SH4 Hb)].
      rewrite cc_gen_length by (unfold OPND_SZ; lia). lia.
    - eapply vec32_live; [eapply vec32_frame; [exact V2|] |].
      + intros a Ha. unfold vec32_fp, zwin in Ha. destruct Ha as [Ha|(Hb & Ha)].
        * apply HEQ. unfold O_V2, O_M2, PARSER_SIZE in *. lia.
        * pose proof V2 as (_ & _ & _ & Hlen & _).
          assert (Hin : In (t3a (c_v2 c), 4 * t3c (c_v2 c)) (rest_m1 c)) by (apply I5; subst P5; destruct (Z.eqb_spec (t3a (c_v2 c)) 0); [lia | left; reflexivity]).
          apply (BEQ (t3a (c_v2 c)) (4 * t3c (c_v2 c)) a Hin). unfold Zlen in *. lia.
      + intros Hb Hl. apply LIVE; [| exact Hl]. apply I5. subst P5. destruct (Z.eqb_spec (t3a (c_v2 c)) 0); [lia | left; reflexivity].
    - intros Hb. pose proof V2 as (_ & _ & _ & Hlen & _).
      assert (Hin : In (t3a (c_v2 c), 4 * t3c (c_v2 c)) (rest_m1 c)) by (apply I5; subst P5; destruct (Z.eqb_spec (t3a (c_v2 c)) 0); [lia | left; reflexivity]).
      eapply (SEQ (t3a (c_v2 c)) (4 * t3c (c_v2 c))); [exact Hin | | exact (SH5 Hb)].
      rewrite cc_gen_length by (unfold Zlen in *; lia). lia.
    - eapply vec32_live; [eapply vec32_frame; [exact V3|] |].
      + intros a Ha. unfold vec32_fp, zwin in Ha. destruct Ha as [Ha|(Hb & Ha)].
        * apply HEQ. unfold O_V3, O_M2, PARSER_SIZE in *. lia.
        * pose proof V3 as (_ & _ & _ & Hlen & _).
          assert (Hin : In (t3a (c_v3 c), 4 * t3c (c_v3 c)) (rest_m1 c)) by (apply I6; subst P6; destruct (Z.eqb_spec (t3a (c_v3 c)) 0); [lia | left; reflexivity]).
          apply (BEQ (t3a (c_v3 c)) (4 * t3c (c_v3 c)) a Hin). unfold Zlen in *. lia.
      + intros Hb Hl. apply LIVE; [| exact Hl]. apply I6. subst P6. destruct (Z.eqb_spec (t3a (c_v3 c)) 0); [lia | left; reflexivity].
    - intros Hb. pose proof V3 as (_ & _ & _ & Hlen & _).
      assert (Hin : In (t3a (c_v3 c), 4 * t3c (c_v3 c)) (rest_m1 c)) by (apply I6; subst P6; destruct (Z.eqb_spec (t3a (c_v3 c)) 0); [lia | left; reflexivity]).
      eapply (SEQ (t3a (c_v3 c)) (4 * t3c (c_v3 c))); [exact Hin | | exact (SH6 Hb)].
      rewrite cc_gen_length by (unfold Zlen in *; lia). lia.
  Qed.
End Keep.

Section WM.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.

  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.

  Hypothesis HOWN : rt_own H.
  #[local] Notation ent := (Z * (Z * Z))%type.

  Lemma HHm : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma LINV_fr : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Proof.
    intros m m' W L MU WM FW. apply (LINV_cl m m' L). intros a Ha HC. apply MU. unfold wa. rewrite unsigned_lit by lia.
    assert (HA : a < AIMG_TOP) by (unfold aimg_client, AIMG_TOP in *; lia).
    clear - FW HA. induction W as [|[lo hi] W IH]; cbn; [exact I|].
    apply Forall_cons_iff in FW as [F1 F2]. cbn [fst] in F1. split; [lia | exact (IH F2)].
  Qed.

  Definition mx1 (w : pmwA H) : list (Z * Z) := [(wa_p w + O_M1, wa_p w + O_M1 + 40)].

  Lemma pmxa_emp_m1 : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl s' m' mo' (LB' LBm LBr LBm' : list block)
      (bl bc : Z) (ents : list ent) (bl' bc' : Z) (ents' : list ent) (rehashed : bool) (errv' : word),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c ins tbl ftbl ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    c_m1 c = (bl, bc, ents) ->
    Permutation LBs (LBm ++ LBr) -> lbl LBr = rest_m1 c ->
    pm_bud (wa_n w) (set_m1A c (bl', bc', ents')) ->
    (rehashed = false -> bl' = bl /\ bc' = bc) -> (rehashed = true -> bc' = bseq_next bc) -> In bc BSEQ -> bc <> BSEQ_LAST ->

    as_RHEAP H s' LB' m' -> Permutation LB' ((wa_LB0 w ++ LBr) ++ LBm') -> Permutation (lbl LBm') (umap_blocks 24 bl' bc' ents') ->
    as_MPRES H mo mo' -> mem_inv asegs m' ->
    stk asegs m' (wa_lo w) (wa_s1 w) -> rw_cells asegs m' (errno_addr (wa_tp w)) [C4 errv'] -> as_rauxv_ok H m' (wa_B w) ->
    xpres H (wa_LB0 w ++ LBr) (wa_s1 w) (mx1 w) m m' ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB') m' (wa_p w + O_M1) bl' bc' ents' -> umap_sh m' 24 (bl', bc', ents') ->
    wr_at asegs m' (wa_p w + O_M1) 40 ->
    as_RFS H (PMLF H w) m' -> ACONST m' -> stack0 m' (wa_lo w) (wa_shi w) ->
    as_AL H s' >= as_AL H s - (if rehashed then ICM (8 * bc') else 0) ->
    PMXA H LINV w s' LB' (LBm' ++ LBr) m' mo' (set_m1A c (bl', bc', ents')) ins tbl ftbl.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl s' m' mo' LB' LBm LBr LBm' bl bc ents bl' bc' ents' rehashed errv'
           OK X0 Hknn Hfk Em1 PS ELr BUD' NRH RH Hbs Hlast RH' PE' PM' MP' MI' STK' ERR' RA' XP U1' SH1' WR' RFS' AC' S0' AL'.
    pose proof HHm as HH.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (p_range H w OK) as [PR1 PR2].
    pose proof (wk_n H w OK) as WN.
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (wk_papp H w OK) as (PA & PA0 & PA16).
    pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & (fp0 & Hfp0 & PF1 & PF2 & PF3 & PF4)).
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as RH0.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as [OWN1 OWN2].
    pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (A1 & A2 & A3 & A4).
    set (LBk := wa_LB0 w ++ LBr) in *.
    set (c' := set_m1A c (bl', bc', ents')) in *.
    set (LBs' := LBm' ++ LBr).

    assert (INr : forall b, In b LBr -> In b LBs) by (intros b Hb; apply (Permutation_in _ (Permutation_sym PS)); apply in_or_app; right; exact Hb).
    assert (LBk1 : forall b, In b LBk -> In b LB).
    { intros b Hb. apply (Permutation_in _ (Permutation_sym OWN1)). unfold LBk in Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      - apply in_or_app; left; exact Hb.
      - apply in_or_app; right; apply in_or_app; left. exact (INr b Hb). }
    assert (LBk0 : forall b, In b (wa_LB0 w) -> In b LBk) by (intros b Hb; unfold LBk; apply in_or_app; left; exact Hb).
    assert (INr' : forall b, In b LBr -> In b LB') by (intros b Hb; apply (Permutation_in _ (Permutation_sym PE')); apply in_or_app; left; unfold LBk; apply in_or_app; right; exact Hb).
    assert (P1 : Permutation LB' (wa_LB0 w ++ LBs' ++ [])).
    { rewrite app_nil_r. unfold LBs'. eapply perm_trans; [exact PE'|]. unfold LBk. rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app_comm. }
    assert (P2 : Permutation (lbl LBs') (c_blocks c')).
    { unfold LBs'. replace (lbl (LBm' ++ LBr)) with (lbl LBm' ++ lbl LBr) by (unfold lbl; rewrite map_app; reflexivity). rewrite ELr.
      eapply perm_trans; [| apply Permutation_sym; exact (cbk_m1' c (bl', bc', ents'))]. cbn [t3a t3b t3c fst snd]. apply Permutation_app_tail. exact PM'. }
    pose proof (HOWN s' LB' m' RH') as OWNall.
    assert (OWN3 : lb_own LBs' m').
    { eapply lb_own_incl; [| exact OWNall]. intros b Hb. apply (Permutation_in _ (Permutation_sym P1)). apply in_or_app; right. rewrite app_nil_r. exact Hb. }
    assert (MEAS' : pm_meas_ok (wa_n w) LBs') by (apply (pm_meas_of_bud (wa_n w) c' LBs'); [lia | exact BUD' | exact P2]).
    assert (RESV' : pm_cap c' + PM_RESERVE <= po_cost (wa_n w)) by (apply pm_resv_of_bud; [exact WN | exact BUD']).
    assert (AL1 : as_AL H s' >= as_AL H (wa_s0 w) - pm_phi c' - 0).
    { destruct rehashed.
      - pose proof (RH eq_refl) as Ebc'. pose proof (phi_rehash_m1 c bl bc ents bl' ents' Em1 Hbs Hlast) as PG.
        subst bc'. fold c' in PG. clear - A1 AL' PG. lia.
      - destruct (NRH eq_refl) as [-> ->]. pose proof (phi_same_m1 c bl bc ents ents' Em1) as PG. fold c' in PG. clear - A1 AL' PG. lia. }

    assert (FXI : Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) (mx1 w)) by (unfold mx1; apply Forall_cons; [cbn [fst]; unfold O_M1; lia | apply Forall_nil]).
    assert (LI' : LINV m') by (apply (LINV_cl m m' (xa_linv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)); eapply (xpres_img H); [exact XP | exact FXI]).
    assert (FX : Forall (xv_ok4 H w LBs ftbl) (mx1 w)).
    { unfold mx1. apply Forall_cons; [| apply Forall_nil]. right; left. cbn [fst snd]. unfold O_M1, PARSER_SIZE. lia. }
    assert (FXW : Forall (fun iv : Z * Z => (snd iv <= wa_ff w + 24 \/ wa_ff w + 16376 <= fst iv) \/ wr_at asegs m' (fst iv) (snd iv - fst iv)) (mx1 w)).
    { unfold mx1. apply Forall_cons; [| apply Forall_nil]. right. cbn [fst snd]. replace (wa_p w + O_M1 + 40 - (wa_p w + O_M1)) with 40 by lia. exact WR'. }

    assert (Hp_fs : as_FSB H <= wa_p w /\ wa_p w + PARSER_SIZE <= as_FSB H + AFS_SIZE) by (unfold AFS_HDR in *; lia).
    assert (HEQ : forall a, wa_p w + O_M2 <= a < wa_p w + PARSER_SIZE -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { intros a Ha. apply (XP a); [unfold O_M2, PARSER_SIZE in *; lia|]. split.
      - right; right; right; right; left. unfold O_M2, PARSER_SIZE in *. lia.
      - unfold mx1. cbn [rin_ivs fst snd]. unfold O_M1, O_M2 in *. lia. }
    assert (BLKr : forall A n, In (A, n) (rest_m1 c) -> exists q, In (q, A, n) LBr /\ In (q, A, n) LBk /\ In (q, A, n) LB /\ ablock_range H A n).
    { intros A n Hin. rewrite <- ELr in Hin. destruct (lbl_in_inv _ _ _ Hin) as (q & Hq). exists q.
      assert (Hk : In (q, A, n) LBk) by (unfold LBk; apply in_or_app; right; exact Hq).
      split; [exact Hq|]. split; [exact Hk|]. split; [exact (LBk1 _ Hk)|]. exact (ah_blocks H HH _ _ _ _ RH0 (LBk1 _ Hk)). }
    assert (BEQ : forall A n a, In (A, n) (rest_m1 c) -> A <= a < A + n -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { intros A n a Hin Ha. destruct (BLKr A n Hin) as (q & Hq & Hk & HL & (R0 & R16 & Rn & RI & RC & RF & RAPP)).
      apply (XP a); [lia|]. split.
      - right; right; left. exists (q, A, n). split; [exact Hk | cbn; lia].
      - unfold mx1. cbn [rin_ivs fst snd]. unfold AFS_HDR, O_M1, PARSER_SIZE in *. lia. }
    assert (SEQ : forall A n sbs, In (A, n) (rest_m1 c) -> Z.of_nat (length sbs) <= nsh n -> SHAD m A sbs -> SHAD m' A sbs).
    { intros A n sbs Hin Hlen SH. destruct (BLKr A n Hin) as (q & Hq & Hk & HL & (R0 & R16 & Rn & RI & RC & RF & RAPP)).
      eapply (xpres_SHAD H); [exact XP | exact SH |]. split.
      - right; right; right; left. exists (q, A, n). split; [exact Hk | cbn; lia].
      - unfold mx1. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
        pose proof (aapp_disjoint_sh (wa_p w) PARSER_SIZE A n PA ltac:(lia) ltac:(pose proof (aapp_bounds _ _ RAPP Rn); lia) Rn) as D.
        unfold O_M1, PARSER_SIZE in *. destruct D; lia. }
    assert (LIVE : forall b, In b (rest_m1 c) -> In b (lbl LB) -> In b (lbl LB')).
    { intros [A n] Hin _. destruct (BLKr A n Hin) as (q & Hq & _). exact (lbl_in LB' q A n (INr' _ Hq)). }
    pose proof (pmc_keep_m1 (wa_p w) (lbl LB) (lbl LB') m m' c
                  (xa_m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)
                  (xa_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_v3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)
                  (proj1 (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)) HEQ BEQ SEQ LIVE)
      as (U2' & U3' & SH2' & SH3' & V1' & VS1' & V2' & VS2' & V3' & VS3').
    assert (SHc' : pmc_sh m' c').
    { unfold pmc_sh. unfold c', set_m1A. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3].
      split; [exact SH1'|]. split; [exact SH2'|]. split; [exact SH3'|]. split; [exact VS1'|]. split; [exact VS2' | exact VS3']. }
    assert (MDh : mdef m' (wa_p w + O_M1) (PARSER_SIZE - O_M1)).
    { eapply mdef_hdrs; [exact U1' | exact U2' | exact U3' | exact V1' | exact V2' | exact V3']. }

    eapply (pmxa_xv4 H HH LINV w s LB LBs m mo c ins tbl ftbl [] 0 s' LB' LBs' m' mo' c' [] 0 LBk (mx1 w) []);
      [exact OK | exact X0 | exact Hknn | exact RH' | exact MP' | exact MI' | exact STK' | exists errv'; exact ERR' | exact RA' | exact RFS' | exact AC' | exact S0'
      | exact LI' | apply Forall_nil | rewrite app_nil_r; exact XP | exact FX | exact FXW | exact MDh | exact Hfk
      | exact LBk1 | exact LBk0
      | exact P1 | exact P2 | exact OWN3 | exact MEAS' | apply lb_own_nil | cbn; lia
      | exact AL1 | exact RESV' | exact A4
      | reflexivity | reflexivity | reflexivity | reflexivity
      | exact U1' | exact U2' | exact U3' | exact V1' | exact V2' | exact V3' | exact SHc' ].
  Qed.

  Lemma bseq_next_le2 : forall bc, In bc BSEQ -> bc <> BSEQ_LAST -> bseq_next bc <= 2 * bc + 63.
  Proof.
    intros bc Hin Hl. unfold BSEQ in Hin. unfold BSEQ_LAST in Hl.
    repeat (destruct Hin as [<-|Hin];
      [first [lazymatch goal with |- ?l <= _ => let v := eval vm_compute in l in change l with v end; lia | exfalso; apply Hl; reflexivity] |]).
    destruct Hin.
  Qed.

  Lemma bud_emp_m1 : forall n c bl bc (ents : list ent) bl' bc' (ents' : list ent),
    pm_bud n c -> c_m1 c = (bl, bc, ents) -> In bc BSEQ -> bc <> BSEQ_LAST ->
    2 * (Zlength ents + 1) <= n + 2 -> Zlength ents' <= Zlength ents + 1 ->
    (bc' = bc \/ ((bc = 0 \/ Zlength ents = bc) /\ bc' = bseq_next bc)) ->
    pm_bud n (set_m1A c (bl', bc', ents')).
  Proof.
    intros n c bl bc ents bl' bc' ents' BUD E Hbs Hl ACC LEN CASE.
    pose proof (bseq_next_le2 bc Hbs Hl) as LE. pose proof (bseq_next_ge2 bc Hbs Hl) as GE. pose proof (LbB_HFind.BSEQ_boundA bc Hbs) as B0.
    assert (N2 : bseq_next 0 = 2) by reflexivity.
    unfold pm_bud in *. unfold set_m1A. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd] in *.
    rewrite E in BUD. cbn [t3a t3b t3c fst snd] in BUD.
    destruct BUD as ((C1a & C1b & C1c) & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
    unfold Zlength in *.
    refine (conj (conj _ (conj C1b C1c)) (conj _ (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 C9))))))));
      [clear - ACC LEN; lia |].
    destruct CASE as [-> | [[-> | EL] ->]]; [exact C2 | rewrite N2; clear - C2 ACC; lia | clear - C2 ACC LE GE EL B0; lia].
  Qed.

  Lemma pm_emplace_m1 : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl msF R F fc (ret sok sot key : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c ins tbl ftbl ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 (emp_entry EMP_U32)) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (wa_p w + O_M1) -> PropExec.getr R 11%bv = Z_to_bv 64 (wa_ff w + sok) ->
    PropExec.getr R 13%bv = Z_to_bv 64 (wa_ff w + sot) ->

    accessible m (wa_ff w + sok) 4 -> 24 <= sok -> sok + 4 <= 15616 -> sok mod 4 = 0 ->
    obj_sh_ok ins sot 8 = true -> 24 <= sot -> sot + 8 <= 15616 -> sot mod 8 = 0 ->
    rw_cells asegs m (wa_ff w + sok) [C4 (Z_to_bv 64 key)] -> 0 <= key < 2 ^ 32 ->
    rw_cells asegs m (wa_ff w + sot) [C8 (Z_to_bv 64 (wa_ff w + sok))] ->

    pm_bud (wa_n w) c -> 2 * (Zlength (t3c (c_m1 c)) + 1) <= wa_n w + 2 ->
    (forall msF1 mo1 m1 (s1 : as_St H) (LB1 LBs1 : list block) (F1 : bvmap 5 word) (fc1 : bv 32)
            (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (p v : Z) (t : Z * Z * list ent) (inserted : bool),
       as_AKREL H s1 (mkCfg msF1 mo1) ->
       as_VIS H s1 msF1 = MS (mkR (Z_to_bv 64 ret) (PropExec.getr R 2%bv) (PropExec.getr R 3%bv) (PropExec.getr R 4%bv) t0 t1 t2
                                   (PropExec.getr R 8%bv) (PropExec.getr R 9%bv) (Z_to_bv 64 p) (Z_to_bv 64 (b2z inserted)) a2 a3 a4 a5 a6 a7
                                   (PropExec.getr R 18%bv) (PropExec.getr R 19%bv) (PropExec.getr R 20%bv) (PropExec.getr R 21%bv)
                                   (PropExec.getr R 22%bv) (PropExec.getr R 23%bv) (PropExec.getr R 24%bv) (PropExec.getr R 25%bv)
                                   (PropExec.getr R 26%bv) (PropExec.getr R 27%bv) t3 t4 t5 t6)
                              F1 (Z_to_bv 64 ret) fc1 None m1 (seg_rom asegs) ->
       frm_zero fc1 ->
       PMXA H LINV w s1 LB1 LBs1 m1 mo1 (set_m1A c t) ins tbl ftbl ->
       In (p, (key, v)) (t3c t) -> 0 <= v < 2 ^ 32 ->
       Zlength (t3c (c_m1 c)) <= Zlength (t3c t) <= Zlength (t3c (c_m1 c)) + 1 ->
       (inserted = false -> t3c t = t3c (c_m1 c)) ->
       (inserted = true -> v = 0 /\ Permutation (t3c t) ((p, (key, 0)) :: t3c (c_m1 c))) ->
       pm_bud (wa_n w) (set_m1A c t) ->

       (t3b t = t3b (c_m1 c) \/ ((t3b (c_m1 c) = 0 \/ Zlength (t3c (c_m1 c)) = t3b (c_m1 c)) /\ t3b t = bseq_next (t3b (c_m1 c)))) ->
       In (t3b (c_m1 c)) BSEQ -> t3b (c_m1 c) <> BSEQ_LAST ->
       (forall k cs, 0 <= k -> k + Z.of_nat (cells_size cs) <= 16384 -> rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m1 (wa_ff w + k) cs) ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl msF R F fc ret sok sot key Q OK X Hknn Hfk KR VIS RF FRZ
           G1 Hr2 Hr G2 G4 G10 G11 G13 Hokk Hk1 Hk2 Hk4 Hokt Ht1 Ht2 Ht8 RWk Hkey RWt BUD ACC K.
    pose proof HHm as HH.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (wk_papp H w OK) as (PA & PA0 & PA16). pose proof (p_range H w OK) as [PR1 PR2].
    pose proof (wk_stack H w OK) as (S1 & S2 & S3 & S4 & S5 & S6). pose proof (wk_s1 H w OK) as [T1 T2].
    pose proof (wk_n H w OK) as WN. pose proof (wk_B64 H w OK) as B64.
    pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & (fp0 & Hfp0 & PF1 & PF2 & PF3 & PF4)).
    pose proof (lf0_apart_ff H w fp0 (wa_p w) PARSER_SIZE OK Hfp0 PF1 PF2) as PFF.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 OWN2].
    pose proof (xa_errno _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (errv & ERR).
    pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (A1 & A2 & A3 & A4).
    pose proof (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (SHc & ADp & _).
    pose proof (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as FSH.
    destruct (c_m1 c) as [[bl bc] ents] eqn:Em1. cbn [t3a t3b t3c fst snd] in *.
    pose proof (xa_m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as U. rewrite Em1 in U. cbn [t3a t3b t3c fst snd] in U.
    pose proof SHc as (SH1 & _). rewrite Em1 in SH1.
    pose proof (u_bseq U) as Hbs. pose proof (LbB_HFind.BSEQ_boundA bc Hbs) as B0.
    pose proof BUD as BUDc. unfold pm_bud in BUDc. rewrite Em1 in BUDc. cbn [t3a t3b t3c fst snd] in BUDc.
    destruct BUDc as ((C1a & _ & _) & C2 & _).
    assert (Hlast : bc <> BSEQ_LAST) by (unfold BSEQ_LAST; clear - C2 WN; lia).
    pose proof (bseq_next_le2 bc Hbs Hlast) as LE2.
    destruct (bseq_next_factsE bc Hbs Hlast) as (_ & Hbcn & Hn28 & _).

    pose proof OWN2 as OWN2'. rewrite <- (app_nil_r (c_blocks c)) in OWN2'.
    destruct (lbl_perm_splitR LBs (mblk1 c) (rest_m1 c) ltac:(eapply perm_trans; [exact OWN2 | exact (cbk_m1 c)])) as (LBm & LBr & PS & ELm & ELr).
    unfold mblk1 in ELm. rewrite Em1 in ELm. cbn [t3a t3b t3c fst snd] in ELm.
    set (LBk := wa_LB0 w ++ LBr).
    assert (PE : Permutation LB (LBk ++ LBm)).
    { eapply perm_trans; [exact OWN1|]. rewrite app_nil_r. unfold LBk. rewrite <- app_assoc. apply Permutation_app_head.
      eapply perm_trans; [exact PS | apply Permutation_app_comm]. }
    assert (OWNm : lb_own LBm m).
    { eapply lb_own_incl; [| exact (xa_lbown _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)]. intros b Hb. apply (Permutation_in _ (Permutation_sym PS)). apply in_or_app; left; exact Hb. }

    assert (TRd : trace_ok (as_TR H) APC0_FREE [emp_del_ra EMP_U32]).
    { pose proof (wk_tr H w OK) as TR. unfold pm_tr_ok, PM_DEL_RAS in TR. exact (proj1 (Forall_forall _ _) TR 0xfad2c ltac:(cbn; tauto)). }

    change (fsz PM_FCLASS) with 16384 in *.
    assert (ADt : addressable m (wa_ff w + sot) 8) by exact (ff_addressable m (wa_ff w) ins sot 8 FSH Hokt).
    assert (AKk : accessible m (wa_ff w + sok) 4) by exact Hokk.
    assert (AKt : accessible m (wa_ff w + sot) 8) by (apply (addressable_accessible m (wa_ff w + sot) 8 (wa_ff w + sot) 8 ADt); [lia | lia | unfold AAPP_HI in *; lia]).
    assert (FKk : fldA m (wa_ff w + sok) 4 key).
    { pose proof (fld_of_cell4 m (wa_ff w + sok) (Z_to_bv 64 key) RWk ltac:(lia)) as FL. rewrite HLib.u64_of_Z in FL by lia. exact FL. }
    assert (FKt : fldA m (wa_ff w + sot) 8 (wa_ff w + sok)).
    { pose proof (fld_of_cell8 m (wa_ff w + sot) (Z_to_bv 64 (wa_ff w + sok)) RWt ltac:(lia)) as FL. rewrite HLib.u64_of_Z in FL by lia. exact FL. }
    assert (ESRC : forall so n, 0 <= so -> so + n <= 15616 -> 0 <= n <= 8 -> emp_src H LBk (wa_s1 w) (wa_p w + O_M1) (wa_ff w + so) n).
    { intros so n Hso Hson Hn. split; [| split].
      - right; right; right; right; left. clear - F1 F2 Hso Hson Hn. unfold AFS_HDR in *. lia.
      - right; right; right; right; right; left. split; [apply sh_mono; clear - F1 Hso; unfold AFS_HDR in *; lia|].
        assert (sh (wa_ff w + so) + nsh n <= sh (wa_ff w + so + 16)) by (unfold sh, nsh; Z.div_mod_to_equations; lia).
        assert (sh (wa_ff w + so + 16) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; clear - F2 Hson Hn; lia). lia.
      - unfold apart. unfold O_M1, PARSER_SIZE in *. clear - PFF Hso Hson Hn. lia. }

    pose proof (pm_phi_le_cap c) as PCc.
    assert (AL0 : 0 <= as_AL H s) by (unfold PM_RESERVE in *; clear - A1 A2 A3 PCc; lia).
    assert (RICM : (bc = 0 \/ Zlength ents = bc) -> ICM (8 * bseq_next bc) <= as_AL H s).
    { intros CASE.
      pose proof (bud_emp_m1 (wa_n w) c bl bc ents 1 (bseq_next bc) ((1, (key, 0)) :: ents) BUD Em1 Hbs Hlast ACC
                    ltac:(unfold Zlength; cbn [length]; lia) (or_intror (conj CASE eq_refl))) as BUDg.
      pose proof (pm_resv_of_bud (wa_n w) _ WN BUDg) as RESVg.
      pose proof (phi_rehash_m1 c bl bc ents 1 ((1, (key, 0)) :: ents) Em1 Hbs Hlast) as PG.
      match type of RESVg with pm_cap ?cc + _ <= _ => pose proof (pm_phi_le_cap cc) as PCg end.
      clear - A1 A3 RESVg PG PCg. unfold PM_RESERVE in *. lia. }
    pose proof (pmxa_meas_LB H LINV w s LB LBs m mo c ins tbl ftbl [] 0 OK X) as (M1 & M2 & M3).
    pose proof (pmxa_meas_LB2 H LINV w s LB LBs m mo c ins tbl ftbl [] 0 OK X) as (M4 & M5).
    pose proof (nsmall_bounds (8 * bseq_next bc) ltac:(lia)) as NSB. pose proof (nlg_bounds (8 * bseq_next bc)) as NLB.

    rewrite (rfull_eq R RF) in VIS.
    eapply (ah_seq H HH).
    { eapply (LbB_HEmp.emp_u32_okA H HHbp) with (obj := wa_p w + O_M1) (keyp := wa_ff w + sok) (tupp := wa_ff w + sot) (keyp2 := wa_ff w + sok)
        (key := key) (bl := bl) (bc := bc) (ents := ents) (LB := LB) (LB0 := LBk) (LBm := LBm) (LF := PMLF H w)
        (lo := wa_lo w) (B := wa_B w) (shi := wa_shi w) (errv := errv) (s := s) (m := m) (mo := mo);
      [ exact VIS | exact FRZ | exact G10 | exact G11 | exact G13
      | exact U | exact SH1 | exact PE | rewrite ELm; apply Permutation_refl
      | apply (pw_addr_sub8 m (wa_p w) PARSER_SIZE O_M1 40 ADp); unfold O_M1, PARSER_SIZE; try reflexivity; lia
      | apply (wr_at_of_mdef m (wa_p w) PARSER_SIZE O_M1 40 (xa_pdef _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)); unfold O_M1, PARSER_SIZE; lia
      | exists fp0; split; [right; exact Hfp0 | unfold O_M1, PARSER_SIZE in *; lia]
      | unfold O_M1, PARSER_SIZE in *; lia
      | intros b Hb; pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (_ & _ & _ & _ & _ & RFb & _); unfold AFS_HDR, O_M1, PARSER_SIZE in *; clear - RFb PF1 PF2 PF3 PF4; lia
      | exact FKk | exact AKk | rewrite G2, u64_of_Z by lia; apply ESRC; lia
      | exact FKt | exact AKt | rewrite G2, u64_of_Z by lia; apply ESRC; lia
      | exact FKk | exact AKk | rewrite G2, u64_of_Z by lia; apply ESRC; lia
      | clear - Q2 Hk4; Z.div_mod_to_equations; lia | clear - Q2 Ht8; Z.div_mod_to_equations; lia | clear - Q2 Hk4; Z.div_mod_to_equations; lia
      | exact Hkey
      | clear - ACC WN; unfold Zlength in *; lia | exact Hlast
      | exact RH | exact KR | exact AL0
      | clear - M4 NSB; unfold nsmall in *; destruct (Z.leb_spec (8 * bseq_next bc) 64512); lia | exact M2 | clear - M5 NLB; lia
      | exact RICM | exact TRd
      | exact (xa_rauxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | rewrite G2, u64_of_Z by lia; lia | exact B64
      | rewrite G2, u64_of_Z by lia; clear - Q12; Z.div_mod_to_equations; lia
      | rewrite G2, u64_of_Z by lia; exact (proj1 (stk_split asegs m (wa_lo w) (wa_s1 w) (wa_sp0 w) (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) ltac:(lia)))
      | lia | rewrite G2, u64_of_Z by lia; unfold AEMP_STACK, AOPNEW_STACK, AMALLOC_STACK, APM_STACK in *; lia
      | rewrite G4; exact ERR | exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | rewrite G4; exact (wk_tp H w OK)
      | rewrite G1, u64_of_Z by lia; exact Hr2
      | exact (xa_aconst _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | exact (xa_rfs _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | exact (xa_stack0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)
      | rewrite G2, u64_of_Z by lia; lia
      | exact OWNm ]. }
    intros [ms1 mo1] POST.
    destruct POST as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & errv1 & s1 & LB' & LBm' & F' & fc' & p & v & bl' & bc'
                      & ents' & inserted & rehashed & POST).
    cbv zeta in POST.
    destruct POST as (VIS1 & FRZ1 & KR1 & MP1 & MI1 & ST1 & ER1 & RA1 & U1 & SH1' & AD1 & WR1 & Hin & NINS & INS & NRH & RHD & RH1 & PE1 & PM1 & OW1 & XP1 & RF1 & AC1' & S01 & AL1).
    cbn [cfg_ms cfg_model] in VIS1, KR1, MP1.
    rewrite G1, (ret_pc_even ret Hr Hr2) in VIS1. rewrite G2, u64_of_Z in ST1 by lia. rewrite G4 in ER1. rewrite G2, u64_of_Z in XP1 by lia.

    pose proof U1 as U1d. destruct U1d as [_ _ _ _ Ubseq' Uload' _ _ _ _ _ _ _ _ Unode' _].
    assert (LEN : Zlength ents <= Zlength ents' <= Zlength ents + 1).
    { destruct inserted.
      - pose proof (Permutation_length (proj2 (INS eq_refl))) as E. unfold Zlength. rewrite E. cbn [length]. lia.
      - destruct (NINS eq_refl) as [-> _]. lia. }
    assert (CASE : bc' = bc \/ ((bc = 0 \/ Zlength ents = bc) /\ bc' = bseq_next bc)).
    { destruct rehashed; [right; exact (RHD eq_refl) | left; exact (proj2 (NRH eq_refl))]. }
    assert (BUD1 : pm_bud (wa_n w) (set_m1A c (bl', bc', ents'))) by exact (bud_emp_m1 (wa_n w) c bl bc ents bl' bc' ents' BUD Em1 Hbs Hlast ACC (proj2 LEN) CASE).
    assert (X1 : PMXA H LINV w s1 LB' (LBm' ++ LBr) m1 mo1 (set_m1A c (bl', bc', ents')) ins tbl ftbl).
    { eapply (pmxa_emp_m1 w s LB LBs m mo c ins tbl ftbl s1 m1 mo1 LB' LBm LBr LBm' bl bc ents bl' bc' ents' rehashed errv1);
        [ exact OK | exact X | exact Hknn | exact Hfk | exact Em1 | exact PS | exact ELr | exact BUD1
        | exact NRH | intros Hrh; exact (proj2 (RHD Hrh)) | exact Hbs | exact Hlast
        | exact RH1 | exact PE1 | exact PM1 | exact MP1 | exact MI1 | exact ST1 | exact ER1 | exact RA1
        | exact XP1 | exact U1 | exact SH1' | exact WR1 | exact RF1 | exact AC1' | exact S01 | exact AL1 ]. }
    destruct (Unode' p key v Hin) as (_ & _ & _ & _ & _ & _ & _ & NV & _). pose proof (proj1 NV) as Rv. cbn in Rv.
    eapply (K ms1 mo1 m1 s1 LB' (LBm' ++ LBr) F' fc' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' p v (bl', bc', ents') inserted);
      [ exact KR1 | exact VIS1 | exact FRZ1 | exact X1 | exact Hin | exact Rv | cbn [t3c snd]; exact LEN
      | intros Hf; cbn [t3c snd]; exact (proj1 (NINS Hf)) | intros Ht; cbn [t3c snd]; exact (INS Ht) | exact BUD1
      | cbn [t3a t3b t3c fst snd]; exact CASE | cbn [t3a t3b t3c fst snd]; exact Hbs | cbn [t3a t3b t3c fst snd]; exact Hlast |].

    intros k cs Hk Hkc RWc. eapply (xpres_rw_cells H); [exact XP1 | exact RWc |]. split.
    - right; right; right; right; left. clear - F1 F2 Hk Hkc. unfold AFS_HDR in *. lia.
    - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. unfold O_M1, PARSER_SIZE in *. clear - PFF Hk Hkc. lia.
  Qed.

  Lemma umapx_set_val24A : forall L m m' obj bl bc (l1 l2 : list ent) (p k v v' : Z),
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) L m obj bl bc (l1 ++ (p, (k, v)) :: l2) -> 0 <= v' < 2 ^ 32 ->
    munch [(p + 20, p + 24)] m m' -> (forall x, m x <> None -> m' x <> None) ->
    rw_cells asegs m' (p + 20) [C4 (Z_to_bv 64 v')] ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) L m' obj bl bc (l1 ++ (p, (k, v')) :: l2).
  Proof.
    intros L m m' obj bl bc l1 l2 p k v v' U Hv' MU DM RW.
    destruct U as [UH Ual Ulo Uhi Ubseq Uload Ublive Ublal Ubllo Ublhi Ublobj Ubkt Unodup Uchain Unode Unapart].
    assert (Hinp : In (p, (k, v)) (l1 ++ (p, (k, v)) :: l2)) by (apply in_app_iff; right; left; reflexivity).
    destruct (Unode p k v Hinp) as (Hlive & Hp0 & Hp47 & Hpal & Ck8 & Ck16 & Rk & Nv & Apo & Apb).
    assert (Efst : map fst (l1 ++ (p, (k, v')) :: l2) = map fst (l1 ++ (p, (k, v)) :: l2)) by (rewrite !map_app; reflexivity).
    assert (Elen : HRep.Zlength (l1 ++ (p, (k, v')) :: l2) = HRep.Zlength (l1 ++ (p, (k, v)) :: l2)) by (unfold HRep.Zlength; rewrite !length_app; reflexivity).
    assert (Ehd : forall l, hdaddr ((p, (k, v')) :: l) = hdaddr ((p, (k, v)) :: l)) by (intros; reflexivity).
    assert (Ehd2 : hdaddr (l1 ++ (p, (k, v')) :: l2) = hdaddr (l1 ++ (p, (k, v)) :: l2)) by (destruct l1; reflexivity).

    assert (AG : forall a n, 0 <= a < 2 ^ 64 -> a + n <= 2 ^ 64 -> apart (p + 20) 4 a n -> HRepFacts.agree_on m m' a n).
    { intros a n Ha Han Hap. apply (agree_of_munchW [(p + 20, p + 24)] m m' a n MU); [| lia | lia].
      intros x Hx. cbn. unfold apart in Hap. lia. }
    assert (KEEP : forall a (wd : N) x, cellw ASEGS m a wd x -> 0 <= a -> a + Z.of_N wd <= 2 ^ 47 -> apart (p + 20) 4 a (Z.of_N wd) -> cellw ASEGS m' a wd x).
    { intros a wd x C Ha Hw Hap. eapply cellw_agree; [exact C | apply AG; [lia | lia | exact Hap] | lia | lia]. }

    assert (OTHER : forall q kq vq, In (q, (kq, vq)) (l1 ++ (p, (k, v)) :: l2) -> q <> p -> apart q 24 p 24).
    { intros q kq vq Hq Hne. apply Unapart; [| | exact Hne]; apply in_map_iff; [exists (q, (kq, vq)) | exists (p, (k, v))]; auto. }
    constructor; rewrite ?Efst, ?Elen; try assumption.
    -   destruct UH as [H1 H2 H3 H4 H5 H6]. constructor; rewrite ?Ehd2, ?Elen; unfold cell8, cell4 in *;
        try (apply KEEP; [assumption | lia | cbn; lia | unfold apart in *; cbn; lia]).
      intros i Hi. apply DM. exact (H6 i Hi).
    -   intros i Hi. destruct (Ubkt i Hi) as (b & Cb & Hb). exists b. split.
      + unfold cell8 in *. apply KEEP; [exact Cb | lia | cbn; lia |].
        assert (Hbc : bc <> 0) by lia. pose proof (Apb Hbc) as Ap. unfold apart in *. cbn. lia.
      + unfold bucket_ok in *. rewrite Efst. destruct Hb as [Hb|[Hb|(Hb1 & Hb2 & Hb3)]]; [left; exact Hb | right; left; exact Hb | right; right].
        split; [exact Hb1|]. split; [destruct l1; discriminate|]. rewrite Hb3. destruct l1; reflexivity.
    -
      assert (CH : forall (ents : list ent), chain ASEGS m ents ->
                     (forall q kq vq, In (q, (kq, vq)) ents -> q = p \/ apart q 24 p 24) ->
                     (forall q kq vq, In (q, (kq, vq)) ents -> 0 < q /\ q + 24 <= 2 ^ 47) ->
                     chain ASEGS m' ents).
      { intros ents. induction ents as [|[q [kq vq]] ents IH]; intros C Hq Hr; [exact Logic.I|]. cbn [chain] in C |- *. destruct C as [C1 C2].
        split; [| apply IH; [exact C2 | intros q' k' u' H'; apply (Hq q' k' u'); right; exact H' | intros q' k' u' H'; apply (Hr q' k' u'); right; exact H']].
        unfold cell8 in *. destruct (Hr q kq vq (or_introl eq_refl)) as [Hq0 Hq47].
        apply KEEP; [exact C1 | lia | cbn; lia |]. destruct (Hq q kq vq (or_introl eq_refl)) as [-> | Hap]; unfold apart in *; cbn; lia. }
      assert (CH2 : chain ASEGS m' (l1 ++ (p, (k, v)) :: l2)).
      { apply CH; [exact Uchain | |].
        - intros q kq vq Hq. destruct (Z.eq_dec q p) as [-> | Hne]; [left; reflexivity | right; exact (OTHER q kq vq Hq Hne)].
        - intros q kq vq Hq. destruct (Unode q kq vq Hq) as (_ & H0 & H47 & _). lia. }
      clear - CH2 Ehd. revert CH2. generalize l2. induction l1 as [|[q [kq vq]] l1 IH]; intros l2' C; cbn [chain app] in C |- *.
      + exact C.
      + destruct C as [C1 C2]. split; [| apply IH; exact C2]. destruct l1; [cbn in C1 |- *; exact C1 | exact C1].
    -   intros q kq vq Hq.
      assert (NP : ~ In p (map fst l1) /\ ~ In p (map fst l2)).
      { rewrite map_app in Unodup. cbn [map fst] in Unodup. apply (proj1 (list_relations.list.NoDup_app _ _)) in Unodup. destruct Unodup as (N1 & NX & N2).
        split.
        - intros H1. refine (NX p _ _); [apply list_elem_of_In; exact H1 | apply list_elem_of_In; left; reflexivity].
        - intros H2. apply (proj1 (list_relations.list.NoDup_cons _ _)) in N2. destruct N2 as [N2 _]. apply N2. apply list_elem_of_In. exact H2. }
      destruct NP as [NP1 NP2].
      apply in_app_iff in Hq. destruct Hq as [Hq|[Hq|Hq]].
      + assert (Hne : q <> p) by (intros ->; apply NP1; apply in_map_iff; exists (p, (kq, vq)); auto).
        assert (Hq' : In (q, (kq, vq)) (l1 ++ (p, (k, v)) :: l2)) by (apply in_app_iff; left; exact Hq).
        destruct (Unode q kq vq Hq') as (L1 & L2 & L3 & L4 & C8 & C16 & RK & NV & AP1 & AP2). pose proof (OTHER q kq vq Hq' Hne) as AP.
        unfold cell8, cell4, nval24 in *. repeat match goal with |- _ /\ _ => split end; try assumption; try lia;
          (apply KEEP; [assumption | lia | cbn; lia | unfold apart in *; cbn; lia]).
      + injection Hq. intros -> -> ->.
        unfold cell8, cell4, nval24 in *. repeat match goal with |- _ /\ _ => split end; try assumption; try lia;
          try (apply KEEP; [assumption | lia | cbn; lia | unfold apart; cbn; lia]).
        eapply cellw4_of_rw_cells; [exact RW | assumption | lia].
      + assert (Hne : q <> p) by (intros ->; apply NP2; apply in_map_iff; exists (p, (kq, vq)); auto).
        assert (Hq' : In (q, (kq, vq)) (l1 ++ (p, (k, v)) :: l2)) by (apply in_app_iff; right; right; exact Hq).
        destruct (Unode q kq vq Hq') as (L1 & L2 & L3 & L4 & C8 & C16 & RK & NV & AP1 & AP2). pose proof (OTHER q kq vq Hq' Hne) as AP.
        unfold cell8, cell4, nval24 in *. repeat match goal with |- _ /\ _ => split end; try assumption; try lia;
          (apply KEEP; [assumption | lia | cbn; lia | unfold apart in *; cbn; lia]).
  Qed.

  Lemma pm_m1_setval : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl m' (bl bc : Z) (l1 l2 : list ent) (p k v v' : Z),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo (set_m1A c (bl, bc, l1 ++ (p, (k, v)) :: l2)) ins tbl ftbl ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    munch [(p + 20, p + 24)] m m' -> wmono asegs m m' -> (forall x, m x <> None -> m' x <> None) -> mem_inv asegs m' ->
    rw_cells asegs m' (p + 20) [C4 (Z_to_bv 64 v')] -> 0 <= v' < 2 ^ 32 ->
    PMXA H LINV w s LB LBs m' mo (set_m1A c (bl, bc, l1 ++ (p, (k, v')) :: l2)) ins tbl ftbl.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl m' bl bc l1 l2 p k v v' OK X0 Hknn Hfk MU WM DM MI' RW Hv'.
    pose proof HHm as HH.
    set (c0 := set_m1A c (bl, bc, l1 ++ (p, (k, v)) :: l2)) in *.
    set (c1 := set_m1A c (bl, bc, l1 ++ (p, (k, v')) :: l2)).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND. pose proof (p_range H w OK) as [PR1 PR2]. pose proof (wk_papp H w OK) as (PA & PA0 & PA16).
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as [OWN1 OWN2].
    pose proof (xa_m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as U. unfold c0, set_m1A in U. cbn [c_m1 c_m2 c_m3 t3a t3b t3c fst snd] in U.
    assert (Hinp : In (p, (k, v)) (l1 ++ (p, (k, v)) :: l2)) by (apply in_app_iff; right; left; reflexivity).
    pose proof U as Ud. destruct Ud as [_ _ _ _ _ _ _ _ _ _ _ _ Unodup _ Unode Unapart].
    destruct (Unode p k v Hinp) as (Hlive & Hp0 & Hp47 & Hpal & _).
    set (xb := (p, 24)).
    assert (XBc : In xb (c_blocks c0)).
    { apply (Permutation_in _ (Permutation_sym (cbk_m1 c0))). apply in_or_app; left. unfold mblk1, c0, set_m1A. cbn [c_m1 c_m2 c_m3 t3a t3b t3c fst snd].
      unfold umap_blocks. apply in_or_app; right. apply in_map_iff. exists (p, (k, v)). split; [reflexivity | exact Hinp]. }
    destruct (xb_facts H HH w s LB LBs [] m c0 xb OK RH OWN1 OWN2 XBc) as (pid & XB1 & XB2 & XB3 & XBR). unfold xb in XB1, XB2, XB3, XBR. cbn [fst snd] in XB1, XB2, XB3, XBR.
    assert (XB : fst xb <> 0 -> In xb (lbl LB)) by (intros _; exact XB3).
    assert (FV : Forall (vwin H w O_V1 xb) [(p + 20, p + 24)]).
    { apply Forall_cons; [| apply Forall_nil]. split; [cbn; lia|]. right; left. unfold xb. cbn [fst snd]. lia. }
    assert (FW : Forall (fun iv => sown H w iv \/ vwin H w O_V1 xb iv) [(p + 20, p + 24)]).
    { apply Forall_cons; [| apply Forall_nil]. right. split; [cbn; lia|]. right; left. unfold xb. cbn [fst snd]. lia. }
    assert (HO1 : O_V1 <= O_V1) by lia. assert (HO2 : O_V1 + 24 <= PARSER_SIZE) by (unfold O_V1, PARSER_SIZE; lia).

    assert (ND : List.NoDup (c_blocks c0)) by exact (cblocks_nodup H HH s LB (wa_LB0 w) LBs [] m c0 RH OWN1 OWN2).
    assert (NEr : forall q, In q (rest_m1 c0) -> q <> xb).
    { intros q Hq E. subst q.
      pose proof (Permutation_NoDup (cbk_m1 c0) ND) as ND2. apply NoDup_app_remove_r in ND2 as ND1.

      pose proof (Permutation_NoDup (cbk_m1 c0) ND) as ND3.
      assert (INm : In xb (mblk1 c0)).
      { unfold mblk1, c0, set_m1A. cbn [c_m1 c_m2 c_m3 t3a t3b t3c fst snd]. unfold umap_blocks. apply in_or_app; right. apply in_map_iff. exists (p, (k, v)). split; [reflexivity | exact Hinp]. }
      clear - ND3 INm Hq. induction (mblk1 c0) as [|y l IH]; [destruct INm|].
      cbn [app] in ND3. inversion ND3 as [|y' l' NI ND4]; subst. destruct INm as [<-|INm]; [apply NI; apply in_or_app; right; exact Hq | exact (IH ND4 INm)]. }
    assert (PEQ : forall a, wa_p w <= a < wa_p w + PARSER_SIZE -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { intros a Ha. apply MU. rewrite unsigned_lit by (unfold PARSER_SIZE in Ha; lia). cbn.
      pose proof XBR as (R0 & R16 & Rn & RI & RC & RF & RAPP).
      pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & (fp0 & Hfp0 & PF1 & PF2 & PF3 & PF4)).
      split; [unfold AFS_HDR, PARSER_SIZE in *; clear - Ha RF PF1 PF2 PF3 PF4; lia | exact I]. }
    assert (BEQ : forall A n a, In (A, n) (rest_m1 c0) -> A <= a < A + n -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { intros A n a Hin Ha.
      assert (HinC : In (A, n) (c_blocks c0)) by (apply (Permutation_in _ (Permutation_sym (cbk_m1 c0))); apply in_or_app; right; exact Hin).
      destruct (xb_facts H HH w s LB LBs [] m c0 (A, n) OK RH OWN1 OWN2 HinC) as (pid' & _ & _ & HinL & (B0 & _ & _ & _ & BC & _)). cbn [fst snd] in HinL, B0, BC.
      apply MU. rewrite unsigned_lit by lia. eapply disjoint_outside; [| split; [apply Z.le_refl | apply Z.lt_add_pos_r, Z.lt_0_1]].
      apply Forall_disjoint. eapply Forall_impl; [| exact FW]. intros iv Hiv.
      apply (vsw_apart_blk H HH w s LB m O_V1 xb iv A n a 1 OK RH XB HO1 HO2 Hiv HinL (NEr _ Hin)); lia. }
    assert (SEQ : forall A n sbs, In (A, n) (rest_m1 c0) -> Z.of_nat (length sbs) <= nsh n -> SHAD m A sbs -> SHAD m' A sbs).
    { intros A n sbs Hin Hlen SH.
      assert (HinC : In (A, n) (c_blocks c0)) by (apply (Permutation_in _ (Permutation_sym (cbk_m1 c0))); apply in_or_app; right; exact Hin).
      destruct (xb_facts H HH w s LB LBs [] m c0 (A, n) OK RH OWN1 OWN2 HinC) as (pid' & _ & _ & HinL & _). cbn [fst snd] in HinL.
      eapply SHAD_transport; [exact SH | exact MU | exact WM |].
      apply Forall_disjoint. eapply Forall_impl; [| exact FW]. intros iv Hiv.
      apply (vsw_apart_blksh H HH w s LB m O_V1 xb iv A n (sh A) _ OK RH XB HO1 HO2 Hiv HinL (NEr _ Hin)); lia. }
    pose proof (pmc_keep_m1 (wa_p w) (lbl LB) (lbl LB) m m' c0
                  (xa_m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)
                  (xa_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_v3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)
                  (proj1 (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0))
                  (fun a Ha => PEQ a ltac:(unfold O_M2, PARSER_SIZE in *; lia)) BEQ SEQ (fun b _ Hb => Hb))
      as (U2' & U3' & SH2' & SH3' & V1' & VS1' & V2' & VS2' & V3' & VS3').

    pose proof (umapx_set_val24A (lbl LB) m m' (wa_p w + O_M1) bl bc l1 l2 p k v v' U Hv' MU DM RW) as UN.
    assert (SHN : umap_sh m' 24 (bl, bc, l1 ++ (p, (k, v')) :: l2)).
    { pose proof (proj1 (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)) as SHall. unfold c0, set_m1A, pmc_sh in SHall. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3] in SHall.
      pose proof (proj1 SHall) as SB0. destruct SB0 as [SB SN].
      unfold umap_sh. cbn [t3a t3b t3c fst snd] in *.
      assert (TR : forall A n, 0 <= A -> A + n <= AAPP_HI -> 0 <= n -> addressable m A n -> addressable m' A n).
      { intros A n HA HAn Hn AD. eapply addressable_transport; [exact AD | exact MU | exact WM |].
        apply Forall_disjoint. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
        pose proof (aapp_disjoint_sh p 24 A n (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 XBR)))))) HA HAn Hn) as D. destruct D; lia. }
      split.
      - intros Hbc. pose proof (SB Hbc) as AD. pose proof AD as (A0 & _). destruct U as [_ _ _ _ _ _ _ _ Ubllo Ublhi _ _ _ _ _ _].
        apply TR; [lia | | lia | exact AD]. pose proof (proj1 (proj2 AD)). unfold AAPP_HI in *. cbn in *. lia.
      - intros q kq vq Hq. assert (Hq' : exists vq0, In (q, (kq, vq0)) (l1 ++ (p, (k, v)) :: l2)).
        { apply in_app_iff in Hq. destruct Hq as [Hq|[Hq|Hq]]; [exists vq; apply in_app_iff; left; exact Hq | injection Hq; intros; subst; exists v; exact Hinp | exists vq; apply in_app_iff; right; right; exact Hq]. }
        destruct Hq' as [vq0 Hq0]. pose proof (SN q kq vq0 Hq0) as AD. destruct (Unode q kq vq0 Hq0) as (_ & Q0 & Q47 & _).
        apply TR; [lia | unfold AAPP_HI; lia | lia | exact AD]. }
    assert (SHc' : pmc_sh m' c1).
    { unfold pmc_sh, c1, set_m1A. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3].
      split; [exact SHN|]. split; [exact SH2'|]. split; [exact SH3'|]. split; [exact VS1'|]. split; [exact VS2' | exact VS3']. }
    assert (XBw : fst xb <> 0 -> wr_at asegs m' (sh (fst xb)) (nsh (snd xb))).
    { intros _. cbn [fst snd]. destruct SHN as [_ SN']. destruct (SN' p k v' ltac:(apply in_app_iff; right; left; reflexivity)) as [_ (_ & _ & [_ W])].
      rewrite shadow_of_length in W by lia. exact W. }
    assert (CBe : c_blocks c1 = c_blocks c0) by (unfold c1, c0, set_m1A, c_blocks; cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd]; unfold umap_blocks; rewrite !map_app; reflexivity).
    pose proof (pmxa_vupd_gen H HH LINV LINV_fr w s LB LBs m mo c0 ins tbl ftbl [] 0 m' mo c1 [(p + 20, p + 24)] [] O_V1 xb OK X0 Hknn Hfk) as VG.
    rewrite app_nil_r in VG.
    apply VG; [exact MU | exact WM | exact DM | apply (ah_mpres_refl H HH) | exact MI'
             | exact (proj1 (stk_split asegs m' (wa_lo w) (wa_s1 w) (wa_sp0 w) (stk_keep m m' _ _ (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) WM DM) ltac:(pose proof (pm_geom H w OK) as G; cbn zeta in G; lia)))
             | exact FV | apply Forall_nil | exact HO1 | exact HO2 | intros _; exact XBc | exact XBw | exact CBe
             | reflexivity | reflexivity | reflexivity | reflexivity
             | exact UN | exact U2' | exact U3' | exact V1' | exact V2' | exact V3' | exact SHc' ].
  Qed.
End WM.
