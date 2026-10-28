(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition stc_ofA {HCEIL : HeapCeil} {H : asr} (w : pmwA H) (c : pmc) : stateC :=
  {| st_words := wa_words w; st_nwords := wa_n w; st_diag := wa_diag w;
     st_widx := c_widx c; st_icount := c_icount c; st_endian := c_endian c; st_flags := c_reqconv c;
     st_m1 := c_m1 c; st_m2 := c_m2 c; st_m3 := c_m3 c;
     st_v1 := (t3a (c_v1 c), t3a (c_v1 c) + OPND_SZ * t3b (c_v1 c), t3a (c_v1 c) + OPND_SZ * t3c (c_v1 c));
     st_v2 := (t3a (c_v2 c), t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c)), t3a (c_v2 c) + 4 * t3c (c_v2 c));
     st_v3 := (t3a (c_v3 c), t3a (c_v3 c) + 4 * Zlen (t3b (c_v3 c)), t3a (c_v3 c) + 4 * t3c (c_v3 c)) |}.
Definition prc_ofA {HCEIL : HeapCeil} {H : asr} (w : pmwA H) (c : pmc) : parserC :=
  {| pc_cons := wa_cons w; pc_user := wa_user w; pc_state := stc_ofA w c |}.

Lemma vob_eq : forall b n cap, vec_opnd_blocks b cap = vec_blocks (b, b + OPND_SZ * n, b + OPND_SZ * cap).
Proof.
  intros b n cap. unfold vec_opnd_blocks, vec_blocks. cbn [t3a t3b t3c fst snd].
  destruct (b =? 0); [reflexivity|]. f_equal. f_equal. lia.
Qed.
Lemma v32b_eq : forall b k cap, (if b =? 0 then [] else [(b, 4 * cap)]) = vec_blocks (b, b + 4 * k, b + 4 * cap).
Proof.
  intros b k cap. unfold vec_blocks. cbn [t3a t3b t3c fst snd].
  destruct (b =? 0); [reflexivity|]. f_equal. f_equal. lia.
Qed.

Lemma state_blocks_of {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) c,
  c_blocks c = state_blocks (stc_ofA w c) ++ c_tr c.
Proof.
  intros w c. unfold c_blocks, state_blocks, stc_ofA. cbn [st_m1 st_m2 st_m3 st_v1 st_v2 st_v3].
  rewrite (vob_eq (t3a (c_v1 c)) (t3b (c_v1 c)) (t3c (c_v1 c))).
  rewrite (v32b_eq (t3a (c_v2 c)) (Zlen (t3b (c_v2 c))) (t3c (c_v2 c))).
  rewrite (v32b_eq (t3a (c_v3 c)) (Zlen (t3b (c_v3 c))) (t3c (c_v3 c))).
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma cell8_of_fld : forall m a v, 0 <= v < 2 ^ 64 -> fld ASEGS m a 8 v -> cell8 ASEGS m a v.
Proof. intros m a v Hv F. split; [change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hv | exact F]. Qed.

Lemma cell4_of_fld : forall m a v, 0 <= v < 2 ^ 32 -> fld ASEGS m a 4 v -> cell4 ASEGS m a v.
Proof. intros m a v Hv F. split; [change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); exact Hv | exact F]. Qed.

Lemma rdn_2_join : forall segs m (x : word) b0 b1, PropExec.rdn segs m x 1 = Some [b0] -> PropExec.rdn segs m (x + 1)%bv 1 = Some [b1] ->
  PropExec.rdn segs m x 2 = Some [b0; b1].
Proof.
  intros segs m x b0 b1 R0 R1. cbn [PropExec.rdn] in *.
  destruct (match m x with Some b => Some b | None => PropExec.seg_rom segs x end) as [c0|]; [|discriminate].
  destruct (match m (x + 1)%bv with Some b => Some b | None => PropExec.seg_rom segs (x + 1)%bv end) as [c1|]; [|discriminate].
  injection R0 as ->. injection R1 as ->. reflexivity.
Qed.

Lemma cellw2_of_flds : forall m a x, 0 <= a -> a + 2 < 2 ^ 64 -> (x = 0 \/ x = 1) ->
  fld ASEGS m a 1 x -> fld ASEGS m (a + 1) 1 0 -> cellw ASEGS m a 2 x.
Proof.
  intros m a x H0 H1 Hx F1 F2. split; [change (2 ^ (8 * Z.of_N 2)) with 65536; lia|].
  unfold fld in *. change (N.to_nat 2) with 2%nat.
  replace (Z_to_bv 64 (a + 1)) with (Z_to_bv 64 a + 1)%bv in F2.
  2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. change (bv_unsigned (1%bv : bv 64)) with 1.
      rewrite (Z.mod_small a) by lia. rewrite (Z.mod_small (a + 1)) by lia. reflexivity. }
  destruct Hx as [-> | ->].
  - change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] in *.
    change (word_to_le_bytes 2 (Z_to_bv 64 0)) with [Z_to_bv 8 0; Z_to_bv 8 0]. exact (rdn_2_join _ _ _ _ _ F1 F2).
  - change (word_to_le_bytes 1 (Z_to_bv 64 1)) with [Z_to_bv 8 1] in F1.
    change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] in F2.
    change (word_to_le_bytes 2 (Z_to_bv 64 1)) with [Z_to_bv 8 1; Z_to_bv 8 0]. exact (rdn_2_join _ _ _ _ _ F1 F2).
Qed.

Lemma vraw_of_vec_opnd : forall L m v b n cap, @vec_opnd AC_A ASEGS LY_A MI_A L m v b n cap ->
  @vraw AC_A ASEGS LY_A MI_A L m v b (b + OPND_SZ * n) (b + OPND_SZ * cap).
Proof.
  intros L m v b n cap (Hv & Hv' & HD & Hn & Hb & F0 & F1 & F2). unfold OPND_SZ in *.
  assert (R : 0 <= b /\ b + 20 * cap <= 2 ^ 63) by (destruct Hb as [(-> & ->)|(B0 & _ & _ & B1 & _)]; lia).
  constructor.
  - apply cell8_of_fld; [lia | exact F0].
  - apply cell8_of_fld; [lia | exact F1].
  - apply cell8_of_fld; [lia | exact F2].
  - destruct Hb as [(-> & ->)|(B0 & _ & B2 & B3 & HIn & _)]; [left; lia | right].
    split; [lia|]. split; [replace (b + 20 * cap - b) with (20 * cap) by lia; exact HIn | lia].
Qed.

Lemma vraw_of_vec32 : forall L m v b xs cap, @vec32 AC_A ASEGS LY_A MI_A L m v b xs cap ->
  @vraw AC_A ASEGS LY_A MI_A L m v b (b + 4 * Zlen xs) (b + 4 * cap).
Proof.
  intros L m v b xs cap (Hv & Hv' & HD & Hn & Hb & F0 & F1 & F2 & FE).
  assert (R : 0 <= b /\ b + 4 * cap <= 2 ^ 63) by (destruct Hb as [(-> & ->)|(B0 & _ & _ & B1 & _)]; lia).
  constructor.
  - apply cell8_of_fld; [lia | exact F0].
  - apply cell8_of_fld; [lia | exact F1].
  - apply cell8_of_fld; [lia | exact F2].
  - destruct Hb as [(-> & ->)|(B0 & _ & B2 & B3 & HIn & _)]; [left; lia | right].
    split; [lia|]. split; [replace (b + 4 * cap - b) with (4 * cap) by lia; exact HIn | lia].
Qed.

Lemma vec_sh_of_opnd : forall m b n cap, (b <> 0 -> SHAD m b (cc_gen (OPND_SZ * cap) (OPND_SZ * n))) ->
  vec_sh m (b, b + OPND_SZ * n, b + OPND_SZ * cap).
Proof.
  intros m b n cap HS. unfold vec_sh. cbn [t3a t3b t3c fst snd]. intros Hb.
  replace (b + OPND_SZ * cap - b) with (OPND_SZ * cap) by lia. replace (b + OPND_SZ * n - b) with (OPND_SZ * n) by lia. exact (HS Hb).
Qed.
Lemma vec_sh_of_32 : forall m b (xs : list Z) cap, (b <> 0 -> SHAD m b (cc_gen (4 * cap) (4 * Zlen xs))) ->
  vec_sh m (b, b + 4 * Zlen xs, b + 4 * cap).
Proof.
  intros m b xs cap HS. unfold vec_sh. cbn [t3a t3b t3c fst snd]. intros Hb.
  replace (b + 4 * cap - b) with (4 * cap) by lia. replace (b + 4 * Zlen xs - b) with (4 * Zlen xs) by lia. exact (HS Hb).
Qed.

Lemma map_fst_lbl : forall LB, map fst (lbl LB) = map blk_addr LB.
Proof. intros LB. unfold lbl. rewrite map_map. reflexivity. Qed.

Section Bundle.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Lemma HHx : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma nodup_addrs : forall s LB m L L', as_RHEAP H s LB m -> Permutation LB (L ++ L') -> List.NoDup (map blk_addr L).
  Proof.
    intros s LB m L L' RH P.
    pose proof (ah_nodup H HHx _ _ _ RH) as ND.
    assert (NDL : List.NoDup (map blk_id L)).
    { apply (Permutation_map blk_id) in P. apply (Permutation_NoDup P) in ND. rewrite map_app in ND.
      exact (NoDup_app_remove_r _ _ ND). }
    assert (INL : forall b, In b L -> In b LB) by (intros b Hb; apply (Permutation_in _ (Permutation_sym P)); apply in_app_iff; left; exact Hb).
    clear P. induction L as [|b L IH]; cbn [map]; [constructor|].
    cbn [map] in NDL. inversion NDL as [|? ? NIb ND2]; subst.
    constructor.
    - intros Hin. apply in_map_iff in Hin as (b' & Ea & Hb').
      assert (Ne : blk_id b' <> blk_id b) by (intros E; apply NIb; rewrite <- E; apply in_map; exact Hb').
      destruct (ah_disj H HHx _ _ _ b' b RH (INL b' (or_intror Hb')) (INL b (or_introl eq_refl)) Ne) as [D|D];
        pose proof (ah_blocks H HHx _ _ _ _ RH (INL b (or_introl eq_refl))) as (_ & _ & Bn & _);
        pose proof (ah_blocks H HHx _ _ _ _ RH (INL b' (or_intror Hb'))) as (_ & _ & Bn' & _); lia.
    - apply IH; [exact ND2 | intros b0 Hb0; apply INL; right; exact Hb0].
  Qed.

  Lemma pmxa_bundle : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl spal,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl [] spal -> c_tr c = [] ->
    parser_repA LB m (wa_p w) (prc_ofA w c) /\ parser_sh m (wa_p w) (prc_ofA w c)
    /\ state_own LB (wa_LB0 w) LBs (pc_state (prc_ofA w c)) /\ lb_own LBs m /\ st_vsteps (pc_state (prc_ofA w c)).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl spal OK X Htr.
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (wk_papp H w OK) as (PA & PA0 & PA16).
    pose proof (p_range H w OK) as (PR1 & PR2).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 OWN2].
    rewrite app_nil_r in OWN1.
    pose proof (wk_n H w OK) as Hn. pose proof (wk_diag H w OK) as Hd.
    assert (Hw : 0 <= wa_words w < 2 ^ 64).
    { destruct (wk_words H w OK) as [[E0 _]|(pw & k & _ & Rg & W0 & _ & Whi & _ & _)]; lia. }
    assert (SB : state_blocks (stc_ofA w c) = c_blocks c) by (rewrite (state_blocks_of w c), Htr, app_nil_r; reflexivity).
    pose proof (xa_pdef _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as PD.
    split; [| split; [| split; [| split]]].
    - constructor; cbn [prc_ofA pc_cons pc_user pc_state].
      + exact (xa_cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
      + exact (xa_user _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
      + exact (xa_hdrfn _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
      + exact (xa_insfn _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
      + exact (xa_hunk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
      + unfold ST_OFF. constructor; cbn [stc_ofA st_words st_nwords st_diag st_widx st_icount st_endian st_flags st_m1 st_m2 st_m3 st_v1 st_v2 st_v3].
        * apply cell8_of_fld; [exact Hw | exact (xa_words _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)].
        * replace (wa_p w + 48 + 8) with (wa_p w + O_N) by (unfold O_N; lia).
          apply cell8_of_fld; [lia | exact (xa_n _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)].
        * replace (wa_p w + 48 + 16) with (wa_p w + O_DIAG) by (unfold O_DIAG; lia).
          apply cell8_of_fld; [exact Hd | exact (xa_diag _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)].
        * replace (wa_p w + 48 + 24) with (wa_p w + O_WIDX) by (unfold O_WIDX; lia).
          apply cell8_of_fld; [lia | exact (xa_widx _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)].
        * replace (wa_p w + 48 + 32) with (wa_p w + O_ICOUNT) by (unfold O_ICOUNT; lia).
          apply cell8_of_fld; [lia | exact (xa_icount _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)].
        * replace (wa_p w + 48 + 40) with (wa_p w + O_ENDIAN) by (unfold O_ENDIAN; lia).
          apply cell4_of_fld; [lia | exact (xa_endian _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)].
        * replace (wa_p w + 48 + 44) with (wa_p w + O_FLAGS) by (unfold O_FLAGS; lia).
          apply cellw2_of_flds; [unfold O_FLAGS; lia | unfold O_FLAGS, PARSER_SIZE in *; lia | exact Sc4 | exact (xa_flags _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)
                                | exact (xa_retry _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)].
        * replace (wa_p w + 48 + 48) with (wa_p w + O_M1) by (unfold O_M1; lia). exact (xa_m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
        * replace (wa_p w + 48 + 88) with (wa_p w + O_M2) by (unfold O_M2; lia). exact (xa_m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
        * replace (wa_p w + 48 + 128) with (wa_p w + O_M3) by (unfold O_M3; lia). exact (xa_m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
        * replace (wa_p w + 48 + 168) with (wa_p w + O_V1) by (unfold O_V1; lia). cbn [t3a t3b t3c fst snd].
          exact (vraw_of_vec_opnd _ _ _ _ _ _ (xa_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)).
        * replace (wa_p w + 48 + 192) with (wa_p w + O_V2) by (unfold O_V2; lia). cbn [t3a t3b t3c fst snd].
          exact (vraw_of_vec32 _ _ _ _ _ _ (xa_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)).
        * replace (wa_p w + 48 + 216) with (wa_p w + O_V3) by (unfold O_V3; lia). cbn [t3a t3b t3c fst snd].
          exact (vraw_of_vec32 _ _ _ _ _ _ (xa_v3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)).
        * intros i Hi. replace (wa_p w + 48 + i) with (wa_p w + (48 + i)) by lia. apply PD. unfold PARSER_SIZE. lia.
        * Z.div_mod_to_equations. lia.
        * rewrite SB. apply NoDup_ListNoDup.
          apply (Permutation_NoDup (Permutation_map fst OWN2)). rewrite map_fst_lbl.
          apply (nodup_addrs s LB m LBs (wa_LB0 w)). { exact (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X). }
          eapply Permutation_trans; [exact OWN1 | apply Permutation_app_comm].
      + intros i Hi. apply PD. unfold ST_OFF, PARSER_SIZE in *. lia.
      + exact PA16.
      + unfold PARSER_SIZE in *. lia.
      + exact (xa_consf _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
      + exact (xa_consd _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
      + pose proof (wk_pcons H w OK) as PC. unfold apart, PARSER_SIZE in *. lia.
    - pose proof (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as ((U1 & U2 & U3 & V1 & V2 & V3) & SHp & SHc).
      split; [exact SHp|]. split; [exact SHc|].
      unfold state_sh. cbn [prc_ofA pc_state stc_ofA st_m1 st_m2 st_m3 st_v1 st_v2 st_v3].
      split; [exact U1|]. split; [exact U2|]. split; [exact U3|].
      split; [exact (vec_sh_of_opnd m _ _ _ V1) |]. split; [exact (vec_sh_of_32 m _ _ _ V2) | exact (vec_sh_of_32 m _ _ _ V3)].
    - split; [exact OWN1 |]. change (Permutation (lbl LBs) (state_blocks (stc_ofA w c))). rewrite SB. exact OWN2.
    - exact (xa_lbown _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
    - unfold st_vsteps. cbn [prc_ofA pc_state stc_ofA st_v1 st_v2 st_v3 t3a t3b t3c fst snd].
      pose proof (xa_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (_ & _ & _ & V1 & _).
      split; [exists (t3b (c_v1 c)); unfold OPND_SZ; split; [lia | reflexivity]|].
      split; [exists (Zlen (t3b (c_v2 c))); split; [unfold Zlen; lia | reflexivity]|].
      exists (Zlen (t3b (c_v3 c))); split; [unfold Zlen; lia | reflexivity].
  Qed.
End Bundle.

Lemma state_rep_keepA : forall LB m m' st c,
  @state_rep AC_A ASEGS LY_A MI_A (lbl LB) m st c -> 0 < st -> st + 240 <= 2 ^ 47 ->
  (forall a, state_foot st c a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  @state_rep AC_A ASEGS LY_A MI_A (lbl LB) m' st c.
Proof.
  intros LB m m' st c SR Hlo Hhi HM.
  destruct SR as [W0 W1 W2 W3 W4 W5 W6 Sm1 Sm2 Sm3 Sv1 Sv2 Sv3 Sdef Sal Snd].
  assert (AGO : forall o k, 0 <= o -> o + k <= 240 -> HRepFacts.agree_on m m' (st + o) k).
  { intros o k Ho Hk i Hi. apply HM. left. lia. }
  assert (CW : forall o (wd : N) v, cellw ASEGS m (st + o) wd v -> 0 <= o -> o + Z.of_N wd <= 240 -> cellw ASEGS m' (st + o) wd v).
  { intros o wd v C Ho Hk. eapply cellw_agree; [exact C | apply AGO; lia | lia | lia]. }
  assert (UF : forall NS (V : Type) (o bl bc : Z) (ents : list (Z * (Z * V))) a,
            (forall x, In x (umap_blocks NS bl bc ents) -> In x (state_blocks c)) -> 0 <= o -> o + 40 <= 240 ->
            umap_foot NS (st + o) bl bc ents a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
  { intros NS V o bl bc ents a Hs Ho Hk Hf. apply HM.
    destruct (umap_foot_cases NS (st + o) bl bc ents a Hf) as [H0|(b & Hb & Hab)]; [left; lia | right].
    exists b. split; [apply Hs; exact Hb | exact Hab]. }
  unfold state_blocks in *.
  constructor.
  - replace st with (st + 0) by lia. apply CW; [rewrite Z.add_0_r; exact W0 | lia | cbn; lia].
  - apply CW; [exact W1 | lia | cbn; lia].
  - apply CW; [exact W2 | lia | cbn; lia].
  - apply CW; [exact W3 | lia | cbn; lia].
  - apply CW; [exact W4 | lia | cbn; lia].
  - apply CW; [exact W5 | lia | cbn; lia].
  - apply CW; [exact W6 | lia | cbn; lia].
  - eapply (umapx_agree ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (nval24_agree ASEGS) ltac:(lia));
      [exact Sm1 | intros a Hf; refine (UF _ _ _ _ _ _ _ _ _ _ Hf); [intros x Hx; rewrite !in_app_iff; tauto | lia | lia] | intros p n Hp Hl; exact Hl].
  - eapply (umapx_agree ASEGS LY_A MI_A 32 (Z * Z * Z)%type (nval32 ASEGS) (nval32_agree ASEGS) ltac:(lia));
      [exact Sm2 | intros a Hf; refine (UF _ _ _ _ _ _ _ _ _ _ Hf); [intros x Hx; rewrite !in_app_iff; tauto | lia | lia] | intros p n Hp Hl; exact Hl].
  - eapply (umapx_agree ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (nval24_agree ASEGS) ltac:(lia));
      [exact Sm3 | intros a Hf; refine (UF _ _ _ _ _ _ _ _ _ _ Hf); [intros x Hx; rewrite !in_app_iff; tauto | lia | lia] | intros p n Hp Hl; exact Hl].
  - destruct Sv1 as [B E C BLK]. constructor; [apply CW; [exact B | lia | cbn; lia] | replace (st + 168 + 8) with (st + 176) by lia; apply CW; [replace (st + 176) with (st + 168 + 8) by lia; exact E | lia | cbn; lia]
      | replace (st + 168 + 16) with (st + 184) by lia; apply CW; [replace (st + 184) with (st + 168 + 16) by lia; exact C | lia | cbn; lia] | exact BLK].
  - destruct Sv2 as [B E C BLK]. constructor; [apply CW; [exact B | lia | cbn; lia] | replace (st + 192 + 8) with (st + 200) by lia; apply CW; [replace (st + 200) with (st + 192 + 8) by lia; exact E | lia | cbn; lia]
      | replace (st + 192 + 16) with (st + 208) by lia; apply CW; [replace (st + 208) with (st + 192 + 16) by lia; exact C | lia | cbn; lia] | exact BLK].
  - destruct Sv3 as [B E C BLK]. constructor; [apply CW; [exact B | lia | cbn; lia] | replace (st + 216 + 8) with (st + 224) by lia; apply CW; [replace (st + 224) with (st + 216 + 8) by lia; exact E | lia | cbn; lia]
      | replace (st + 216 + 16) with (st + 232) by lia; apply CW; [replace (st + 232) with (st + 216 + 16) by lia; exact C | lia | cbn; lia] | exact BLK].
  - eapply defined_agree; [exact Sdef | replace st with (st + 0) by lia; apply AGO; lia].
  - exact Sal.
  - exact Snd.
Qed.

Lemma parser_repA_keep : forall LB m m' p c,
  parser_repA LB m p c -> 0 <= pc_cons c -> pc_cons c + 48 < 2 ^ 64 ->
  (forall a, parser_foot p c a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  (forall a, pc_cons c + 32 <= a < pc_cons c + 40 -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  parser_repA LB m' p c.
Proof.
  intros LB m m' p c PR Hc0 Hc1 HM HC.
  destruct PR as [Pcons Puser Phdr Pins Phunk Pst Pdef Pal Prange Pconsf Pconsm Pconsd]. unfold PARSER_SIZE in *.
  assert (AGp : forall k n, 0 <= k -> k + n <= 288 -> CRep.agree_on (zwin (p + k) (p + k + n)) m m').
  { intros k n Hk Hkn a Ha. unfold zwin in Ha. apply HM. left. unfold PARSER_SIZE. lia. }
  assert (FP : forall k (w : nat) v, 0 <= k -> k + Z.of_nat w <= 288 -> fld ASEGS m (p + k) w v -> fld ASEGS m' (p + k) w v).
  { intros k w v Hk Hkw F. eapply fld_agree; [lia | lia | exact F |]. exact (AGp k (Z.of_nat w) Hk Hkw). }
  constructor.
  - apply (FP 8 8%nat); [lia | cbn; lia | exact Pcons].
  - apply (FP 16 8%nat); [lia | cbn; lia | exact Puser].
  - apply (FP 24 8%nat); [lia | cbn; lia | exact Phdr].
  - apply (FP 32 8%nat); [lia | cbn; lia | exact Pins].
  - apply (FP 40 1%nat); [lia | cbn; lia | exact Phunk].
  - unfold ST_OFF in *. eapply state_rep_keepA; [exact Pst | lia | lia |].
    intros a Ha. apply HM. unfold parser_foot. right. unfold ST_OFF. exact Ha.
  - intros i Hi. unfold ST_OFF in Hi. rewrite (HM (p + i)) by (left; unfold PARSER_SIZE; lia). apply Pdef. exact Hi.
  - exact Pal.
  - exact Prange.
  - eapply fld_agree; [lia | cbn; lia | exact Pconsf |]. intros a Ha. unfold zwin in Ha. cbn in Ha. apply HC. lia.
  - intros i Hi. rewrite (HC (pc_cons c + 32 + i)) by lia. apply Pconsm. exact Hi.
  - exact Pconsd.
Qed.
