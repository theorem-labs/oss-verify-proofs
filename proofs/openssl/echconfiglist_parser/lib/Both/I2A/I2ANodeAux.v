(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_Xpres AsStack0.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain
  FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom FxGeomA I2Canon I2Mach I2Image I2Run I2RunA.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import I2AInv I2ANodeLib I2ANodeMem I2AShadow I2AArgs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia := Zify.zify; xlia zchecker.

Section Aux.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable IMX : fimage.
  Variable A : i2aconsts.
  Local Abbreviation K := (ka_K A).
  Local Abbreviation IM := (im_ro IMX).
  Hypothesis HK : KA_ok A = true.
  Hypothesis HHx : asan_rt_hyps_x H.
  Hypothesis HIMX : image_ok asegs IMX.
  Hypothesis HWRX : image_wr_ok IMX.
  Let HH : asan_rt_hyps H := proj1 HHx.
  (* [comment removed for export] *)
  Hypothesis HSH0 : forall m, ACONST m -> mem_inv asegs m -> sh0_facts A m.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma new_block_apart : forall s' LB m' p Ab n SP a k,
    as_RHEAP H s' ((p, Ab, n) :: LB) m' -> aclient_range H LB SP a k -> aceil <= SP -> 0 < k ->
    a + k <= Ab \/ Ab + n <= a.
  Proof.
    intros s' LB m' p Ab n SP a k HP HR CE Hk. acb.
    pose proof (ah_blocks H HH _ _ _ (p, Ab, n) HP (or_introl eq_refl)) as (R1 & R2 & R3 & R4 & R5 & R6 & R7). cbn in R1, R2, R3, R4, R5, R6, R7.
    pose proof (ah_fsb H HH _ _ _ HP) as (F1 & F2 & F3 & F4).
    destruct HR as [C|[C|[(b & Hb & C1 & C2)|[(b & Hb & C1 & C2)|[C|[C|C]]]]]].
    - right. slia.
    - specialize (C (a + k - 1) ltac:(slia)). unfold aimg_client, AIMG_TOP in *. slia.
    - pose proof (ah_nodup H HH _ _ _ HP) as ND. cbn in ND. inversion ND; subst.
      assert (NE : blk_id (p, Ab, n) <> blk_id b).
      { cbn. intros E. apply H2. apply in_map_iff. exists b. split; [symmetry; exact E| exact Hb]. }
      destruct (ah_disj H HH _ _ _ (p, Ab, n) b HP (or_introl eq_refl) (or_intror Hb) NE) as [D|D]; cbn in D; slia.
    - pose proof (ah_blocks H HH _ _ _ b HP (or_intror Hb)) as (S1 & _ & S3 & _ & S5 & _ & S7).
      destruct (aapp_disjoint_sh Ab n (blk_addr b) (blk_size b) R7 ltac:(slia) ltac:(aapp_unfold; slia) S3); slia.
    - slia.
    - assert (E : sh (as_FSB H + AFS_SIZE) = sh (as_FSB H) + nsh AFS_SIZE) by (clear - F3; unfold sh, nsh, AFS_SIZE; Z.div_mod_to_equations; slia).
      rewrite E in C.
      destruct (aapp_disjoint_sh Ab n (as_FSB H) AFS_SIZE R7 ltac:(unfold AIMG_TOP in *; slia) ltac:(aapp_unfold; unfold AFS_SIZE in *; slia) ltac:(unfold AFS_SIZE; slia)); slia.
    - destruct R7 as [[P1 P2]|[P1 P2]].
      + right. assert (T : 0 <= aceil < AAPP_HI) by (unfold AAPP_HI; clear - ACEILB; slia).
        pose proof (sh_in_shadowland aceil T). unfold ALOWSH_LO in *. slia.
      + left. unfold AHI_LO in *. slia.
  Qed.

  Lemma new_shadow_apart : forall s' LB m' p Ab n SP a k,
    as_RHEAP H s' ((p, Ab, n) :: LB) m' -> aclient_range H LB SP a k -> aceil <= SP -> 0 < k ->
    a + k <= sh Ab \/ sh Ab + nsh n <= a.
  Proof.
    intros s' LB m' p Ab n SP a k HP HR CE Hk. acb.
    pose proof (ah_blocks H HH _ _ _ (p, Ab, n) HP (or_introl eq_refl)) as (R1 & R2 & R3 & R4 & R5 & R6 & R7). cbn in R1, R2, R3, R4, R5, R6, R7.
    pose proof (ah_fsb H HH _ _ _ HP) as (F1 & F2 & F3 & F4).
    pose proof (sh_aapp_range Ab n R7 R3) as (Q1 & Q2 & Q3).
    unfold AHI_LO in Q3.
    destruct HR as [C|[C|[(b & Hb & C1 & C2)|[(b & Hb & C1 & C2)|[C|[C|C]]]]]].
    - right. slia.
    - specialize (C (a + k - 1) ltac:(slia)). left. unfold aimg_client in C. revert Q1. unfold sh, AIMG_TOP. rewrite ASHADOW_BASE_val. slia.
    - pose proof (ah_blocks H HH _ _ _ b HP (or_intror Hb)) as (S1 & _ & S3 & _ & S5 & _ & S7).
      destruct (aapp_disjoint_sh (blk_addr b) (blk_size b) Ab n S7 ltac:(slia) ltac:(aapp_unfold; slia) R3); slia.
    - (* [comment removed for export] *)
      pose proof (ah_nodup H HH _ _ _ HP) as ND. cbn in ND. inversion ND; subst.
      assert (NE : blk_id (p, Ab, n) <> blk_id b).
      { cbn. intros E. apply H2. apply in_map_iff. exists b. split; [symmetry; exact E| exact Hb]. }
      pose proof (ah_blocks H HH _ _ _ b HP (or_intror Hb)) as (_ & S2 & S3 & _).
      destruct (ah_disj H HH _ _ _ (p, Ab, n) b HP (or_introl eq_refl) (or_intror Hb) NE) as [D|D]; cbn in D;
        [right | left]; clear - D C1 C2 R2 R3 S2 S3 Hk; unfold nsh, sh in *; Z.div_mod_to_equations; slia.
    - destruct (aapp_disjoint_sh (as_FSB H) AFS_SIZE Ab n F4 ltac:(slia) ltac:(aapp_unfold; slia) R3); unfold AFS_SIZE in *; slia.
    - (* [comment removed for export] *)
      destruct R6 as [D|D]; [right | left]; clear - D C F3 R2 R3 Hk; unfold nsh, sh, AFS_SIZE in *; Z.div_mod_to_equations; slia.
    - right. slia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma regions_sep_agree : forall (rho rho'' : int -> word) M,
    regions_sep rho M -> (forall t rg, iget t M = Some rg -> rho'' t = rho t) -> regions_sep rho'' M.
  Proof.
    intros rho rho'' M Hs Hag t t' rg rg' Hne Ht Ht'. rewrite (Hag _ _ Ht), (Hag _ _ Ht'). exact (Hs t t' rg rg' Hne Ht Ht').
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma abs_part_of_ACONST : forall rho m,
    rho 0%uint63 = Z_to_bv 64 0 -> rho 3%uint63 = Z_to_bv 64 0 -> ACONST m -> mem_inv asegs m ->
    mem_part asegs IM rho m 3%uint63 (abs_region (ka_sh0lo A) (ka_sh0len A) (ka_sh0 A)).
  Proof.
    intros rho m Hr0 Hr3 HAC Hinv.
    destruct (HK_parts A HK) as (_ & _ & _ & _ & _ & _ & Hs0). unfold K_sh0_ok in Hs0. rewrite !andb_true_iff in Hs0.
    destruct Hs0 as [[Hlo Hlen] Hcells]. apply Z.eqb_eq in Hlo. apply Z.eqb_eq in Hlen. rewrite forallb_forall in Hcells.
    pose proof (HSH0 m HAC Hinv) as SF. unfold sh0_facts in SF. rewrite Forall_forall in SF.
    apply (abs_region_part IM rho Hr0 m); [exact Hr3 | rewrite Hlo; reflexivity | rewrite Hlen; reflexivity
      | rewrite Hlo; unfold sh, AIMG_LO; rewrite ASHADOW_BASE_val; slia | rewrite Hlen; unfold sh, AIMG_TOP; rewrite ASHADOW_BASE_val; slia |].
    intros a c Hin. specialize (Hcells (a, c) Hin). specialize (SF (a, c) Hin). cbn [fst snd] in Hcells, SF.
    rewrite !andb_true_iff in Hcells. destruct Hcells as [[[H8 Ha] Hb] Hcv].
    apply Uint63.eqb_spec in H8. apply (f_equal to_Z) in H8. rewrite to_Z_land7 in H8. change (to_Z 0%uint63) with 0 in H8.
    apply Z.leb_le in Ha. apply Z.leb_le in Hb. rewrite Hlo, Hlen.
    split; [exact H8|]. split; [exact Ha|]. split; [exact Hb|].
    destruct c as [[t w]| |sl]; [| discriminate Hcv |].
    - apply Uint63.eqb_spec in Hcv. subst t. exact (conj eq_refl SF).
    - exact SF.
  Qed.

  (* [comment removed for export] *)
  Lemma old_parts : forall Q st rho msF mo s LB G FF XS ms (rho'' : int -> word) m' (LBk : list block) (SPn : Z) (rm : list int) t' rg',
    I2RAX H IMX A Q st rho msF mo s LB G FF XS ms ->
    (forall t, to_Z t < to_Z (a_n st) -> rho'' t = rho t) ->
    (forall a, 0 <= a < 2 ^ 64 -> aclient_addr H LBk SPn a ->
       rview asegs m' (wa a) = rview asegs (ms_mem ms) (wa a) /\ (wview asegs (ms_mem ms) (wa a) <> None -> wview asegs m' (wa a) <> None)) ->
    SPn <= q_sp0 Q ->
    (forall g, In g G -> ~ In (g_tag g) rm -> In (g_id g, g_addr g, to_Z (g_size g)) LBk) ->
    (forall b, In b LBk -> In b LB) ->
    ACONST m' -> mem_inv asegs m' ->
    iget t' (f_mem (a_F st)) = Some rg' ->
    t' <> 0%uint63 -> t' <> 1%uint63 ->
    (forall g, In g G -> In (g_tag g) rm -> t' <> g_tag g /\ t' <> (g_tag g + 1)%uint63) ->
    mem_part asegs IM rho'' m' t' rg'.
  Proof.
    intros Q st rho msF mo s LB G FF XS ms rho'' m' LBk SPn rm t' rg' X Hag Hkeep HSP HGk HLBk HAC Hinv' Ht' Ht0 Ht1 Hrm.
    pose proof X as X'.
    destruct X' as [Xvis XRn Xcan Xfr Xfc Xrom Xr0 Xr1 Xr2 Xr3 Xag' Xn0 Xak Xmp Xheap Xrfs Xac Xst0 Xch XCH0 Xs0v Xpfo XAL XAL0
                    XG XGin XGnd XGtnd XGnew XGstk XFF XFFin XFFnd XFFtnd XTsep XFFlen XXS Xdom Xreg0 Xreg1 Xreg2 Xreg3 Xro Xinb Xkinds
                    Xcost Xcnt Xstk Xlo Xaux Xinv Xerr Xsh0 XLB0 XLB0h Xnamed XLBsub Xframe].
    destruct Xlo as (Hal & Hl2 & HB & Hsp16 & Hsp32 & HB64 & Hshi). acb. pose proof (i63_range (c_stack K)) as Hcs.
    assert (Hr0'' : rho'' 0%uint63 = Z_to_bv 64 0) by (rewrite Hag by (change (to_Z 0%uint63) with 0; slia); exact Xr0).
    assert (Hag'' : agree (a_n st) rho rho'') by (split; [exact Hr0'' | intros t Ht; exact (Hag t Ht)]).
    pose proof (XRn rho'' Hag'') as HR. pose proof (R_mem _ _ _ _ _ HR) as Hmem.
    pose proof (ah_fsb H HH _ _ _ Xheap) as (F1 & F2 & F3 & F4).
    destruct (HK_err A HK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ef3 & _ & Est16 & Est40). unfold AFS_STACK in Ef3.
    destruct (Xdom t' rg' Ht') as [-> | [-> | [-> | [-> | [Hb | [Hbs | [Hf | [Hfs | Hfl]]]]]]]]; [congruence | congruence | | | | | | |].
    - (* [comment removed for export] *)
      rewrite Xreg2 in Ht'. injection Ht' as <-.
      pose proof (stack0_bounds _ _ _ Xst0) as [SB1 SB2].
      assert (SR : sh aceil <= sh (q_sp0 Q - to_Z (c_stack K)) /\ sh (q_sp0 Q - to_Z (c_stack K)) + nsh (to_Z (c_stack K)) <= sh (q_sp0 Q) /\ sh (q_sp0 Q) <= AHI_LO).
      { split; [apply sh_mono; slia|]. split.
        - clear - Hsp32 Hcs Est16. unfold nsh, sh. Z.div_mod_to_equations. slia.
        - clear - SB2 Hshi. unfold sh, AHI_LO, AAPP_HI in *. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. slia. }
      apply (mem_part_transfer asegs IM rho'' (ms_mem ms) m' 2%uint63 _ (sh (q_sp0 Q - to_Z (c_stack K)))).
      + rewrite Hag by (change (to_Z 2%uint63) with 2; slia). exact Xr2.
      + pose proof (sh_above_image (q_sp0 Q - to_Z (c_stack K)) ltac:(slia)). unfold AIMG_TOP in *. slia.
      + unfold sh_region. cbn [rg_len]. rewrite (nsh_eq (c_stack K)) by slia. fold (nsh (to_Z (c_stack K))). unfold AHI_LO in SR. slia.
      + intros a Ha. unfold sh_region in Ha. cbn [rg_lo rg_len] in Ha. rewrite (nsh_eq (c_stack K)) in Ha by slia. change (to_Z 0%uint63) with 0 in Ha.
        fold (nsh (to_Z (c_stack K))) in Ha.
        apply Hkeep; [unfold AHI_LO in SR; pose proof (sh_above_image (q_sp0 Q - to_Z (c_stack K)) ltac:(slia)); unfold AIMG_TOP in *; slia|].
        unfold aclient_addr. do 6 right. slia.
      + intros pn sg _. discriminate.
      + exact (mem_part_of _ _ _ _ _ _ _ Hmem Xreg2).
    - (* [comment removed for export] *)
      rewrite Xreg3 in Ht'. injection Ht' as <-.
      apply abs_part_of_ACONST; [exact Hr0'' | rewrite Hag by (change (to_Z 3%uint63) with 3; slia); exact Xr3 | exact HAC | exact Hinv'].
    - (* [comment removed for export] *)
      apply in_map_iff in Hb as (g & <- & Hg).
      pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & (rgg & Hgg & Hlog & Hleng & _) & _).
      rewrite Hgg in Ht'. injection Ht' as <-.
      pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
      assert (Hnrm : ~ In (g_tag g) rm) by (intros Hin'; exact (proj1 (Hrm g Hg Hin') eq_refl)).
      apply (mem_part_transfer asegs IM rho'' (ms_mem ms) m' (g_tag g) rgg (g_addr g)).
      + rewrite Hag by slia. exact Hrg.
      + slia.
      + rewrite Hleng. slia.
      + intros a Ha. rewrite Hlog, Hleng in Ha. change (to_Z 0%uint63) with 0 in Ha.
        apply Hkeep; [slia|]. unfold aclient_addr. do 2 right. left. exists (g_id g, g_addr g, to_Z (g_size g)). split; [exact (HGk g Hg Hnrm) | cbn [blk_addr blk_size fst snd]; slia].
      + intros pn sg _. exact Ht0.
      + exact (mem_part_of _ _ _ _ _ _ _ Hmem Hgg).
    - (* [comment removed for export] *)
      apply in_map_iff in Hbs as (g & <- & Hg).
      pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & _ & Hsh).
      destruct (Hsh rg' Ht') as (-> & Hrs & Had).
      pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
      pose proof (sh_aapp_range (g_addr g) (to_Z (g_size g)) R7 R3) as (Q1 & Q2 & Q3).
      assert (Hnrm : ~ In (g_tag g) rm) by (intros Hin'; exact (proj2 (Hrm g Hg Hin') eq_refl)).
      pose proof (i63_range (g_size g)). destruct Xn0 as [_ Hn60]. pose proof (i63_range (g_tag g)).
      assert (Etg1 : to_Z (g_tag g + 1)%uint63 = to_Z (g_tag g) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; slia).
      apply (mem_part_transfer asegs IM rho'' (ms_mem ms) m' (g_tag g + 1)%uint63 _ (sh (g_addr g))).
      + rewrite Hag by (rewrite Etg1; slia). exact Hrs.
      + pose proof (sh_above_image (g_addr g) ltac:(slia)). unfold AIMG_TOP in *. slia.
      + unfold sh_region. cbn [rg_len]. rewrite (nsh_eq (g_size g)) by slia. fold (nsh (to_Z (g_size g))). unfold AHI_LO in Q3. slia.
      + intros a Ha. unfold sh_region in Ha. cbn [rg_lo rg_len] in Ha. rewrite (nsh_eq (g_size g)) in Ha by slia. change (to_Z 0%uint63) with 0 in Ha.
        fold (nsh (to_Z (g_size g))) in Ha.
        apply Hkeep; [pose proof (sh_above_image (g_addr g) ltac:(slia)); unfold AIMG_TOP, AHI_LO in *; slia|].
        unfold aclient_addr. do 3 right. left. exists (g_id g, g_addr g, to_Z (g_size g)). split; [exact (HGk g Hg Hnrm) | cbn [blk_addr blk_size fst snd]; slia].
      + intros pn sg _. intros E. apply (f_equal to_Z) in E. rewrite Etg1 in E. change (to_Z 0%uint63) with 0 in E. slia.
      + exact (mem_part_of _ _ _ _ _ _ _ Hmem Ht').
    - (* [comment removed for export] *)
      apply in_map_iff in Hf as (f & <- & Hf).
      pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hk & Htg1 & Htg2 & (rgf & Hgf & Hlof & Hlenf & _) & _).
      rewrite Hgf in Ht'. injection Ht' as <-.
      destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2 & K3 & K4 & K5) _].
      pose proof (fsz_pos (to_Z (f_k f)) ltac:(slia)).
      apply (mem_part_transfer asegs IM rho'' (ms_mem ms) m' (f_tag f) rgf (f_ff f)).
      + rewrite Hag by slia. exact Hf0.
      + unfold AFS_HDR, AIMG_TOP in *. slia.
      + rewrite Hlenf, (fsz_eq _ Hk). slia.
      + intros a Ha. rewrite Hlof, Hlenf, (fsz_eq _ Hk) in Ha. change (to_Z 0%uint63) with 0 in Ha.
        apply Hkeep; [unfold AFS_HDR, AIMG_TOP in *; slia|]. unfold aclient_addr. do 4 right. left. unfold AFS_HDR in *. slia.
      + intros pn sg _. exact Ht0.
      + exact (mem_part_of _ _ _ _ _ _ _ Hmem Hgf).
    - (* [comment removed for export] *)
      apply in_map_iff in Hfs as (f & <- & Hf).
      pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hk & Htg1 & Htg2 & _ & (rgs & Hgs & Hlos & Hlens & _) & _).
      rewrite Hgs in Ht'. injection Ht' as <-.
      destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2 & K3 & K4 & K5) _].
      pose proof (fsz_pos (to_Z (f_k f)) ltac:(slia)). pose proof (fsz_fshn (to_Z (f_k f)) ltac:(slia)) as [E1 E2].
      destruct Xn0 as [_ Hn60]. pose proof (i63_range (f_tag f)).
      assert (Etg1 : to_Z (f_tag f + 1)%uint63 = to_Z (f_tag f) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; slia).
      assert (B : AIMG_TOP <= f_ff f /\ f_ff f + AsIface.fsz (to_Z (f_k f)) <= AAPP_HI) by (aapp_unfold; unfold AFS_HDR, AFS_SIZE in *; slia).
      pose proof (sh_above_image (f_ff f) ltac:(unfold AIMG_TOP in B; slia)) as S1.
      pose proof (sh_nsh_high (f_ff f) (AsIface.fsz (to_Z (f_k f))) ltac:(unfold AIMG_TOP in B; slia) ltac:(slia) (proj2 B)) as S2.
      apply (mem_part_transfer asegs IM rho'' (ms_mem ms) m' (f_tag f + 1)%uint63 rgs (sh (f_ff f))).
      + rewrite Hag by (rewrite Etg1; slia). exact Hf1.
      + unfold AIMG_TOP in *. slia.
      + rewrite Hlens, E1. unfold AHI_LO in *. slia.
      + intros a Ha. rewrite Hlos, Hlens in Ha. change (to_Z 0%uint63) with 0 in Ha.
        apply Hkeep; [unfold AIMG_TOP, AHI_LO in *; slia|]. unfold aclient_addr. do 5 right. left.
        pose proof (sh_mono (as_FSB H) (f_ff f) ltac:(unfold AFS_HDR in *; slia)).
        assert (sh (f_ff f) + fshn (to_Z (f_k f)) <= sh (as_FSB H + AFS_SIZE)).
        { rewrite E1. pose proof (frame_al8 H _ _ _ (conj K1 (conj K2 (conj K3 (conj K4 K5))))) as A8. clear - K3 A8 E2 H0. unfold nsh, sh. Z.div_mod_to_equations. slia. }
        slia.
      + intros pn sg _. intros E. apply (f_equal to_Z) in E. rewrite Etg1 in E. change (to_Z 0%uint63) with 0 in E. slia.
      + exact (mem_part_of _ _ _ _ _ _ _ Hmem Hgs).
    - (* [comment removed for export] *)
      apply in_map_iff in Hfl as (f & <- & Hf).
      pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hk & Htg1 & Htg2 & _ & _ & Hflg & _).
      rewrite Hflg in Ht'. injection Ht' as <-.
      destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2 & K3 & K4 & K5) _].
      destruct Xn0 as [_ Hn60]. pose proof (i63_range (f_tag f)).
      assert (Etg2 : to_Z (f_tag f + 2)%uint63 = to_Z (f_tag f) + 2) by (rewrite to_Z_add_small; change (to_Z 2%uint63) with 2; slia).
      apply (mem_part_transfer asegs IM rho'' (ms_mem ms) m' (f_tag f + 2)%uint63 flag_region (f_fp f)).
      + rewrite Hag by (rewrite Etg2; slia). exact Hf2.
      + unfold AFS_FLAGS, AFS_HDR, AIMG_TOP in *. slia.
      + unfold flag_region. cbn [rg_len]. change (to_Z 1%uint63) with 1. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE in *. slia.
      + intros a Ha. unfold flag_region in Ha. cbn [rg_lo rg_len] in Ha. change (to_Z 0%uint63) with 0 in Ha. change (to_Z 1%uint63) with 1 in Ha.
        apply Hkeep; [unfold AFS_FLAGS, AFS_HDR, AFS_SIZE, AIMG_TOP in *; slia|]. unfold aclient_addr. do 4 right. left. unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *. slia.
      + intros pn sg _. intros E. apply (f_equal to_Z) in E. rewrite Etg2 in E. change (to_Z 0%uint63) with 0 in E. slia.
      + exact (mem_part_of _ _ _ _ _ _ _ Hmem Hflg).
  Qed.
End Aux.
