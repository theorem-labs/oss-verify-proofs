(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCallX ECH_Xpres AsStack0 SecLazy.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain
  FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom FxGeomA I2Canon I2Mach I2Image I2Run I2RunA.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import I2AInv I2ANodeLib I2ANodeMem I2AShadow I2AArgs I2ANodeAux I2ANodeKit I2ANodeM I2ANodeSig.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia0 := Zify.zify; xlia zchecker.
(* [comment removed for export] *)
Ltac slia :=
  repeat match goal with
         | HB : @eq bool _ _ |- _ => clear HB
         | HB : _ = Z.min _ _ |- _ => clear HB
         | HB : context [to_Z (Uint63.add _ _)] |- _ => clear HB
         | HB : context [to_Z (Uint63.sub _ _)] |- _ => clear HB
         end;
  Zify.zify; xlia zchecker.
Ltac snia := Zify.zify; xnia zchecker.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma to_Z_lsr3' : forall x : int, to_Z (x >> 3)%uint63 = to_Z x / 8.
Proof. intros x. rewrite Uint63.lsr_spec. change (2 ^ to_Z 3%uint63) with 8. reflexivity. Qed.

Lemma fsz_bounds : forall k, 0 <= k <= 6 -> 64 <= AsIface.fsz k <= 4096 /\ AsIface.fsz k mod 8 = 0 /\ AsIface.fsz k = 2 ^ (6 + k).
Proof.
  intros k Hk. unfold AsIface.fsz. pose proof (Z.pow_le_mono_r 2 0 k ltac:(slia) ltac:(slia)) as P0. pose proof (Z.pow_le_mono_r 2 k 6 ltac:(slia) ltac:(slia)) as P6.
  change (2 ^ 0) with 1 in P0. change (2 ^ 6) with 64 in P6. rewrite Z.pow_add_r by slia. change (2 ^ 6) with 64.
  split; [slia|]. split; [| reflexivity]. replace (64 * 2 ^ k) with ((8 * 2 ^ k) * 8) by slia. apply Z_mod_mult.
Qed.

Lemma Some_inj' {T} (a b : T) : Some a = Some b -> a = b.
Proof. intros E. injection E as E'. exact E'. Qed.

Section FFR.
  Variable IM : fimage.
  Variable rho : int -> word.
  Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Lemma ff_region_part : forall m t (k : int) spv flagv (ff fp : Z) (spw : word) junk1 junk2,
    rho t = wa ff -> t <> 0%uint63 -> to_Z t < 2 ^ 60 ->
    0 <= to_Z k <= 6 -> 0 < ff -> ff + AsIface.fsz (to_Z k) < 2 ^ 47 -> ff mod AsIface.fsz (to_Z k) = 0 ->
    dv rho spv = spw -> dv rho flagv = Z_to_bv 64 fp ->
    rw_cells asegs m ff [Cells.CB 24%nat junk1; C8 spw; Cells.CB (Z.to_nat (AsIface.fsz (to_Z k) - 40)) junk2; C8 (Z_to_bv 64 fp)] ->
    mem_part asegs IM rho m t (ff_region k spv flagv).
  Proof.
    intros m t k spv flagv ff fp spw junk1 junk2 Ht Ht0 Ht60 Hk Hff0 Hffhi Hal Hsp Hfl RW.
    pose proof (fsz_eq k Hk) as E1. pose proof (fsz_bounds (to_Z k) Hk) as (FB & F8 & FP). pose proof (i63_range k) as Hk63.
    set (Zk := AsIface.fsz (to_Z k)) in *.
    assert (E2 : to_Z (I2RunA.fsz k >> 3)%uint63 = Zk / 8) by (rewrite to_Z_lsr3', E1; reflexivity).
    assert (E3 : to_Z (I2RunA.fsz k >> 3 - 1)%uint63 = Zk / 8 - 1).
    { rewrite to_Z_sub_small; [rewrite E2; change (to_Z 1%uint63) with 1; reflexivity| rewrite E2; change (to_Z 1%uint63) with 1; clear - FB; Z.div_mod_to_equations; slia]. }
    assert (E6 : to_Z (6 + k)%uint63 = 6 + to_Z k) by (rewrite Uint63.add_spec; change (to_Z 6%uint63) with 6; apply Z.mod_small; change wB with (2 ^ 63); slia).
    assert (HuA : bv_unsigned (rho t) = ff) by (rewrite Ht; apply wa_unsigned; slia).
    destruct RW as [[WF BY] WR]. cbn [cells_wf cell_wf] in WF. destruct WF as (L1 & _ & L2 & _ & _).
    cbn [cells_bytes cbytes cells_size csize Nat.add] in BY, WR.
    assert (LEN : Z.of_nat (24 + (8 + (Z.to_nat (Zk - 40) + (8 + 0))))%nat = Zk) by slia. rewrite LEN in WR. destruct WR as (_ & _ & WR).
    destruct BY as (_ & BL & BY). rewrite !length_app, L1, L2, !length_le8 in BL, BY. cbn [length] in BY, BL.
    split.
    - (* [comment removed for export] *)
      unfold region_ok. cbv beta iota delta [I2RunA.ff_region rg_len rg_lo rg_align rg_clo rg_chi rg_kind]. rewrite HuA, E1, E6. fold Zk.
      change (to_Z 0%uint63) with 0. unfold clo_dflt, chi_dflt. change (to_Z 0) with 0. change (to_Z 9223372036854775807) with (2 ^ 63 - 1).
      rewrite <- FP. cbn [rkind_ok]. repeat split; first [slia| exact Hal| idtac].
    - intros pn p Hpn Hp. pose proof (i63_range pn) as Hpn63.
      set (CELLS := iset (I2RunA.fsz k >> 3 - 1)%uint63 (CV flagv) (iset 3%uint63 (CV spv) iempty)) in *.
      set (P0 := PG true PKUnk CELLS) in *.
      assert (ERG : ff_region k spv flagv = RGK 0%uint63 (I2RunA.fsz k) (6 + k)%uint63 (Some PKUnk) (iset 0%uint63 P0 iempty) clo_dflt chi_dflt RK_plain) by reflexivity.
      rewrite ERG in Hp |- *. cbv beta iota delta [FxMem.page_at rg_pages rg_dflt] in Hp. rewrite iget_iset, iget_iempty in Hp.
      cbn [rg_lo rg_len]. rewrite E1. fold Zk. change (to_Z 0%uint63) with 0.
      destruct (pn =? 0)%uint63 eqn:Epn.
      + apply Uint63.eqb_spec in Epn. subst pn. apply Some_inj' in Hp. subst p. change (to_Z 0%uint63) with 0.
        split; [| slia].
        assert (EB : blim (RGK 0%uint63 (I2RunA.fsz k) (6 + k)%uint63 (Some PKUnk) (iset 0%uint63 P0 iempty) clo_dflt chi_dflt RK_plain) 0%uint63 = Zk).
        { unfold blim. cbn [rg_len]. rewrite E1. fold Zk. change (to_Z 0%uint63) with 0. slia. }
        rewrite EB.
        assert (ADR : forall j, 0 <= j < Zk -> adr rho t (0 * 4096 + j) = wa (ff + j)).
        { intros j Hj. rewrite (adr_eq_wa rho t ff (0 * 4096 + j) Ht) by slia. f_equal; slia. }
        cbv beta delta [page_ok]. change (to_Z 0%uint63) with 0.
        split; [| split; [| split]].
        * intros _ j Hj. rewrite ADR by slia. apply WR. slia.
        * intros ci v Hci Hcell j Hj. pose proof (i63_range ci) as Hci63.
          cbv beta iota delta [FxMem.cell_at pg_cells pg_kind P0 CELLS] in Hcell. rewrite !iget_iset, iget_iempty in Hcell.
          destruct (ci =? I2RunA.fsz k >> 3 - 1)%uint63 eqn:Ec1.
          -- apply Uint63.eqb_spec in Ec1. apply (f_equal to_Z) in Ec1. rewrite E3 in Ec1. apply Some_inj' in Hcell. subst v. rewrite Hfl.
             assert (E8 : Zk = 8 * (Zk / 8)) by (clear - F8 FB; Z.div_mod_to_equations; slia).
             replace (0 * 4096 + to_Z ci * 8 + Z.of_nat j) with (0 * 4096 + (Zk - 8 + Z.of_nat j)) by slia.
             rewrite (ADR (Zk - 8 + Z.of_nat j)) by slia. rewrite wbytes8_le8.
             change (rview asegs m (wa (ff + (Zk - 8 + Z.of_nat j)))) with (mrd asegs m (wa (ff + (Zk - 8 + Z.of_nat j)))).
             replace (ff + (Zk - 8 + Z.of_nat j)) with (ff + Z.of_nat (24 + 8 + Z.to_nat (Zk - 40) + j)%nat) by slia.
             rewrite BY by slia. rewrite app_assoc, app_assoc. rewrite nth_error_app2 by (rewrite !length_app, L1, L2, length_le8; slia).
             rewrite !length_app, L1, L2, length_le8. f_equal. slia.
          -- destruct (ci =? 3)%uint63 eqn:Ec3; [| discriminate Hcell].
             apply Uint63.eqb_spec in Ec3. subst ci. apply Some_inj' in Hcell. subst v. rewrite Hsp. change (to_Z 3%uint63) with 3.
             replace (0 * 4096 + 3 * 8 + Z.of_nat j) with (0 * 4096 + (24 + Z.of_nat j)) by slia.
             rewrite (ADR (24 + Z.of_nat j)) by slia. rewrite wbytes8_le8.
             change (rview asegs m (wa (ff + (24 + Z.of_nat j)))) with (mrd asegs m (wa (ff + (24 + Z.of_nat j)))).
             replace (ff + (24 + Z.of_nat j)) with (ff + Z.of_nat (24 + j)%nat) by slia.
             rewrite BY by slia. rewrite nth_error_app2 by (rewrite L1; slia). rewrite L1. rewrite nth_error_app1 by (rewrite length_le8; slia). f_equal. slia.
        * intros ci sl Hci Hcib Hg. exfalso. cbv beta iota delta [pg_cells P0 CELLS] in Hg. rewrite !iget_iset, iget_iempty in Hg.
          destruct (ci =? I2RunA.fsz k >> 3 - 1)%uint63; [discriminate Hg|]. destruct (ci =? 3)%uint63; discriminate Hg.
        * intros ci Hci Hcut. exfalso. clear - Hcut F8 Hci. Z.div_mod_to_equations. slia.
      + destruct (t =? 0)%uint63 eqn:Et; [apply Uint63.eqb_spec in Et; congruence|].
        destruct (page_in_region _ pn) eqn:Hpir; [| discriminate Hp]. exfalso.
        destruct (page_in_region_spec _ _ Hpir) as (_ & _ & Hlt & _). cbn [rg_len] in Hlt. rewrite E1 in Hlt.
        apply Uint63.eqb_false_spec in Epn. apply Epn. apply to_Z_inj. change (to_Z 0%uint63) with 0. clear - Hlt FB Hpn63. subst Zk. snia.
  Qed.
End FFR.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section AuxK.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable IMX : fimage.
  Variable A : i2aconsts.
  Local Abbreviation K := (ka_K A).
  Local Abbreviation IM := (im_ro IMX).
  Hypothesis HK : KA_ok A = true.
  Hypothesis HHx : asan_rt_hyps_x H.
  Hypothesis HSH0 : forall m, ACONST m -> mem_inv asegs m -> sh0_facts A m.
  Let HH : asan_rt_hyps H := proj1 HHx.

  Lemma old_parts_keep : forall Q st rho msF mo s LB G FF XS ms (rho'' : int -> word) m' (KEEP : Z -> Prop) (rm : list int) t' rg',
    I2RAX H IMX A Q st rho msF mo s LB G FF XS ms ->
    (forall t, to_Z t < to_Z (a_n st) -> rho'' t = rho t) ->
    (forall a, 0 <= a < 2 ^ 64 -> KEEP a ->
       rview asegs m' (wa a) = rview asegs (ms_mem ms) (wa a) /\ (wview asegs (ms_mem ms) (wa a) <> None -> wview asegs m' (wa a) <> None)) ->
    (forall t' rg' a, iget t' (f_mem (a_F st)) = Some rg' -> t' <> 0%uint63 -> t' <> 1%uint63 -> ~ In t' rm ->
        bv_unsigned (rho t') + to_Z (rg_lo rg') <= a < bv_unsigned (rho t') + to_Z (rg_len rg') -> KEEP a) ->
    ACONST m' -> mem_inv asegs m' ->
    iget t' (f_mem (a_F st)) = Some rg' ->
    t' <> 0%uint63 -> t' <> 1%uint63 -> ~ In t' rm ->
    mem_part asegs IM rho'' m' t' rg'.
  Proof.
    intros Q st rho msF mo s LB G FF XS ms rho'' m' KEEP rm t' rg' X Hag Hkeep HKR HAC Hinv' Ht' Ht0 Ht1 Hrm.
    pose proof (fun a => HKR t' rg' a Ht' Ht0 Ht1 Hrm) as KR. cbn beta in KR. clear HKR.
    pose proof X as X'.
    destruct X' as [Xvis XRn Xcan Xfr Xfc Xrom Xr0 Xr1 Xr2 Xr3 Xag' Xn0 Xak Xmp Xheap Xrfs Xac Xst0 Xch XCH0 Xs0v Xpfo XAL XAL0
                    XG XGin XGnd XGtnd XGnew XGstk XFF XFFin XFFnd XFFtnd XTsep XFFlen XXS Xdom Xreg0 Xreg1 Xreg2 Xreg3 Xro Xinb Xkinds
                    Xcost Xcnt Xstk Xlo Xaux Xinv Xerr Xsh0 XLB0 XLB0h Xnamed XLBsub Xframe XFFstk].
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
        apply KR. rewrite Xr2. unfold sh_region. cbn [rg_lo rg_len]. rewrite (nsh_eq (c_stack K)) by slia. change (to_Z 0%uint63) with 0. fold (nsh (to_Z (c_stack K))).
        rewrite wa_unsigned by (unfold AHI_LO in SR; pose proof (sh_above_image (q_sp0 Q - to_Z (c_stack K)) ltac:(slia)); unfold AIMG_TOP in *; slia). slia.
      + intros pn sg _. discriminate.
      + exact (mem_part_of _ _ _ _ _ _ _ Hmem Xreg2).
    - (* [comment removed for export] *)
      rewrite Xreg3 in Ht'. injection Ht' as <-.
      apply (abs_part_of_ACONST IMX A HK HSH0); [exact Hr0'' | rewrite Hag by (change (to_Z 3%uint63) with 3; slia); exact Xr3 | exact HAC | exact Hinv'].
    - (* [comment removed for export] *)
      apply in_map_iff in Hb as (g & <- & Hg).
      pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & (rgg & Hgg & Hlog & Hleng & _) & _).
      rewrite Hgg in Ht'. injection Ht' as <-.
      pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
      apply (mem_part_transfer asegs IM rho'' (ms_mem ms) m' (g_tag g) rgg (g_addr g)).
      + rewrite Hag by slia. exact Hrg.
      + slia.
      + rewrite Hleng. slia.
      + intros a Ha. rewrite Hlog, Hleng in Ha. change (to_Z 0%uint63) with 0 in Ha.
        apply Hkeep; [slia|]. apply KR. rewrite Hrg, Hlog, Hleng. change (to_Z 0%uint63) with 0. rewrite wa_unsigned by slia. slia.
      + intros pn sg _. exact Ht0.
      + exact (mem_part_of _ _ _ _ _ _ _ Hmem Hgg).
    - (* [comment removed for export] *)
      apply in_map_iff in Hbs as (g & <- & Hg).
      pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & _ & Hsh).
      destruct (Hsh rg' Ht') as (-> & Hrs & Had).
      pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
      pose proof (sh_aapp_range (g_addr g) (to_Z (g_size g)) R7 R3) as (Q1 & Q2 & Q3).
      pose proof (i63_range (g_size g)). destruct Xn0 as [_ Hn60]. pose proof (i63_range (g_tag g)).
      assert (Etg1 : to_Z (g_tag g + 1)%uint63 = to_Z (g_tag g) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; slia).
      apply (mem_part_transfer asegs IM rho'' (ms_mem ms) m' (g_tag g + 1)%uint63 _ (sh (g_addr g))).
      + rewrite Hag by (rewrite Etg1; slia). exact Hrs.
      + pose proof (sh_above_image (g_addr g) ltac:(slia)). unfold AIMG_TOP in *. slia.
      + unfold sh_region. cbn [rg_len]. rewrite (nsh_eq (g_size g)) by slia. fold (nsh (to_Z (g_size g))). unfold AHI_LO in Q3. slia.
      + intros a Ha. unfold sh_region in Ha. cbn [rg_lo rg_len] in Ha. rewrite (nsh_eq (g_size g)) in Ha by slia. change (to_Z 0%uint63) with 0 in Ha.
        fold (nsh (to_Z (g_size g))) in Ha.
        apply Hkeep; [pose proof (sh_above_image (g_addr g) ltac:(slia)); unfold AIMG_TOP, AHI_LO in *; slia|].
        apply KR. rewrite Hrs. unfold sh_region. cbn [rg_lo rg_len]. rewrite (nsh_eq (g_size g)) by slia. change (to_Z 0%uint63) with 0. fold (nsh (to_Z (g_size g))).
        rewrite wa_unsigned by (pose proof (sh_above_image (g_addr g) ltac:(slia)); unfold AIMG_TOP, AHI_LO in *; slia). slia.
      + intros pn sg _. intros E. apply (f_equal to_Z) in E. rewrite Etg1 in E. change (to_Z 0%uint63) with 0 in E. slia.
      + exact (mem_part_of _ _ _ _ _ _ _ Hmem Ht').
    - (* [comment removed for export] *)
      apply in_map_iff in Hf as (f & <- & Hf).
      pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hk & Htg1 & Htg2 & (rgf & Hgf & Hlof & Hlenf & _) & _).
      rewrite Hgf in Ht'. injection Ht' as <-.
      destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2' & K3 & K4 & K5) _].
      pose proof (fsz_pos (to_Z (f_k f)) ltac:(slia)).
      apply (mem_part_transfer asegs IM rho'' (ms_mem ms) m' (f_tag f) rgf (f_ff f)).
      + rewrite Hag by slia. exact Hf0.
      + unfold AFS_HDR, AIMG_TOP in *. slia.
      + rewrite Hlenf, (fsz_eq _ Hk). slia.
      + intros a Ha. rewrite Hlof, Hlenf, (fsz_eq _ Hk) in Ha. change (to_Z 0%uint63) with 0 in Ha.
        apply Hkeep; [unfold AFS_HDR, AIMG_TOP in *; slia|]. apply KR. rewrite Hf0, Hlof, Hlenf, (fsz_eq _ Hk). change (to_Z 0%uint63) with 0.
        rewrite wa_unsigned by (unfold AFS_HDR, AIMG_TOP in *; slia). slia.
      + intros pn sg _. exact Ht0.
      + exact (mem_part_of _ _ _ _ _ _ _ Hmem Hgf).
    - (* [comment removed for export] *)
      apply in_map_iff in Hfs as (f & <- & Hf).
      pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hk & Htg1 & Htg2 & _ & (rgs & Hgs & Hlos & Hlens & _) & _).
      rewrite Hgs in Ht'. injection Ht' as <-.
      destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2' & K3 & K4 & K5) _].
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
        apply Hkeep; [unfold AIMG_TOP, AHI_LO in *; slia|]. apply KR. rewrite Hf1, Hlos, Hlens. change (to_Z 0%uint63) with 0.
        rewrite wa_unsigned by (unfold AIMG_TOP, AHI_LO in *; slia). slia.
      + intros pn sg _. intros E. apply (f_equal to_Z) in E. rewrite Etg1 in E. change (to_Z 0%uint63) with 0 in E. slia.
      + exact (mem_part_of _ _ _ _ _ _ _ Hmem Hgs).
    - (* [comment removed for export] *)
      apply in_map_iff in Hfl as (f & <- & Hf).
      pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hk & Htg1 & Htg2 & _ & _ & Hflg & _).
      rewrite Hflg in Ht'. injection Ht' as <-.
      destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2' & K3 & K4 & K5) _].
      destruct Xn0 as [_ Hn60]. pose proof (i63_range (f_tag f)).
      assert (Etg2 : to_Z (f_tag f + 2)%uint63 = to_Z (f_tag f) + 2) by (rewrite to_Z_add_small; change (to_Z 2%uint63) with 2; slia).
      apply (mem_part_transfer asegs IM rho'' (ms_mem ms) m' (f_tag f + 2)%uint63 flag_region (f_fp f)).
      + rewrite Hag by (rewrite Etg2; slia). exact Hf2.
      + unfold AFS_FLAGS, AFS_HDR, AIMG_TOP in *. slia.
      + unfold flag_region. cbn [rg_len]. change (to_Z 1%uint63) with 1. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE in *. slia.
      + intros a Ha. unfold flag_region in Ha. cbn [rg_lo rg_len] in Ha. change (to_Z 0%uint63) with 0 in Ha. change (to_Z 1%uint63) with 1 in Ha.
        apply Hkeep; [unfold AFS_FLAGS, AFS_HDR, AFS_SIZE, AIMG_TOP in *; slia|]. apply KR. rewrite Hf2. unfold flag_region. cbn [rg_lo rg_len]. change (to_Z 0%uint63) with 0. change (to_Z 1%uint63) with 1.
        rewrite wa_unsigned by (unfold AFS_FLAGS, AFS_HDR, AFS_SIZE, AIMG_TOP in *; slia). slia.
      + intros pn sg _. intros E. apply (f_equal to_Z) in E. rewrite Etg2 in E. change (to_Z 0%uint63) with 0 in E. slia.
      + exact (mem_part_of _ _ _ _ _ _ _ Hmem Hflg).
  Qed.

  (* [comment removed for export] *)
  Lemma mem_part_transfer0 : forall (rho : int -> word) m m' rg,
    rho 0%uint63 = Z_to_bv 64 0 -> to_Z (rg_len rg) < 2 ^ 64 ->
    (forall a, to_Z (rg_lo rg) <= a < to_Z (rg_len rg) ->
        rview asegs m' (wa a) = rview asegs m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None)) ->
    mem_part asegs IM rho m 0%uint63 rg -> mem_part asegs IM rho m' 0%uint63 rg.
  Proof.
    intros rho m m' rg Hr0 Hlen Hm [Hro Hpages]. split; [exact Hro|].
    intros pn p Hpn Hp. destruct (Hpages pn p Hpn Hp) as (Hok & Hlo & Hlt).
    split; [|split; [exact Hlo | exact Hlt]].
    pose proof (i63_range pn). pose proof (i63_range (rg_lo rg)). pose proof (i63_range (rg_len rg)).
    pose proof (clim8_le rg pn Hlt) as Hcl.
    eapply page_ok_transfer; [|exact Hok].
    intros j Hj. assert (E0 : rho 0%uint63 = wa 0) by (rewrite Hr0; reflexivity).
    rewrite (adr_eq_wa rho 0%uint63 0 (to_Z pn * 4096 + j) E0) by slia.
    exact (Hm (0 + (to_Z pn * 4096 + j)) ltac:(slia)).
  Qed.

  (* [comment removed for export] *)
  Lemma rview_overlay_high : forall m a, AIMG_TOP <= a < 2 ^ 64 -> rview asegs m (wa a) = m (wa a).
  Proof.
    intros m a Ha. unfold rview. destruct (m (wa a)); [reflexivity|]. unfold memory_read.
    rewrite wa_unsigned by (unfold AIMG_TOP in Ha; slia). rewrite asegs_find_segment_none_high by (unfold AIMG_TOP in Ha; slia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma flag_byte_live : forall Q st rho msF mo s LB G FF XS ms f,
    I2RAX H IMX A Q st rho msF mo s LB G FF XS ms -> In f FF ->
    exists b, ms_mem ms (wa (f_fp f)) = Some b.
  Proof.
    intros Q st rho msF mo s LB G FF XS ms f X Hf.
    pose proof (r_Rn _ _ _ _ _ _ _ _ _ _ _ _ _ _ X rho (agree_refl _ rho (r_rho0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X))) as HR.
    pose proof (R_mem _ _ _ _ _ HR) as [Hregs _].
    pose proof (proj1 (Forall_forall _ _) (r_FFin _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) f Hf) as (_ & _ & Hf2 & _ & _ & _ & _ & _ & Hflg & _).
    destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2 & K3 & K4 & K5) (F1 & F2 & F3 & F4)]. acb.
    assert (FPR : AIMG_TOP <= f_fp f < 2 ^ 64) by (clear - K5 F1 F2 ACEILB; unfold AFS_FLAGS, AFS_HDR, AFS_SIZE, AIMG_TOP in *; slia).
    destruct (Hregs _ _ Hflg) as [_ PGS].
    set (P0 := PG false PKUnk (iset 0%uint63 (CB (SL (SK 1) SU SU SU SU SU SU SU)) iempty)).
    assert (PA : page_at IM flag_region (f_tag f + 2)%uint63 0%uint63 = Some P0).
    { cbv beta iota delta [FxMem.page_at flag_region rg_pages]. rewrite iget_iset, Uint63.eqb_refl. reflexivity. }
    destruct (PGS 0%uint63 P0 ltac:(change (to_Z 0%uint63) with 0; slia) PA) as ((_ & _ & SL' & _) & _).
    assert (EB : blim flag_region 0%uint63 = 1) by reflexivity. rewrite EB in SL'.
    pose proof (SL' 0%uint63 (SL (SK 1%uint63) SU SU SU SU SU SU SU) ltac:(change (to_Z 0%uint63) with 0; slia) ltac:(change (to_Z 0%uint63) with 0; slia)
                  ltac:(cbv beta iota delta [P0 pg_cells]; rewrite iget_iset, Uint63.eqb_refl; reflexivity) 0%uint63 ltac:(change (to_Z 0%uint63) with 0; slia)) as [SK' _].
    specialize (SK' ltac:(change (to_Z 0%uint63) with 0; slia)). rewrite sget_SL in SK' by (change (to_Z 0%uint63) with 0; slia). change (to_Z 0%uint63) with 0 in SK'.
    cbn [Z.to_nat nth] in SK'. cbv beta iota delta [FxRel.slot_ok] in SK'.
    rewrite (adr_eq_wa rho (f_tag f + 2)%uint63 (f_fp f) (0 * 4096 + 0 * 8 + 0) Hf2) in SK' by (clear - FPR; unfold AIMG_TOP in FPR; slia).
    replace (f_fp f + (0 * 4096 + 0 * 8 + 0)) with (f_fp f) in SK' by (clear; slia). rewrite rview_overlay_high in SK' by exact FPR.
    exists (Z_to_bv 8 (to_Z 1%uint63)). exact SK'.
  Qed.
End AuxK.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SB.
  Variable segs : list Segment.
  Variable IM : fimage.
  Variable rho : int -> word.
  Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.
  Variable code : itrie finstr.
  Hypothesis Hcode : code_ok segs code.

  (* [comment removed for export] *)
  Lemma sb_flag_step : forall F ms sz rs1 rs2 imm ft fp,
    R segs IM rho F ms ->
    iget (f_pc F) code = Some (FStore sz rs1 rs2 imm) ->
    fv_alu (f_mem F) ALU_ADD (FxState.rget F rs1) (FV 0 imm) = Some (FV ft (W64 0 0)) ->
    conc63 (FxState.rget F rs2) = Some 0%uint63 -> msz_int sz = 1%uint63 ->
    rho ft = wa fp -> 0 <= fp < 2 ^ 64 -> to_Z ft < 2 ^ 60 ->
    wview segs (ms_mem ms) (wa fp) <> None ->
    step segs ms = MachineOk (ms_of ms (inval_resv (wa fp) (with_pc (Z_to_bv 64 (to_Z (f_pc F + 4)%uint63)) (core_of ms))) (write_to_mem (ms_mem ms) (wa fp) [b8 0]))
    /\ to_Z (f_pc F) < pc_bound - 4.
  Proof.
    intros F ms sz rs1 rs2 imm ft fp HR Hi Ea Hz Hsz Hft Hfp Hft60 Hwr.
    destruct (code_entry segs IM rho code Hcode F ms _ HR Hi) as (Hpc & w & Hf & [[He E]|(He & i & Hd & Hc)]); [discriminate E|].
    split; [| exact Hpc].
    rewrite (step_decode segs ms w i Hf He Hd).
    pose proof (R_regs_ok segs IM rho F ms HR) as HM. pose proof (R_pc _ _ _ _ _ HR) as Epc. pose proof (pc_plus4 _ Hpc) as Enpc.
    pose proof (R_regs _ _ _ _ _ HR) as Hregs.
    destruct i; cbn [compile] in Hc; repeat lazymatch type of Hc with (match ?x with _ => _ end) = _ => destruct x end; try discriminate Hc.
    apply some_inj in Hc. injection Hc as Esz Ers1 Ers2 Eimm. subst sz rs1 rs2 imm.
    apply (fv_alu_sound rho Hrho0 _ _ _ _ _ HM) in Ea. rewrite (dv_conc rho Hrho0), wbv_w_of_bv, <- Hregs in Ea.
    rewrite (dv_tag_zero rho ft Hft60) in Ea. rewrite Hft in Ea. unfold alu64, alu in Ea.
    pose proof (conc63_inv _ _ Hz) as Ez. lazymatch type of Ez with FxState.rget F (ireg ?r) = _ => pose proof (Hregs r) as Hv end. rewrite Ez, (dv_conc63 rho _ Hrho0) in Hv. change (to_Z 0%uint63) with 0 in Hv.
    unfold exec. cbn [core_of c_pc]. rewrite Epc, Enpc. cbn zeta. rewrite <- Ea. rewrite Hv.
    lazymatch type of Hsz with msz_int ?q = _ => destruct q; try discriminate Hsz end.
    rewrite (interp_store_val segs SZ1 (wa fp) (Z_to_bv 64 0) _ (ms_mem ms)).
    2:{ apply store_ok_intro. intros j Hj. destruct j as [|j]; [| cbn in Hj; exfalso; slia]. rewrite aoff_0. exact Hwr. }
    rewrite interp_done. reflexivity.
  Qed.
End SB.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint gfdel (t : int) (FF : list gframe) : list gframe :=
  match FF with [] => [] | f :: r => if (f_tag f =? t)%uint63 then r else f :: gfdel t r end.

Lemma ff_remove_map : forall t FF, ff_remove t (map (fun f => (f_tag f, f_k f)) FF) = map (fun f => (f_tag f, f_k f)) (gfdel t FF).
Proof. induction FF as [|f FF IH]; intros; [reflexivity|]. cbn [map ff_remove gfdel fst]. destruct (f_tag f =? t)%uint63; [reflexivity|]. cbn [map]. rewrite IH. reflexivity. Qed.

Lemma gfdel_In : forall t FF f, In f (gfdel t FF) -> In f FF.
Proof. induction FF as [|g FF IH]; intros f Hf; [exact Hf|]. cbn [gfdel] in Hf. destruct (f_tag g =? t)%uint63; [right; exact Hf|]. destruct Hf as [<-|Hf]; [left; reflexivity| right; exact (IH _ Hf)]. Qed.

Lemma gfdel_NoDup_map : forall {B} (h : gframe -> B) t FF, List.NoDup (map h FF) -> List.NoDup (map h (gfdel t FF)).
Proof.
  induction FF as [|g FF IH]; intros ND; [constructor|]. cbn [gfdel]. cbn [map] in ND. apply NoDup_cons_iff in ND as [NI ND].
  destruct (f_tag g =? t)%uint63; [assumption|]. cbn [map]. constructor; [| exact (IH ND)].
  intros Hin. apply NI. apply in_map_iff in Hin as (f & <- & Hf). apply in_map. exact (gfdel_In _ _ _ Hf).
Qed.

Lemma gfdel_NoDup_app : forall (h : gframe -> Z) t FF (l : list Z), List.NoDup (map h FF ++ l) -> List.NoDup (map h (gfdel t FF) ++ l).
Proof.
  induction FF as [|g FF IH]; intros l ND; [exact ND|]. cbn [gfdel]. cbn [map app] in ND. apply NoDup_cons_iff in ND as [NI ND].
  destruct (f_tag g =? t)%uint63; [assumption|]. cbn [map app]. constructor; [| exact (IH _ ND)].
  intros Hin. apply NI. apply in_app_iff in Hin. apply in_app_iff. destruct Hin as [Hin|Hin]; [left| right; exact Hin].
  apply in_map_iff in Hin as (f & <- & Hf). apply in_map. exact (gfdel_In _ _ _ Hf).
Qed.

Lemma gfdel_length : forall t FF, In t (map f_tag FF) -> (length (gfdel t FF) + 1 = length FF)%nat.
Proof.
  induction FF as [|g FF IH]; intros Hin; [destruct Hin|]. cbn [gfdel]. destruct (f_tag g =? t)%uint63 eqn:E; [cbn; lia|].
  cbn [length]. cbn [map] in Hin. destruct Hin as [Hin|Hin]; [apply Uint63.eqb_false_spec in E; congruence|]. rewrite <- (IH Hin). reflexivity.
Qed.

Lemma gfdel_keep : forall t FF f, In f FF -> f_tag f <> t -> In f (gfdel t FF).
Proof.
  induction FF as [|g FF IH]; intros f Hf Hne; [destruct Hf|]. cbn [gfdel]. destruct (f_tag g =? t)%uint63 eqn:E.
  - destruct Hf as [<-|Hf]; [apply Uint63.eqb_spec in E; congruence| exact Hf].
  - destruct Hf as [<-|Hf]; [left; reflexivity| right; exact (IH _ Hf Hne)].
Qed.

(* [comment removed for export] *)
Lemma gfdel_not_self : forall FF f0 f, List.NoDup (map f_tag FF) -> In f0 FF -> In f (gfdel (f_tag f0) FF) -> f <> f0.
Proof.
  induction FF as [|g FF IH]; intros f0 f ND I0 Hf; [destruct I0|]. cbn [map] in ND. apply NoDup_cons_iff in ND as [NI ND]. cbn [gfdel] in Hf.
  destruct (f_tag g =? f_tag f0)%uint63 eqn:E.
  - apply Uint63.eqb_spec in E. intros ->. destruct I0 as [<-|I0]; [apply NI; apply in_map; exact Hf| apply NI; rewrite E; apply in_map; exact I0].
  - apply Uint63.eqb_false_spec in E. destruct I0 as [<-|I0]; [congruence|]. destruct Hf as [<-|Hf]; [intros ->; congruence| exact (IH _ _ ND I0 Hf)].
Qed.

(* [comment removed for export] *)
Lemma lf_remove_gfdel : forall FF f0 (LF0 : list fframe), List.NoDup (map f_tag FF) -> List.NoDup (map f_ff FF ++ map ff_addr LF0) -> In f0 FF ->
  lf_remove (f_ff f0) (map ff_of FF ++ LF0) = map ff_of (gfdel (f_tag f0) FF) ++ LF0.
Proof.
  induction FF as [|g FF IH]; intros f0 LF0 NDT NDA I0; [destruct I0|]. cbn [map app lf_remove gfdel]. cbn [ff_addr ff_of fst snd].
  cbn [map] in NDT. apply NoDup_cons_iff in NDT as [NT NDT]. cbn [map app] in NDA. apply NoDup_cons_iff in NDA as [NA NDA].
  destruct (f_tag g =? f_tag f0)%uint63 eqn:E.
  - apply Uint63.eqb_spec in E. assert (Eg : g = f0). { destruct I0 as [<-|I0]; [reflexivity|]. exfalso. apply NT. rewrite E. apply in_map. exact I0. }
    subst g. rewrite Z.eqb_refl. reflexivity.
  - apply Uint63.eqb_false_spec in E. destruct I0 as [<-|I0]; [congruence|].
    assert (NE : f_ff g <> f_ff f0). { intros EQ. apply NA. apply in_app_iff. left. rewrite EQ. apply in_map. exact I0. }
    rewrite (proj2 (Z.eqb_neq _ _) NE). cbn [map app]. rewrite (IH _ _ NDT NDA I0). reflexivity.
Qed.

(* [comment removed for export] *)
Section NodeS.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable IMX : fimage.
  Variable A : i2aconsts.
  Local Abbreviation K := (ka_K A).
  Local Abbreviation IM := (im_ro IMX).
  Local Abbreviation RO := (ro_of (ka_K A)).
  Hypothesis HK : KA_ok A = true.
  Hypothesis HHx : asan_rt_hyps_x H.
  Hypothesis HIMX : image_ok asegs IMX.
  Hypothesis HWRX : image_wr_ok IMX.
  Hypothesis HSH0 : forall m, ACONST m -> mem_inv asegs m -> sh0_facts A m.
  Let HH : asan_rt_hyps H := proj1 HHx.

  Ltac hk_err :=
    let E1 := fresh "Eerr" in let E2 := fresh "Eerr8" in let E3 := fresh "Ebi" in let E4 := fresh "Ewin" in let E5 := fresh "Eac" in
    let E6 := fresh "Etp" in let E7 := fresh "Em1" in let E8 := fresh "Em2" in let E9 := fresh "Em3" in let E10 := fresh "Em4" in
    let E11 := fresh "Ef1" in let E12 := fresh "Ef2" in let E13 := fresh "Ef3" in let E14 := fresh "Ef4" in
    let E15 := fresh "Est16" in let E16 := fresh "Est40" in
    destruct (HK_err A HK) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16);
    pose proof (i63_range (c_errbi K)); pose proof (i63_range (c_errcell K)); pose proof (i63_range (c_stack K));
    pose proof (i63_range (c_mstack K)).

  (* [comment removed for export] *)
  Lemma fsm_class_ok : forall pc k, fsm_class pc (ka_fsm A) = Some k ->
    (to_Z pc = AFS_MALLOC_0 /\ k = 0%uint63) \/ (to_Z pc = AFS_MALLOC_1 /\ k = 1%uint63)
    \/ (to_Z pc = AFS_MALLOC_2 /\ k = 2%uint63) \/ (to_Z pc = AFS_MALLOC_4 /\ k = 4%uint63).
  Proof.
    intros pc k Hc. destruct (HK_parts A HK) as (_ & _ & Hpcs & _). unfold K_pcs_ok in Hpcs. rewrite !andb_true_iff in Hpcs.
    destruct Hpcs as [[[[_ Hf] _] _] _]. rewrite forallb_forall in Hf.
    revert Hc. induction (ka_fsm A) as [|[p k'] l IH]; intros Hc; [discriminate Hc|]. cbn [fsm_class] in Hc.
    destruct (p =? pc)%uint63 eqn:E.
    - apply Uint63.eqb_spec in E. subst p. injection Hc as ->. specialize (Hf (pc, k) (or_introl eq_refl)). cbn [fst snd] in Hf.
      rewrite !orb_true_iff, !andb_true_iff in Hf.
      destruct Hf as [[[[E1 E2]|[E1 E2]]|[E1 E2]]|[E1 E2]]; apply Z.eqb_eq in E1; apply Uint63.eqb_spec in E2; subst k; [left| right; left| right; right; left| right; right; right]; split; assumption || reflexivity.
    - apply IH; [intros x Hx; apply Hf; right; exact Hx| exact Hc].
  Qed.

  Lemma fsm_stmt : forall pc k, fsm_class pc (ka_fsm A) = Some k -> stack_malloc_stmt H (to_Z k) (to_Z pc) /\ 0 <= to_Z k <= 6.
  Proof.
    intros pc k Hc. pose proof HHx as (HH' & _ & S0 & S2 & _).
    destruct (fsm_class_ok pc k Hc) as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]].
    - split; [exact S0| change (to_Z 0%uint63) with 0; lia].
    - split; [exact (ah_fs1 H HH)| change (to_Z 1%uint63) with 1; lia].
    - split; [exact S2| change (to_Z 2%uint63) with 2; lia].
    - split; [exact (ah_fs4 H HH)| change (to_Z 4%uint63) with 4; lia].
  Qed.

  Lemma fresh_frame_sub : forall LF LF' k ff fp, fresh_frame H LF k ff fp -> (forall f, In f LF' -> In f LF) -> fresh_frame H LF' k ff fp.
  Proof. intros LF LF' k ff fp (R & F & D) SUB. split; [exact R|]. split; [exact F|]. intros f Hf. exact (D f (SUB f Hf)). Qed.

  Lemma map_ff_addr_of : forall FF : list gframe, map ff_addr (map ff_of FF) = map f_ff FF.
  Proof. induction FF as [|f FF IH]; [reflexivity|]. cbn [map]. rewrite IH. reflexivity. Qed.

  Theorem anode_fsmalloc_sound : anode_fsmalloc_sig H IMX A.
  Proof.
    unfold anode_fsmalloc_sig, anode_concl.
    intros Q st st' rho msF mo k Hnode Hcls Hc0 (s & LB & G & FF & XS & ms & X).
    (* [comment removed for export] *)
    unfold anode_fsmalloc in Hnode.
    destruct (call_okn K (ka_fstack A) st) as [[off l]|] eqn:Hco; [|discriminate].
    match type of Hnode with (if ?b then _ else _) = _ => destruct b eqn:Hguard; [|discriminate] end.
    match type of Hnode with match ?d with _ => _ end = _ => destruct d as [M2|] eqn:HM2; [|discriminate] end.
    injection Hnode as <-.
    destruct (call_okn_inv A _ _ _ _ Hco) as (Hsp & Hlk & Htp & Hrv & Hep & Hn59 & Hn2).
    destruct (call_sp_n_inv A _ _ _ Hsp) as (Esp2 & Hoff1 & Hoff2 & Hoff16).
    destruct (call_link_inv _ _ Hlk) as (Era & Hl2 & Hl62).
    pose proof (tp_ok_inv _ _ Htp) as Etp. pose proof (resv_none_inv _ Hrv) as Eresv.
    rewrite andb_true_iff in Hguard. destruct Hguard as [Hk6 Hffmax]. apply Uint63.ltb_spec in Hffmax.
    destruct (fsm_stmt _ _ Hcls) as [STM HkZ]. unfold stack_malloc_stmt in STM.
    (* [comment removed for export] *)
    pose proof X as X'.
    destruct X' as [Xvis XRn Xcan Xfr Xfc Xrom Xr0 Xr1 Xr2 Xr3 Xag Xn0 Xak Xmp Xheap Xrfs Xac Xst0 Xch XCH0 Xs0v Xpfo XAL XAL0
                    XG XGin XGnd XGtnd XGnew XGstk XFF XFFin XFFnd XFFtnd XTsep XFFlen XXS Xdom Xreg0 Xreg1 Xreg2 Xreg3 Xro Xinb Xkinds
                    Xcost Xcnt Xstk Xlo Xaux Xinv Xerr Xsh0 XLB0 XLB0h Xnamed XLBsub Xframe XFFstk].
    set (F := a_F st) in *. set (t := a_n st) in *.
    pose proof (i63_range t) as Ht. change (to_Z two59) with (2 ^ 59) in Hn59.
    assert (Et1 : to_Z (t + 1)%uint63 = to_Z t + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; slia).
    assert (Et2 : to_Z (t + 2)%uint63 = to_Z t + 2) by (rewrite to_Z_add_small; change (to_Z 2%uint63) with 2; slia).
    assert (Et17 : to_Z (t + 17)%uint63 = to_Z t + 17) by (rewrite to_Z_add_small; change (to_Z 17%uint63) with 17; slia).
    (* [comment removed for export] *)
    unfold drop_stack in HM2. rewrite !iget_iset in HM2.
    assert (N1 : forall x c, to_Z c < 4 -> 4 <= to_Z x -> (c =? x)%uint63 = false).
    { intros x c Hc Hx. destruct (c =? x)%uint63 eqn:E; [|reflexivity]. apply Uint63.eqb_spec in E. subst c. exfalso. clear - Hc Hx. slia. }
    destruct Xn0 as [Xn0a Xn0b].
    assert (N1t := N1 t 1%uint63 ltac:(change (to_Z 1%uint63) with 1; slia) ltac:(slia)).
    assert (N0t := N1 t 0%uint63 ltac:(change (to_Z 0%uint63) with 0; slia) ltac:(slia)).
    assert (N2t := N1 t 2%uint63 ltac:(change (to_Z 2%uint63) with 2; slia) ltac:(slia)).
    assert (N3t := N1 t 3%uint63 ltac:(change (to_Z 3%uint63) with 3; slia) ltac:(slia)).
    assert (N1s := N1 (t + 1)%uint63 1%uint63 ltac:(change (to_Z 1%uint63) with 1; slia) ltac:(rewrite Et1; slia)).
    assert (N0s := N1 (t + 1)%uint63 0%uint63 ltac:(change (to_Z 0%uint63) with 0; slia) ltac:(rewrite Et1; slia)).
    assert (N2s := N1 (t + 1)%uint63 2%uint63 ltac:(change (to_Z 2%uint63) with 2; slia) ltac:(rewrite Et1; slia)).
    assert (N3s := N1 (t + 1)%uint63 3%uint63 ltac:(change (to_Z 3%uint63) with 3; slia) ltac:(rewrite Et1; slia)).
    assert (N1f := N1 (t + 2)%uint63 1%uint63 ltac:(change (to_Z 1%uint63) with 1; slia) ltac:(rewrite Et2; slia)).
    assert (N0f := N1 (t + 2)%uint63 0%uint63 ltac:(change (to_Z 0%uint63) with 0; slia) ltac:(rewrite Et2; slia)).
    assert (N2f := N1 (t + 2)%uint63 2%uint63 ltac:(change (to_Z 2%uint63) with 2; slia) ltac:(rewrite Et2; slia)).
    assert (N3f := N1 (t + 2)%uint63 3%uint63 ltac:(change (to_Z 3%uint63) with 3; slia) ltac:(rewrite Et2; slia)).
    rewrite N1s, N1f, N1t in HM2.
    destruct (iget 1%uint63 (f_mem F)) as [rg1|] eqn:Hrg1; [|discriminate HM2]. injection HM2 as <-.
    assert (Hag : agree t rho rho) by (apply agree_refl; exact Xr0).
    pose proof (XRn rho Hag) as HR.
    pose proof (canonR_R asegs IM rho F ms HR Xcan) as Ems.
    rewrite Xfr, Xfc, Xrom, Eresv in Ems. cbn [option_map] in Ems.
    assert (Erv : forall k, rv rho F k = dv rho (FxState.rget F (of_Z k))) by (intros; reflexivity).
    hk_err. acb. unfold AFS_STACK, AINTRIN_STACK, AMALLOC_STACK, AREALLOC_STACK, AFREE_STACK in *. pose proof (i63_range (c_stack K)) as Hcs.
    destruct Xlo as (Hhl & Hlsp & HspB & Hsp16 & Hsp32 & HB64 & Hshi). pose proof (i63_range off) as Hoff.
    assert (Esp : rv rho F 2 = adr rho 1%uint63 (to_Z off)).
    { rewrite Erv. change (of_Z 2) with 2%uint63. fold F in Esp2. rewrite Esp2. apply dv_adr; [cbn; slia | reflexivity]. }
    assert (Espu : bv_unsigned (rv rho F 2) = q_sp0 Q - to_Z (c_stack K) + to_Z off).
    { rewrite Esp. rewrite (adr_wa rho 1%uint63 _ _ Xr1); slia. }
    assert (Etpv : rv rho F 4 = Z_to_bv 64 ATP).
    { rewrite Erv. change (of_Z 4) with 4%uint63. fold F in Etp. rewrite Etp, (dv_conc63 rho _ Xr0). f_equal. exact Etp0. }
    assert (Erav : rv rho F 1 = Z_to_bv 64 (to_Z l)).
    { rewrite Erv. change (of_Z 1) with 1%uint63. fold F in Era. rewrite Era. apply dv_conc63. exact Xr0. }
    (* [comment removed for export] *)
    destruct (stk_split asegs _ (q_lo Q) (bv_unsigned (rv rho F 2)) (q_sp0 Q) Xstk ltac:(rewrite Espu; slia)) as [Hstk_lo Hstk_hi].
    (* [comment removed for export] *)
    destruct (HK_caps A HK) as (Hcap1 & Hcap2 & Hcap3). pose proof (i63_range (ka_fsmax A)) as Hfsmax.
    assert (LENFF : length (a_ff st) = length FF) by (rewrite XFF; apply length_map).
    rewrite LENFF in Hffmax. rewrite Uint63.of_Z_spec in Hffmax. change wB with (2 ^ 63) in Hffmax.
    unfold AFS_MAXLIVE in XFFlen. rewrite Z.mod_small in Hffmax by slia.
    assert (LENLF : (length (LF_of Q FF) < AFS_MAXLIVE)%nat).
    { unfold LF_of, AFS_MAXLIVE. rewrite length_app, length_map. clear - XFFlen Hffmax. slia. }
    pose proof (ah_thr H HH _ _ _ Xheap) as Hthr.
    (* [comment removed for export] *)
    pose proof Xvis as Xvis0. rewrite Ems in Xvis0.
    eapply (ah_lift H HH _ _ s msF _ mo Xak Xvis0).
    { eapply STM; [exact Xrfs| exact LENLF| exact Hstk_lo| slia| rewrite Espu; slia| exact Xinv| exact Etpv| exact Xac| exact Hthr]. }
    intros msF' mo' Hak' Hmp' Hpost. unfold stack_malloc_post in Hpost.
    destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & ff & fp & junk1 & junk2
                       & Evis' & MU & WM & Hinv' & Hstk' & Hrfs' & Hfr & Hsh & Hfl & Hac').
    apply (ah_done H HH). cbn [cfg_ms cfg_model].
    (* [comment removed for export] *)
    pose proof (fresh_of_RFS H HH _ _ _ _ _ Hrfs') as FRESH.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    pose proof (proj1 FRESH) as (_ & _ & _ & FAL & _).
    pose proof (fsz_bounds (to_Z k) HkZ) as (FB & F8 & FP). pose proof (fsz_fshn (to_Z k) ltac:(slia)) as [EFN EF8].
    pose proof (fsz_eq k HkZ) as EFZ.
    set (Zk := AsIface.fsz (to_Z k)) in *.
    set (SP := bv_unsigned (rv rho F 2)) in *.
    set (W := [(SP - 1024, SP); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + Zk); (sh ff, sh ff + fshn (to_Z k))]) in *.
    set (W4 := [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + Zk); (sh ff, sh ff + fshn (to_Z k))]).
    assert (Hkeep : forall a, 0 <= a < 2 ^ 64 -> outside W a ->
                     rview asegs m' (wa a) = rview asegs (ms_mem ms) (wa a) /\ (wview asegs (ms_mem ms) (wa a) <> None -> wview asegs m' (wa a) <> None)).
    { intros a Ha Ho. split; [apply rview_eq_of_mem; apply MU; rewrite wa_unsigned by slia; exact Ho| intros Wv; apply WM; exact Wv]. }

    (* [comment removed for export] *)
    set (L17 := [wa ff; wa (sh ff); wa fp; t0'; t1'; t2'; a1'; a2'; a3'; a4'; a5'; a6'; a7'; t3'; t4'; t5'; t6']).
    set (rho' := rho_ext rho t L17).
    exists rho'.
    assert (Hag' : agree t rho rho') by (apply agree_ext; [slia | slia | exact Xr0]).
    assert (Et3 : to_Z (t + 3)%uint63 = to_Z t + 3) by (rewrite to_Z_add_small; change (to_Z 3%uint63) with 3; slia).
    assert (EL17 : forall x (kk : nat), (kk < 17)%nat -> to_Z x = to_Z t + Z.of_nat kk -> rho' x = nth kk L17 w0).
    { intros x kk Hk Hx. subst rho'. apply (rho_ext_at rho t L17 x kk); [subst L17; cbn; slia | exact Hx]. }
    assert (Erho't : rho' t = wa ff) by (rewrite (EL17 t 0%nat); [reflexivity | slia | slia]).
    assert (Erho's : rho' (t + 1)%uint63 = wa (sh ff)) by (rewrite (EL17 _ 1%nat); [reflexivity | slia | rewrite Et1; slia]).
    assert (Erho'f : rho' (t + 2)%uint63 = wa fp) by (rewrite (EL17 _ 2%nat); [reflexivity | slia | rewrite Et2; slia]).
    destruct Xreg0 as (rg0 & Hrg0 & Hlo0 & Hlen0 & Hd0 & Hpg0). fold F in Hrg0. rewrite ?Hrg1 in Hrg0.
    destruct Xreg1 as (rg1_ & Hrg1_ & Hlo1 & Hlen1 & Hd1 & Hk1' & Hal1). fold F in Hrg1_. assert (Erg1 : rg1_ = rg1) by (clear - Hrg1 Hrg1_; congruence). subst rg1_.
    pose proof (ah_fsb H HH _ _ _ Xheap) as (F1 & F2 & F3 & F4).
    pose proof (stack0_bounds _ _ _ Xst0) as [SB1 SB2].
    assert (SR : sh aceil <= sh (q_sp0 Q - to_Z (c_stack K)) /\ sh (q_sp0 Q - to_Z (c_stack K)) + nsh (to_Z (c_stack K)) <= sh (q_sp0 Q)
                 /\ sh (q_sp0 Q) <= AHI_LO /\ AIMG_TOP <= sh (q_sp0 Q - to_Z (c_stack K))).
    { split; [apply sh_mono; clear - Hlsp Hhl; slia|]. split; [| split].
      - clear - Hsp32 Hcs Est16. unfold nsh, sh. Z.div_mod_to_equations. slia.
      - clear - SB2 Hshi. unfold sh, AHI_LO, AAPP_HI in *. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. slia.
      - apply sh_above_image. clear - Hlsp Hhl ACEILB. slia. }
    assert (ESHF : sh ff + fshn (to_Z k) = sh (ff + Zk)) by (rewrite EF8, sh_add8; reflexivity).
    assert (SHF1 : sh (ff + Zk) <= sh aceil) by (apply sh_mono; clear - R2; slia).
    assert (SAI : AIMG_TOP <= sh ff) by (apply sh_above_image; clear - R1; unfold AIMG_TOP, AFS_HDR in R1; slia).
    pose proof (sh_aapp_range _ _ P9 ltac:(clear; unfold AFS_SIZE; slia0)) as (_ & _ & SHC).
    assert (NEWLO : ff + Zk <= q_sp0 Q - to_Z (c_stack K) /\ sh ff + fshn (to_Z k) <= q_sp0 Q - to_Z (c_stack K) /\ fp + 1 <= q_sp0 Q - to_Z (c_stack K)).
    { clear - R2 P2 FB ESHF SHF1 SHC Hhl Hlsp ACEILB. unfold AHI_LO in *. slia. }
    (* [comment removed for export] *)
    assert (HDJ : forall t' rg', iget t' (f_mem F) = Some rg' -> t' <> 1%uint63 ->
              disjoint_from W (bv_unsigned (rho t') + to_Z (rg_lo rg')) (to_Z (rg_len rg') - to_Z (rg_lo rg'))).
    { intros t' rg' Ht' Hne1.
      destruct (Xdom t' rg' Ht') as [-> | [-> | [-> | [-> | [Hb | [Hbs | [Hf | [Hfs | Hfl']]]]]]]].
      - rewrite Hrg0 in Ht'. injection Ht' as <-. rewrite Xr0, Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. rewrite Hlo0, Hlen0.
        subst W. cbn [disjoint_from]. clear - SAI R1 P1 P7 F1 Hhl Hlsp Espu Hoff1 Ef1 ACEILB. unfold AIMG_TOP, AIMG_LO, AFS_HDR, AFS_FLAGS in *. repeat split; slia.
      - exfalso. exact (Hne1 eq_refl).
      - rewrite Xreg2 in Ht'. injection Ht' as <-. rewrite Xr2. unfold sh_region. cbn [rg_lo rg_len]. rewrite (nsh_eq (c_stack K)) by slia.
        change (to_Z 0%uint63) with 0. fold (nsh (to_Z (c_stack K))).
        rewrite wa_unsigned by (clear - SR Hcs; unfold AIMG_TOP, AHI_LO, nsh in SR; Z.div_mod_to_equations; slia).
        pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE (q_sp0 Q - to_Z (c_stack K)) (to_Z (c_stack K)) P9 ltac:(clear - Hlsp Hhl ACEILB; slia) ltac:(clear - SB2 Hshi; slia) ltac:(clear - Hcs; slia)) as D1.
        subst W. cbn [disjoint_from]. clear - D1 SR ESHF SHF1 P3 P4 P5 P6 Espu Hoff1 Ef1 Hhl Hlsp ACEILB FB. unfold AHI_LO, AFS_HDR, AFS_FLAGS, AFS_SIZE in *. repeat split; slia.
      - rewrite Xreg3 in Ht'. injection Ht' as <-. rewrite Xr3, Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. unfold abs_region. cbn [rg_lo rg_len].
        destruct (HK_parts A HK) as (_ & _ & _ & _ & _ & _ & Hs0). unfold K_sh0_ok in Hs0. rewrite !andb_true_iff in Hs0. destruct Hs0 as [[Hslo Hslen] _].
        apply Z.eqb_eq in Hslo. apply Z.eqb_eq in Hslen. rewrite Hslo, Hslen.
        subst W. cbn [disjoint_from].
        destruct P9 as [[Q1 Q2]|[Q1 Q2]]; clear - Q1 Q2 R1 P1 P3 P4 P5 P6 F1 Hhl Hlsp Espu Hoff1 Ef1 ACEILB FB;
          unfold sh, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO, AFS_HDR, AFS_FLAGS, AFS_SIZE in *; rewrite ASHADOW_BASE_val in *; repeat split; Z.div_mod_to_equations;
          slia.
      - apply in_map_iff in Hb as (g & <- & Hg).
        pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & (rgg & Hgg & Hlog & Hleng & _) & _).
        rewrite Hgg in Ht'. injection Ht' as <-. rewrite Hlog, Hleng, Hrg. change (to_Z 0%uint63) with 0.
        pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
        rewrite wa_unsigned by (clear - G1 G3 G5 ACEILB; slia).
        pose proof (fsobj_disjoint H HH _ _ _ _ _ _ _ (SP - 1024) SP Xrfs (fsobj_block H HH _ _ _ (LF_of Q FF) _ _ _ Xheap Hin) FRESH
                      ltac:(clear - G1; slia) G3 ltac:(clear - G5 ACEILB; unfold AAPP_HI; slia) G7 ltac:(left; clear - G5 Hhl Hlsp Espu Hoff1 Ef1; slia)) as D.
        replace (g_addr g + 0) with (g_addr g) by slia. replace (to_Z (g_size g) - 0) with (to_Z (g_size g)) by slia. exact D.
      - apply in_map_iff in Hbs as (g & <- & Hg).
        pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & _ & Hshg). destruct (Hshg rg' Ht') as (-> & Hrs & _).
        pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
        unfold sh_region. cbn [rg_lo rg_len]. rewrite (nsh_eq (g_size g)) by (clear - G1 G5 ACEILB; slia). change (to_Z 0%uint63) with 0. fold (nsh (to_Z (g_size g))).
        pose proof (i63_range (g_tag g)). rewrite Hrs.
        pose proof (sh_aapp_range (g_addr g) (to_Z (g_size g)) G7 G3) as (U1 & U2 & U3). pose proof (sh_above_image (g_addr g) ltac:(slia)) as SAg.
        rewrite wa_unsigned by (clear - U2 U3 SAg G1 Hsz; unfold AIMG_TOP, AHI_LO, nsh in *; Z.div_mod_to_equations; slia).
        pose proof (fsobj_disjoint_sh H HH _ _ _ _ _ _ _ (SP - 1024) SP Xrfs (fsobj_block H HH _ _ _ (LF_of Q FF) _ _ _ Xheap Hin) FRESH
                      ltac:(clear - G1; slia) G3 ltac:(clear - G5 ACEILB; unfold AAPP_HI; slia) ltac:(clear - Hhl Hlsp Espu Hoff1 Ef1; slia)) as D.
        replace (sh (g_addr g) + 0) with (sh (g_addr g)) by slia. replace (nsh (to_Z (g_size g)) - 0) with (nsh (to_Z (g_size g))) by slia. exact D.
      - apply in_map_iff in Hf as (f & <- & Hf).
        pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hkf & Htg1 & Htg2 & (rgf & Hgf & Hlof & Hlenf & _) & _).
        rewrite Hgf in Ht'. injection Ht' as <-. rewrite Hlof, Hlenf, Hf0, (fsz_eq _ Hkf). change (to_Z 0%uint63) with 0.
        destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2' & K3 & K4 & K5) _]. pose proof (fsz_pos (to_Z (f_k f)) ltac:(slia)) as FPf.
        rewrite wa_unsigned by (clear - K2' K3 F1 F2 ACEILB FPf; unfold AIMG_TOP, AFS_HDR, AFS_SIZE in *; slia).
        assert (OBf : fsobj H (LF_of Q FF) (f_ff f) (AsIface.fsz (to_Z (f_k f)))).
        { eapply (fsobj_inframe H _ (ff_of f)); [unfold LF_of; apply in_or_app; left; apply in_map; exact Hf| cbn; slia| cbn; slia]. }
        pose proof (fsobj_disjoint H HH _ _ _ _ _ _ _ (SP - 1024) SP Xrfs OBf FRESH ltac:(clear - K2' F1 ACEILB; unfold AFS_HDR, AIMG_TOP in *; slia) ltac:(clear - FPf; slia)
                      ltac:(clear - K3 F2 ACEILB; unfold AAPP_HI; slia) (aapp_sub (as_FSB H) AFS_SIZE (f_ff f) (AsIface.fsz (to_Z (f_k f))) F4 ltac:(clear - K2'; unfold AFS_HDR in *; slia) K3)
                      ltac:(left; clear - K3 F2 Hhl Hlsp Espu Hoff1 Ef1; slia)) as D.
        replace (f_ff f + 0) with (f_ff f) by slia. replace (AsIface.fsz (to_Z (f_k f)) - 0) with (AsIface.fsz (to_Z (f_k f))) by slia. exact D.
      - apply in_map_iff in Hfs as (f & <- & Hf).
        pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hkf & Htg1 & Htg2 & _ & (rgs & Hgs & Hlos & Hlens & _) & _).
        rewrite Hgs in Ht'. injection Ht' as <-. rewrite Hlos, Hlens, Hf1. change (to_Z 0%uint63) with 0.
        destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2' & K3 & K4 & K5) _]. pose proof (fsz_pos (to_Z (f_k f)) ltac:(slia)) as FPf.
        pose proof (fsz_fshn (to_Z (f_k f)) ltac:(slia)) as [E1 E2].
        assert (B : AIMG_TOP <= f_ff f /\ f_ff f + AsIface.fsz (to_Z (f_k f)) <= AAPP_HI) by (clear - K2' K3 F1 F2 ACEILB FPf; unfold AIMG_TOP, AFS_HDR, AFS_SIZE, AAPP_HI in *; slia).
        pose proof (sh_above_image (f_ff f) ltac:(unfold AIMG_TOP in B; slia)) as SA1.
        pose proof (sh_nsh_high (f_ff f) (AsIface.fsz (to_Z (f_k f))) ltac:(unfold AIMG_TOP in B; slia) ltac:(slia) (proj2 B)) as SA2.
        rewrite wa_unsigned by (clear - B SA1 SA2 FPf E1; unfold AIMG_TOP, AHI_LO, nsh in *; Z.div_mod_to_equations; slia).
        assert (OBf : fsobj H (LF_of Q FF) (f_ff f) (AsIface.fsz (to_Z (f_k f)))).
        { eapply (fsobj_inframe H _ (ff_of f)); [unfold LF_of; apply in_or_app; left; apply in_map; exact Hf| cbn; slia| cbn; slia]. }
        pose proof (fsobj_disjoint_sh H HH _ _ _ _ _ _ _ (SP - 1024) SP Xrfs OBf FRESH ltac:(clear - B; unfold AIMG_TOP in B; slia) ltac:(clear - FPf; slia)
                      (proj2 B) ltac:(clear - Hhl Hlsp Espu Hoff1 Ef1; slia)) as D.
        rewrite E1. replace (sh (f_ff f) + 0) with (sh (f_ff f)) by slia. replace (nsh (AsIface.fsz (to_Z (f_k f))) - 0) with (nsh (AsIface.fsz (to_Z (f_k f)))) by slia. exact D.
      - apply in_map_iff in Hfl' as (f & <- & Hf).
        pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hkf & Htg1 & Htg2 & _ & _ & Hflg & _).
        rewrite Hflg in Ht'. injection Ht' as <-. unfold flag_region. cbn [rg_lo rg_len]. change (to_Z 0%uint63) with 0. change (to_Z 1%uint63) with 1. rewrite Hf2.
        destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2' & K3 & K4 & K5) _].
        rewrite wa_unsigned by (clear - K5 F1 F2 ACEILB; unfold AFS_FLAGS, AFS_HDR, AFS_SIZE, AIMG_TOP in *; slia).
        destruct FRESH as (_ & _ & FD). destruct (FD (ff_of f) ltac:(unfold LF_of; apply in_or_app; left; apply in_map; exact Hf)) as [_ NEQ]. cbn in NEQ.
        pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE ff Zk P9 ltac:(clear - R1; unfold AIMG_TOP, AFS_HDR in R1; slia) ltac:(clear - R2 ACEILB; unfold AAPP_HI; slia) ltac:(clear - FB; slia)) as D2. rewrite <- EFN in D2.
        subst W. cbn [disjoint_from]. clear - K5 NEQ D2 P3 P4 P5 P6 F2 Hhl Hlsp Espu Hoff1 Ef1 FB. unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *. repeat split; slia. }

    (* [comment removed for export] *)
    set (ms1 := MS (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) t0' t1' t2' (rv rho F 8) (rv rho F 9) (Z_to_bv 64 ff)
                     a1' a2' a3' a4' a5' a6' a7' (rv rho F 18) (rv rho F 19) (rv rho F 20) (rv rho F 21) (rv rho F 22) (rv rho F 23)
                     (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) t3' t4' t5' t6') (q_F Q) (ret_pc (rv rho F 1)) (q_fc Q) None m' (seg_rom asegs)).
    set (SHR := sh_region true t (I2RunA.fsz k)) in *. set (FFR := ff_region k (FxState.rget F 2) (FV (t + 2)%uint63 w_zero)) in *.
    exists s, LB, G, (GFr t k ff fp :: FF), (XS ++ W4), ms1.
    assert (HRn' : Rn asegs IM (t + 17)%uint63 rho'
              (FS (ret_of l) (iset 10 (FV t w_zero) (clobber clob14 (t + 3) (f_regs F)))
                  (iset 1 (drop_below off rg1) (iset (t + 1) SHR (iset (t + 2) flag_region (iset t FFR (f_mem F))))) None)
              ms1).
    { intros rho'' Hag''. subst ms1.
      assert (HagF : agree t rho rho'') by (eapply agree_trans; [exact Hag' | exact Hag'' | rewrite Et17; slia]).
      pose proof (XRn rho'' HagF) as HR''. rewrite Ems in HR''.
      assert (Erho'' : forall x, to_Z x < to_Z t + 17 -> rho'' x = rho' x) by (intros x Hx; apply (proj2 Hag''); rewrite Et17; exact Hx).
      assert (Hrho''0 : rho'' 0%uint63 = Z_to_bv 64 0) by exact (proj1 Hag'').
      assert (Erho''t : rho'' t = wa ff) by (rewrite Erho'' by slia; exact Erho't).
      assert (Erho''s : rho'' (t + 1)%uint63 = wa (sh ff)) by (rewrite Erho'' by (rewrite Et1; slia); exact Erho's).
      assert (Erho''f : rho'' (t + 2)%uint63 = wa fp) by (rewrite Erho'' by (rewrite Et2; slia); exact Erho'f).
      assert (Erho''old : forall x, to_Z x < to_Z t -> rho'' x = rho x).
      { intros x Hx. rewrite Erho'' by slia. subst rho'. apply rho_ext_old. exact Hx. }
      assert (Erho''1 : rho'' 1%uint63 = wa (q_sp0 Q - to_Z (c_stack K))) by (rewrite Erho''old by (change (to_Z 1%uint63) with 1; slia); exact Xr1).
      pose proof (R_mem _ _ _ _ _ HR'') as Hmem''. cbn [f_mem ms_mem] in Hmem''.
      constructor.
      - (* [comment removed for export] *) cbn [ms_pc_val f_pc]. rewrite Erav. apply ret_pc_of_link. exact Hl2.
      - (* [comment removed for export] *)
        change (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) t0' t1' t2' (rv rho F 8) (rv rho F 9) (Z_to_bv 64 ff)
                     a1' a2' a3' a4' a5' a6' a7' (rv rho F 18) (rv rho F 19) (rv rho F 20) (rv rho F 21) (rv rho F 22) (rv rho F 23)
                     (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) t3' t4' t5' t6')
          with (mkRl [rv rho F 1; rv rho F 2; rv rho F 3; rv rho F 4; t0'; t1'; t2'; rv rho F 8; rv rho F 9; Z_to_bv 64 ff;
                      a1'; a2'; a3'; a4'; a5'; a6'; a7'; rv rho F 18; rv rho F 19; rv rho F 20; rv rho F 21; rv rho F 22; rv rho F 23;
                      rv rho F 24; rv rho F 25; rv rho F 26; rv rho F 27; t3'; t4'; t5'; t6']).
        apply R_regs_of_match; [exact Hrho''0 | reflexivity |].
        change (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) (rv rho F 5) (rv rho F 6) (rv rho F 7) (rv rho F 8) (rv rho F 9) (rv rho F 10)
                     (rv rho F 11) (rv rho F 12) (rv rho F 13) (rv rho F 14) (rv rho F 15) (rv rho F 16) (rv rho F 17) (rv rho F 18) (rv rho F 19) (rv rho F 20)
                     (rv rho F 21) (rv rho F 22) (rv rho F 23) (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) (rv rho F 28) (rv rho F 29) (rv rho F 30) (rv rho F 31))
          with (mkRl [rv rho F 1; rv rho F 2; rv rho F 3; rv rho F 4; rv rho F 5; rv rho F 6; rv rho F 7; rv rho F 8; rv rho F 9; rv rho F 10;
                      rv rho F 11; rv rho F 12; rv rho F 13; rv rho F 14; rv rho F 15; rv rho F 16; rv rho F 17; rv rho F 18; rv rho F 19; rv rho F 20;
                      rv rho F 21; rv rho F 22; rv rho F 23; rv rho F 24; rv rho F 25; rv rho F 26; rv rho F 27; rv rho F 28; rv rho F 29; rv rho F 30; rv rho F 31]) in HR''.
        pose proof (regs_match_of_R _ _ _ _ _ _ _ _ _ _ _ HR'') as Hpre.
        assert (Hnd14 : List.NoDup clob14) by (apply nodupb_spec; reflexivity).
        assert (Hcl : forall kr : int, iget kr (clobber clob14 (t + 3) (f_regs F)) =
                      match index_of kr clob14 with
                      | Some i => Some (FV (of_Z (to_Z (t + 3)%uint63 + Z.of_nat i)) w_zero)
                      | None => iget kr (f_regs F) end).
        { intros kr. apply iget_clobber; [exact Hnd14 | rewrite Et3; cbn [length clob14]; slia]. }
        apply regs_match_intro. cbn [seq].
        repeat (apply Forall_cons || apply Forall_nil);
          cbn [nth Nat.sub Z.of_nat Pos.of_succ_nat Pos.succ];
          match goal with |- _ = dv _ (FxState.rget ?FF' ?kr) =>
            let kk := eval vm_compute in kr in change kr with kk; rewrite (rget_regs' FF' kk eq_refl) end;
          cbn [f_regs]; rewrite iget_iset;
          match goal with |- _ = dv _ match (if ?b then _ else _) with _ => _ end => let bb := eval vm_compute in b in change b with bb end;
          cbv iota.
        all: try (rewrite Hcl;
                  match goal with |- _ = dv _ match match ?ix with _ => _ end with _ => _ end =>
                    let ii := eval vm_compute in ix in change ix with ii end; cbv iota).
        all: first
          [ match goal with |- Z_to_bv 64 ?AA = dv ?rr (FV ?tt w_zero) => rewrite (dv_tag_zero rr tt) by slia; rewrite Erho''t; reflexivity end
          | match goal with |- _ = dv ?rr (FV (of_Z (to_Z ?t1 + Z.of_nat ?i)) w_zero) =>
              let Etag := fresh "Etag" in
              assert (Etag : to_Z (of_Z (to_Z t1 + Z.of_nat i)) = to_Z t1 + Z.of_nat i)
                by (rewrite Uint63.of_Z_spec; apply Z.mod_small; change wB with (2 ^ 63); clear - Hn59 Et3 Ht; slia0);
              rewrite (dv_tag_zero rr (of_Z (to_Z t1 + Z.of_nat i))) by (rewrite Etag; clear - Hn59 Et3 Ht; slia0);
              rewrite (Erho'' (of_Z (to_Z t1 + Z.of_nat i))) by (rewrite Etag; clear - Hn59 Et3 Ht; slia0);
              rewrite (EL17 (of_Z (to_Z t1 + Z.of_nat i)) (S (S (S i)))); [reflexivity | clear; slia0 | rewrite Etag; clear - Et3 Ht; slia0]
            end
          | match goal with |- rv _ _ ?kz = dv _ match iget ?ki (f_regs ?FF') with _ => _ end =>
              rewrite <- (rget_regs' FF' ki eq_refl);
              let kn := eval vm_compute in (Z.to_nat kz) in
              let HP := fresh "HP" in
              pose proof (Hpre kn ltac:(slia)) as HP; cbn [nth Nat.sub Z.of_nat Pos.of_succ_nat Pos.succ] in HP; exact HP
            end
          ].
      - reflexivity.
      - reflexivity.
      - (* [comment removed for export] *)
        cbn [f_mem ms_mem].
        apply mem_ok_parts.
        + intros t' rg' Ht'. rewrite !iget_iset in Ht'.
          destruct (t' =? 1)%uint63 eqn:E1.
          * (* [comment removed for export] *) apply Uint63.eqb_spec in E1. subst t'. injection Ht' as <-.
            destruct (Xkinds 1%uint63 rg1 Hrg1 ltac:(intros E; discriminate E)) as [_ Hkd1].
            apply (stack_part asegs IM rho'' (ms_mem ms) m' rg1 off (q_sp0 Q - to_Z (c_stack K)) (q_lo Q) (q_sp0 Q)).
            -- exact Erho''1.
            -- exact Hlo1.
            -- exact Hd1.
            -- exact Hkd1.
            -- rewrite Hlen1. reflexivity.
            -- rewrite Hlen1. clear - Hoff Hoff2; slia.
            -- clear - Hoff16 Hoff. Z.div_mod_to_equations. slia.
            -- exact (mem_part_of _ _ _ _ _ _ _ Hmem'' Hrg1).
            -- exact Xstk.
            -- clear - Hhl Hlsp ACEILB; slia.
            -- rewrite <- Espu. exact Hstk'.
            -- intros a Ha. destruct Xstk as (_ & H64 & _). apply Hkeep; [clear - Ha H64 Hhl Hlsp Hoff ACEILB; slia |].
               subst W. cbn [outside]. clear - Ha Espu R2 FB P4 P8 F2 Hhl Hlsp Hoff SHF1 ESHF SHC ACEILB. unfold AFS_FLAGS, AFS_HDR, AFS_SIZE, AHI_LO in *. repeat split; slia.
          * destruct (t' =? t + 1)%uint63 eqn:Ets.
            -- (* [comment removed for export] *) apply Uint63.eqb_spec in Ets. subst t'. injection Ht' as <-. subst SHR.
               apply (sh_region_part IM rho'' Hrho''0 true m' t (I2RunA.fsz k) ff).
               ++ exact Erho''s.
               ++ rewrite Erho''t. apply wa_unsigned. clear - R1 R2 FB ACEILB. unfold AIMG_TOP, AFS_HDR in *. slia.
               ++ slia.
               ++ rewrite EFZ. fold Zk. clear - FB. slia.
               ++ rewrite EFZ. fold Zk. clear - R2 ACEILB. unfold AAPP_HI. slia.
               ++ rewrite EFZ. fold Zk. rewrite shadow_of_mult8 by (clear - FB F8; slia). unfold poison_bytes in Hsh.
                  replace (Z.to_nat (Zk / 8)) with (Z.to_nat (fshn (to_Z k))) by (clear - EF8 FB; slia). exact Hsh.
            -- destruct (t' =? t + 2)%uint63 eqn:Etf.
               ++ (* [comment removed for export] *) apply Uint63.eqb_spec in Etf. subst t'. injection Ht' as <-.
                  apply (flag_region_part IM rho'' m' t fp); [exact Erho''f| slia| clear - P1; unfold AIMG_TOP, AFS_FLAGS in P1; slia| clear - P2 R2 FB ACEILB; slia| exact Hfl].
               ++ destruct (t' =? t)%uint63 eqn:Et'.
                  ** (* [comment removed for export] *) apply Uint63.eqb_spec in Et'. subst t'. injection Ht' as <-. subst FFR.
                     apply (ff_region_part IM rho'' m' t k (FxState.rget F 2) (FV (t + 2)%uint63 w_zero) ff fp (rv rho F 2) junk1 junk2).
                     --- exact Erho''t.
                     --- intros E. apply (f_equal to_Z) in E. change (to_Z 0%uint63) with 0 in E. clear - E Xn0a Xn0b. slia.
                     --- slia.
                     --- exact HkZ.
                     --- clear - R1; unfold AIMG_TOP, AFS_HDR in R1; slia.
                     --- fold Zk. clear - R2 ACEILB. slia.
                     --- exact FAL.
                     --- rewrite (dv_agree t rho rho'' _ HagF) by (rewrite Esp2; cbn [vtag]; change (to_Z 1%uint63) with 1; slia). rewrite Erv. reflexivity.
                     --- rewrite dv_tag_zero by (rewrite Et2; slia). rewrite Erho''f. reflexivity.
                     --- exact Hfr.
                  ** destruct (t' =? 0)%uint63 eqn:E0.
                     --- (* [comment removed for export] *) apply Uint63.eqb_spec in E0. subst t'. rewrite Hrg0 in Ht'. injection Ht' as <-.
                         apply (mem_part_transfer0 IMX rho'' (ms_mem ms) m' rg0 Hrho''0); [rewrite Hlen0; unfold AIMG_TOP; slia| | exact (mem_part_of _ _ _ _ _ _ _ Hmem'' Hrg0)].
                         intros a Ha. rewrite Hlo0, Hlen0 in Ha. apply Hkeep; [clear - Ha; unfold AIMG_LO, AIMG_TOP in Ha; slia|].
                         eapply disjoint_outside; [apply (HDJ 0%uint63 rg0 Hrg0 ltac:(intros E; discriminate E))|].
                         rewrite Xr0, Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. rewrite Hlo0, Hlen0. clear - Ha. slia.
                     --- (* [comment removed for export] *)
                         assert (Hne0 : t' <> 0%uint63) by (intros E; subst t'; rewrite Uint63.eqb_refl in E0; discriminate).
                         assert (Hne1 : t' <> 1%uint63) by (intros E; subst t'; rewrite Uint63.eqb_refl in E1; discriminate).
                         apply (old_parts_keep H IMX A HK HHx HSH0 _ _ _ _ _ _ _ _ _ _ _ rho'' m' (outside W) [] t' rg' X).
                         +++ intros x Hx. apply Erho''old. exact Hx.
                         +++ exact Hkeep.
                         +++ intros t2 rg2 a Ht2 Hn0 Hn1 _ Ha. eapply disjoint_outside; [apply (HDJ t2 rg2 Ht2 Hn1)| clear - Ha; slia].
                         +++ exact Hac'.
                         +++ exact Hinv'.
                         +++ exact Ht'.
                         +++ exact Hne0.
                         +++ exact Hne1.
                         +++ intros [].
        + (* [comment removed for export] *)
          intros t1 t2 r1 r2 Hne Hi1 Hi2. rewrite !iget_iset in Hi1, Hi2.
          (* [comment removed for export] *)
          assert (OLDLT : forall x rg, iget x (f_mem F) = Some rg -> to_Z x < to_Z t).
          { intros x rg Hx. destruct (Xdom x rg Hx) as [-> | [-> | [-> | [-> | [Hb | [Hbs | [Hf | [Hfs | Hfl']]]]]]]];
              [change (to_Z 0%uint63) with 0; clear - Xn0a Xn0b; slia| change (to_Z 1%uint63) with 1; clear - Xn0a Xn0b; slia
              | change (to_Z 2%uint63) with 2; clear - Xn0a Xn0b; slia| change (to_Z 3%uint63) with 3; clear - Xn0a Xn0b; slia| ..].
            - apply in_map_iff in Hb as (g & <- & Hg). pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & _ & Htg2 & _). clear - Htg2. slia.
            - apply in_map_iff in Hbs as (g & <- & Hg). pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & _ & Htg2 & _). pose proof (i63_range (g_tag g)).
              rewrite to_Z_add_small by (change (to_Z 1%uint63) with 1; clear - Htg2 H4 Hn59; slia0). change (to_Z 1%uint63) with 1. clear - Htg2. slia.
            - apply in_map_iff in Hf as (f & <- & Hf). pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Htg2 & _). clear - Htg2. slia.
            - apply in_map_iff in Hfs as (f & <- & Hf). pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Htg2 & _). pose proof (i63_range (f_tag f)).
              rewrite to_Z_add_small by (change (to_Z 1%uint63) with 1; clear - Htg2 H4 Hn59; slia0). change (to_Z 1%uint63) with 1. clear - Htg2. slia.
            - apply in_map_iff in Hfl' as (f & <- & Hf). pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Htg2 & _). pose proof (i63_range (f_tag f)).
              rewrite to_Z_add_small by (change (to_Z 2%uint63) with 2; clear - Htg2 H4 Hn59; slia0). change (to_Z 2%uint63) with 2. clear - Htg2. slia. }
          (* [comment removed for export] *)
          assert (FOOT : forall x r,
                    (if (x =? 1)%uint63 then Some (drop_below off rg1) else if (x =? t + 1)%uint63 then Some SHR else if (x =? t + 2)%uint63 then Some flag_region
                     else if (x =? t)%uint63 then Some FFR else iget x (f_mem F)) = Some r ->
                    (x = t /\ bv_unsigned (rho'' x) + to_Z (rg_lo r) = ff /\ bv_unsigned (rho'' x) + to_Z (rg_len r) = ff + Zk)
                    \/ (x = (t + 1)%uint63 /\ bv_unsigned (rho'' x) + to_Z (rg_lo r) = sh ff /\ bv_unsigned (rho'' x) + to_Z (rg_len r) = sh ff + fshn (to_Z k))
                    \/ (x = (t + 2)%uint63 /\ bv_unsigned (rho'' x) + to_Z (rg_lo r) = fp /\ bv_unsigned (rho'' x) + to_Z (rg_len r) = fp + 1)
                    \/ (to_Z x < to_Z t /\ exists rg, iget x (f_mem F) = Some rg /\ rg_lo rg = rg_lo r /\ rg_len rg = rg_len r)).
          { intros x r Hx.
            destruct (x =? 1)%uint63 eqn:Ex1.
            - apply Uint63.eqb_spec in Ex1. subst x. injection Hx as <-. do 3 right. split; [change (to_Z 1%uint63) with 1; clear - Xn0a Xn0b; slia|].
              exists rg1. split; [exact Hrg1| split; reflexivity].
            - destruct (x =? t + 1)%uint63 eqn:Exs.
              + apply Uint63.eqb_spec in Exs. subst x. injection Hx as <-. right; left. split; [reflexivity|]. subst SHR. unfold sh_region. cbn [rg_lo rg_len].
                rewrite (nsh_eq (I2RunA.fsz k)) by (rewrite EFZ; clear - FB; slia). rewrite EFZ. fold Zk. change (to_Z 0%uint63) with 0. rewrite EFN. fold (nsh Zk).
                rewrite Erho''s, wa_unsigned by (clear - SAI SHF1 ESHF SHC EF8 FB ACEILB; unfold AIMG_TOP, AHI_LO in *; slia). rewrite <- EFN. clear. slia.
              + destruct (x =? t + 2)%uint63 eqn:Exf.
                * apply Uint63.eqb_spec in Exf. subst x. injection Hx as <-. do 2 right; left. split; [reflexivity|]. unfold flag_region. cbn [rg_lo rg_len].
                  change (to_Z 0%uint63) with 0. change (to_Z 1%uint63) with 1. rewrite Erho''f, wa_unsigned by (clear - P1 P2 R2 FB ACEILB; unfold AIMG_TOP, AFS_FLAGS in *; slia). clear. slia.
                * destruct (x =? t)%uint63 eqn:Ext.
                  -- apply Uint63.eqb_spec in Ext. subst x. injection Hx as <-. left. split; [reflexivity|]. subst FFR. unfold ff_region. cbn [rg_lo rg_len].
                     rewrite EFZ. fold Zk. change (to_Z 0%uint63) with 0. rewrite Erho''t, wa_unsigned by (clear - R1 R2 FB ACEILB; unfold AIMG_TOP, AFS_HDR in *; slia). clear. slia.
                  -- do 3 right. split; [exact (OLDLT _ _ Hx)|]. exists r. split; [exact Hx| split; reflexivity]. }
          (* [comment removed for export] *)
          pose proof (aapp_disjoint_sh ff Zk ff Zk (aapp_sub (as_FSB H) AFS_SIZE ff Zk P9 ltac:(clear - P5; unfold AFS_HDR in P5; slia) P6)
                        ltac:(clear - R1; unfold AIMG_TOP, AFS_HDR in R1; slia) ltac:(clear - R2 ACEILB; unfold AAPP_HI; slia) ltac:(clear - FB; slia)) as NS1.
          rewrite <- EFN in NS1.
          pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE ff Zk P9 ltac:(clear - R1; unfold AIMG_TOP, AFS_HDR in R1; slia) ltac:(clear - R2 ACEILB; unfold AAPP_HI; slia) ltac:(clear - FB; slia)) as NS2.
          rewrite <- EFN in NS2.
          (* [comment removed for export] *)
          assert (OLDNEW : forall x q lo' hi', iget x (f_mem F) = Some q ->
                    ((lo' = ff /\ hi' = ff + Zk) \/ (lo' = sh ff /\ hi' = sh ff + fshn (to_Z k)) \/ (lo' = fp /\ hi' = fp + 1)) ->
                    hi' <= bv_unsigned (rho'' x) + to_Z (rg_lo q) \/ bv_unsigned (rho'' x) + to_Z (rg_len q) <= lo').
          { intros x q lo' hi' Hx Hw. rewrite (Erho''old x (OLDLT _ _ Hx)).
            destruct (Uint63.eqb x 1) eqn:Ex1.
            - apply Uint63.eqb_spec in Ex1. subst x. rewrite Hrg1 in Hx. injection Hx as <-. rewrite Xr1, Hlo1, Hlen1. change (to_Z 0%uint63) with 0.
              rewrite wa_unsigned by (clear - Hhl Hlsp HspB HB64 Hcs ACEILB; slia). left. clear - Hw NEWLO. slia.
            - apply Uint63.eqb_false_spec in Ex1. pose proof (HDJ x q Hx Ex1) as D. subst W. cbn [disjoint_from] in D. destruct D as (_ & _ & D3 & D4 & D5 & _).
              clear - Hw D3 D4 D5. slia. }
          destruct (FOOT t1 r1 Hi1) as [(-> & A1 & B1) | [(-> & A1 & B1) | [(-> & A1 & B1) | (L1 & q1 & Hq1 & Lo1 & Le1)]]];
          destruct (FOOT t2 r2 Hi2) as [(-> & A2 & B2) | [(-> & A2 & B2) | [(-> & A2 & B2) | (L2 & q2 & Hq2 & Lo2 & Le2)]]].
          all: try (exfalso; exact (Hne eq_refl)).
          all: try (clear - A1 B1 A2 B2 NS1 NS2 P2 P3 P4 FB; unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *; slia).
          * rewrite <- Lo2, <- Le2. destruct (OLDNEW t2 q2 ff (ff + Zk) Hq2 ltac:(left; split; reflexivity)) as [D|D]; clear - D A1 B1; slia.
          * rewrite <- Lo2, <- Le2. destruct (OLDNEW t2 q2 (sh ff) (sh ff + fshn (to_Z k)) Hq2 ltac:(right; left; split; reflexivity)) as [D|D]; clear - D A1 B1; slia.
          * rewrite <- Lo2, <- Le2. destruct (OLDNEW t2 q2 fp (fp + 1) Hq2 ltac:(right; right; split; reflexivity)) as [D|D]; clear - D A1 B1; slia.
          * rewrite <- Lo1, <- Le1. destruct (OLDNEW t1 q1 ff (ff + Zk) Hq1 ltac:(left; split; reflexivity)) as [D|D]; clear - D A2 B2; slia.
          * rewrite <- Lo1, <- Le1. destruct (OLDNEW t1 q1 (sh ff) (sh ff + fshn (to_Z k)) Hq1 ltac:(right; left; split; reflexivity)) as [D|D]; clear - D A2 B2; slia.
          * rewrite <- Lo1, <- Le1. destruct (OLDNEW t1 q1 fp (fp + 1) Hq1 ltac:(right; right; split; reflexivity)) as [D|D]; clear - D A2 B2; slia.
          * rewrite <- Lo1, <- Le1, <- Lo2, <- Le2. exact (proj2 Hmem'' t1 t2 q1 q2 Hne Hq1 Hq2). }

    (* [comment removed for export] *)
    assert (Hkeep0 : forall a, 0 <= a < 2 ^ 64 -> outside W a ->
                     m' (wa a) = ms_mem ms (wa a) /\ (wview asegs (ms_mem ms) (wa a) <> None -> wview asegs m' (wa a) <> None)).
    { intros a Ha Ho. split; [apply MU; rewrite wa_unsigned by (clear - Ha; slia); exact Ho| intros Wv; apply WM; exact Wv]. }
    assert (SHM1 : sh (as_FSB H) <= sh ff) by (apply sh_mono; clear - P5; unfold AFS_HDR in P5; slia).
    assert (SHM2 : sh (ff + Zk) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; clear - P6; slia).
    assert (CW : Forall (aclient_write_ok H LB) W).
    { subst W. apply Forall_cons; [left; cbn [fst snd]; clear - Hhl Hlsp Espu Hoff1 Ef1; slia|].
      apply Forall_cons; [do 4 right; left; cbn [fst snd]; clear; unfold AFS_FLAGS, AFS_SIZE; slia|].
      apply Forall_cons; [do 4 right; left; cbn [fst snd]; clear - P3 P4; unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *; slia|].
      apply Forall_cons; [do 4 right; left; cbn [fst snd]; clear - P5 P6; unfold AFS_HDR in *; slia|].
      apply Forall_cons; [do 5 right; left; cbn [fst snd]; clear - SHM1 SHM2 ESHF; slia| apply Forall_nil]. }
    assert (SW : Forall stack0_ok W).
    { subst W. apply Forall_cons; [apply stack0_ok_app; cbn [fst snd]; clear - Hhl Hlsp Espu Hoff1 Ef1 ACEILB; unfold AHI_LO; slia|].
      apply Forall_cons; [eapply stack0_ok_aapp; [exact P9| clear; slia| clear; unfold AFS_FLAGS, AFS_SIZE; slia]|].
      apply Forall_cons; [eapply stack0_ok_aapp; [exact P9| clear - P3; unfold AFS_FLAGS in P3; slia| clear - P4; unfold AFS_HDR, AFS_SIZE in *; slia]|].
      apply Forall_cons; [eapply stack0_ok_aapp; [exact P9| clear - P5; unfold AFS_HDR in P5; slia| exact P6]|].
      apply Forall_cons; [apply stack0_ok_sh'; [clear - R1; unfold AIMG_TOP, AFS_HDR in R1; slia| clear - EF8 FB; slia| rewrite <- EF8; exact R2]| apply Forall_nil]. }
    (* [comment removed for export] *)
    assert (GDJ : forall g, In g G -> disjoint_from W (g_addr g) (to_Z (g_size g)) /\ disjoint_from W (sh (g_addr g)) (nsh (to_Z (g_size g)))).
    { intros g Hg. pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & _).
      pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & G6 & G7). split.
      - exact (fsobj_disjoint H HH _ _ _ _ _ _ _ (SP - 1024) SP Xrfs (fsobj_block H HH _ _ _ (LF_of Q FF) _ _ _ Xheap Hin) FRESH
                 ltac:(clear - G1; slia) G3 ltac:(clear - G5 ACEILB; unfold AAPP_HI; slia) G7 ltac:(left; clear - G5 Hhl Hlsp Espu Hoff1 Ef1; slia)).
      - exact (fsobj_disjoint_sh H HH _ _ _ _ _ _ _ (SP - 1024) SP Xrfs (fsobj_block H HH _ _ _ (LF_of Q FF) _ _ _ Xheap Hin) FRESH
                 ltac:(clear - G1; slia) G3 ltac:(clear - G5 ACEILB; unfold AAPP_HI; slia) ltac:(clear - Hhl Hlsp Espu Hoff1 Ef1; slia)). }
    assert (NCF : forall x c, to_Z c < 4 -> 4 <= to_Z x -> (x =? c)%uint63 = false).
    { intros x c Hc Hx. destruct (x =? c)%uint63 eqn:E; [|reflexivity]. apply Uint63.eqb_spec in E. subst c. exfalso. clear - Hc Hx. slia. }
    assert (N1t' := NCF t 1%uint63 ltac:(change (to_Z 1%uint63) with 1; clear; slia) ltac:(clear - Xn0a Xn0b; slia)).
    assert (N1s' := NCF (t + 1)%uint63 1%uint63 ltac:(change (to_Z 1%uint63) with 1; clear; slia) ltac:(rewrite Et1; clear - Xn0a Xn0b; slia)).
    assert (N1f' := NCF (t + 2)%uint63 1%uint63 ltac:(change (to_Z 1%uint63) with 1; clear; slia) ltac:(rewrite Et2; clear - Xn0a Xn0b; slia)).
    assert (Htst : (t =? t + 1)%uint63 = false) by (destruct (t =? t + 1)%uint63 eqn:E; [|reflexivity]; apply Uint63.eqb_spec in E; apply (f_equal to_Z) in E; rewrite Et1 in E; exfalso; clear - E; slia).
    assert (Htft : (t =? t + 2)%uint63 = false) by (destruct (t =? t + 2)%uint63 eqn:E; [|reflexivity]; apply Uint63.eqb_spec in E; apply (f_equal to_Z) in E; rewrite Et2 in E; exfalso; clear - E; slia).
    assert (Hsft : (t + 2 =? t + 1)%uint63 = false) by (destruct (t + 2 =? t + 1)%uint63 eqn:E; [|reflexivity]; apply Uint63.eqb_spec in E; apply (f_equal to_Z) in E; rewrite Et1, Et2 in E; exfalso; clear - E; slia).
    (* [comment removed for export] *)
    assert (OLDIF : forall x (rr : option region), to_Z x < to_Z t -> 4 <= to_Z x ->
              (if (x =? 1)%uint63 then Some (drop_below off rg1) else if (x =? t + 1)%uint63 then Some SHR else if (x =? t + 2)%uint63 then Some flag_region
               else if (x =? t)%uint63 then Some FFR else rr) = rr).
    { intros x rr Hx H4x. rewrite (NCF x 1%uint63 ltac:(change (to_Z 1%uint63) with 1; slia) H4x).
      destruct (x =? t + 1)%uint63 eqn:E1'; [apply Uint63.eqb_spec in E1'; apply (f_equal to_Z) in E1'; exfalso; clear - E1' Et1 Hx; slia0|].
      destruct (x =? t + 2)%uint63 eqn:E2'; [apply Uint63.eqb_spec in E2'; apply (f_equal to_Z) in E2'; exfalso; clear - E2' Et2 Hx; slia0|].
      destruct (x =? t)%uint63 eqn:E3'; [apply Uint63.eqb_spec in E3'; apply (f_equal to_Z) in E3'; exfalso; clear - E3' Hx; slia|]. reflexivity. }
    pose proof (ah_RFS_nodup H HH _ _ Hrfs') as FND. cbn [map ff_addr fst snd] in FND. unfold LF_of in FND. rewrite map_app, map_ff_addr_of in FND.
    destruct Xnamed as [XG0in XLB0nd].
    constructor; cbn [a_F a_n a_blk a_ff a_cost a_cnt a_cs mk f_mem f_pc f_regs f_resv ms_regs ms_mem ms_fregs ms_fcsr ms_rom MS ms1].
    - exact Evis'.
    - exact HRn'.
    - apply canonR_mkR.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - subst rho'. rewrite rho_ext_old; [exact Xr0 | change (to_Z 0%uint63) with 0; clear - Xn0a Xn0b; slia].
    - subst rho'. rewrite rho_ext_old; [exact Xr1 | change (to_Z 1%uint63) with 1; clear - Xn0a Xn0b; slia].
    - subst rho'. rewrite rho_ext_old; [exact Xr2 | change (to_Z 2%uint63) with 2; clear - Xn0a Xn0b; slia].
    - subst rho'. rewrite rho_ext_old; [exact Xr3 | change (to_Z 3%uint63) with 3; clear - Xn0a Xn0b; slia].
    - eapply agree_trans; [exact Xag | exact Hag' | clear - Xn0a Xn0b; slia].
    - rewrite Et17. clear - Xn0a Xn0b Hn59. slia.
    - exact Hak'.
    - exact (ah_mpres_trans H HH _ _ _ Xmp Hmp').
    - eapply (ah_RHEAP_frame H HH); [exact Xheap| exact MU| exact WM| exact CW].
    - exact Hrfs'.
    - exact Hac'.
    - eapply stack0_transport; [exact Xst0| exact MU| exact WM| exact SW].
    - eapply (chain_via_munch H HH); [exact Xch| exact MU|]. intros fp' ra' Hin. specialize (XCH0 fp' ra' Hin).
      subst W. cbn [disjoint_from]. clear - XCH0 NEWLO P3 Hhl Hlsp Espu Hoff Hoff2. repeat split; slia.
    - exact XCH0.
    - exact Xs0v.
    - exact Xpfo.
    - exact XAL.
    - exact XAL0.
    - exact XG.
    - (* [comment removed for export] *) apply Forall_forall. intros g Hg.
      pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & (rgg & Hgg & Hlog & Hleng & Hkg & Halg & Hdfg) & Hshg).
      pose proof (i63_range (g_tag g)) as Htg.
      assert (Etg1 : to_Z (g_tag g + 1)%uint63 = to_Z (g_tag g) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; clear - Htg2 Htg Hn59; slia0).
      split; [exact Hin|]. split; [subst rho'; rewrite rho_ext_old by (clear - Htg2; slia); exact Hrg|]. split; [exact Hsz|]. split; [exact Htg1|].
      split; [rewrite Et17; clear - Htg2; slia|]. split.
      + exists rgg. rewrite !iget_iset. rewrite (OLDIF (g_tag g) _ ltac:(clear - Htg2; slia) Htg1). split; [exact Hgg|]. repeat split; assumption.
      + intros rg' Hrg'. rewrite !iget_iset in Hrg'. rewrite (OLDIF (g_tag g + 1)%uint63 _ ltac:(rewrite Etg1; clear - Htg2; slia) ltac:(rewrite Etg1; clear - Htg1; slia)) in Hrg'.
        destruct (Hshg rg' Hrg') as (Erg' & Hrs & Had'). split; [exact Erg'|]. split; [subst rho'; rewrite rho_ext_old by (rewrite Etg1; clear - Htg2; slia); exact Hrs|].
        eapply addressable_transport; [exact Had'| exact MU| exact WM| exact (proj2 (GDJ g Hg))].
    - exact XGnd.
    - exact XGtnd.
    - exact XGnew.
    - (* [comment removed for export] *) apply Forall_forall. intros g Hg. pose proof (proj1 (Forall_forall _ _) XGstk g Hg) as Hs.
      pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & _).
      apply (stk_pres asegs (ms_mem ms)); [exact Hs|]. intros a Ha. apply Hkeep0; [clear - Ha G1 G5 ACEILB; slia|].
      eapply disjoint_outside; [exact (proj1 (GDJ g Hg))| exact Ha].
    - (* [comment removed for export] *) cbn [map f_tag f_k]. rewrite XFF. reflexivity.
    - (* [comment removed for export] *) apply Forall_cons.
      + cbn [f_tag f_k f_ff f_fp]. split; [exact Erho't|]. split; [exact Erho's|]. split; [exact Erho'f|]. split; [exact HkZ|].
        split; [clear - Xn0a Xn0b; slia|]. split; [rewrite Et17; clear; slia|].
        split; [exists FFR; rewrite !iget_iset, N1t', Htst, Htft, Uint63.eqb_refl; split; [reflexivity|]; subst FFR; unfold ff_region; cbn [rg_lo rg_len rg_kind rg_align];
               repeat split; try reflexivity; rewrite Uint63.add_spec; change (to_Z 6%uint63) with 6; rewrite Z.mod_small by (change wB with (2 ^ 63); clear - HkZ; slia); clear - HkZ; slia|].
        split; [exists SHR; rewrite !iget_iset, N1s', Uint63.eqb_refl; split; [reflexivity|]; subst SHR; unfold sh_region; cbn [rg_lo rg_len rg_kind];
               split; [reflexivity|]; split; [rewrite (nsh_eq (I2RunA.fsz k)) by (rewrite EFZ; clear - FB; slia); rewrite EFZ; fold Zk; rewrite EFN; reflexivity| reflexivity]|].
        split; [rewrite !iget_iset, N1f', Hsft, Uint63.eqb_refl; reflexivity|].
        split; [apply rin_ivs_app; right; subst W4; cbn [rin_ivs fst snd]; do 2 right; left; clear - FB; slia|].
        split; [intros a Ha; apply rin_ivs_app; right; subst W4; cbn [rin_ivs fst snd]; do 2 right; left; clear - Ha; slia|].
        split; [intros a Ha; apply rin_ivs_app; right; subst W4; cbn [rin_ivs fst snd]; do 3 right; left; clear - Ha; slia|].
        apply rin_ivs_app; right; subst W4; cbn [rin_ivs fst snd]; right; left; clear; slia.
      + apply Forall_forall. intros f Hf.
        pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hkf & Htg1 & Htg2 & (rgf & Hgf & Hlof & Hlenf & Hkdf & Half & Hdff) & (rgs & Hgs & Hlos & Hlens & Hks) & Hflg & X1 & X2 & X3 & X4).
        pose proof (i63_range (f_tag f)) as Htg.
        assert (Etg1 : to_Z (f_tag f + 1)%uint63 = to_Z (f_tag f) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; clear - Htg2 Htg Hn59; slia0).
        assert (Etg2 : to_Z (f_tag f + 2)%uint63 = to_Z (f_tag f) + 2) by (rewrite to_Z_add_small; change (to_Z 2%uint63) with 2; clear - Htg2 Htg Hn59; slia0).
        split; [subst rho'; rewrite rho_ext_old by (clear - Htg2; slia); exact Hf0|]. split; [subst rho'; rewrite rho_ext_old by (rewrite Etg1; clear - Htg2; slia); exact Hf1|].
        split; [subst rho'; rewrite rho_ext_old by (rewrite Etg2; clear - Htg2; slia); exact Hf2|]. split; [exact Hkf|]. split; [exact Htg1|]. split; [rewrite Et17; clear - Htg2; slia|].
        split; [exists rgf; rewrite !iget_iset, (OLDIF (f_tag f) _ ltac:(clear - Htg2; slia) Htg1); split; [exact Hgf|]; repeat split; assumption|].
        split; [exists rgs; rewrite !iget_iset, (OLDIF (f_tag f + 1)%uint63 _ ltac:(rewrite Etg1; clear - Htg2; slia) ltac:(rewrite Etg1; clear - Htg1; slia)); split; [exact Hgs|]; repeat split; assumption|].
        split; [rewrite !iget_iset, (OLDIF (f_tag f + 2)%uint63 _ ltac:(rewrite Etg2; clear - Htg2; slia) ltac:(rewrite Etg2; clear - Htg1; slia)); exact Hflg|].
        split; [apply rin_ivs_app; left; exact X1|]. split; [intros a Ha; apply rin_ivs_app; left; exact (X2 a Ha)|].
        split; [intros a Ha; apply rin_ivs_app; left; exact (X3 a Ha)|]. apply rin_ivs_app; left; exact X4.
    - (* [comment removed for export] *) cbn [map f_ff]. exact FND.
    - (* [comment removed for export] *) cbn [map f_tag]. constructor; [| exact XFFtnd]. intros Hin. apply in_map_iff in Hin as (f & E & Hf).
      pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Htg2 & _). rewrite E in Htg2. clear - Htg2. slia.
    - (* [comment removed for export] *) destruct XTsep as (S1 & S2 & S3). split; [exact S1| split].
      + intros g f Hg [<-|Hf]; cbn [f_tag]; [| exact (S2 g f Hg Hf)].
        pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & _ & Htg2 & _). left. clear - Htg2. slia.
      + intros f f' [<-|Hf] [<-|Hf'] Hne; cbn [f_tag].
        * exfalso. exact (Hne eq_refl).
        * pose proof (proj1 (Forall_forall _ _) XFFin f' Hf') as (_ & _ & _ & _ & _ & Htg2 & _). right. clear - Htg2. slia.
        * pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Htg2 & _). left. clear - Htg2. slia.
        * exact (S3 f f' Hf Hf' Hne).
    - (* [comment removed for export] *) cbn [length]. unfold AFS_MAXLIVE. clear - XFFlen Hffmax Hfsmax. slia.
    - (* [comment removed for export] *) apply Forall_app. split; [exact XXS|]. subst W4. apply (fs_scratch_of_fresh H). eapply fresh_frame_sub; [exact FRESH|]. intros f Hf. unfold LF_of. apply in_or_app. right. exact Hf.
    - (* [comment removed for export] *) intros t' rg' Ht'. rewrite !iget_iset in Ht'.
      destruct (t' =? 1)%uint63 eqn:E1; [apply Uint63.eqb_spec in E1; right; left; exact E1|].
      destruct (t' =? t + 1)%uint63 eqn:Ets; [apply Uint63.eqb_spec in Ets; do 7 right; left; cbn [map f_tag]; left; symmetry; exact Ets|].
      destruct (t' =? t + 2)%uint63 eqn:Etf; [apply Uint63.eqb_spec in Etf; do 8 right; cbn [map f_tag]; left; symmetry; exact Etf|].
      destruct (t' =? t)%uint63 eqn:Et'; [apply Uint63.eqb_spec in Et'; do 6 right; left; cbn [map f_tag]; left; symmetry; exact Et'|].
      destruct (Xdom t' rg' Ht') as [H0' | [H1' | [H2' | [H3' | [Hb' | [Hbs' | [Hf' | [Hfs' | Hfl'']]]]]]]];
        [left; exact H0' | right; left; exact H1' | do 2 right; left; exact H2' | do 3 right; left; exact H3'
        | do 4 right; left; exact Hb' | do 5 right; left; exact Hbs' | do 6 right; left; cbn [map]; right; exact Hf' | do 7 right; left; cbn [map]; right; exact Hfs'
        | do 8 right; cbn [map]; right; exact Hfl''].
    - (* [comment removed for export] *) exists rg0. rewrite !iget_iset. change ((0 =? 1)%uint63) with false. rewrite N0s, N0f, N0t. cbv iota. split; [exact Hrg0|]. split; [exact Hlo0|]. split; [exact Hlen0|]. split; [exact Hd0| exact Hpg0].
    - (* [comment removed for export] *) exists (drop_below off rg1). rewrite iget_iset. rewrite Uint63.eqb_refl. split; [reflexivity|]. unfold drop_below. cbn [rg_lo rg_len rg_dflt rg_kind rg_align]. repeat split; assumption.
    - (* [comment removed for export] *) rewrite !iget_iset. change ((2 =? 1)%uint63) with false. rewrite N2s, N2f, N2t. exact Xreg2.
    - (* [comment removed for export] *) rewrite !iget_iset. change ((3 =? 1)%uint63) with false. rewrite N3s, N3f, N3t. exact Xreg3.
    - (* [comment removed for export] *) destruct Xro as (rg0_ & Hrg0_ & Hroc). assert (rg0_ = rg0) by (fold F in Hrg0_; clear - Hrg0 Hrg0_; congruence). subst rg0_.
      exists rg0. rewrite !iget_iset. change ((0 =? 1)%uint63) with false. rewrite N0s, N0f, N0t. split; [exact Hrg0| exact Hroc].
    - (* [comment removed for export] *) intros t' rg' pn p' ci c Ht' Hp' Hc. pose proof (i63_range ci) as Hci. pose proof (i63_range pn) as Hpn. rewrite !iget_iset in Ht'.
      destruct (t' =? 1)%uint63 eqn:E1.
      + injection Ht' as <-. destruct (drop_below_pages_inv _ _ _ _ Hp') as (p0 & Hp0 & _ & ->).
        unfold drop_below. cbn [rg_len]. unfold drop_page in Hc. cbn [fst snd] in Hc.
        destruct (pn =? off >> 12)%uint63.
        * cbn [pg_cells] in Hc. destruct (keep_cells_ge_inv _ _ _ _ Hc) as [_ Hc']. exact (Xinb 1%uint63 rg1 pn p0 ci c Hrg1 Hp0 Hc').
        * exact (Xinb 1%uint63 rg1 pn p0 ci c Hrg1 Hp0 Hc).
      + destruct (t' =? t + 1)%uint63 eqn:Ets.
        * (* [comment removed for export] *)
          injection Ht' as <-. subst SHR. unfold sh_region in Hp' |- *. cbn [rg_pages rg_len] in Hp' |- *. rewrite iget_iset, iget_iempty in Hp'.
          destruct (pn =? 0)%uint63 eqn:Epn; [|discriminate]. apply Uint63.eqb_spec in Epn. subst pn. injection Hp' as <-. cbn [pg_cells] in Hc.
          destruct (sh_cells_inv (I2RunA.fsz k) ci c ltac:(rewrite EFZ; clear - FB; slia) Hc) as [Hcilt ->].
          rewrite (nsh_eq (I2RunA.fsz k)) by (rewrite EFZ; clear - FB; slia). change (to_Z 0%uint63) with 0. rewrite EFZ in Hcilt |- *. fold Zk in Hcilt |- *.
          split; [clear - Hcilt Hci FB; Z.div_mod_to_equations; slia|]. split; [clear - Hcilt Hci FB; Z.div_mod_to_equations; slia|].
          intros v Ev. unfold sh_cell in Ev. destruct (((ci + 1) * 8 <=? I2RunA.fsz k >> 3))%uint63 eqn:Ecv; [|discriminate].
          apply (proj1 (leb8_spec ci (I2RunA.fsz k) ltac:(clear - Hcilt Hci FB; Z.div_mod_to_equations; slia) ltac:(rewrite EFZ; clear - FB; slia))) in Ecv. rewrite EFZ in Ecv.
          clear - Ecv Hci FB. Z.div_mod_to_equations. slia.
        * destruct (t' =? t + 2)%uint63 eqn:Etf.
          -- injection Ht' as <-. cbv beta iota delta [flag_region rg_pages rg_len] in Hp'. cbv beta iota delta [flag_region rg_len]. rewrite iget_iset, iget_iempty in Hp'.
             destruct (pn =? 0)%uint63 eqn:Epn; [|discriminate]. apply Uint63.eqb_spec in Epn. subst pn. apply Some_inj' in Hp'. subst p'. cbv beta iota delta [pg_cells] in Hc.
             rewrite iget_iset, iget_iempty in Hc. destruct (ci =? 0)%uint63 eqn:Eci; [|discriminate]. apply Uint63.eqb_spec in Eci. subst ci. apply Some_inj' in Hc. subst c.
             change (to_Z 0%uint63) with 0. change (to_Z 1%uint63) with 1. split; [clear; slia|]. split; [clear; slia|]. intros v Ev. discriminate Ev.
          -- destruct (t' =? t)%uint63 eqn:Et'.
             ++ injection Ht' as <-. subst FFR. cbv beta iota delta [ff_region rg_pages rg_len] in Hp'. cbv beta iota delta [ff_region rg_len]. rewrite iget_iset, iget_iempty in Hp'.
                destruct (pn =? 0)%uint63 eqn:Epn; [|discriminate]. apply Uint63.eqb_spec in Epn. subst pn. apply Some_inj' in Hp'. subst p'. cbv beta iota delta [pg_cells] in Hc.
                rewrite !iget_iset, iget_iempty in Hc. change (to_Z 0%uint63) with 0. rewrite EFZ. fold Zk.
                assert (E3 : to_Z (I2RunA.fsz k >> 3 - 1)%uint63 = Zk / 8 - 1).
                { rewrite to_Z_sub_small; rewrite to_Z_lsr3', EFZ; change (to_Z 1%uint63) with 1; [reflexivity| clear - FB; Z.div_mod_to_equations; slia0]. }
                destruct (ci =? I2RunA.fsz k >> 3 - 1)%uint63 eqn:Ec1.
                ** apply Uint63.eqb_spec in Ec1. apply (f_equal to_Z) in Ec1. rewrite E3 in Ec1. clear - Ec1 FB F8. split; [Z.div_mod_to_equations; slia|]. split; [Z.div_mod_to_equations; slia|]. intros _ _. Z.div_mod_to_equations; slia.
                ** destruct (ci =? 3)%uint63 eqn:Ec3; [|discriminate]. apply Uint63.eqb_spec in Ec3. subst ci. change (to_Z 3%uint63) with 3. clear - FB. split; [slia|]. split; [slia|]. intros _ _. slia.
             ++ exact (Xinb t' rg' pn p' ci c Ht' Hp' Hc).
    - (* [comment removed for export] *) intros t' rg' Ht' Ht'0. rewrite !iget_iset in Ht'.
      destruct (t' =? 1)%uint63 eqn:E1.
      + injection Ht' as <-. apply Uint63.eqb_spec in E1. subst t'. destruct (Xkinds 1%uint63 rg1 Hrg1 Ht'0) as [Hdu1 Hku1].
        unfold drop_below. cbn [rg_dflt rg_pages]. split; [exact Hdu1|].
        intros pn p' Hp'. destruct (drop_below_pages_inv _ _ _ _ Hp') as (p0 & Hp0 & _ & ->).
        unfold drop_page. cbn [fst snd]. destruct (pn =? off >> 12)%uint63; cbn [pg_kind]; exact (Hku1 _ _ Hp0).
      + destruct (t' =? t + 1)%uint63 eqn:Ets.
        * injection Ht' as <-. subst SHR. unfold sh_region. cbn [rg_dflt rg_pages]. split; [left; reflexivity|].
          intros pn p' Hp'. rewrite iget_iset, iget_iempty in Hp'. destruct (pn =? 0)%uint63; [injection Hp' as <-; reflexivity | discriminate].
        * destruct (t' =? t + 2)%uint63 eqn:Etf.
          -- injection Ht' as <-. cbv beta iota delta [flag_region rg_dflt rg_pages]. split; [right; reflexivity|].
             intros pn p' Hp'. rewrite iget_iset, iget_iempty in Hp'. destruct (pn =? 0)%uint63; [apply Some_inj' in Hp'; subst p'; reflexivity | discriminate].
          -- destruct (t' =? t)%uint63 eqn:Et'.
             ++ injection Ht' as <-. subst FFR. cbv beta iota delta [ff_region rg_dflt rg_pages]. split; [left; reflexivity|].
                intros pn p' Hp'. rewrite iget_iset, iget_iempty in Hp'. destruct (pn =? 0)%uint63; [apply Some_inj' in Hp'; subst p'; reflexivity | discriminate].
             ++ exact (Xkinds t' rg' Ht' Ht'0).
    - exact Xcost.
    - exact Xcnt.
    - (* [comment removed for export] *) apply (stk_merge asegs m' (q_lo Q) SP (q_sp0 Q)); [exact Hstk' | | clear - Hhl Hlsp Espu Hoff Hoff2; slia].
      apply (stk_pres asegs (ms_mem ms)); [exact Hstk_hi|]. intros a Ha. destruct Hstk_hi as (_ & Hhi64 & _). apply Hkeep0; [clear - Ha Hhi64 Hhl Hlsp Espu Hoff ACEILB; slia|].
      subst W. cbn [outside]. clear - Ha NEWLO P3 Espu Hoff Hoff2. repeat split; slia.
    - repeat split; assumption.
    - eapply (ah_rauxv_frame H HH); [exact Xaux| exact MU| exact WM| exact CW].
    - exact Hinv'.
    - apply (stk_pres asegs (ms_mem ms)); [exact Xerr|]. intros a Ha. apply Hkeep0; [clear - Ha Eerr H0 H1; unfold errA, AERRNO, ATP in *; slia|].
      subst W. cbn [outside]. clear - Ha Eerr H0 H1 R1 P1 F1 SAI Hhl Hlsp Espu Hoff1 Ef1 ACEILB. unfold errA, AERRNO, ATP, AIMG_TOP, AFS_HDR, AFS_FLAGS in *. repeat split; slia.
    - exact (HSH0 _ Hac' Hinv').
    - exact XLB0.
    - exact XLB0h.
    - split; [exact XG0in | exact XLB0nd].
    - exact XLBsub.
    - (* [comment removed for export] *) intros a Ha Hcl Hna Hnx Hne Hnxs. rewrite <- (Xframe a Ha Hcl Hna Hnx Hne ltac:(intros KK; apply Hnxs; apply rin_ivs_app; left; exact KK)).
      assert (NW4 : ~ rin_ivs W4 a) by (intros KK; apply Hnxs; apply rin_ivs_app; right; exact KK). subst W4. cbn [rin_ivs fst snd] in NW4.
      assert (LOW : SP <= a \/ a < aceil).
      { unfold client0, aclient_addr in Hcl. destruct Hcl as [Hs | [Hst | [(b & Hb & Hr) | [(b & Hb & Hr) | [Hfs | [Hfss | Hss]]]]]].
        - left. clear - Hs Hlsp Espu Hoff2. slia.
        - right. clear - Hst ACEILB. unfold aimg_client, AIMG_LO, AIMG_TOP in *. slia.
        - right. destruct (XLB0h b Hb) as [_ Bh]. clear - Hr Bh. slia.
        - right. destruct (XLB0h b Hb) as [B0 Bh]. pose proof (sh_nsh_high (blk_addr b) (blk_size b) B0 ltac:(clear - Hr; unfold nsh in Hr; Z.div_mod_to_equations; slia) ltac:(clear - Bh ACEILB; unfold AAPP_HI; slia)) as SB.
          clear - Hr SB ACEILB. unfold AHI_LO in *. slia.
        - right. clear - Hfs F2. slia.
        - right. pose proof (sh_below_app (as_FSB H + AFS_SIZE) ltac:(clear - F1 F2 ACEILB; unfold AIMG_TOP, AAPP_HI, AFS_SIZE in *; slia)) as SB.
          pose proof (sh_mono a). clear - Hfss SB ACEILB. unfold AHI_LO, sh in *. rewrite ?ASHADOW_BASE_val in *. Z.div_mod_to_equations. slia.
        - right. clear - Hss ACEILB. unfold AHI_LO in *. slia. }
      assert (OUT : outside W a) by (subst W; cbn [outside]; clear - NW4 LOW Hhl Hlsp Espu Hoff1 Ef1; repeat split; slia).
      exact (proj1 (Hkeep0 a Ha OUT)).
    - (* [comment removed for export] *) apply Forall_cons.
      + cbn [f_ff f_k]. pose proof (stk_of_rw_cells asegs m' ff _ Hfr) as HsN. cbn [cells_size csize] in HsN.
        match type of HsN with stk _ _ _ ?hi => replace hi with (ff + AsIface.fsz (to_Z k)) in HsN by (fold Zk; clear - FB; slia) end. exact HsN.
      + apply Forall_forall. intros f__ Hf__. pose proof (proj1 (Forall_forall _ _) XFFstk f__ Hf__) as HsF.
        pose proof (proj1 (Forall_forall _ _) XFFin f__ Hf__) as (Hf0' & _ & _ & Hkf' & Htg1' & _ & (rgf' & Hgf' & Hlof' & Hlenf' & _) & _).
        destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf__) as [(KF1 & KF2 & KF3 & KF4 & KF5) _]. pose proof (fsz_pos (to_Z (f_k f__)) ltac:(clear - Hkf'; slia)) as FPf.
        apply (stk_pres asegs (ms_mem ms)); [exact HsF|]. intros a__ Ha__.
        apply Hkeep0; [clear - Ha__ KF2 KF3 F1 F2 FPf ACEILB; unfold AFS_HDR, AIMG_TOP in *; slia|].
        eapply disjoint_outside; [apply (HDJ (f_tag f__) rgf' Hgf' ltac:(intros E; rewrite E in Htg1'; change (to_Z 1%uint63) with 1 in Htg1'; clear - Htg1'; slia))|].
        rewrite Hf0', Hlof', Hlenf', (fsz_eq _ Hkf'). change (to_Z 0%uint63) with 0.
        rewrite wa_unsigned by (clear - KF2 KF3 F1 F2 FPf ACEILB; unfold AFS_HDR, AIMG_TOP in *; slia). clear - Ha__. slia.
  Qed.

  (* [comment removed for export] *)
  Theorem anode_fsfree_sound : forall code, code_ok asegs code -> anode_fsfree_sig H IMX A code.
  Proof.
    intros code Hcode. unfold anode_fsfree_sig, anode_concl.
    intros Q st st' rho msF mo Hnode Hc0 (s & LB & G & FF & XS & ms & X).
    (* [comment removed for export] *)
    unfold anode_fsfree in Hnode.
    destruct (iget (f_pc (a_F st)) code) as [fi|] eqn:Hi; [|discriminate].
    destruct fi as [ | | | | | sz rs1 rs2 imm | | | | | | | | | | | ]; try discriminate Hnode.
    destruct (fv_alu (f_mem (a_F st)) ALU_ADD (FxState.rget (a_F st) rs1) (FV 0 imm)) as [[ft [top o]]|] eqn:Ea; [|discriminate].
    destruct (conc63 (FxState.rget (a_F st) rs2)) as [z|] eqn:Hz; [|discriminate].
    match type of Hnode with (if ?b then _ else _) = _ => destruct b eqn:Hguard; [|discriminate] end.
    injection Hnode as <-.
    rewrite !andb_true_iff in Hguard. destruct Hguard as [[[[[[Htop Ho] Hz0] Hmsz] Hft3] Hex] Hrv].
    apply Uint63.eqb_spec in Htop. apply Uint63.eqb_spec in Ho. apply Uint63.eqb_spec in Hz0. apply Uint63.eqb_spec in Hmsz. subst top o z.
    apply Uint63.leb_spec in Hft3. change (to_Z 3%uint63) with 3 in Hft3. pose proof (resv_none_inv _ Hrv) as Eresv.
    (* [comment removed for export] *)
    pose proof X as X'.
    destruct X' as [Xvis XRn Xcan Xfr Xfc Xrom Xr0 Xr1 Xr2 Xr3 Xag Xn0 Xak Xmp Xheap Xrfs Xac Xst0 Xch XCH0 Xs0v Xpfo XAL XAL0
                    XG XGin XGnd XGtnd XGnew XGstk XFF XFFin XFFnd XFFtnd XTsep XFFlen XXS Xdom Xreg0 Xreg1 Xreg2 Xreg3 Xro Xinb Xkinds
                    Xcost Xcnt Xstk Xlo Xaux Xinv Xerr Xsh0 XLB0 XLB0h Xnamed XLBsub Xframe XFFstk].
    set (F := a_F st) in *. set (n := a_n st) in *.
    pose proof (i63_range n) as Hn. pose proof (i63_range ft) as Hft. destruct Xn0 as [Xn0a Xn0b].
    (* [comment removed for export] *)
    rewrite XFF in Hex. apply existsb_exists in Hex as ([tg kg] & Hin & Etg). apply in_map_iff in Hin as (f0 & Ef0 & Hf0). injection Ef0 as E1 E2. subst tg kg.
    cbn [fst] in Etg. apply Uint63.eqb_spec in Etg.
    pose proof (proj1 (Forall_forall _ _) XFFin f0 Hf0) as (Hf00 & Hf01 & Hf02 & Hkf0 & Htg01 & Htg02 & (rgf0 & Hgf0 & _) & (rgs0 & Hgs0 & _) & Hflg0 & X01 & X02 & X03 & X04).
    pose proof (i63_range (f_tag f0)) as Htg0.
    assert (Et01 : to_Z (f_tag f0 + 1)%uint63 = to_Z (f_tag f0) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; clear - Htg02 Htg0 Xn0b; slia0).
    assert (Et02 : to_Z (f_tag f0 + 2)%uint63 = to_Z (f_tag f0) + 2) by (rewrite to_Z_add_small; change (to_Z 2%uint63) with 2; clear - Htg02 Htg0 Xn0b; slia0).
    assert (Eft : ft = (f_tag f0 + 2)%uint63) by (symmetry; exact Etg).
    assert (Et : (ft - 2)%uint63 = f_tag f0).
    { apply to_Z_inj. rewrite to_Z_sub_small by (change (to_Z 2%uint63) with 2; clear - Hft3; slia0). rewrite Eft, Et02. change (to_Z 2%uint63) with 2. clear; slia0. }
    rewrite Et. rewrite ?Eft. subst ft.
    set (t := f_tag f0) in *.
    destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf0) as [(K1 & K2 & K3 & K4 & K5) (F1 & F2 & F3 & F4)]. acb.
    (* [comment removed for export] *)
    assert (Hag : agree n rho rho) by (apply agree_refl; exact Xr0).
    pose proof (XRn rho Hag) as HR.
    assert (WRF : wview asegs (ms_mem ms) (wa (f_fp f0)) <> None).
    { destruct (flag_byte_live H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf0) as [bf Hbf]. unfold wview. rewrite Hbf. discriminate. }
    destruct (sb_flag_step asegs IM rho Xr0 code Hcode F ms sz rs1 rs2 imm (t + 2)%uint63 (f_fp f0) HR Hi Ea Hz Hmsz Hf02
                ltac:(clear - K5 F1 F2 ACEILB; unfold AFS_FLAGS, AFS_HDR, AFS_SIZE, AIMG_TOP in *; slia0) ltac:(rewrite Et02; clear - Htg02 Xn0b; slia0) WRF) as [STEP Hpc].
    set (m' := write_to_mem (ms_mem ms) (wa (f_fp f0)) [b8 0]) in *.
    set (ms1 := ms_of ms (inval_resv (wa (f_fp f0)) (with_pc (Z_to_bv 64 (to_Z (f_pc F + 4)%uint63)) (core_of ms))) m') in *.
    pose proof Xvis as Xvis0.
    eapply (ah_lift H HH (fun x => x = ms1) _ s msF ms mo Xak Xvis0).
    { eapply evt_step; [| apply evt_done; reflexivity]. split; [exact (R_svc _ _ _ _ _ HR)| exact STEP]. }
    intros msF' mo' Hak' Hmp' Evis'. apply (ah_done H HH). cbn [cfg_ms cfg_model].
    exists rho.
    (* [comment removed for export] *)
    assert (FPR : 0 <= f_fp f0 /\ f_fp f0 + 1 <= 2 ^ 64) by (clear - K5 F1 F2 ACEILB; unfold AFS_FLAGS, AFS_HDR, AFS_SIZE, AIMG_TOP in *; slia0).
    assert (MU : munch [(f_fp f0, f_fp f0 + 1)] (ms_mem ms) m').
    { subst m'. apply munch_write; [apply munch_refl| clear - FPR; slia0| cbn [length]; clear - FPR; slia0| cbn [length inside]; clear; slia0]. }
    assert (WM : wmono asegs (ms_mem ms) m') by (subst m'; apply wmono_write; apply wmono_refl).
    assert (Hkeep0 : forall a, 0 <= a < 2 ^ 64 -> a <> f_fp f0 ->
                     m' (wa a) = ms_mem ms (wa a) /\ (wview asegs (ms_mem ms) (wa a) <> None -> wview asegs m' (wa a) <> None)).
    { intros a Ha Hne. split; [apply MU; rewrite wa_unsigned by (clear - Ha; slia0); cbn [outside]; clear - Hne; split; [slia0| exact I]| intros Wv; apply WM; exact Wv]. }
    assert (Hkeep : forall a, 0 <= a < 2 ^ 64 -> a <> f_fp f0 ->
                     rview asegs m' (wa a) = rview asegs (ms_mem ms) (wa a) /\ (wview asegs (ms_mem ms) (wa a) <> None -> wview asegs m' (wa a) <> None)).
    { intros a Ha Hne. destruct (Hkeep0 a Ha Hne) as [E W']. split; [apply rview_eq_of_mem; exact E| exact W']. }
    assert (RD0 : mrd asegs m' (wa (f_fp f0)) = Some (b8 0)).
    { unfold mrd. subst m'. rewrite (write_to_mem_spec [b8 0] (ms_mem ms) (f_fp f0) (wa (f_fp f0))) by (cbn [length]; clear - FPR; slia0).
      rewrite wa_unsigned by (clear - FPR; slia0). cbn [length]. replace ((f_fp f0 <=? f_fp f0) && (f_fp f0 <? f_fp f0 + Z.of_nat 1))%bool with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; clear; slia0).
      rewrite Z.sub_diag. reflexivity. }
    assert (CW : Forall (aclient_write_ok H LB) [(f_fp f0, f_fp f0 + 1)]).
    { apply Forall_cons; [do 4 right; left; cbn [fst snd]; clear - K5; unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *; slia0| apply Forall_nil]. }
    assert (SW : Forall stack0_ok [(f_fp f0, f_fp f0 + 1)]).
    { apply Forall_cons; [eapply stack0_ok_aapp; [exact F4| clear - K5; unfold AFS_FLAGS in K5; slia0| clear - K5; unfold AFS_HDR, AFS_SIZE in *; slia0]| apply Forall_nil]. }
    (* [comment removed for export] *)
    pose proof (R_mem _ _ _ _ _ HR) as Hmem.
    assert (FPSEP : forall x rg a, iget x (f_mem F) = Some rg -> x <> (t + 2)%uint63 ->
              bv_unsigned (rho x) + to_Z (rg_lo rg) <= a < bv_unsigned (rho x) + to_Z (rg_len rg) -> a <> f_fp f0).
    { intros x rg a Hx Hne Ha. pose proof (proj2 Hmem x (t + 2)%uint63 rg flag_region Hne Hx Hflg0) as SEP.
      unfold flag_region in SEP. cbn [rg_lo rg_len] in SEP. change (to_Z 0%uint63) with 0 in SEP. change (to_Z 1%uint63) with 1 in SEP.
      rewrite Hf02, wa_unsigned in SEP by (clear - FPR; slia0). clear - SEP Ha. slia0. }

    assert (Hac' : ACONST m').
    { eapply ACONST_frame; [exact Xac| exact MU| exact WM|]. apply Forall_cons; [eapply aconst_ok_aapp; [exact F4| cbn [fst snd]; clear - K5; unfold AFS_FLAGS in K5; slia0| cbn [fst snd]; clear - K5; unfold AFS_HDR, AFS_SIZE in *; slia0]| apply Forall_nil]. }
    assert (Hinv' : mem_inv asegs m').
    { intros a b Hab. subst m'. apply write_to_mem_some in Hab as [Hm | (i & Hii & ->)]; [exact (Xinv _ _ Hm)|].
      apply asegs_ro_addr_false_high. cbn [length] in Hii. rewrite (wa_unsigned (f_fp f0)) by (clear - FPR; slia0). rewrite wa_unsigned by (clear - FPR Hii; slia0). clear - K5 F1 Hii FPR. unfold AFS_FLAGS, AIMG_TOP in *. slia0. }
    (* [comment removed for export] *)
    set (FF' := gfdel t FF).
    assert (HFF' : forall f, In f FF' -> In f FF /\ f <> f0) by (intros f Hf; split; [exact (gfdel_In _ _ _ Hf)| exact (gfdel_not_self _ _ _ XFFtnd Hf0 Hf)]).
    destruct XTsep as (S1 & S2 & S3).
    assert (TG : forall g, In g G -> to_Z (g_tag g) + 2 <= to_Z t \/ to_Z t + 3 <= to_Z (g_tag g)) by (intros g Hg; exact (S2 g f0 Hg Hf0)).
    assert (TF : forall f, In f FF' -> to_Z (f_tag f) + 3 <= to_Z t \/ to_Z t + 3 <= to_Z (f_tag f)).
    { intros f Hf. destruct (HFF' f Hf) as [Hf1 Hne]. exact (S3 f f0 Hf1 Hf0 Hne). }
    assert (IGET' : forall x, iget x (iremove (t + 2) (iremove (t + 1) (iremove t (f_mem F)))) =
                     if (x =? t + 2)%uint63 then None else if (x =? t + 1)%uint63 then None else if (x =? t)%uint63 then None else iget x (f_mem F)).
    { intros x. rewrite !iget_iremove. reflexivity. }
    assert (OLDX : forall x (rr : option region), to_Z x <> to_Z t -> to_Z x <> to_Z t + 1 -> to_Z x <> to_Z t + 2 ->
              (if (x =? t + 2)%uint63 then None else if (x =? t + 1)%uint63 then None else if (x =? t)%uint63 then None else rr) = rr).
    { intros x rr N0 N1' N2'.
      destruct (x =? t + 2)%uint63 eqn:E2'; [apply Uint63.eqb_spec in E2'; apply (f_equal to_Z) in E2'; rewrite Et02 in E2'; exfalso; exact (N2' E2')|].
      destruct (x =? t + 1)%uint63 eqn:E1'; [apply Uint63.eqb_spec in E1'; apply (f_equal to_Z) in E1'; rewrite Et01 in E1'; exfalso; exact (N1' E1')|].
      destruct (x =? t)%uint63 eqn:E0'; [apply Uint63.eqb_spec in E0'; apply (f_equal to_Z) in E0'; exfalso; exact (N0 E0')|]. reflexivity. }
    (* [comment removed for export] *)
    assert (OLDREV : forall x rg, (if (x =? t + 2)%uint63 then None else if (x =? t + 1)%uint63 then None else if (x =? t)%uint63 then None else iget x (f_mem F)) = Some rg ->
              iget x (f_mem F) = Some rg /\ x <> t /\ x <> (t + 1)%uint63 /\ x <> (t + 2)%uint63).
    { intros x rg Hx. destruct (x =? t + 2)%uint63 eqn:E2'; [discriminate|]. destruct (x =? t + 1)%uint63 eqn:E1'; [discriminate|]. destruct (x =? t)%uint63 eqn:E0'; [discriminate|].
      apply Uint63.eqb_false_spec in E2'. apply Uint63.eqb_false_spec in E1'. apply Uint63.eqb_false_spec in E0'. repeat split; assumption. }
    destruct Xreg0 as (rg0 & Hrg0 & Hlo0 & Hlen0 & Hd0 & Hpg0). fold F in Hrg0.
    destruct Xreg1 as (rg1 & Hrg1 & Hlo1 & Hlen1 & Hd1 & Hk1' & Hal1). fold F in Hrg1.
    destruct Xlo as (Hhl & Hlsp & HspB & Hsp16 & Hsp32 & HB64 & Hshi). pose proof (i63_range (c_stack K)) as Hcs.
    destruct (HK_err A HK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Est16 & Est40).
    exists s, LB, G, FF', XS, ms1.
    destruct (inval_resv_facts (wa (f_fp f0)) (with_pc (Z_to_bv 64 (to_Z (f_pc F + 4)%uint63)) (core_of ms))) as (I1 & I2 & I3).
    assert (HRn' : Rn asegs IM n rho (FS (f_pc F + 4)%uint63 (f_regs F) (iremove (t + 2) (iremove (t + 1) (iremove t (f_mem F)))) None) ms1).
    { intros rho'' Hag''. pose proof (XRn rho'' Hag'') as HR''. pose proof (R_mem _ _ _ _ _ HR'') as Hmem''. cbn [f_mem] in Hmem''.
      assert (Hrho''0 : rho'' 0%uint63 = Z_to_bv 64 0) by exact (proj1 Hag'').
      assert (Erho'' : forall x, to_Z x < to_Z n -> rho'' x = rho x) by (intros x Hx; apply (proj2 Hag''); exact Hx).
      subst ms1. apply (R_intro_step asegs IM rho'' ms); cbn [f_pc f_regs f_mem f_resv].
      - rewrite I1. reflexivity.
      - intros r. rewrite I2. cbn [with_pc]. exact (R_regs _ _ _ _ _ HR'' r).
      - rewrite I3. cbn [with_pc c_resv core_of option_map]. pose proof (R_resv _ _ _ _ _ HR'') as RV. cbn [ms_resv] in RV. rewrite Eresv in RV. cbn [option_map] in RV. rewrite RV. reflexivity.
      - apply mem_ok_parts.
        + intros x rg Hx. rewrite IGET' in Hx. destruct (OLDREV x rg Hx) as (Hx' & Nx0 & Nx1 & Nx2). clear Hx.
          destruct (x =? 0)%uint63 eqn:E0.
          * apply Uint63.eqb_spec in E0. subst x. rewrite Hrg0 in Hx'. injection Hx' as <-.
            apply (mem_part_transfer0 IMX rho'' (ms_mem ms) m' rg0 Hrho''0); [rewrite Hlen0; unfold AIMG_TOP; clear; slia0| | exact (mem_part_of _ _ _ _ _ _ _ Hmem'' Hrg0)].
            intros a Ha. rewrite Hlo0, Hlen0 in Ha. apply Hkeep; [clear - Ha; unfold AIMG_LO, AIMG_TOP in Ha; slia0|]. clear - Ha K5 F1. unfold AIMG_LO, AIMG_TOP, AFS_FLAGS in *. slia0.
          * destruct (x =? 1)%uint63 eqn:E1.
            -- apply Uint63.eqb_spec in E1. subst x. rewrite Hrg1 in Hx'. injection Hx' as <-.
               apply (mem_part_transfer asegs IM rho'' (ms_mem ms) m' 1%uint63 rg1 (q_sp0 Q - to_Z (c_stack K))).
               ++ rewrite Erho'' by (change (to_Z 1%uint63) with 1; clear - Xn0a; slia0). exact Xr1.
               ++ clear - Hhl Hlsp ACEILB. slia0.
               ++ rewrite Hlen1. clear - Hlsp HspB HB64 Hcs. slia0.
               ++ intros a Ha. rewrite Hlo1, Hlen1 in Ha. change (to_Z 0%uint63) with 0 in Ha. apply Hkeep; [clear - Ha Hhl Hlsp HspB HB64 Hcs ACEILB; slia0|].
                  clear - Ha K5 F2 Hhl Hlsp. unfold AFS_HDR, AFS_SIZE in *. slia0.
               ++ intros pn sg _. intros E. discriminate E.
               ++ exact (mem_part_of _ _ _ _ _ _ _ Hmem'' Hrg1).
            -- apply Uint63.eqb_false_spec in E0. apply Uint63.eqb_false_spec in E1.
               apply (old_parts_keep H IMX A HK HHx HSH0 _ _ _ _ _ _ _ _ _ _ _ rho'' m' (fun a => a <> f_fp f0) [(t + 2)%uint63] x rg X).
               ++ exact Erho''.
               ++ exact Hkeep.
               ++ intros t2 rg2 a Ht2 _ _ Hrm Ha. apply (FPSEP t2 rg2 a Ht2); [intros ->; apply Hrm; left; reflexivity| exact Ha].
               ++ exact Hac'.
               ++ exact Hinv'.
               ++ exact Hx'.
               ++ exact E0.
               ++ exact E1.
               ++ cbn. intros [E|[]]. exact (Nx2 (eq_sym E)).
        + intros t1 t2 r1 r2 Hne H1 H2. rewrite IGET' in H1, H2. destruct (OLDREV t1 r1 H1) as (H1' & _). destruct (OLDREV t2 r2 H2) as (H2' & _).
          exact (proj2 Hmem'' t1 t2 r1 r2 Hne H1' H2'). }
    assert (CW' := CW). assert (FLEN : (length FF' + 1 = length FF)%nat) by (subst FF'; apply gfdel_length; apply in_map_iff; exists f0; split; [reflexivity| exact Hf0]).
    destruct Xnamed as [XG0in XLB0nd].
    constructor; cbn [a_F a_n a_blk a_ff a_cost a_cnt a_cs mk f_mem f_pc f_regs f_resv].
    - exact Evis'.
    - exact HRn'.
    - subst ms1. cbn [ms_regs ms_of]. replace (c_regs (inval_resv (wa (f_fp f0)) (with_pc (Z_to_bv 64 (to_Z (f_pc F + 4)%uint63)) (core_of ms)))) with (ms_regs ms); [exact Xcan|].
      unfold inval_resv. destruct (c_resv (with_pc (Z_to_bv 64 (to_Z (f_pc F + 4)%uint63)) (core_of ms))); [destruct (bv_unsigned _ =? bv_unsigned _)%Z; reflexivity| reflexivity].
    - subst ms1. cbn [ms_fregs ms_of]. rewrite inval_resv_fregs. cbn [with_pc c_fregs core_of]. exact Xfr.
    - subst ms1. cbn [ms_fcsr ms_of]. rewrite inval_resv_fcsr. cbn [with_pc c_fcsr core_of]. exact Xfc.
    - subst ms1. cbn [ms_rom ms_of]. exact Xrom.
    - exact Xr0.
    - exact Xr1.
    - exact Xr2.
    - exact Xr3.
    - exact Xag.
    - split; [exact Xn0a| exact Xn0b].
    - exact Hak'.
    - exact (ah_mpres_trans H HH _ _ _ Xmp Hmp').
    - subst ms1. cbn [ms_mem ms_of]. eapply (ah_RHEAP_frame H HH); [exact Xheap| exact MU| exact WM| exact CW].
    - subst ms1. cbn [ms_mem ms_of]. unfold LF_of. subst FF'. rewrite <- (lf_remove_gfdel FF f0 (q_LF0 Q) XFFtnd XFFnd Hf0).
      eapply (ah_release H HH); [exact Xrfs| unfold LF_of; apply in_or_app; left; apply in_map_iff; exists f0; split; [reflexivity| exact Hf0]| exact MU| exact WM| | exact RD0].
      apply Forall_cons; [right; cbn [fst snd]; split; reflexivity| apply Forall_nil].
    - subst ms1. cbn [ms_mem ms_of]. exact Hac'.
    - subst ms1. cbn [ms_mem ms_of]. eapply stack0_transport; [exact Xst0| exact MU| exact WM| exact SW].
    - subst ms1. cbn [ms_mem ms_of]. eapply (chain_via_munch H HH); [exact Xch| exact MU|]. intros fp' ra' Hin. specialize (XCH0 fp' ra' Hin).
      cbn [disjoint_from]. split; [| exact I]. right. clear - XCH0 K5 F2 Hhl Hlsp Hcs. unfold AFS_HDR, AFS_SIZE in *. slia0.
    - exact XCH0.
    - exact Xs0v.
    - exact Xpfo.
    - exact XAL.
    - exact XAL0.
    - exact XG.
    - (* [comment removed for export] *) apply Forall_forall. intros g Hg.
      pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & (rgg & Hgg & Hlog & Hleng & Hkg & Halg & Hdfg) & Hshg).
      pose proof (i63_range (g_tag g)) as Htg. pose proof (TG g Hg) as TGg.
      assert (Etg1 : to_Z (g_tag g + 1)%uint63 = to_Z (g_tag g) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; clear - Htg2 Htg Xn0b; slia0).
      split; [exact Hin|]. split; [exact Hrg|]. split; [exact Hsz|]. split; [exact Htg1|]. split; [exact Htg2|]. split.
      + exists rgg. rewrite IGET', (OLDX (g_tag g)) by (clear - TGg; slia0). split; [exact Hgg|]. repeat split; assumption.
      + intros rg' Hrg'. rewrite IGET', (OLDX (g_tag g + 1)%uint63) in Hrg' by (rewrite Etg1; clear - TGg; slia0).
        destruct (Hshg rg' Hrg') as (Erg' & Hrs & Had'). split; [exact Erg'|]. split; [exact Hrs|]. subst ms1. cbn [ms_mem ms_of].
        pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
        eapply addressable_transport; [exact Had'| exact MU| exact WM|]. cbn [disjoint_from]. split; [| exact I].
        pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE (g_addr g) (to_Z (g_size g)) F4 ltac:(clear - G1; slia0) ltac:(clear - G5 ACEILB; unfold AAPP_HI; slia0) G3) as D.
        clear - D K5. unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *. slia0.
    - exact XGnd.
    - exact XGtnd.
    - exact XGnew.
    - (* [comment removed for export] *) apply Forall_forall. intros g Hg. pose proof (proj1 (Forall_forall _ _) XGstk g Hg) as Hs. subst ms1. cbn [ms_mem ms_of].
      pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
      apply (stk_pres asegs (ms_mem ms)); [exact Hs|]. intros a Ha. apply Hkeep0; [clear - Ha G1 G5 ACEILB; slia0|].
      clear - Ha G6 K5. unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *. slia0.
    - (* [comment removed for export] *) rewrite XFF. subst FF' t. rewrite ff_remove_map. reflexivity.
    - (* [comment removed for export] *) apply Forall_forall. intros f Hf. destruct (HFF' f Hf) as [HfF Hnef]. pose proof (TF f Hf) as TFf.
      pose proof (proj1 (Forall_forall _ _) XFFin f HfF) as (Hfa & Hfb & Hfc & Hkf & Htg1 & Htg2 & (rgf & Hgf & Hlof & Hlenf & Hkdf & Half & Hdff) & (rgs & Hgs & Hlos & Hlens & Hks) & Hflg & X1 & X2 & X3 & X4).
      pose proof (i63_range (f_tag f)) as Htg.
      assert (Etg1 : to_Z (f_tag f + 1)%uint63 = to_Z (f_tag f) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; clear - Htg2 Htg Xn0b; slia0).
      assert (Etg2 : to_Z (f_tag f + 2)%uint63 = to_Z (f_tag f) + 2) by (rewrite to_Z_add_small; change (to_Z 2%uint63) with 2; clear - Htg2 Htg Xn0b; slia0).
      split; [exact Hfa|]. split; [exact Hfb|]. split; [exact Hfc|]. split; [exact Hkf|]. split; [exact Htg1|]. split; [exact Htg2|].
      split; [exists rgf; rewrite IGET', (OLDX (f_tag f)) by (clear - TFf; slia0); split; [exact Hgf|]; repeat split; assumption|].
      split; [exists rgs; rewrite IGET', (OLDX (f_tag f + 1)%uint63) by (rewrite Etg1; clear - TFf; slia0); split; [exact Hgs|]; repeat split; assumption|].
      split; [rewrite IGET', (OLDX (f_tag f + 2)%uint63) by (rewrite Etg2; clear - TFf; slia0); exact Hflg|].
      split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. exact X4.
    - (* [comment removed for export] *) subst FF'. apply gfdel_NoDup_app. exact XFFnd.
    - (* [comment removed for export] *) subst FF'. apply gfdel_NoDup_map. exact XFFtnd.
    - (* [comment removed for export] *) split; [exact S1| split].
      + intros g f Hg Hf. exact (S2 g f Hg (proj1 (HFF' f Hf))).
      + intros f f' Hf Hf' Hne. exact (S3 f f' (proj1 (HFF' f Hf)) (proj1 (HFF' f' Hf')) Hne).
    - (* [comment removed for export] *) clear - XFFlen FLEN. slia0.
    - exact XXS.
    - (* [comment removed for export] *) intros t' rg' Ht'. rewrite IGET' in Ht'. destruct (OLDREV t' rg' Ht') as (Ht'' & Nt0 & Nt1 & Nt2).
      destruct (Xdom t' rg' Ht'') as [H0' | [H1' | [H2' | [H3' | [Hb' | [Hbs' | [Hf' | [Hfs' | Hfl'']]]]]]]];
        [left; exact H0' | right; left; exact H1' | do 2 right; left; exact H2' | do 3 right; left; exact H3' | do 4 right; left; exact Hb' | do 5 right; left; exact Hbs' | ..].
      + do 6 right; left. apply in_map_iff in Hf' as (f & Ef & Hf). apply in_map_iff. exists f. split; [exact Ef|]. subst FF'. apply gfdel_keep; [exact Hf| intros E; apply Nt0; rewrite <- Ef, E; reflexivity].
      + do 7 right; left. apply in_map_iff in Hfs' as (f & Ef & Hf). apply in_map_iff. exists f. split; [exact Ef|]. subst FF'. apply gfdel_keep; [exact Hf| intros E; apply Nt1; rewrite <- Ef, E; reflexivity].
      + do 8 right. apply in_map_iff in Hfl'' as (f & Ef & Hf). apply in_map_iff. exists f. split; [exact Ef|]. subst FF'. apply gfdel_keep; [exact Hf| intros E; apply Nt2; rewrite <- Ef, E; reflexivity].
    - (* [comment removed for export] *) exists rg0. rewrite IGET', (OLDX 0%uint63) by (change (to_Z 0%uint63) with 0; clear - Htg01; slia0). split; [exact Hrg0|]. split; [exact Hlo0|]. split; [exact Hlen0|]. split; [exact Hd0| exact Hpg0].
    - (* [comment removed for export] *) exists rg1. rewrite IGET', (OLDX 1%uint63) by (change (to_Z 1%uint63) with 1; clear - Htg01; slia0). split; [exact Hrg1|]. repeat split; assumption.
    - (* [comment removed for export] *) rewrite IGET', (OLDX 2%uint63) by (change (to_Z 2%uint63) with 2; clear - Htg01; slia0). exact Xreg2.
    - (* [comment removed for export] *) rewrite IGET', (OLDX 3%uint63) by (change (to_Z 3%uint63) with 3; clear - Htg01; slia0). exact Xreg3.
    - (* [comment removed for export] *) destruct Xro as (rg0_ & Hrg0_ & Hroc). exists rg0_. rewrite IGET', (OLDX 0%uint63) by (change (to_Z 0%uint63) with 0; clear - Htg01; slia0). split; [exact Hrg0_| exact Hroc].
    - (* [comment removed for export] *) intros t' rg' pn p' ci c Ht' Hp' Hc. rewrite IGET' in Ht'. destruct (OLDREV t' rg' Ht') as (Ht'' & _). exact (Xinb t' rg' pn p' ci c Ht'' Hp' Hc).
    - (* [comment removed for export] *) intros t' rg' Ht' Ht'0. rewrite IGET' in Ht'. destruct (OLDREV t' rg' Ht') as (Ht'' & _). exact (Xkinds t' rg' Ht'' Ht'0).
    - exact Xcost.
    - exact Xcnt.
    - (* [comment removed for export] *) subst ms1. cbn [ms_mem ms_of]. apply (stk_pres asegs (ms_mem ms)); [exact Xstk|]. intros a Ha. destruct Xstk as (_ & Hhi64 & _).
      apply Hkeep0; [clear - Ha Hhi64 Hhl ACEILB; slia0|]. clear - Ha K5 F2 Hhl Hlsp Hcs. unfold AFS_HDR, AFS_SIZE in *. slia0.
    - repeat split; assumption.
    - subst ms1. cbn [ms_mem ms_of]. eapply (ah_rauxv_frame H HH); [exact Xaux| exact MU| exact WM| exact CW].
    - subst ms1. cbn [ms_mem ms_of]. exact Hinv'.
    - subst ms1. cbn [ms_mem ms_of]. destruct (HK_err A HK) as (Eerr & _). pose proof (i63_range (c_errbi K)) as EB1. pose proof (i63_range (c_errcell K)) as EB2.
      apply (stk_pres asegs (ms_mem ms)); [exact Xerr|]. intros a Ha. apply Hkeep0; [clear - Ha Eerr EB1 EB2; unfold errA, AERRNO, ATP in *; slia0|].
      clear - Ha Eerr EB1 EB2 K5 F1. unfold errA, AERRNO, ATP, AIMG_TOP, AFS_FLAGS in *. slia0.
    - subst ms1. cbn [ms_mem ms_of]. exact (HSH0 _ Hac' Hinv').
    - exact XLB0.
    - exact XLB0h.
    - split; [exact XG0in | exact XLB0nd].
    - exact XLBsub.
    - (* [comment removed for export] *) subst ms1. cbn [ms_mem ms_of]. intros a Ha Hcl Hna Hnx Hne Hnxs. rewrite <- (Xframe a Ha Hcl Hna Hnx Hne Hnxs).
      apply (proj1 (Hkeep0 a Ha ltac:(intros ->; exact (Hnxs X04)))).
    - (* [comment removed for export] *) subst ms1. cbn [ms_mem ms_of]. apply Forall_forall. intros f__ Hf__. destruct (HFF' f__ Hf__) as [HfF__ Hnef__].
      pose proof (proj1 (Forall_forall _ _) XFFstk f__ HfF__) as HsF.
      destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X HfF__) as [(KF1 & KF2 & KF3 & KF4 & KF5) _]. pose proof (fsz_pos (to_Z (f_k f__)) ltac:(clear - KF1; slia0)) as FPf.
      destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf0) as [(K01 & K02 & K03 & K04 & K05) (FB1 & FB2 & FB3' & FB4')].
      apply (stk_pres asegs (ms_mem ms)); [exact HsF|]. intros a__ Ha__.
      apply Hkeep0; [clear - Ha__ KF2 KF3 FB1 FB2 FPf ACEILB; unfold AFS_HDR, AIMG_TOP in *; slia0| clear - Ha__ KF2 K05; unfold AFS_FLAGS, AFS_HDR in *; slia0].
  Qed.
End NodeS.
