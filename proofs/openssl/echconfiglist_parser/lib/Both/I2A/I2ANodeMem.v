(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prog.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain
  FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom I2Canon I2Mach I2Image I2Run I2RunA FxGeomA.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import I2AInv I2ANodeLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia := Zify.zify; xlia zchecker.

(* [comment removed for export] *)
Definition gblock_range (A n : Z) : Prop := 0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n < 2 ^ 47 /\ True.

Section Mem.
  Variable segs : list Segment.
  Variable IM : fimage.
  Variable rho : int -> word.
  Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.

  (* [comment removed for export] *)
  Definition mem_part (m : word -> option byte) (t : int) (rg : region) : Prop :=
    region_ok rho t rg
    /\ forall pn p, to_Z pn < 2 ^ 50 -> page_at IM rg t pn = Some p ->
         page_ok segs IM rho m t pn (blim rg pn) p
         /\ to_Z (rg_lo rg) <= to_Z pn * 4096 /\ to_Z pn * 4096 < to_Z (rg_len rg).

  Lemma mem_ok_parts : forall M m,
    (forall t rg, iget t M = Some rg -> mem_part m t rg) -> regions_sep rho M -> mem_ok segs IM rho M m.
  Proof. intros M m H Hs. split; [exact H | exact Hs]. Qed.

  Lemma mem_part_of : forall M m t rg, mem_ok segs IM rho M m -> iget t M = Some rg -> mem_part m t rg.
  Proof. intros M m t rg [H _] Ht. exact (H t rg Ht). Qed.

  (* [comment removed for export] *)
  Lemma clim8_le : forall rg pn, to_Z pn * 4096 < to_Z (rg_len rg) -> blim rg pn <= to_Z (rg_len rg) - to_Z pn * 4096.
  Proof. intros rg pn H. unfold blim. slia. Qed.
  Lemma clim8_le_page : forall rg pn, blim rg pn <= 4096.
  Proof. intros rg pn. unfold blim. slia. Qed.
  Lemma clim_nonneg : forall rg pn, to_Z pn * 4096 < to_Z (rg_len rg) -> 0 <= blim rg pn.
  Proof. intros rg pn H. unfold blim. slia. Qed.

  Lemma adr_eq_wa : forall t A z, rho t = wa A -> 0 <= A -> 0 <= z -> A + z < 2 ^ 64 -> adr rho t z = wa (A + z).
  Proof.
    intros t A z Ht HA Hz Hlt. apply bv_eq. rewrite (adr_wa rho t A z Ht HA Hz Hlt). rewrite wa_unsigned by slia. reflexivity.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mem_part_transfer : forall m m' t rg A,
    rho t = wa A -> 0 <= A -> A + to_Z (rg_len rg) < 2 ^ 64 ->
    (forall a, A + to_Z (rg_lo rg) <= a < A + to_Z (rg_len rg) ->
        rview segs m' (wa a) = rview segs m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)) ->
    (forall pn sg, find_seg IM (pn << 12)%uint63 = Some sg -> t <> 0%uint63) ->
    mem_part m t rg -> mem_part m' t rg.
  Proof.
    intros m m' t rg A Ht HA Hlen Hm Hnoimg [Hro Hpages]. split; [exact Hro|].
    intros pn p Hpn Hp. destruct (Hpages pn p Hpn Hp) as (Hok & Hlo & Hlt).
    split; [|split; [exact Hlo | exact Hlt]].
    pose proof (i63_range pn). pose proof (i63_range (rg_lo rg)).
    pose proof (clim8_le rg pn Hlt) as Hcl.
    eapply page_ok_transfer; [|exact Hok].
    intros j Hj. rewrite (adr_eq_wa t A (to_Z pn * 4096 + j) Ht) by slia.
    exact (Hm (A + (to_Z pn * 4096 + j)) ltac:(slia)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Context {HCEIL : HeapCeil}.

  Lemma blk_region_part : forall m t n al A,
    rho t = wa A -> t <> 0%uint63 -> to_Z t < 2 ^ 60 ->
    gblock_range A (to_Z n) -> A mod 2 ^ to_Z al = 0 -> 0 <= to_Z al ->
    to_Z n < 2 ^ 40 ->
    wr_at segs m A (to_Z n) ->
    mem_part m t (blk_region n al iempty).
  Proof.
    intros m t n al A Ht Ht0 Hpl (R1 & R2 & R3 & R4 & R5) Hal Hal0 Hn Hrw.
    pose proof hceil_lt_2p47. pose proof (i63_range n).
    assert (HuA : bv_unsigned (rho t) = A) by (rewrite Ht; apply wa_unsigned; slia).
    split.
    - (* [comment removed for export] *)
      unfold region_ok, blk_region. cbn [rg_len rg_lo rg_align rg_clo rg_chi rg_kind]. rewrite HuA.
      change (to_Z 0%uint63) with 0. unfold clo_dflt, chi_dflt. change (to_Z 0) with 0. change (to_Z 9223372036854775807) with (2 ^ 63 - 1).
      repeat split; try slia; try exact Hal.
    - intros pn p Hpn Hp. unfold page_at, blk_region in Hp. cbn [rg_pages rg_dflt] in Hp. rewrite iget_iempty in Hp.
      destruct (t =? 0)%uint63 eqn:Et; [apply Uint63.eqb_spec in Et; congruence|].
      destruct (page_in_region (RGK 0 n al (Some PKUnk) iempty clo_dflt chi_dflt RK_plain) pn) eqn:Hpir; [|discriminate].
      injection Hp as <-.
      destruct (page_in_region_spec _ _ Hpir) as (_ & Hlo & Hlt & _). cbn [rg_lo rg_len] in Hlo, Hlt |- *.
      change (to_Z 0%uint63) with 0 in Hlo |- *.
      split; [| split; [exact Hlo | exact Hlt]].
      apply page_ok_dflt. intros j Hj. pose proof (i63_range pn). unfold blk_region in Hj.
      pose proof (clim8_le (RGK 0%uint63 n al (Some PKUnk) iempty clo_dflt chi_dflt RK_plain) pn Hlt) as Hcl. cbn [rg_len] in Hcl.
      destruct Hrw as (W0 & W1 & W).
      rewrite (adr_eq_wa t A (to_Z pn * 4096 + j) Ht) by slia.
      apply W. slia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma keep_cells_ge_inv : forall ci0 cells ci c,
    iget ci (keep_cells_ge ci0 cells) = Some c -> to_Z ci0 <= to_Z ci /\ iget ci cells = Some c.
  Proof.
    intros ci0 cells ci c H. unfold keep_cells_ge in H.
    destruct (iget_iof_list_map_In fst snd _ _ _ H) as ([k v] & Hin & Hk & ->). cbn [fst snd] in Hk |- *. subst k.
    apply filter_In in Hin as [Hin Hge]. cbn [fst] in Hge. apply Uint63.leb_spec in Hge.
    split; [exact Hge|]. apply (proj1 (ielements_spec _ _ _)). exact Hin.
  Qed.

  Lemma drop_below_pages_inv : forall off rg pn p',
    iget pn (rg_pages (drop_below off rg)) = Some p' ->
    exists p, iget pn (rg_pages rg) = Some p /\ to_Z (off >> 12)%uint63 <= to_Z pn
              /\ p' = drop_page (off >> 12)%uint63 ((off land 4095) >> 3)%uint63 (pn, p).
  Proof.
    intros off rg pn p' H. unfold drop_below in H. cbn [rg_pages] in H.
    destruct (iget_iof_list_map_In fst (fun pp => drop_page (off >> 12)%uint63 ((off land 4095) >> 3)%uint63 pp) _ _ _ H)
      as ([k v] & Hin & Hk & ->). cbn [fst] in Hk. subst k.
    apply filter_In in Hin as [Hin Hge]. cbn [fst] in Hge. apply Uint63.leb_spec in Hge.
    exists v. split; [apply (proj1 (ielements_spec _ _ _)); exact Hin|]. split; [exact Hge | reflexivity].
  Qed.

  Lemma drop_below_geom : forall off rg, same_geom rg (drop_below off rg).
  Proof. intros. unfold drop_below. repeat split; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma page_at_drop_below : forall off rg t pn p',
    t <> 0%uint63 ->
    page_at IM (drop_below off rg) t pn = Some p' ->
    (exists p, iget pn (rg_pages rg) = Some p /\ to_Z (off >> 12)%uint63 <= to_Z pn
               /\ p' = drop_page (off >> 12)%uint63 ((off land 4095) >> 3)%uint63 (pn, p))
    \/ (exists k, rg_dflt rg = Some k /\ page_in_region rg pn = true /\ p' = PG true k iempty
                  /\ (page_at IM rg t pn = Some p' \/ (exists p, iget pn (rg_pages rg) = Some p))).
  Proof.
    intros off rg t pn p' Ht H. unfold page_at in H.
    destruct (iget pn (rg_pages (drop_below off rg))) as [p0|] eqn:E.
    - injection H as <-. left. exact (drop_below_pages_inv _ _ _ _ E).
    - destruct (t =? 0)%uint63 eqn:Et; [apply Uint63.eqb_spec in Et; congruence|].
      assert (Epir : page_in_region (drop_below off rg) pn = page_in_region rg pn) by reflexivity.
      assert (Edf : rg_dflt (drop_below off rg) = rg_dflt rg) by reflexivity.
      rewrite Edf, Epir in H.
      destruct (rg_dflt rg) as [k|] eqn:Ek; [|discriminate].
      destruct (page_in_region rg pn) eqn:Hpir; [|discriminate]. injection H as <-.
      right. exists k. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      unfold page_at. destruct (iget pn (rg_pages rg)) as [p|] eqn:Ep; [right; exists p; reflexivity|].
      left. rewrite Et, Ek, Hpir. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma stack_part : forall m m' rg1 off S lo sp0,
    rho 1%uint63 = wa S ->
    rg_lo rg1 = 0%uint63 -> rg_dflt rg1 = Some PKUnk ->
    (forall pn p, iget pn (rg_pages rg1) = Some p -> pg_kind p = PKUnk) ->
    S = sp0 - to_Z (rg_len rg1) ->
    0 <= to_Z off <= to_Z (rg_len rg1) -> to_Z off mod 8 = 0 ->
    mem_part m 1%uint63 rg1 ->
    stk segs m lo sp0 -> 0 <= lo <= S ->
    stk segs m' lo (S + to_Z off) ->
    (forall a, S + to_Z off <= a < sp0 -> rview segs m' (wa a) = rview segs m (wa a)
                                        /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)) ->
    mem_part m' 1%uint63 (drop_below off rg1).
  Proof.
    intros m m' rg1 off S lo sp0 H1 Hlo1 Hd1 Hk1 HS Hoff Hoff8 [Hro Hpages] Hstk Hlo Hstk' Hhi.
    pose proof (i63_range (rg_len rg1)) as Hlen. pose proof (i63_range off).
    destruct Hstk as (_ & Hsp0 & Hstkm). destruct Hstk' as (_ & _ & Hstkm').
    assert (Hwr : forall a, S <= a < sp0 -> wview segs m' (wa a) <> None).
    { intros a Ha. destruct (Z.lt_ge_cases a (S + to_Z off)).
      - apply (proj1 (Hstkm' a ltac:(slia))).
      - apply (proj2 (Hhi a ltac:(slia))). apply (proj1 (Hstkm a ltac:(slia))). }
    assert (Hrv : forall a, S + to_Z off <= a < sp0 -> rview segs m' (wa a) = rview segs m (wa a)).
    { intros a Ha. exact (proj1 (Hhi a Ha)). }
    split.
    { (* [comment removed for export] *) exact Hro. }
    intros pn p' Hpn Hp'. pose proof (i63_range pn).
    assert (Egeo : blim (drop_below off rg1) pn = blim rg1 pn) by reflexivity. rewrite Egeo.
    cbn [drop_below rg_lo rg_len].
    destruct (page_at_drop_below off rg1 1%uint63 pn p' ltac:(intros E; discriminate E) Hp')
      as [(p & Hp & Hge & ->) | (k & Hk & Hpir & -> & Hold)].
    - (* [comment removed for export] *)
      assert (Hpa : page_at IM rg1 1%uint63 pn = Some p) by (unfold page_at; rewrite Hp; reflexivity).
      destruct (Hpages pn p Hpn Hpa) as (Hok & Hlo' & Hlt).
      split; [| split; [exact Hlo' | exact Hlt]].
      pose proof (clim8_le rg1 pn Hlt) as Hcl. pose proof (clim_nonneg rg1 pn Hlt).
      unfold drop_page. cbn [fst snd].
      destruct (pn =? (off >> 12))%uint63 eqn:Epn.
      + (* [comment removed for export] *)
        apply Uint63.eqb_spec in Epn.
        assert (Epn4 : to_Z pn * 4096 = to_Z off - to_Z off mod 4096).
        { subst pn. rewrite to_Z_lsr12. Z.div_mod_to_equations. slia. }
        destruct Hok as (Hokw & Hokc & Hoks & Hokcut). split; [|split; [|split]].
        * intros _ j Hj. rewrite (adr_eq_wa 1%uint63 S (to_Z pn * 4096 + j) H1) by slia. apply Hwr. slia.
        * intros ci v Hci Hc j Hj. unfold cell_at in Hc. cbn [pg_cells pg_kind] in Hc.
          destruct (iget ci (keep_cells_ge ((off land 4095) >> 3) (pg_cells p))) as [c|] eqn:Eg.
          -- destruct (keep_cells_ge_inv _ _ _ _ Eg) as [Hcige Hc0].
             rewrite to_Z_lsr3, to_Z_land4095 in Hcige. pose proof (i63_range ci).
             assert (Hci8 : to_Z off - to_Z off mod 4096 + to_Z ci * 8 >= to_Z off).
             { pose proof (Z.mod_pos_bound (to_Z off) 4096 ltac:(slia)). Z.div_mod_to_equations. nia. }
             assert (Hcb : to_Z ci * 8 + Z.of_nat j < blim rg1 pn) by (clear -Hci Hj; Z.div_mod_to_equations; slia).
             rewrite (adr_eq_wa 1%uint63 S _ H1) by slia. rewrite Hrv by slia. rewrite <- (adr_eq_wa 1%uint63 S _ H1) by slia.
             apply (Hokc ci v Hci); [|exact Hj]. unfold cell_at. rewrite Hc0. destruct c as [v0| |sl0]; [exact Hc | discriminate | discriminate].
          -- rewrite (Hk1 pn p Hp) in Hc. discriminate.
        * intros ci sl Hci Hcib Hg j Hj. cbn [pg_cells] in Hg.
          destruct (keep_cells_ge_inv _ _ _ _ Hg) as [Hcige Hc0].
          rewrite to_Z_lsr3, to_Z_land4095 in Hcige. pose proof (i63_range ci).
          assert (Hci8 : to_Z off - to_Z off mod 4096 + to_Z ci * 8 >= to_Z off).
          { pose proof (Z.mod_pos_bound (to_Z off) 4096 ltac:(slia)). Z.div_mod_to_equations. nia. }
          destruct (Hoks ci sl Hci Hcib Hc0 j Hj) as [Hin Hout]. split; [|exact Hout]. intros Hjb. specialize (Hin Hjb).
          rewrite slot_ok_val. rewrite (adr_eq_wa 1%uint63 S _ H1) by slia. rewrite Hrv by slia.
          rewrite <- (adr_eq_wa 1%uint63 S _ H1) by slia. rewrite <- slot_ok_val. exact Hin.
        * intros ci Hci Hcut. specialize (Hokcut ci Hci Hcut). unfold cell_at in Hokcut |- *. cbn [pg_cells pg_kind].
          rewrite (Hk1 pn p Hp) in Hokcut.
          destruct (iget ci (keep_cells_ge ((off land 4095) >> 3) (pg_cells p))) as [c|] eqn:Eg; [|rewrite (Hk1 pn p Hp); reflexivity].
          destruct (keep_cells_ge_inv _ _ _ _ Eg) as [_ Hc0]. rewrite Hc0 in Hokcut. exact Hokcut.
      + (* [comment removed for export] *)
        assert (Hgt : to_Z (off >> 12)%uint63 < to_Z pn).
        { destruct (Z.eq_dec (to_Z (off >> 12)%uint63) (to_Z pn)) as [E|]; [|slia]. exfalso.
          apply to_Z_inj in E. subst pn. rewrite Uint63.eqb_refl in Epn. discriminate. }
        rewrite to_Z_lsr12 in Hgt.
        assert (Habove : to_Z off <= to_Z pn * 4096) by (Z.div_mod_to_equations; nia).
        eapply page_ok_transfer; [|exact Hok]. intros j Hj.
        rewrite (adr_eq_wa 1%uint63 S (to_Z pn * 4096 + j) H1) by slia. split; [apply Hrv; slia|].
        intros _. apply Hwr. slia.
    - (* [comment removed for export] *)
      destruct (page_in_region_spec _ _ Hpir) as (_ & Hlo' & Hlt & _).
      split; [| split; [exact Hlo' | exact Hlt]].
      rewrite Hd1 in Hk. injection Hk as <-.
      pose proof (clim8_le rg1 pn Hlt) as Hcl.
      apply page_ok_dflt. intros j Hj.
      rewrite (adr_eq_wa 1%uint63 S (to_Z pn * 4096 + j) H1) by slia. apply Hwr. slia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable IMX : fimage.
  Hypothesis HIM : IM = im_ro IMX.
  Hypothesis HIMX : image_ok segs IMX.
  Hypothesis HWRX : image_wr_ok IMX.

  Lemma IM_ok : image_ok segs IM. Proof. rewrite HIM. apply im_ro_ok. exact HIMX. Qed.
  Lemma IM_wr_ok : image_wr_ok IM. Proof. rewrite HIM. apply im_ro_wr_ok. exact HWRX. Qed.

  (* [comment removed for export] *)
  Lemma ro_seg_clear : forall m sg a,
    mem_inv segs m -> In sg IM -> to_Z (sg_base sg) <= a < to_Z (sg_base sg) + to_Z (sg_size sg) ->
    m (Z_to_bv 64 a) = None.
  Proof.
    intros m sg a Hinv Hin Ha.
    pose proof (proj1 (Forall_forall _ _) IM_ok sg Hin) as (seg & Hseg & Eb & Es & _ & _ & Ew & _ & _ & Hle & Hfind).
    assert (Hw : sg_wr sg = false).
    { rewrite HIM in Hin. unfold im_ro in Hin. apply filter_In in Hin as [_ Hn]. destruct (sg_wr sg); [discriminate | reflexivity]. }
    destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [|reflexivity]. exfalso.
    pose proof (Hinv _ _ E) as Hro. unfold ro_addr in Hro.
    pose proof (i63_range (sg_base sg)). pose proof (i63_range (sg_size sg)).
    rewrite Z_to_bv_unsigned in Hro. unfold bv_wrap in Hro. change (bv_modulus 64) with (2 ^ 64) in Hro.
    rewrite Z.mod_small in Hro by slia. rewrite (Hfind a Ha), Ew, Hw in Hro. discriminate.
  Qed.

  Lemma region0_part : forall (KK : i2consts) m m' rg0 p te (ev : word) (keep : Z -> Prop),
    mem_part m 0%uint63 rg0 ->
    rg_dflt rg0 = None ->
    (forall pn p, iget pn (rg_pages rg0) = Some p -> seg_wr_page IMX pn = true /\ pg_kind p = PKUnk) ->
    (forall pn p ci c, iget pn (rg_pages rg0) = Some p -> iget ci (pg_cells p) = Some c ->
        keep (to_Z pn * 4096 + to_Z ci * 8) \/ to_Z pn * 4096 + to_Z ci * 8 = to_Z (c_errcell KK)
        \/ (exists sl, c = CB sl /\ forall j : int, 0 <= to_Z j < 8 ->
                          slot_val rho (sget j sl) (rview segs m' (wa (to_Z pn * 4096 + to_Z ci * 8 + to_Z j))))) ->
    (forall c a, keep c -> c <= a < c + 8 -> rview segs m' (wa a) = rview segs m (wa a)) ->
    iget (c_errcell KK >> 12)%uint63 (rg_pages rg0) = Some p ->
    mem_inv segs m' ->
    rw_cells segs m' (to_Z (c_errcell KK) + to_Z (c_errbi KK)) [C4 ev] ->
    dv rho (FV te w_zero) = ev ->
    to_Z (c_errcell KK) mod 8 = 0 -> to_Z (c_errbi KK) + 4 <= 8 -> to_Z (c_errcell KK) + 8 <= to_Z (rg_len rg0) ->
    to_Z (rg_len rg0) mod 4096 = 0 ->
    mem_part m' 0%uint63 (err_region KK te rg0 p).
  Proof.
    intros KK m m' rg0 p te ev keep [Hro Hpages] Hdf Hpg Hcells Hkeep Hpe Hinv Herr Hev He8 Hbi Hein Hlen4096.
    pose proof (i63_range (c_errcell KK)) as Hec. pose proof (i63_range (c_errbi KK)) as Heb. pose proof (i63_range (rg_len rg0)).
    set (pne := (c_errcell KK >> 12)%uint63). set (cie := ((c_errcell KK land 4095) >> 3)%uint63).
    assert (Epne : to_Z pne = to_Z (c_errcell KK) / 4096) by (subst pne; apply to_Z_lsr12).
    assert (Ecie : to_Z cie = (to_Z (c_errcell KK) mod 4096) / 8) by (subst cie; rewrite to_Z_lsr3, to_Z_land4095; reflexivity).
    assert (Ecell : to_Z pne * 4096 + to_Z cie * 8 = to_Z (c_errcell KK)).
    { rewrite Epne, Ecie. Z.div_mod_to_equations. nia. }
    split.
    { exact Hro. }
    intros pn p' Hpn Hp'. pose proof (i63_range pn).
    assert (Ecl : blim (err_region KK te rg0 p) pn = blim rg0 pn) by reflexivity. rewrite Ecl.
    unfold err_region in Hp' |- *. cbn [rg_lo rg_len rg_pages rg_dflt] in Hp' |- *.
    unfold page_at in Hp'. cbn [rg_pages rg_dflt] in Hp'. rewrite iget_iset in Hp'.
    destruct (pn =? c_errcell KK >> 12)%uint63 eqn:Epn.
    - (* [comment removed for export] *)
      apply Uint63.eqb_spec in Epn. injection Hp' as <-. fold pne in Epn. subst pn.
      assert (Hpa : page_at IM rg0 0%uint63 pne = Some p) by (unfold page_at; fold pne in Hpe; rewrite Hpe; reflexivity).
      destruct (Hpages pne p Hpn Hpa) as (Hok & Hlo' & Hlt).
      split; [| split; [exact Hlo' | exact Hlt]].
      pose proof (clim8_le rg0 pne Hlt) as Hcl. pose proof (clim_nonneg rg0 pne Hlt).
      fold pne in Hpe. destruct (Hpg pne p Hpe) as [Hsw Hkind].
      destruct Hok as (Hokw & Hokc & Hoks & Hokcut).
      assert (Hbl : blim rg0 pne = 4096) by (unfold blim; rewrite Epne; clear -Hlt Hlen4096 Hec Epne; rewrite Epne in Hlt; Z.div_mod_to_equations; nia).
      split; [|split; [|split]].
      4:{ (* [comment removed for export] *) intros ci Hci Hcut. exfalso. rewrite Hbl in Hcut. slia. }
      + (* [comment removed for export] *)
        intros _ j Hj. cbn [pg_wr].
        unfold seg_wr_page in Hsw. destruct (find_seg IMX (pne << 12)%uint63) as [sg|] eqn:Hsg; [|discriminate].
        rewrite (adr_eq_wa 0%uint63 0 _ ltac:(rewrite Hrho0; reflexivity)) by (pose proof (clim8_le_page rg0 pne); slia).
        rewrite Z.add_0_l. unfold wa.
        exact (wview_image_wr segs IMX HIMX HWRX (MS (mkRl []) (mkRl []) (Z_to_bv 64 0) (Z_to_bv 32 0) None m' m') pne sg j Hpn Hsg Hsw ltac:(pose proof (clim8_le_page rg0 pne); slia)).
      + (* [comment removed for export] *)
        intros ci v Hci Hc j Hj. pose proof (i63_range ci).
        unfold cell_at in Hc. cbn [pg_cells pg_kind] in Hc. rewrite iget_iset in Hc.
        destruct (ci =? (c_errcell KK land 4095) >> 3)%uint63 eqn:Eci; [discriminate|].
        destruct (iget ci (pg_cells p)) as [c|] eqn:Hc0; [| rewrite Hkind in Hc; discriminate].
        destruct (Hcells pne p ci c Hpe Hc0) as [Hk | [Heq | (slx & Ecx & _)]].
        * rewrite (adr_eq_wa 0%uint63 0 _ ltac:(rewrite Hrho0; reflexivity)) by slia. rewrite Z.add_0_l.
          rewrite (Hkeep _ _ Hk) by slia.
          rewrite <- (Z.add_0_l (to_Z pne * 4096 + to_Z ci * 8 + Z.of_nat j)).
          rewrite <- (adr_eq_wa 0%uint63 0 _ ltac:(rewrite Hrho0; reflexivity)) by slia.
          apply (Hokc ci v Hci); [|exact Hj]. unfold cell_at. rewrite Hc0. exact Hc.
        * exfalso. fold cie in Eci. assert (ci = cie); [|subst ci; rewrite Uint63.eqb_refl in Eci; discriminate].
          apply to_Z_inj. slia.
        * exfalso. rewrite Ecx in Hc. discriminate.
      + (* [comment removed for export] *)
        intros ci sl Hci Hcib Hg j Hj. pose proof (i63_range ci). pose proof (i63_range j).
        split; [intros Hjb | intros Hjb; exfalso; rewrite Hbl in Hjb, Hcib; clear -Hjb Hcib Hj Hci; slia].
        cbn [pg_cells] in Hg. rewrite iget_iset in Hg.
        destruct (ci =? (c_errcell KK land 4095) >> 3)%uint63 eqn:Eci.
        * (* [comment removed for export] *)
          apply Uint63.eqb_spec in Eci. fold cie in Eci. subst ci. injection Hg as <-.
          rewrite slot_ok_val.
          unfold err_cell.
          (* [comment removed for export] *)
          assert (Esg : forall s0 s1 s2 s3 s4 s5 s6 s7,
                    sget j (SL s0 s1 s2 s3 s4 s5 s6 s7) = nth (Z.to_nat (to_Z j)) [s0; s1; s2; s3; s4; s5; s6; s7] SU).
          { intros. destruct (int_cases8 j Hj) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; reflexivity. }
          rewrite Esg.
          assert (Enth : nth (Z.to_nat (to_Z j)) [err_slot KK te 0; err_slot KK te 1; err_slot KK te 2; err_slot KK te 3;
                                            err_slot KK te 4; err_slot KK te 5; err_slot KK te 6; err_slot KK te 7]%uint63 SU
                         = err_slot KK te j).
          { destruct (int_cases8 j Hj) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; reflexivity. }
          rewrite Enth. unfold err_slot.
          destruct ((c_errbi KK <=? j) && (j <? c_errbi KK + 4))%uint63 eqn:Erange; [|exact I].
          apply andb_true_iff in Erange as [E1 E2]. apply Uint63.leb_spec in E1. apply Uint63.ltb_spec in E2.
          rewrite Uint63.add_spec in E2. change (to_Z 4%uint63) with 4 in E2. change wB with (2 ^ 63) in E2. rewrite Z.mod_small in E2 by slia.
          cbn [slot_val]. rewrite Hev.
          rewrite (adr_eq_wa 0%uint63 0 _ ltac:(rewrite Hrho0; reflexivity)) by slia. rewrite Z.add_0_l, Ecell.
          destruct Herr as [[_ (B0 & B1 & Hb)] _]. cbn [cells_bytes cbytes] in B1, Hb. rewrite app_nil_r in B1, Hb.
          rewrite length_le4 in B1, Hb.
          specialize (Hb (Z.to_nat (to_Z j - to_Z (c_errbi KK))) ltac:(slia)).
          replace (to_Z (c_errcell KK) + to_Z (c_errbi KK) + Z.of_nat (Z.to_nat (to_Z j - to_Z (c_errbi KK)))) with (to_Z (c_errcell KK) + to_Z j) in Hb by slia.
          unfold mrd in Hb. unfold rview. cbn [PropExec.seg_rom] in Hb.
          rewrite Uint63.sub_spec. change wB with (2 ^ 63). rewrite Z.mod_small by slia.
          rewrite <- (nth_error_le4_le8 ev (Z.to_nat (to_Z j - to_Z (c_errbi KK))) ltac:(slia)). rewrite <- Hb. unfold PropExec.seg_rom. reflexivity.
        * destruct (Hcells pne p ci (CB sl) Hpe Hg) as [Hk | [Heq | (slx & Ecx & Hpin)]].
          -- rewrite slot_ok_val. rewrite (adr_eq_wa 0%uint63 0 _ ltac:(rewrite Hrho0; reflexivity)) by slia. rewrite Z.add_0_l.
             rewrite (Hkeep _ _ Hk) by slia.
             rewrite <- (Z.add_0_l (to_Z pne * 4096 + to_Z ci * 8 + to_Z j)).
             rewrite <- (adr_eq_wa 0%uint63 0 _ ltac:(rewrite Hrho0; reflexivity)) by slia.
             rewrite <- slot_ok_val. exact (proj1 (Hoks ci sl Hci Hcib Hg j Hj) Hjb).
          -- exfalso. fold cie in Eci. assert (ci = cie); [|subst ci; rewrite Uint63.eqb_refl in Eci; discriminate].
             apply to_Z_inj. slia.
          -- (* [comment removed for export] *)
             injection Ecx as <-.
             rewrite slot_ok_val. rewrite (adr_eq_wa 0%uint63 0 _ ltac:(rewrite Hrho0; reflexivity)) by slia. rewrite Z.add_0_l.
             exact (Hpin j Hj).
    - (* [comment removed for export] *)
      destruct (iget pn (rg_pages rg0)) as [p0|] eqn:Hp0.
      + injection Hp' as <-.
        assert (Hpa : page_at IM rg0 0%uint63 pn = Some p0) by (unfold page_at; rewrite Hp0; reflexivity).
        destruct (Hpages pn p0 Hpn Hpa) as (Hok & Hlo' & Hlt).
        split; [| split; [exact Hlo' | exact Hlt]].
        pose proof (clim8_le rg0 pn Hlt) as Hcl. pose proof (clim_nonneg rg0 pn Hlt).
        destruct (Hpg pn p0 Hp0) as [Hsw Hkind]. destruct Hok as (Hokw & Hokc & Hoks & Hokcut).
        split; [|split; [|split]].
        4:{ exact Hokcut. }
        * intros Hw j Hj.
          unfold seg_wr_page in Hsw. destruct (find_seg IMX (pn << 12)%uint63) as [sg|] eqn:Hsg; [|discriminate].
          rewrite (adr_eq_wa 0%uint63 0 _ ltac:(rewrite Hrho0; reflexivity)) by (pose proof (clim8_le_page rg0 pn); slia).
          rewrite Z.add_0_l. unfold wa.
          exact (wview_image_wr segs IMX HIMX HWRX (MS (mkRl []) (mkRl []) (Z_to_bv 64 0) (Z_to_bv 32 0) None m' m') pn sg j Hpn Hsg Hsw ltac:(pose proof (clim8_le_page rg0 pn); slia)).
        * intros ci v Hci Hc j Hj. pose proof (i63_range ci).
          unfold cell_at in Hc.
          destruct (iget ci (pg_cells p0)) as [c|] eqn:Hc0; [| rewrite Hkind in Hc; discriminate].
          destruct (Hcells pn p0 ci c Hp0 Hc0) as [Hk | [Heq | (slx & Ecx & _)]].
          -- rewrite (adr_eq_wa 0%uint63 0 _ ltac:(rewrite Hrho0; reflexivity)) by slia. rewrite Z.add_0_l.
             rewrite (Hkeep _ _ Hk) by slia.
             rewrite <- (Z.add_0_l (to_Z pn * 4096 + to_Z ci * 8 + Z.of_nat j)).
             rewrite <- (adr_eq_wa 0%uint63 0 _ ltac:(rewrite Hrho0; reflexivity)) by slia.
             apply (Hokc ci v Hci); [|exact Hj]. unfold cell_at. rewrite Hc0. exact Hc.
          -- exfalso. (* [comment removed for export] *)
             pose proof (clim_le rg0 pn) as HclX. unfold clim in HclX.
             assert (pn = pne); [|subst pn; subst pne; rewrite Uint63.eqb_refl in Epn; discriminate].
             apply to_Z_inj. rewrite Epne. Z.div_mod_to_equations. nia.
          -- exfalso. rewrite Ecx in Hc. discriminate.
        * intros ci sl Hci Hcib Hg j Hj. pose proof (i63_range ci). pose proof (i63_range j).
          destruct (Hoks ci sl Hci Hcib Hg j Hj) as [Hin Hout]. split; [intros Hjb; specialize (Hin Hjb) | exact Hout].
          destruct (Hcells pn p0 ci (CB sl) Hp0 Hg) as [Hk | [Heq | (slx & Ecx & Hpin)]].
          -- rewrite slot_ok_val. rewrite (adr_eq_wa 0%uint63 0 _ ltac:(rewrite Hrho0; reflexivity)) by slia. rewrite Z.add_0_l.
             rewrite (Hkeep _ _ Hk) by slia.
             rewrite <- (Z.add_0_l (to_Z pn * 4096 + to_Z ci * 8 + to_Z j)).
             rewrite <- (adr_eq_wa 0%uint63 0 _ ltac:(rewrite Hrho0; reflexivity)) by slia.
             rewrite <- slot_ok_val. exact Hin.
          -- exfalso. pose proof (blim_le rg0 pn) as HblX.
             assert (pn = pne); [|subst pn; subst pne; rewrite Uint63.eqb_refl in Epn; discriminate].
             apply to_Z_inj. rewrite Epne. Z.div_mod_to_equations. nia.
          -- injection Ecx as <-.
             rewrite slot_ok_val. rewrite (adr_eq_wa 0%uint63 0 _ ltac:(rewrite Hrho0; reflexivity)) by slia. rewrite Z.add_0_l.
             exact (Hpin j Hj).
      + (* [comment removed for export] *)
        change (0 =? 0)%uint63 with true in Hp'. cbv iota in Hp'.
        destruct (find_seg IM (pn << 12)%uint63) as [sg|] eqn:Hsg; [| rewrite Hdf in Hp'; discriminate].
        injection Hp' as <-.
        assert (Hpa : page_at IM rg0 0%uint63 pn = Some (PG (sg_wr sg) PKImage iempty)).
        { unfold page_at. rewrite Hp0. change (0 =? 0)%uint63 with true. cbv iota. rewrite Hsg. reflexivity. }
        destruct (Hpages pn _ Hpn Hpa) as (Hok & Hlo' & Hlt).
        split; [| split; [exact Hlo' | exact Hlt]].
        replace (blim rg0 pn) with 4096 by (unfold blim; clear -Hlt Hlen4096; Z.div_mod_to_equations; nia).
        apply (page_ok_image_init segs IM rho m' pn sg IM_ok IM_wr_ok Hrho0 Hpn Hsg).
        intros a Ha. destruct (find_seg_spec _ _ _ Hsg) as (Hin & _). exact (ro_seg_clear m' sg a Hinv Hin Ha).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma copy_prefix_inv : forall k n' rg pn p',
    iget pn (copy_prefix k n' rg) = Some p' ->
    exists p, iget pn (rg_pages rg) = Some p /\ to_Z pn * 4096 + 8 <= to_Z k
              /\ page_in_region (blk_region n' 4 iempty) pn = true /\ p' = copy_page k (pn, p).
  Proof.
    intros k n' rg pn p' H. unfold copy_prefix in H.
    destruct (iget_iof_list_map_In fst (fun pp => copy_page k pp) _ _ _ H) as ([q v] & Hin & Hk & ->). cbn [fst] in Hk. subst q.
    apply filter_In in Hin as [Hin Hc]. cbn [fst] in Hc. apply andb_true_iff in Hc as [Hc1 Hc2].
    pose proof (i63_range pn). pose proof (i63_range k).
    apply Uint63.leb_spec in Hc1.
    destruct (page_in_region_spec _ _ Hc2) as (Hpn50 & _).
    rewrite toZ_add_small in Hc1.
    2:{ rewrite (toZ_lsl_small pn 12 12%uint63); [change (to_Z 8%uint63) with 8; change (2 ^ 12) with 4096; slia | reflexivity | slia | change (2 ^ 12) with 4096; slia]. }
    rewrite (toZ_lsl_small pn 12 12%uint63) in Hc1; [| reflexivity | slia | change (2 ^ 12) with 4096; slia].
    change (to_Z 8%uint63) with 8 in Hc1. change (2 ^ 12) with 4096 in Hc1.
    exists v. split; [apply (proj1 (ielements_spec _ _ _)); exact Hin|]. split; [slia|]. split; [exact Hc2 | reflexivity].
  Qed.

  Lemma copy_page_cells_inv : forall k pn p ci c,
    to_Z pn < 2 ^ 50 ->
    iget ci (pg_cells (copy_page k (pn, p))) = Some c ->
    iget ci (pg_cells p) = Some c /\ to_Z pn * 4096 + to_Z ci * 8 + 8 <= to_Z k /\ to_Z ci < 512 /\ keep_cell c = true.
  Proof.
    intros k pn p ci c Hpn H. unfold copy_page in H. cbn [pg_cells fst snd] in H.
    destruct (iget_iof_list_map_In fst snd _ _ _ H) as ([q v] & Hin & Hk & ->). cbn [fst snd] in Hk |- *. subst q.
    apply filter_In in Hin as [Hin Hc]. cbn [fst snd] in Hc. rewrite !andb_true_iff in Hc. destruct Hc as [[Hc1 Hc2] Hc3].
    pose proof (i63_range pn). pose proof (i63_range ci). pose proof (i63_range k).
    apply Uint63.ltb_spec in Hc2. change (to_Z 512%uint63) with 512 in Hc2.
    apply Uint63.leb_spec in Hc1.
    assert (Epn : to_Z (pn << 12)%uint63 = to_Z pn * 4096).
    { rewrite (toZ_lsl_small pn 12 12%uint63); [change (2 ^ 12) with 4096; slia | reflexivity | slia | change (2 ^ 12) with 4096; slia]. }
    assert (Eci : to_Z (ci << 3)%uint63 = to_Z ci * 8).
    { rewrite (toZ_lsl_small ci 3 3%uint63); [change (2 ^ 3) with 8; slia | reflexivity | slia | change (2 ^ 3) with 8; slia]. }
    rewrite !toZ_add_small in Hc1 by (rewrite ?toZ_add_small, ?Epn, ?Eci by (rewrite ?Epn, ?Eci; change (to_Z 8%uint63) with 8; slia); change (to_Z 8%uint63) with 8; slia).
    rewrite Epn, Eci in Hc1. change (to_Z 8%uint63) with 8 in Hc1.
    split; [apply (proj1 (ielements_spec _ _ _)); exact Hin|]. repeat split; try slia. exact Hc3.
  Qed.

  Lemma copy_region_part : forall m m' tb t rgb n n' k A A',
    rho tb = wa A -> rho t = wa A' -> tb <> 0%uint63 -> t <> 0%uint63 -> to_Z t < 2 ^ 60 ->
    mem_part m tb rgb -> rg_lo rgb = 0%uint63 -> rg_len rgb = n ->
    gblock_range A (to_Z n) -> gblock_range A' (to_Z n') -> to_Z n' < 2 ^ 40 ->
    to_Z k = Z.min (to_Z n) (to_Z n') ->
    (forall x, 0 <= x < to_Z k -> rview segs m' (wa (A' + x)) = rview segs m (wa (A + x))) ->
    wr_at segs m' A' (to_Z n') ->
    mem_part m' t (blk_region n' 4 (copy_prefix k n' rgb)).
  Proof.
    intros m m' tb t rgb n n' k A A' Htb Ht Htb0 Ht0 Hpl [Hrob Hpb] Hlob Hlenb HrA HrA' Hn' Hk Hcopy Hrw.
    pose proof HrA as (R1 & R2 & R3 & R4 & R5). pose proof HrA' as (S1 & S2 & S3 & S4 & S5).
    pose proof hceil_lt_2p47. pose proof (i63_range n). pose proof (i63_range n'). pose proof (i63_range k).
    destruct (blk_region_part m' t n' 4%uint63 A' Ht Ht0 Hpl HrA' ltac:(change (2 ^ to_Z 4%uint63) with 16; exact S2) ltac:(change (to_Z 4%uint63) with 4; slia) Hn' Hrw)
      as [Hro' Hdefault].
    split; [exact Hro'|].
    intros pn p' Hpn Hp'. pose proof (i63_range pn).
    unfold page_at, blk_region in Hp'. cbn [rg_pages rg_dflt] in Hp'.
    destruct (iget pn (copy_prefix k n' rgb)) as [p0|] eqn:Ecp.
    - (* [comment removed for export] *)
      injection Hp' as <-. destruct (copy_prefix_inv _ _ _ _ _ Ecp) as (p & Hp & Hk8 & Hpir & ->).
      destruct (page_in_region_spec _ _ Hpir) as (_ & Hlo & Hlt & _). unfold blk_region in Hlo, Hlt. cbn [rg_lo rg_len] in Hlo, Hlt.
      change (to_Z 0%uint63) with 0 in Hlo.
      unfold blk_region. cbn [rg_lo rg_len]. change (to_Z 0%uint63) with 0.
      split; [| split; [slia | exact Hlt]].
      assert (Hpa : page_at IM rgb tb pn = Some p) by (unfold page_at; rewrite Hp; reflexivity).
      destruct (Hpb pn p Hpn Hpa) as (Hokb & _ & Hltb). pose proof Hokb as (Hw & Hc & Hs & _).
      pose proof (clim8_le (RGK 0%uint63 n' 4%uint63 (Some PKUnk) (copy_prefix k n' rgb) clo_dflt chi_dflt RK_plain) pn Hlt) as Hcl. cbn [rg_len] in Hcl.
      pose proof (clim_nonneg (RGK 0%uint63 n' 4%uint63 (Some PKUnk) (copy_prefix k n' rgb) clo_dflt chi_dflt RK_plain) pn Hlt) as Hcl0.
      rewrite Hlenb in Hltb.
      assert (Hblim : forall ci : int, to_Z pn * 4096 + to_Z ci * 8 + 8 <= to_Z k -> to_Z ci < 512 ->
                        to_Z ci * 8 + 8 <= blim (RGK 0%uint63 n' 4%uint63 (Some PKUnk) (copy_prefix k n' rgb) clo_dflt chi_dflt RK_plain) pn).
      { intros ci Hoff Hci512. unfold blim. cbn [rg_len]. slia. }
      split; [|split; [|split]].
      + (* [comment removed for export] *) intros _ j Hj. cbn [rg_len] in Hj |- *.
        destruct Hrw as (W0 & W1 & W).
        rewrite (adr_eq_wa t A' (to_Z pn * 4096 + j) Ht) by slia. apply W. slia.
      + (* [comment removed for export] *) intros ci v Hci Hcell j Hj. pose proof (i63_range ci).
        unfold cell_at in Hcell. destruct (iget ci (pg_cells (copy_page k (pn, p)))) as [c|] eqn:Eg; [| cbn [copy_page pg_kind] in Hcell; discriminate].
        destruct (copy_page_cells_inv _ _ _ _ _ Hpn Eg) as (Hc0 & Hoff & Hci512 & _).
        rewrite (adr_eq_wa t A' _ Ht) by slia. rewrite Hcopy by slia. rewrite <- (adr_eq_wa tb A _ Htb) by slia.
        apply (Hc ci v ltac:(apply clim_intro; [slia | rewrite Hlenb; slia])); [|exact Hj].
        unfold cell_at. rewrite Hc0. destruct c as [v0| |sl0]; [exact Hcell | discriminate | discriminate].
      + (* [comment removed for export] *) intros ci sl Hci Hcib Hg j Hj. pose proof (i63_range ci). pose proof (i63_range j).
        destruct (copy_page_cells_inv _ _ _ _ _ Hpn Hg) as (Hc0 & Hoff & Hci512 & _).
        pose proof (Hblim ci Hoff Hci512) as Hcb8.
        split; [intros _ | intros Hout; exfalso; clear -Hout Hcb8 Hj; slia].
        rewrite slot_ok_val. rewrite (adr_eq_wa t A' _ Ht) by slia. rewrite Hcopy by slia. rewrite <- (adr_eq_wa tb A _ Htb) by slia.
        rewrite <- slot_ok_val. apply (page_ok_slots_whole segs IM rho m tb pn _ p ci sl j Hokb ltac:(apply clim_intro; [slia | rewrite Hlenb; slia]) Hc0 Hj).
      + (* [comment removed for export] *)
        intros ci Hci Hcut. unfold cell_at.
        destruct (iget ci (pg_cells (copy_page k (pn, p)))) as [c|] eqn:Eg; [| cbn [copy_page pg_kind]; reflexivity].
        exfalso. pose proof (i63_range ci). destruct (copy_page_cells_inv _ _ _ _ _ Hpn Eg) as (Hc0 & Hoff & Hci512 & _).
        pose proof (Hblim ci Hoff Hci512) as Hb8. clear -Hb8 Hcut. slia.
    - (* [comment removed for export] *)
      destruct (t =? 0)%uint63 eqn:Et; [apply Uint63.eqb_spec in Et; congruence|].
      apply Hdefault; [exact Hpn|]. unfold page_at, blk_region. cbn [rg_pages rg_dflt]. rewrite iget_iempty, Et.
      exact Hp'.
  Qed.
End Mem.
