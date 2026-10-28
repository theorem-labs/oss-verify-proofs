(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain
  FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom FxGeomA I2Canon I2Mach I2Image I2Run I2RunA.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import I2AInv I2ANodeLib I2ANodeMem I2AShadow.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia := Zify.zify; xlia zchecker.

Section Fill.
  Variable segs : list Segment.
  Variable IM : fimage.
  Variable rho : int -> word.
  Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.

  (* [comment removed for export] *)
  Definition rg_inb (rg : region) : Prop :=
    forall pn p ci c, iget pn (rg_pages rg) = Some p -> iget ci (pg_cells p) = Some c ->
      to_Z pn * 4096 + to_Z ci * 8 < to_Z (rg_len rg) /\ to_Z ci < 512 /\ (forall v, c = CV v -> to_Z pn * 4096 + to_Z ci * 8 + 8 <= to_Z (rg_len rg)).
  (* [comment removed for export] *)
  Definition rg_unk (rg : region) : Prop :=
    rg_lo rg = 0%uint63 /\ rg_dflt rg = Some PKUnk /\ forall pn p, iget pn (rg_pages rg) = Some p -> pg_kind p = PKUnk.

  Lemma cur_slots_slots_at : forall p pn ci, pg_kind p = PKUnk -> cur_slots p ci = slots_at IM p pn ci.
  Proof.
    intros p pn ci Hk. unfold cur_slots, slots_at, FxMem.cell_at. destruct (iget ci (pg_cells p)) as [[v| |sl]|]; try reflexivity; rewrite Hk; reflexivity.
  Qed.

  Lemma sget_set_slot : forall (i j : int) sl s, 0 <= to_Z i < 8 -> sget i (set_slot j sl s) = if (i =? j)%uint63 then sl else sget i s.
  Proof.
    intros i j sl s Hi. unfold set_slot.
    destruct (int_cases8 i Hi) as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; cbn [sget sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 Uint63.eqb]; reflexivity.
  Qed.

  Lemma set_slot_sound : forall (j : int) c s g g',
    0 <= to_Z j < 8 -> slots_val rho s g -> g' (Z.to_nat (to_Z j)) = Some (Z_to_bv 8 (to_Z c)) ->
    (forall i : int, i <> j -> 0 <= to_Z i < 8 -> g' (Z.to_nat (to_Z i)) = g (Z.to_nat (to_Z i))) ->
    slots_val rho (set_slot j (SK c) s) g'.
  Proof.
    intros j c s g g' Hj Hs Hnew Hold. apply slots_val_intro. intros i Hi. rewrite sget_set_slot by exact Hi.
    destruct (i =? j)%uint63 eqn:E.
    - apply Uint63.eqb_spec in E. subst i. cbn [slot_val]. exact Hnew.
    - apply Uint63.eqb_false_spec in E. rewrite (Hold i E Hi). exact (slots_val_sget rho s g i Hs Hi).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition wb_page (p : page) (ci j : int) (s : slot) : page :=
    PG true (pg_kind p) (iset ci (norm_slots (set_slot j s (cur_slots p ci))) (pg_cells p)).
  Definition wb_region (rg : region) (pn : int) (p' : page) : region :=
    RGK (rg_lo rg) (rg_len rg) (rg_align rg) (rg_dflt rg) (iset pn p' (rg_pages rg)) (rg_clo rg) (rg_chi rg) (rg_kind rg).
  Definition wb_cur (rg : region) (pn : int) : page := match iget pn (rg_pages rg) with Some p => p | None => PG true PKUnk iempty end.

  Lemma write_byte_inv : forall M t off s M', write_byte M t off s = Some M' ->
    exists rg, iget t M = Some rg /\ pg_wr (wb_cur rg (off >> 12)) = true
      /\ M' = iset t (wb_region rg (off >> 12) (wb_page (wb_cur rg (off >> 12)) ((off land 4095) >> 3) (off land 7) s)) M.
  Proof.
    intros M t off s M' H. unfold write_byte in H. destruct (iget t M) as [rg|]; [|discriminate]. exists rg. split; [reflexivity|].
    unfold wb_cur, wb_region, wb_page. destruct (pg_wr _) eqn:E; [|discriminate]. split; [reflexivity|]. injection H as <-. reflexivity.
  Qed.

  Lemma cell_at_wb : forall p ci c pn ci1,
    FxMem.cell_at IM (PG true (pg_kind p) (iset ci c (pg_cells p))) pn ci1 =
      if (ci1 =? ci)%uint63 then match c with CV v => Some v | _ => None end else FxMem.cell_at IM p pn ci1.
  Proof.
    intros p ci c pn ci1. unfold FxMem.cell_at. cbn [pg_cells pg_kind]. rewrite iget_iset. destruct (ci1 =? ci)%uint63; [destruct c; reflexivity| reflexivity].
  Qed.

  Lemma page_in_region_intro : forall rg pn, rg_lo rg = 0%uint63 -> to_Z (rg_len rg) <= 2 ^ 62 -> 0 <= to_Z pn -> to_Z pn * 4096 < to_Z (rg_len rg) ->
    page_in_region rg pn = true.
  Proof.
    intros rg pn Hlo Hlen Hpn Hlt. pose proof (i63_range (rg_len rg)). unfold page_in_region. rewrite Hlo.
    assert (E : to_Z (pn << 12)%uint63 = to_Z pn * 4096) by (rewrite (toZ_lsl_small pn 12 12%uint63); [reflexivity| reflexivity| slia| change (2 ^ 12) with 4096; slia]).
    rewrite !andb_true_iff. repeat split.
    - apply Uint63.ltb_spec. change (to_Z 1125899906842624%uint63) with (2 ^ 50). slia.
    - apply Uint63.leb_spec. change (to_Z 0%uint63) with 0. rewrite E. slia.
    - apply Uint63.ltb_spec. rewrite E. exact Hlt.
    - apply Uint63.leb_spec. change (to_Z 4611686018427387904%uint63) with (2 ^ 62). exact Hlen.
  Qed.

  Lemma set_slot_sound_gen : forall (j : int) (s0 : slot) s g g',
    0 <= to_Z j < 8 -> slots_val rho s g -> slot_val rho s0 (g' (Z.to_nat (to_Z j))) ->
    (forall i : int, i <> j -> 0 <= to_Z i < 8 -> g' (Z.to_nat (to_Z i)) = g (Z.to_nat (to_Z i))) ->
    slots_val rho (set_slot j s0 s) g'.
  Proof.
    intros j s0 s g g' Hj Hs Hnew Hold. apply slots_val_intro. intros i Hi. rewrite sget_set_slot by exact Hi.
    destruct (i =? j)%uint63 eqn:E.
    - apply Uint63.eqb_spec in E. subst i. exact Hnew.
    - apply Uint63.eqb_false_spec in E. rewrite (Hold i E Hi). exact (slots_val_sget rho s g i Hs Hi).
  Qed.

  Lemma write_slot_sound : forall M t off (s : slot) (b : byte) M' rg mA,
    write_byte M t off s = Some M' -> iget t M = Some rg ->
    mem_part segs IM rho mA t rg -> t <> 0%uint63 -> rg_unk rg -> rg_inb rg ->
    to_Z off < to_Z (rg_len rg) -> slot_val rho s (Some b) ->
    let a := adr rho t (to_Z off) in
    let rg' := wb_region rg (off >> 12) (wb_page (wb_cur rg (off >> 12)) ((off land 4095) >> 3) (off land 7) s) in
    M' = iset t rg' M
    /\ mem_part segs IM rho (write_to_mem mA a [b]) t rg'
    /\ rg_unk rg' /\ rg_inb rg'
    /\ (rg_lo rg' = rg_lo rg /\ rg_len rg' = rg_len rg /\ rg_align rg' = rg_align rg /\ rg_kind rg' = rg_kind rg /\ rg_dflt rg' = rg_dflt rg)
    /\ wview segs mA a <> None.
  Proof.
    intros M t off s b M' rg mA Hwb Hrg Hpart Ht0 (Hlo0 & Hdf & Hkinds) Hinb Hofflt Hsv. cbv zeta.
    destruct (write_byte_inv _ _ _ _ _ Hwb) as (rg_ & Hrg_ & PGWR & HM'). rewrite Hrg in Hrg_. injection Hrg_ as <-.
    pose proof (i63_range off) as Hoff. pose proof (i63_range (rg_len rg)) as Hlen.
    destruct Hpart as [Hreg Hpages]. pose proof Hreg as (Hpl & Hlen62 & _).
    set (pn := (off >> 12)%uint63) in *. set (ci := ((off land 4095) >> 3)%uint63) in *. set (j := (off land 7)%uint63) in *.
    assert (Epn : to_Z pn = to_Z off / 4096) by (subst pn; apply to_Z_lsr12).
    assert (Eci : to_Z ci = (to_Z off mod 4096) / 8) by (subst ci; rewrite to_Z_lsr3, to_Z_land4095; reflexivity).
    assert (Ej : to_Z j = to_Z off mod 8) by (subst j; apply to_Z_land7).
    assert (Hdec : to_Z pn * 4096 + to_Z ci * 8 + to_Z j = to_Z off) by (rewrite Epn, Eci, Ej; apply off_decomp; slia).
    assert (Hpn : 0 <= to_Z pn < 2 ^ 50) by (rewrite Epn; split; [Z.div_mod_to_equations; slia| apply Z.div_lt_upper_bound; slia]).
    assert (Hci : 0 <= to_Z ci < 512) by (rewrite Eci; apply cell_index_range; slia).
    assert (Hj : 0 <= to_Z j < 8) by (rewrite Ej; Z.div_mod_to_equations; slia).
    set (p := wb_cur rg pn) in *.
    assert (Hkp : pg_kind p = PKUnk) by (subst p; unfold wb_cur; destruct (iget pn (rg_pages rg)) as [p0|] eqn:Ep; [exact (Hkinds _ _ Ep)| reflexivity]).
    assert (PA : page_at IM rg t pn = Some p).
    { subst p. unfold wb_cur, page_at. destruct (iget pn (rg_pages rg)) as [p0|] eqn:Ep; [reflexivity|].
      destruct (t =? 0)%uint63 eqn:Et; [apply Uint63.eqb_spec in Et; congruence|]. rewrite Hdf.
      rewrite (page_in_region_intro rg pn Hlo0 Hlen62 ltac:(slia) ltac:(rewrite Epn; Z.div_mod_to_equations; slia)). reflexivity. }
    destruct (Hpages pn p (proj2 Hpn) PA) as [Hpage [Hplo Hplt]]. pose proof Hpage as (Hwv & Hcells & Hslots & Hcut).
    set (B := blim rg pn) in *.
    assert (HB : to_Z ci * 8 + to_Z j < B /\ B <= 4096 /\ B <= to_Z (rg_len rg) - to_Z pn * 4096).
    { subst B. unfold blim. rewrite Epn, Eci, Ej. clear - Hofflt Hoff. Z.div_mod_to_equations. slia. }
    assert (Hcic : to_Z ci < B / 8 \/ to_Z ci * 8 < B < to_Z ci * 8 + 8) by (clear - HB Hci Hj; Z.div_mod_to_equations; slia).
    (* [comment removed for export] *)
    assert (Hcur : slots_val rho (cur_slots p ci) (cell_view segs rho mA t pn ci)).
    { rewrite (cur_slots_slots_at p pn ci Hkp). apply (slots_at_sound_any segs IM rho Hrho0 mA t pn B p ci Hpage (proj1 Hci) Hcic). }
    set (mB := write_to_mem mA (adr rho t (to_Z off)) [b]).
    assert (VIEWj : cell_view segs rho mB t pn ci (Z.to_nat (to_Z j)) = Some b).
    { unfold cell_view. rewrite Z2Nat.id by slia. rewrite Hdec. subst mB. rewrite <- (aoff_0 (adr rho t (to_Z off))) at 2.
      apply (rview_write_in segs); [cbn; slia| reflexivity]. }
    assert (VIEWo : forall i : nat, (i < 8)%nat -> Z.of_nat i <> to_Z j -> cell_view segs rho mB t pn ci i = cell_view segs rho mA t pn ci i).
    { intros i Hi Hne. unfold cell_view. subst mB. apply rview_write_out. intros k Hk. cbn [length] in Hk.
      replace k with 0%nat by slia. apply frame_same_region; clear - Hi Hne Hdec Hoff Hpn Hci; slia. }
    assert (Hnew : cell_val rho (norm_slots (set_slot j s (cur_slots p ci))) (cell_view segs rho mB t pn ci)).
    { apply (norm_slots_sound rho Hrho0). apply (set_slot_sound_gen j s _ (cell_view segs rho mA t pn ci)); [exact Hj| exact Hcur| rewrite VIEWj; exact Hsv|].
      intros i Hne Hi. apply VIEWo; [clear - Hi; slia| rewrite Z2Nat.id by slia; intros E; apply Hne; apply to_Z_inj; exact E]. }
    (* [comment removed for export] *)
    assert (SUhi : forall i : int, 0 <= to_Z i < 8 -> B <= to_Z ci * 8 + to_Z i -> sget i (set_slot j s (cur_slots p ci)) = SU).
    { intros i Hi HiB. rewrite sget_set_slot by exact Hi. destruct (i =? j)%uint63 eqn:E; [apply Uint63.eqb_spec in E; subst i; exfalso; clear - HiB HB; slia|].
      unfold cur_slots. destruct (iget ci (pg_cells p)) as [[v| |sl]|] eqn:Eg.
      - exfalso. assert (CA : FxMem.cell_at IM p pn ci = Some v) by (unfold FxMem.cell_at; rewrite Eg; reflexivity).
        destruct Hcic as [Hw|Hcutc]; [clear - Hw Hi HiB; Z.div_mod_to_equations; slia|]. rewrite (Hcut ci (proj1 Hci) Hcutc) in CA. discriminate CA.
      - unfold slots_unk. destruct (int_cases8 i Hi) as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; reflexivity.
      - exact (proj2 (Hslots ci sl (proj1 Hci) ltac:(clear - HB Hj; slia) Eg i Hi) HiB).
      - unfold slots_unk. destruct (int_cases8 i Hi) as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; reflexivity. }
    assert (CUTCB : to_Z ci * 8 < B < to_Z ci * 8 + 8 -> norm_slots (set_slot j s (cur_slots p ci)) = CB (set_slot j s (cur_slots p ci))).
    { intros Hcutc. apply (norm_slots_SU7). change (sl7 (set_slot j s (cur_slots p ci))) with (sget 7%uint63 (set_slot j s (cur_slots p ci))).
      apply SUhi; [change (to_Z 7%uint63) with 7; slia| change (to_Z 7%uint63) with 7; clear - Hcutc; slia]. }
    split; [exact HM'|]. split; [| split; [| split; [| split; [cbn; repeat split; reflexivity|]]]].
    - (* [comment removed for export] *)
      split; [exact Hreg|]. intros pn1 p1 Hpn1 Hp1. cbn [wb_region rg_lo rg_len] in Hp1 |- *.
      change (blim (wb_region rg pn (wb_page p ci j s)) pn1) with (blim rg pn1).
      assert (Hp1' : (pn1 = pn /\ p1 = wb_page p ci j s) \/ (pn1 <> pn /\ page_at IM rg t pn1 = Some p1)).
      { unfold page_at, wb_region in Hp1. cbn [rg_pages rg_dflt] in Hp1. rewrite iget_iset in Hp1.
        destruct (pn1 =? pn)%uint63 eqn:E; [apply Uint63.eqb_spec in E; left; split; [exact E| injection Hp1 as <-; reflexivity]|].
        apply Uint63.eqb_false_spec in E. right. split; [exact E|]. unfold page_at. exact Hp1. }
      destruct Hp1' as [[-> ->]|[Hnepn Hp1']].
      + split; [| split; [exact Hplo| exact Hplt]]. split; [| split; [| split]].
        * intros _ jj Hjj. subst mB. apply wview_write. exact (Hwv PGWR jj Hjj).
        * intros ci1 v Hci1 Hcell1 jj Hjj. unfold wb_page in Hcell1. rewrite cell_at_wb in Hcell1.
          destruct (ci1 =? ci)%uint63 eqn:E.
          -- apply Uint63.eqb_spec in E. subst ci1. destruct (norm_slots (set_slot j s (cur_slots p ci))) as [v'| |sl'] eqn:En; try discriminate Hcell1.
             injection Hcell1 as <-. exact (Hnew jj Hjj).
          -- apply Uint63.eqb_false_spec in E. pose proof (i63_range ci1) as Rci1.
             change (rview segs mB (adr rho t (to_Z pn * 4096 + to_Z ci1 * 8 + Z.of_nat jj))) with (cell_view segs rho mB t pn ci1 jj).
             unfold cell_view. subst mB. rewrite rview_write_out; [exact (Hcells ci1 v Hci1 Hcell1 jj Hjj)|].
             intros k Hk. cbn [length] in Hk. replace k with 0%nat by slia. apply frame_same_region; [clear - Hci1 Hjj Hpn HB Rci1; slia| clear - Hoff; slia| clear - Hoff; slia|].
             intros EQ. apply E. apply to_Z_inj. clear - EQ Hdec Hjj Hj Hci1 Hci; slia.
        * intros ci1 sl Hci1 Hcb1 Hg1 jj Hjj. unfold wb_page in Hg1. cbn [pg_cells] in Hg1. rewrite iget_iset in Hg1.
          destruct (ci1 =? ci)%uint63 eqn:E.
          -- apply Uint63.eqb_spec in E. subst ci1. apply some_inj in Hg1. rename Hg1 into En.
             assert (Esl : sl = set_slot j s (cur_slots p ci)).
             { destruct (norm_slots_shape (set_slot j s (cur_slots p ci))) as [E0 | [(b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & E8) | (v0 & j0 & v1 & j1 & v2 & j2 & v3 & j3 & v4 & j4 & v5 & j5 & v6 & j6 & v7 & j7 & E8)]].
               - rewrite E0 in En. injection En as En'. first [exact En'| symmetry; exact En'].
               - exfalso. rewrite E8 in En. cbn [norm_slots] in En. discriminate En.
               - rewrite E8 in En. revert En. cbn [norm_slots]. repeat match goal with |- context [if ?b then _ else _] => destruct b end; intros En; try discriminate En;
                 injection En as En'; rewrite E8; first [exact En'| symmetry; exact En']. }
             split.
             ++ intros HjjB. apply (slot_ok_val segs rho). rewrite <- En in Hnew. cbn [cell_val] in Hnew. pose proof (slots_val_sget rho _ _ jj Hnew Hjj) as SV'.
                unfold cell_view in SV'. rewrite Z2Nat.id in SV' by slia. exact SV'.
             ++ intros HjjB. rewrite Esl. exact (SUhi jj Hjj HjjB).
          -- apply Uint63.eqb_false_spec in E. pose proof (i63_range ci1) as Rci1. destruct (Hslots ci1 sl Hci1 Hcb1 Hg1 jj Hjj) as [Hsin Hsout]. split; [| exact Hsout].
             intros HjjB. apply (slot_ok_val segs rho). subst mB. rewrite rview_write_out; [apply (slot_ok_val segs rho); exact (Hsin HjjB)|].
             intros k Hk. cbn [length] in Hk. replace k with 0%nat by slia. apply frame_same_region; [clear - Hci1 Hcb1 Hjj Hpn HB Rci1; slia| clear - Hoff; slia| clear - Hoff; slia|].
             intros EQ. apply E. apply to_Z_inj. clear - EQ Hdec Hjj Hj Hci1 Hci; slia.
        * intros ci1 Hci1 Hcut1. unfold wb_page. rewrite cell_at_wb. destruct (ci1 =? ci)%uint63 eqn:E; [| exact (Hcut ci1 Hci1 Hcut1)].
          apply Uint63.eqb_spec in E. subst ci1. rewrite (CUTCB Hcut1). reflexivity.
      + destruct (Hpages pn1 p1 Hpn1 Hp1') as [Hok Hb1]. split; [| exact Hb1]. subst mB. apply page_ok_frame; [exact Hok|].
        intros ci1 jj k Hci1 Hcb1 Hjj Hk. cbn [length] in Hk. replace k with 0%nat by slia.
        assert (Hne : to_Z pn1 <> to_Z pn) by (intros Q; apply Hnepn, to_Z_inj, Q). pose proof (i63_range pn1) as Rpn1. pose proof (blim_le rg pn1) as Bl1.
        apply frame_same_region; [clear - Hci1 Hcb1 Hjj Rpn1 Hpn1 Bl1; slia| clear - Hoff; slia| clear - Hoff; slia| clear - Hne Hci1 Hcb1 Hjj Bl1 Hdec Hci Hj HB; slia].
    - (* [comment removed for export] *) split; [exact Hlo0|]. split; [exact Hdf|]. intros pn1 p1 Hp1. cbn [wb_region rg_pages] in Hp1. rewrite iget_iset in Hp1.
      destruct (pn1 =? pn)%uint63; [injection Hp1 as <-; cbn; exact Hkp| exact (Hkinds _ _ Hp1)].
    - (* [comment removed for export] *) intros pn1 p1 ci1 c1 Hp1 Hc1. cbn [wb_region rg_pages rg_len] in Hp1 |- *. rewrite iget_iset in Hp1.
      destruct (pn1 =? pn)%uint63 eqn:Epn1.
      + apply Uint63.eqb_spec in Epn1. subst pn1. injection Hp1 as <-. unfold wb_page in Hc1. cbn [pg_cells] in Hc1. rewrite iget_iset in Hc1.
        destruct (ci1 =? ci)%uint63 eqn:Eci1.
        * apply Uint63.eqb_spec in Eci1. subst ci1. apply some_inj in Hc1. rename Hc1 into En. split; [clear - HB Hj; slia|]. split; [exact (proj2 Hci)|].
          intros v Ev. rewrite Ev in En. destruct (Z.lt_ge_cases (to_Z ci * 8 + 7) B) as [Hw|Hw]; [clear - Hw HB; slia|].
          exfalso. rewrite (CUTCB ltac:(clear - Hw HB Hj; slia)) in En. discriminate En.
        * subst p. unfold wb_cur in Hc1. destruct (iget pn (rg_pages rg)) as [p0|] eqn:Ep; [exact (Hinb pn p0 ci1 c1 Ep Hc1)|]. cbn [pg_cells] in Hc1. rewrite iget_iempty in Hc1. discriminate Hc1.
      + exact (Hinb pn1 p1 ci1 c1 Hp1 Hc1).
    - (* [comment removed for export] *)
      specialize (Hwv PGWR (to_Z ci * 8 + to_Z j) ltac:(clear - HB Hci Hj; slia)). replace (to_Z pn * 4096 + (to_Z ci * 8 + to_Z j)) with (to_Z off) in Hwv by (clear - Hdec; slia). exact Hwv.
  Qed.

  Lemma write_byte_sound : forall M t off (c : int) M' rg mA,
    write_byte M t off (SK c) = Some M' -> iget t M = Some rg ->
    mem_part segs IM rho mA t rg -> t <> 0%uint63 -> rg_unk rg -> rg_inb rg ->
    to_Z off < to_Z (rg_len rg) -> to_Z c < 256 ->
    let a := adr rho t (to_Z off) in
    let rg' := wb_region rg (off >> 12) (wb_page (wb_cur rg (off >> 12)) ((off land 4095) >> 3) (off land 7) (SK c)) in
    M' = iset t rg' M
    /\ mem_part segs IM rho (write_to_mem mA a [Z_to_bv 8 (to_Z c)]) t rg'
    /\ rg_unk rg' /\ rg_inb rg'
    /\ (rg_lo rg' = rg_lo rg /\ rg_len rg' = rg_len rg /\ rg_align rg' = rg_align rg /\ rg_kind rg' = rg_kind rg /\ rg_dflt rg' = rg_dflt rg)
    /\ wview segs mA a <> None.
  Proof.
    intros M t off c M' rg mA Hwb Hrg Hpart Ht0 Hunk Hinb Hofflt Hc.
    exact (write_slot_sound M t off (SK c) (Z_to_bv 8 (to_Z c)) M' rg mA Hwb Hrg Hpart Ht0 Hunk Hinb Hofflt eq_refl).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma write_to_mem_cons : forall m a b bs, write_to_mem m a (b :: bs) = write_to_mem (write_to_mem m a [b]) (bv_add a 1%bv) bs.
  Proof. intros. reflexivity. Qed.

  Lemma adr_succ : forall t z, adr rho t (z + 1) = bv_add (adr rho t z) 1%bv.
  Proof. intros t z. rewrite <- (aoff_adr rho t z 1). unfold aoff. reflexivity. Qed.

  Lemma fill_bytes_sound : forall k M t off (c : int) M' rg mA,
    fill_bytes k M t off c = Some M' -> iget t M = Some rg ->
    mem_part segs IM rho mA t rg -> t <> 0%uint63 -> rg_unk rg -> rg_inb rg ->
    to_Z off + Z.of_nat k <= to_Z (rg_len rg) -> to_Z c < 256 ->
    exists rg', iget t M' = Some rg'
      /\ (forall t', t' <> t -> iget t' M' = iget t' M)
      /\ mem_part segs IM rho (write_to_mem mA (adr rho t (to_Z off)) (repeat (Z_to_bv 8 (to_Z c)) k)) t rg'
      /\ rg_unk rg' /\ rg_inb rg'
      /\ (rg_lo rg' = rg_lo rg /\ rg_len rg' = rg_len rg /\ rg_align rg' = rg_align rg /\ rg_kind rg' = rg_kind rg /\ rg_dflt rg' = rg_dflt rg)
      /\ (forall i, 0 <= i < Z.of_nat k -> wview segs mA (adr rho t (to_Z off + i)) <> None).
  Proof.
    induction k as [|k IH]; intros M t off c M' rg mA Hf Hrg Hpart Ht0 Hunk Hinb Hlen Hc.
    - cbn [fill_bytes] in Hf. injection Hf as <-. exists rg. split; [exact Hrg|]. split; [intros; reflexivity|]. split; [cbn [repeat write_to_mem]; exact Hpart|].
      split; [exact Hunk|]. split; [exact Hinb|]. split; [repeat split; reflexivity|]. intros i Hi. exfalso. cbn in Hi. slia.
    - cbn [fill_bytes] in Hf. destruct (write_byte M t off (SK c)) as [M1|] eqn:Hwb; [|discriminate].
      pose proof (i63_range off) as Hoff. pose proof (i63_range (rg_len rg)) as Hlr.
      destruct (write_byte_sound M t off c M1 rg mA Hwb Hrg Hpart Ht0 Hunk Hinb ltac:(slia) Hc) as (HM1 & Hpart1 & Hunk1 & Hinb1 & (G1 & G2 & G3 & G4 & G5) & Hwr).
      set (rg1 := wb_region rg (off >> 12) (wb_page (wb_cur rg (off >> 12)) ((off land 4095) >> 3) (off land 7) (SK c))) in *.
      assert (Hrg1 : iget t M1 = Some rg1) by (rewrite HM1, iget_iset, Uint63.eqb_refl; reflexivity).
      assert (Eoff1 : to_Z (off + 1)%uint63 = to_Z off + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; [reflexivity| slia]).
      destruct (IH M1 t (off + 1)%uint63 c M' rg1 _ Hf Hrg1 Hpart1 Ht0 Hunk1 Hinb1 ltac:(rewrite Eoff1, G2; slia) Hc)
        as (rg' & Hrg' & Hoth & Hpart' & Hunk' & Hinb' & (F1 & F2 & F3 & F4 & F5) & Hwr').
      exists rg'. split; [exact Hrg'|]. split; [intros t' Hne; rewrite (Hoth t' Hne), HM1, iget_iset, (proj2 (Uint63.eqb_false_spec _ _) Hne); reflexivity|].
      split.
      { cbn [repeat]. rewrite write_to_mem_cons. rewrite <- adr_succ. rewrite <- Eoff1. exact Hpart'. }
      split; [exact Hunk'|]. split; [exact Hinb'|]. split; [rewrite F1, F2, F3, F4, F5; repeat split; assumption|].
      intros i Hi. destruct (Z.eq_dec i 0) as [->|Hne].
      + rewrite Z.add_0_r. exact Hwr.
      + assert (W1 : wview segs (write_to_mem mA (adr rho t (to_Z off)) [Z_to_bv 8 (to_Z c)]) (adr rho t (to_Z (off + 1)%uint63 + (i - 1))) <> None).
        { apply Hwr'. cbn [repeat length] in Hi. rewrite Nat2Z.inj_succ in Hi. slia. }
        rewrite Eoff1 in W1. replace (to_Z off + 1 + (i - 1)) with (to_Z off + i) in W1 by slia.
        unfold wview in W1 |- *. cbn [write_to_mem] in W1.
        destruct (bv_eqb (adr rho t (to_Z off + i)) (adr rho t (to_Z off))) eqn:E; [| exact W1].
        exfalso. unfold bv_eqb in E. apply Z.eqb_eq in E. apply bv_eq in E. apply (adr_inj rho) in E; slia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma byte_at_SK_sound : forall M m t off rg b,
    mem_ok segs IM rho M m -> t <> 0%uint63 -> iget t M = Some rg -> rg_inb rg ->
    to_Z off < to_Z (rg_len rg) -> byte_at IM M t off = SK b ->
    rview segs m (adr rho t (to_Z off)) = Some (Z_to_bv 8 (to_Z b)).
  Proof.
    intros M m t off rg b [Hmem _] Ht0 Hrg Hinb Hofflt Hb. pose proof (i63_range off) as Hoff. pose proof (i63_range (rg_len rg)) as Hlr.
    unfold byte_at in Hb. destruct (t =? 0)%uint63 eqn:Et; [apply Uint63.eqb_spec in Et; congruence|]. rewrite Hrg in Hb.
    set (pn := (off >> 12)%uint63) in *. set (ci := ((off land 4095) >> 3)%uint63) in *. set (j := (off land 7)%uint63) in *.
    assert (Epn : to_Z pn = to_Z off / 4096) by (subst pn; apply to_Z_lsr12).
    assert (Eci : to_Z ci = (to_Z off mod 4096) / 8) by (subst ci; rewrite to_Z_lsr3, to_Z_land4095; reflexivity).
    assert (Ej : to_Z j = to_Z off mod 8) by (subst j; apply to_Z_land7).
    assert (Hdec : to_Z pn * 4096 + to_Z ci * 8 + to_Z j = to_Z off) by (rewrite Epn, Eci, Ej; apply off_decomp; slia).
    destruct (Hmem t rg Hrg) as [Hreg Hpages]. pose proof Hreg as (Hpl & Hlen62 & _).
    assert (Hpn : 0 <= to_Z pn < 2 ^ 50) by (rewrite Epn; split; [Z.div_mod_to_equations; slia| apply Z.div_lt_upper_bound; slia]).
    assert (Hci : 0 <= to_Z ci < 512) by (rewrite Eci; apply cell_index_range; slia).
    assert (Hj : 0 <= to_Z j < 8) by (rewrite Ej; Z.div_mod_to_equations; slia).
    destruct (iget pn (rg_pages rg)) as [p|] eqn:Ep; [|discriminate Hb].
    destruct (Hpages pn p (proj2 Hpn) ltac:(unfold page_at; rewrite Ep; reflexivity)) as [(Hwv & Hcells & Hslots & Hcut) [Hplo Hplt]].
    assert (HB : to_Z ci * 8 + to_Z j < blim rg pn /\ blim rg pn <= to_Z (rg_len rg) - to_Z pn * 4096) by (unfold blim; rewrite Epn, Eci, Ej; clear - Hofflt Hoff; Z.div_mod_to_equations; slia).
    rewrite <- Hdec. replace (to_Z j) with (Z.of_nat (Z.to_nat (to_Z j))) by (clear - Hj; slia).
    destruct (iget ci (pg_cells p)) as [[v| |sl]|] eqn:Eg; try discriminate Hb.
    - (* [comment removed for export] *)
      destruct v as [tv w]. unfold vslot in Hb. destruct (tv =? 0)%uint63 eqn:Etv; [|discriminate Hb]. apply Uint63.eqb_spec in Etv. subst tv. injection Hb as <-.
      destruct (Hinb pn p ci (CV (FV 0 w)) Ep Eg) as (_ & _ & Hcv). specialize (Hcv _ eq_refl).
      rewrite (Hcells ci (FV 0 w) ltac:(unfold blim; clear - Hci Hcv; Z.div_mod_to_equations; slia) ltac:(unfold FxMem.cell_at; rewrite Eg; reflexivity) (Z.to_nat (to_Z j)) ltac:(clear - Hj; slia)).
      rewrite (dv_tag0 rho Hrho0), wbytes8_wbv. rewrite w_bytes_nth_byte by (clear - Hj; slia). reflexivity. reflexivity.
    - (* [comment removed for export] *)
      pose proof (proj1 (Hslots ci sl (proj1 Hci) ltac:(clear - HB Hj; slia) Eg j Hj) (proj1 HB)) as SK'. rewrite Hb in SK'. cbn [slot_ok] in SK'.
      rewrite Z2Nat.id by (clear - Hj; slia). exact SK'.
  Qed.
  (* [comment removed for export] *)
  Lemma byte_at_slot_sound : forall M m t off rg,
    mem_part segs IM rho m t rg -> t <> 0%uint63 -> iget t M = Some rg -> rg_inb rg ->
    to_Z off < to_Z (rg_len rg) ->
    slot_val rho (byte_at IM M t off) (rview segs m (adr rho t (to_Z off))).
  Proof.
    intros M m t off rg [Hreg Hpages] Ht0 Hrg Hinb Hofflt. pose proof (i63_range off) as Hoff. pose proof (i63_range (rg_len rg)) as Hlr.
    unfold byte_at. destruct (t =? 0)%uint63 eqn:Et; [apply Uint63.eqb_spec in Et; congruence|]. rewrite Hrg.
    set (pn := (off >> 12)%uint63) in *. set (ci := ((off land 4095) >> 3)%uint63) in *. set (j := (off land 7)%uint63) in *.
    assert (Epn : to_Z pn = to_Z off / 4096) by (subst pn; apply to_Z_lsr12).
    assert (Eci : to_Z ci = (to_Z off mod 4096) / 8) by (subst ci; rewrite to_Z_lsr3, to_Z_land4095; reflexivity).
    assert (Ej : to_Z j = to_Z off mod 8) by (subst j; apply to_Z_land7).
    assert (Hdec : to_Z pn * 4096 + to_Z ci * 8 + to_Z j = to_Z off) by (rewrite Epn, Eci, Ej; apply off_decomp; slia).
    pose proof Hreg as (Hpl & Hlen62 & _).
    assert (Hpn : 0 <= to_Z pn < 2 ^ 50) by (rewrite Epn; split; [Z.div_mod_to_equations; slia| apply Z.div_lt_upper_bound; slia]).
    assert (Hci : 0 <= to_Z ci < 512) by (rewrite Eci; apply cell_index_range; slia).
    assert (Hj : 0 <= to_Z j < 8) by (rewrite Ej; Z.div_mod_to_equations; slia).
    destruct (iget pn (rg_pages rg)) as [p|] eqn:Ep; [| exact I].
    destruct (Hpages pn p (proj2 Hpn) ltac:(unfold page_at; rewrite Ep; reflexivity)) as [(Hwv & Hcells & Hslots & Hcut) [Hplo Hplt]].
    assert (HB : to_Z ci * 8 + to_Z j < blim rg pn /\ blim rg pn <= to_Z (rg_len rg) - to_Z pn * 4096) by (unfold blim; rewrite Epn, Eci, Ej; clear - Hofflt Hoff; Z.div_mod_to_equations; slia).
    rewrite <- Hdec. replace (to_Z j) with (Z.of_nat (Z.to_nat (to_Z j))) by (clear - Hj; slia).
    destruct (iget ci (pg_cells p)) as [[v| |sl]|] eqn:Eg; try exact I.
    - (* [comment removed for export] *)
      destruct (Hinb pn p ci (CV v) Ep Eg) as (_ & _ & Hcv). specialize (Hcv _ eq_refl).
      pose proof (Hcells ci v ltac:(unfold blim; clear - Hci Hcv; Z.div_mod_to_equations; slia) ltac:(unfold FxMem.cell_at; rewrite Eg; reflexivity) (Z.to_nat (to_Z j)) ltac:(clear - Hj; slia)) as HV.
      destruct v as [tv w]. unfold vslot. destruct (tv =? 0)%uint63 eqn:Etv.
      + apply Uint63.eqb_spec in Etv. subst tv. cbn [slot_val]. rewrite HV. rewrite (dv_tag0 rho Hrho0), wbytes8_wbv by reflexivity. cbn [vw]. rewrite w_bytes_nth_byte by (clear - Hj; slia). reflexivity.
      + cbn [slot_val]. exact HV.
    - (* [comment removed for export] *)
      pose proof (proj1 (Hslots ci sl (proj1 Hci) ltac:(clear - HB Hj; slia) Eg j Hj) (proj1 HB)) as SK'.
      apply (proj1 (slot_ok_val segs rho _ _ _)) in SK'. rewrite Z2Nat.id by (clear - Hj; slia). exact SK'.
  Qed.

  (* [comment removed for export] *)
  Lemma byte_at_img_sound : forall M m off,
    image_ok segs IM -> (forall a sg, find_seg IM a = Some sg -> sg_wr sg = false) -> mem_inv segs m ->
    slot_val rho (byte_at IM M 0%uint63 off) (rview segs m (adr rho 0%uint63 (to_Z off))).
  Proof.
    intros M m off HIM Hro Hinv. unfold byte_at. rewrite Uint63.eqb_refl.
    destruct (image_cell IM ((off >> 3) << 3)%uint63) as [v|] eqn:Hc; [| exact I].
    destruct (image_cell_tag _ _ _ Hc) as [w ->]. cbn [slot_val].
    pose proof (i63_range off) as Hoff. set (a8 := ((off >> 3) << 3)%uint63) in *.
    assert (Ea8 : to_Z a8 = to_Z off - to_Z off mod 8).
    { subst a8. rewrite Uint63.lsl_spec, to_Z_lsr3. change (2 ^ to_Z 3%uint63) with 8. change wB with (2 ^ 63). rewrite Z.mod_small by (clear - Hoff; Z.div_mod_to_equations; slia).
      clear - Hoff. Z.div_mod_to_equations. slia. }
    assert (Hal : to_Z a8 mod 8 = 0) by (rewrite Ea8; clear - Hoff; Z.div_mod_to_equations; slia).
    set (j := Z.to_nat (to_Z off mod 8)).
    assert (Hj : (j < 8)%nat) by (subst j; clear - Hoff; Z.div_mod_to_equations; slia).
    pose proof (image_cell_sound segs IM a8 w HIM Hal Hc j Hj) as Hrd.
    replace (to_Z a8 + Z.of_nat j) with (to_Z off) in Hrd by (subst j; rewrite Ea8; clear - Hoff; Z.div_mod_to_equations; slia).
    (* [comment removed for export] *)
    pose proof Hc as Hc'. unfold image_cell in Hc'. destruct (find_seg IM a8) as [sg|] eqn:Hf; [| discriminate Hc']. clear Hc'.
    destruct (find_seg_spec _ _ _ Hf) as (Hin & Hb1 & Hb2). apply Uint63.leb_spec in Hb1. apply Uint63.ltb_spec in Hb2.
    pose proof (proj1 (Forall_forall _ _) HIM sg Hin) as (seg & Hseg & Eb & Es & _ & _ & Ewr & Mb & Ms & Hle & Hfind).
    pose proof (i63_range (sg_base sg)) as Rb. pose proof (i63_range (sg_size sg)) as Rs.
    rewrite Uint63.add_spec in Hb2. change wB with (2 ^ 63) in Hb2. rewrite Z.mod_small in Hb2 by (clear - Rb Rs Hle; slia).
    assert (Hin8 : to_Z (sg_base sg) <= to_Z off < to_Z (sg_base sg) + to_Z (sg_size sg)) by (clear - Hb1 Hb2 Ea8 Hal Mb Ms Hoff; Z.div_mod_to_equations; slia).
    assert (E0 : adr rho 0%uint63 (to_Z off) = Z_to_bv 64 (to_Z off)) by (unfold adr; rewrite Hrho0; apply bv_add_0_Z_to_bv).
    rewrite E0. unfold rview. destruct (m (Z_to_bv 64 (to_Z off))) as [b|] eqn:Em.
    { exfalso. pose proof (Hinv _ _ Em) as RO. unfold ro_addr in RO. rewrite Z_to_bv_unsigned in RO. change (bv_modulus 64) with (2 ^ 64) in RO.
      rewrite (bv_wrap_small 64 (to_Z off)) in RO by (change (bv_modulus 64) with (2 ^ 64); clear - Hoff; slia).
      rewrite (Hfind (to_Z off) Hin8), Ewr, (Hro _ _ Hf) in RO. discriminate RO. }
    rewrite Hrd. cbn [option_map]. change (Z_to_le_bytes 8 (wZ w)) with (Z_to_le_bytes 8 (wZ w)).
    replace (Z_to_le_bytes 8 (wZ w)) with (wbytes8 (wbv w)) by (unfold wbytes8; rewrite wbv_unsigned; reflexivity).
    rewrite wbytes8_wbv. replace j with (Z.to_nat (to_Z (off land 7)%uint63)) by (subst j; rewrite to_Z_land7; reflexivity).
    rewrite w_bytes_nth_byte by (rewrite to_Z_land7; clear - Hoff; Z.div_mod_to_equations; slia). reflexivity.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma byte_at_0_shape : forall M off, (exists b, byte_at IM M 0%uint63 off = SK b) \/ byte_at IM M 0%uint63 off = SU.
  Proof.
    intros M off. unfold byte_at. rewrite Uint63.eqb_refl. destruct (image_cell IM ((off >> 3) << 3)%uint63) as [[tv w]|]; [left; eexists; reflexivity| right; reflexivity].
  Qed.

  Lemma copy_bytes_sound : forall k M td doff ts soff M' rg (mA : word -> option byte) (b0 : byte),
    copy_bytes IM k M td doff ts soff = Some M' -> iget td M = Some rg ->
    mem_part segs IM rho mA td rg -> td <> 0%uint63 -> rg_unk rg -> rg_inb rg ->
    to_Z doff + Z.of_nat k <= to_Z (rg_len rg) -> mem_inv segs mA ->
    (forall (i : nat) (so : int), (i < k)%nat -> to_Z so = (to_Z soff + Z.of_nat i) mod wB -> ts <> 0%uint63 ->
        exists b, rview segs mA (adr rho ts (to_Z so)) = Some b) ->
    (forall (i j : nat) (so : int), (i < k)%nat -> (j < k)%nat -> to_Z so = (to_Z soff + Z.of_nat i) mod wB ->
        adr rho ts (to_Z so) <> aoff (adr rho td (to_Z doff)) j) ->
    (forall (i : nat) (so : int) Mi rgi (mX : word -> option byte), (i < k)%nat -> to_Z so = (to_Z soff + Z.of_nat i) mod wB ->
        iget td Mi = Some rgi -> (forall t', t' <> td -> iget t' Mi = iget t' M) ->
        mem_part segs IM rho mX td rgi -> rg_unk rgi -> rg_inb rgi -> rg_len rgi = rg_len rg ->
        (forall w, (forall j, (j < k)%nat -> w <> aoff (adr rho td (to_Z doff)) j) -> mX w = mA w) ->
        mem_inv segs mX ->
        slot_val rho (byte_at IM Mi ts so) (rview segs mX (adr rho ts (to_Z so)))) ->
    exists rg' (src : list byte), iget td M' = Some rg'
      /\ (forall t', t' <> td -> iget t' M' = iget t' M)
      /\ length src = k
      /\ (forall (i : nat) (so : int), (i < k)%nat -> to_Z so = (to_Z soff + Z.of_nat i) mod wB ->
            rview segs mA (adr rho ts (to_Z so)) = Some (nth i src b0))
      /\ mem_part segs IM rho (write_to_mem mA (adr rho td (to_Z doff)) src) td rg'
      /\ rg_unk rg' /\ rg_inb rg'
      /\ (rg_lo rg' = rg_lo rg /\ rg_len rg' = rg_len rg /\ rg_align rg' = rg_align rg /\ rg_kind rg' = rg_kind rg /\ rg_dflt rg' = rg_dflt rg)
      /\ (forall i, 0 <= i < Z.of_nat k -> wview segs mA (adr rho td (to_Z doff + i)) <> None).
  Proof.
    induction k as [|k IH]; intros M td doff ts soff M' rg mA b0 Hcb Hrg Hpart Ht0 Hunk Hinb Hlen Hinv HRD HDJ HSV.
    - cbn [copy_bytes] in Hcb. injection Hcb as <-. exists rg, []. split; [exact Hrg|]. split; [intros; reflexivity|]. split; [reflexivity|].
      split; [intros i so Hi; exfalso; clear - Hi; slia|].
      split; [cbn [write_to_mem]; exact Hpart|]. split; [exact Hunk|]. split; [exact Hinb|]. split; [repeat split; reflexivity|]. intros i Hi. exfalso. cbn in Hi. slia.
    - cbn [copy_bytes] in Hcb. pose proof (i63_range doff) as Hdoff. pose proof (i63_range soff) as Hsoff. pose proof (i63_range (rg_len rg)) as Hlr.
      assert (Eso0 : to_Z soff = (to_Z soff + Z.of_nat 0) mod wB) by (change wB with (2 ^ 63); rewrite Z.add_0_r, Z.mod_small by exact Hsoff; reflexivity).
      (* [comment removed for export] *)
      pose proof (HSV 0%nat soff M rg mA ltac:(slia) Eso0 Hrg ltac:(intros; reflexivity) Hpart Hunk Hinb eq_refl ltac:(intros; reflexivity) Hinv) as V0.
      set (s := byte_at IM M ts soff) in *.
      assert (STEP : s <> SU /\ exists M1, write_byte M td doff s = Some M1 /\ copy_bytes IM k M1 td (doff + 1) ts (soff + 1) = Some M').
      { destruct s as [bb|vv jj|]; [| | discriminate Hcb]; (split; [intros E; discriminate E|]);
          (destruct (write_byte M td doff _) as [M1|] eqn:Hw; [exists M1; split; [reflexivity| exact Hcb]| discriminate Hcb]). }
      destruct STEP as (HsU & M1 & Hwb & Hcb').
      assert (R0 : exists b, rview segs mA (adr rho ts (to_Z soff)) = Some b).
      { destruct (Uint63.eqb ts 0) eqn:Ets.
        - apply Uint63.eqb_spec in Ets. destruct (byte_at_0_shape M soff) as [[bb Hbb]|HU]; [| exfalso; apply HsU; subst s; rewrite Ets; exact HU].
          subst s. rewrite Ets, Hbb in V0. cbn [slot_val] in V0. rewrite Ets. eexists. exact V0.
        - apply Uint63.eqb_false_spec in Ets. exact (HRD 0%nat soff ltac:(slia) Eso0 Ets). }
      destruct R0 as [b R0]. rewrite R0 in V0.
      destruct (write_slot_sound M td doff s b M1 rg mA Hwb Hrg Hpart Ht0 Hunk Hinb ltac:(slia) V0) as (HM1 & Hpart1 & Hunk1 & Hinb1 & (G1 & G2 & G3 & G4 & G5) & Hwr).
      set (rg1 := wb_region rg (doff >> 12) (wb_page (wb_cur rg (doff >> 12)) ((doff land 4095) >> 3) (doff land 7) s)) in *.
      assert (Hrg1 : iget td M1 = Some rg1) by (rewrite HM1, iget_iset, Uint63.eqb_refl; reflexivity).
      assert (Eoff1 : to_Z (doff + 1)%uint63 = to_Z doff + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; [reflexivity| slia]).
      assert (Esuc : forall i : nat, (to_Z (soff + 1)%uint63 + Z.of_nat i) mod wB = (to_Z soff + Z.of_nat (S i)) mod wB).
      { intros i. rewrite Uint63.add_spec. change (to_Z 1%uint63) with 1. rewrite Nat2Z.inj_succ. rewrite Zplus_mod_idemp_l. f_equal. slia. }
      set (mA1 := write_to_mem mA (adr rho td (to_Z doff)) [b]) in *.
      assert (MA1out : forall w, w <> aoff (adr rho td (to_Z doff)) 0 -> mA1 w = mA w).
      { intros w Hw. subst mA1. apply write_to_mem_out. intros j Hj. cbn [length] in Hj. replace j with 0%nat by slia. exact Hw. }
      assert (Hinv1 : mem_inv segs mA1).
      { intros a bb Ha. destruct (decide (a = adr rho td (to_Z doff))) as [->|NE].
        - destruct (mA (adr rho td (to_Z doff))) as [bo|] eqn:Eo; [exact (Hinv _ _ Eo)|].
          unfold wview in Hwr. rewrite Eo in Hwr. unfold ro_addr. destruct (find_segment segs (bv_unsigned (adr rho td (to_Z doff))) 1) as [seg|]; [| reflexivity].
          destruct (seg_writable seg); [reflexivity| exfalso; exact (Hwr eq_refl)].
        - rewrite MA1out in Ha by (rewrite aoff_0; exact NE). exact (Hinv _ _ Ha). }
      assert (ASUC : forall j : nat, aoff (adr rho td (to_Z (doff + 1)%uint63)) j = aoff (adr rho td (to_Z doff)) (S j)).
      { intros j. rewrite Eoff1. replace (to_Z doff + 1) with (to_Z doff + Z.of_nat 1) by reflexivity. rewrite <- aoff_adr. unfold aoff. rewrite Nat2Z.inj_succ. bv_solve. }
      destruct (IH M1 td (doff + 1)%uint63 ts (soff + 1)%uint63 M' rg1 mA1 b0 Hcb' Hrg1 ltac:(subst mA1; exact Hpart1) Ht0 Hunk1 Hinb1
                   ltac:(rewrite Eoff1, G2; slia) Hinv1) as (rg' & src & Hrg' & Hoth & Hsl & Hsrc & Hpart' & Hunk' & Hinb' & (F1 & F2 & F3 & F4 & F5) & Hwr').
      + (* [comment removed for export] *)
        intros i so Hi Hso Hts. rewrite Esuc in Hso. subst mA1. rewrite rview_write_out; [exact (HRD (S i) so ltac:(slia) Hso Hts)|].
        intros j Hj. cbn [length] in Hj. replace j with 0%nat by slia. exact (HDJ (S i) 0%nat so ltac:(slia) ltac:(slia) Hso).
      + (* [comment removed for export] *)
        intros i j so Hi Hj Hso. rewrite Esuc in Hso. rewrite ASUC. exact (HDJ (S i) (S j) so ltac:(slia) ltac:(slia) Hso).
      + (* [comment removed for export] *)
        intros i so Mi rgi mX Hi Hso HMi Hothi HpX HunkX HinbX HlenX HmX HinvX. rewrite Esuc in Hso.
        apply (HSV (S i) so Mi rgi mX ltac:(slia) Hso HMi); [| exact HpX| exact HunkX| exact HinbX| rewrite HlenX; exact G2| | exact HinvX].
        * intros t' Ht'. rewrite (Hothi t' Ht'), HM1, iget_iset, (proj2 (Uint63.eqb_false_spec _ _) Ht'). reflexivity.
        * intros w Hw. rewrite (HmX w); [apply MA1out; exact (Hw 0%nat ltac:(slia))|]. intros j Hj. rewrite ASUC. apply Hw. slia.
      + exists rg', (b :: src). split; [exact Hrg'|]. split; [intros t' Hne; rewrite (Hoth t' Hne), HM1, iget_iset, (proj2 (Uint63.eqb_false_spec _ _) Hne); reflexivity|].
        split; [cbn [length]; rewrite Hsl; reflexivity|].
        split.
        { intros i so Hi Hso. destruct i as [|i].
          - cbn [nth]. replace so with soff; [exact R0|]. apply to_Z_inj. rewrite Hso. exact Eso0.
          - cbn [nth]. rewrite <- Esuc in Hso. rewrite <- (Hsrc i so ltac:(slia) Hso). subst mA1. symmetry. apply rview_write_out.
            intros j Hj. cbn [length] in Hj. replace j with 0%nat by slia. rewrite Esuc in Hso. exact (HDJ (S i) 0%nat so ltac:(slia) ltac:(slia) Hso). }
        split.
        { cbn [repeat]. rewrite write_to_mem_cons. rewrite <- adr_succ. rewrite <- Eoff1. subst mA1. exact Hpart'. }
        split; [exact Hunk'|]. split; [exact Hinb'|]. split; [rewrite F1, F2, F3, F4, F5; subst rg1; cbn; repeat split; reflexivity|].
        intros i Hi. destruct (Z.eq_dec i 0) as [->|Hne].
        * rewrite Z.add_0_r. exact Hwr.
        * specialize (Hwr' (i - 1) ltac:(slia)). rewrite Eoff1 in Hwr'. replace (to_Z doff + 1 + (i - 1)) with (to_Z doff + i) in Hwr' by slia.
          destruct (decide (adr rho td (to_Z doff + i) = adr rho td (to_Z doff))) as [E|NE]; [rewrite E; exact Hwr|].
          unfold wview in Hwr' |- *. rewrite MA1out in Hwr' by (rewrite aoff_0; exact NE). exact Hwr'.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition wc_page (p : page) (ci : int) (v : fval) : page := PG true (pg_kind p) (iset ci (CV v) (pg_cells p)).

  Lemma write_cell_inv : forall M t off v M', write_cell M t off v = Some M' ->
    exists rg, iget t M = Some rg /\ pg_wr (wb_cur rg (off >> 12)) = true
      /\ M' = iset t (wb_region rg (off >> 12) (wc_page (wb_cur rg (off >> 12)) ((off land 4095) >> 3) v)) M.
  Proof.
    intros M t off v M' H. unfold write_cell in H. destruct (iget t M) as [rg|]; [|discriminate]. exists rg. split; [reflexivity|].
    unfold wb_cur, wb_region, wc_page. destruct (pg_wr _) eqn:E; [|discriminate]. cbn [andb] in H.
    match type of H with (if ?b then _ else _) = _ => destruct b; [|discriminate] end. split; [reflexivity|]. injection H as <-. reflexivity.
  Qed.

  Lemma write_cell_sound : forall M t off v M' rg mA,
    write_cell M t off v = Some M' -> iget t M = Some rg ->
    mem_part segs IM rho mA t rg -> t <> 0%uint63 -> rg_unk rg -> rg_inb rg ->
    to_Z off + 8 <= to_Z (rg_len rg) -> to_Z off mod 8 = 0 ->
    let a := adr rho t (to_Z off) in
    let rg' := wb_region rg (off >> 12) (wc_page (wb_cur rg (off >> 12)) ((off land 4095) >> 3) v) in
    M' = iset t rg' M
    /\ mem_part segs IM rho (write_to_mem mA a (wbytes8 (dv rho v))) t rg'
    /\ rg_unk rg' /\ rg_inb rg'
    /\ (rg_lo rg' = rg_lo rg /\ rg_len rg' = rg_len rg /\ rg_align rg' = rg_align rg /\ rg_kind rg' = rg_kind rg /\ rg_dflt rg' = rg_dflt rg)
    /\ (forall j : nat, (j < 8)%nat -> wview segs mA (aoff a j) <> None).
  Proof.
    intros M t off v M' rg mA Hwc Hrg Hpart Ht0 (Hlo0 & Hdf & Hkinds) Hinb Hoff8 Hal. cbv zeta.
    destruct (write_cell_inv _ _ _ _ _ Hwc) as (rg_ & Hrg_ & PGWR & HM'). rewrite Hrg in Hrg_. injection Hrg_ as <-.
    pose proof (i63_range off) as Hoff. pose proof (i63_range (rg_len rg)) as Hlen.
    destruct Hpart as [Hreg Hpages]. pose proof Hreg as (Hpl & Hlen62 & _).
    set (pn := (off >> 12)%uint63) in *. set (ci := ((off land 4095) >> 3)%uint63) in *.
    assert (Epn : to_Z pn = to_Z off / 4096) by (subst pn; apply to_Z_lsr12).
    assert (Eci : to_Z ci = (to_Z off mod 4096) / 8) by (subst ci; rewrite to_Z_lsr3, to_Z_land4095; reflexivity).
    assert (Hdec : to_Z pn * 4096 + to_Z ci * 8 = to_Z off) by (rewrite Epn, Eci; clear - Hoff Hal; Z.div_mod_to_equations; slia).
    assert (Hpn : 0 <= to_Z pn < 2 ^ 50) by (rewrite Epn; split; [Z.div_mod_to_equations; slia| apply Z.div_lt_upper_bound; slia]).
    assert (Hci : 0 <= to_Z ci < 512) by (rewrite Eci; apply cell_index_range; slia).
    set (p := wb_cur rg pn) in *.
    assert (Hkp : pg_kind p = PKUnk) by (subst p; unfold wb_cur; destruct (iget pn (rg_pages rg)) as [p0|] eqn:Ep; [exact (Hkinds _ _ Ep)| reflexivity]).
    assert (PA : page_at IM rg t pn = Some p).
    { subst p. unfold wb_cur, page_at. destruct (iget pn (rg_pages rg)) as [p0|] eqn:Ep; [reflexivity|].
      destruct (t =? 0)%uint63 eqn:Et; [apply Uint63.eqb_spec in Et; congruence|]. rewrite Hdf.
      rewrite (page_in_region_intro rg pn Hlo0 Hlen62 ltac:(slia) ltac:(rewrite Epn; Z.div_mod_to_equations; slia)). reflexivity. }
    destruct (Hpages pn p (proj2 Hpn) PA) as [Hpage [Hplo Hplt]]. pose proof Hpage as (Hwv & Hcells & Hslots & Hcut).
    set (B := blim rg pn) in *.
    assert (HB : to_Z ci * 8 + 8 <= B /\ B <= 4096 /\ B <= to_Z (rg_len rg) - to_Z pn * 4096).
    { subst B. unfold blim. rewrite Epn, Eci. clear - Hoff8 Hoff Hal. Z.div_mod_to_equations. slia. }
    set (mB := write_to_mem mA (adr rho t (to_Z off)) (wbytes8 (dv rho v))).
    assert (VIEWj : forall j : nat, (j < 8)%nat -> cell_view segs rho mB t pn ci j = nth_error (wbytes8 (dv rho v)) j).
    { intros j Hj. unfold cell_view. rewrite Hdec. subst mB. rewrite <- aoff_adr. apply (rview_write_in' segs); [rewrite length_wbytes8; clear; slia| rewrite length_wbytes8; exact Hj]. }
    split; [exact HM'|]. split; [| split; [| split; [| split; [cbn; repeat split; reflexivity|]]]].
    - (* [comment removed for export] *)
      split; [exact Hreg|]. intros pn1 p1 Hpn1 Hp1. cbn [wb_region rg_lo rg_len] in Hp1 |- *.
      change (blim (wb_region rg pn (wc_page p ci v)) pn1) with (blim rg pn1).
      assert (Hp1' : (pn1 = pn /\ p1 = wc_page p ci v) \/ (pn1 <> pn /\ page_at IM rg t pn1 = Some p1)).
      { unfold page_at, wb_region in Hp1. cbn [rg_pages rg_dflt] in Hp1. rewrite iget_iset in Hp1.
        destruct (pn1 =? pn)%uint63 eqn:E; [apply Uint63.eqb_spec in E; left; split; [exact E| injection Hp1 as <-; reflexivity]|].
        apply Uint63.eqb_false_spec in E. right. split; [exact E|]. unfold page_at. exact Hp1. }
      destruct Hp1' as [[-> ->]|[Hnepn Hp1']].
      + split; [| split; [exact Hplo| exact Hplt]]. split; [| split; [| split]].
        * intros _ jj Hjj. subst mB. apply wview_write. exact (Hwv PGWR jj Hjj).
        * intros ci1 v1 Hci1 Hcell1 jj Hjj. unfold wc_page in Hcell1. rewrite cell_at_wb in Hcell1.
          destruct (ci1 =? ci)%uint63 eqn:E.
          -- apply Uint63.eqb_spec in E. subst ci1. injection Hcell1 as <-. exact (VIEWj jj Hjj).
          -- apply Uint63.eqb_false_spec in E. pose proof (i63_range ci1) as Rci1.
             change (rview segs mB (adr rho t (to_Z pn * 4096 + to_Z ci1 * 8 + Z.of_nat jj))) with (cell_view segs rho mB t pn ci1 jj).
             unfold cell_view. subst mB. rewrite rview_write_out; [exact (Hcells ci1 v1 Hci1 Hcell1 jj Hjj)|].
             intros k Hk. rewrite length_wbytes8 in Hk. apply frame_same_region; [clear - Hci1 Hjj Hpn HB Rci1; slia| clear - Hoff; slia| clear - Hoff Hoff8 Hlen62 Hk; slia|].
             intros EQ. apply E. apply to_Z_inj. clear - EQ Hdec Hjj Hk Hci1 Hci; slia.
        * intros ci1 sl Hci1 Hcb1 Hg1 jj Hjj. unfold wc_page in Hg1. cbn [pg_cells] in Hg1. rewrite iget_iset in Hg1.
          destruct (ci1 =? ci)%uint63 eqn:E; [discriminate Hg1|]. apply Uint63.eqb_false_spec in E. pose proof (i63_range ci1) as Rci1.
          destruct (Hslots ci1 sl Hci1 Hcb1 Hg1 jj Hjj) as [Hsin Hsout]. split; [| exact Hsout].
          intros HjjB. apply (slot_ok_val segs rho). subst mB. rewrite rview_write_out; [apply (slot_ok_val segs rho); exact (Hsin HjjB)|].
          intros k Hk. rewrite length_wbytes8 in Hk. apply frame_same_region; [clear - Hci1 Hcb1 Hjj Hpn HB Rci1; slia| clear - Hoff; slia| clear - Hoff Hoff8 Hlen62 Hk; slia|].
          intros EQ. apply E. apply to_Z_inj. clear - EQ Hdec Hjj Hk Hci1 Hci; slia.
        * intros ci1 Hci1 Hcut1. unfold wc_page. rewrite cell_at_wb. destruct (ci1 =? ci)%uint63 eqn:E; [| exact (Hcut ci1 Hci1 Hcut1)].
          apply Uint63.eqb_spec in E. subst ci1. exfalso. clear - Hcut1 HB. slia.
      + destruct (Hpages pn1 p1 Hpn1 Hp1') as [Hok Hb1]. split; [| exact Hb1]. subst mB. apply page_ok_frame; [exact Hok|].
        intros ci1 jj k Hci1 Hcb1 Hjj Hk. rewrite length_wbytes8 in Hk.
        assert (Hne : to_Z pn1 <> to_Z pn) by (intros Q; apply Hnepn, to_Z_inj, Q). pose proof (i63_range pn1) as Rpn1. pose proof (blim_le rg pn1) as Bl1.
        apply frame_same_region; [clear - Hci1 Hcb1 Hjj Rpn1 Hpn1 Bl1; slia| clear - Hoff; slia| clear - Hoff Hoff8 Hlen62 Hk; slia| clear - Hne Hci1 Hcb1 Hjj Bl1 Hdec Hci HB Hk; slia].
    - (* [comment removed for export] *) split; [exact Hlo0|]. split; [exact Hdf|]. intros pn1 p1 Hp1. cbn [wb_region rg_pages] in Hp1. rewrite iget_iset in Hp1.
      destruct (pn1 =? pn)%uint63; [injection Hp1 as <-; cbn; exact Hkp| exact (Hkinds _ _ Hp1)].
    - (* [comment removed for export] *) intros pn1 p1 ci1 c1 Hp1 Hc1. cbn [wb_region rg_pages rg_len] in Hp1 |- *. rewrite iget_iset in Hp1.
      destruct (pn1 =? pn)%uint63 eqn:Epn1.
      + apply Uint63.eqb_spec in Epn1. subst pn1. injection Hp1 as <-. unfold wc_page in Hc1. cbn [pg_cells] in Hc1. rewrite iget_iset in Hc1.
        destruct (ci1 =? ci)%uint63 eqn:Eci1.
        * apply Uint63.eqb_spec in Eci1. subst ci1. split; [clear - HB; slia|]. split; [exact (proj2 Hci)|]. intros _ _. clear - HB. slia.
        * subst p. unfold wb_cur in Hc1. destruct (iget pn (rg_pages rg)) as [p0|] eqn:Ep; [exact (Hinb pn p0 ci1 c1 Ep Hc1)|]. cbn [pg_cells] in Hc1. rewrite iget_iempty in Hc1. discriminate Hc1.
      + exact (Hinb pn1 p1 ci1 c1 Hp1 Hc1).
    - (* [comment removed for export] *)
      intros j Hj. rewrite aoff_adr. specialize (Hwv PGWR (to_Z ci * 8 + Z.of_nat j) ltac:(clear - HB Hci Hj; slia)).
      replace (to_Z pn * 4096 + (to_Z ci * 8 + Z.of_nat j)) with (to_Z off + Z.of_nat j) in Hwv by (clear - Hdec; slia). exact Hwv.
  Qed.
End Fill.
