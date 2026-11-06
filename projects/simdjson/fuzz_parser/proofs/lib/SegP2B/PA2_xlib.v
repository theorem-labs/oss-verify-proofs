(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge Mem Cells Step Frame SysStep.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells ABase AMalloc_iface AU_iface AU_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2B Require Import APS2_iface A2Lib PA2_kz.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.
Local Notation u := bv_unsigned.
Local Notation M64 := 18446744073709551616.
Local Notation SH := 2147450880%Z (only parsing).

Section CANSEC. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma rw8_of : forall m A w, bytes_at bsegs m A (word_to_le_bytes 8 w) -> wr_at bsegs m A 8 -> rw_cells bsegs m A [C8 w].
Proof.
  intros m A w HB HW. split; [split|].
  - cbn. split; [exact I | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold le8. exact HB.
  - exact HW.
Qed.
Lemma rw4_of : forall m A w, bytes_at bsegs m A (word_to_le_bytes 4 w) -> wr_at bsegs m A 4 -> rw_cells bsegs m A [C4 w].
Proof.
  intros m A w HB HW. split; [split|].
  - cbn. split; [exact I | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold le4. exact HB.
  - exact HW.
Qed.
Lemma wr_at_sub : forall m A n A' n', wr_at bsegs m A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> wr_at bsegs m A' n'.
Proof.
  intros m A n A' n' (H0 & H1 & H) HA HB Hn. split; [lia|]. split; [lia|]. intros i Hi.
  replace (A' + i) with (A + (A' - A + i)) by lia. apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma kx_zero_g : forall segs G ZL E' m b k n, SP.gagree G (mkEZ ZL) E' -> eb (mkEZ ZL) = eb E' ->
  expr_vars_lt G b = true -> expr_vars_lt G n = true -> (zok b && zok n)%bool = true ->
  kentry_ok segs E' m (KZero (SA b k) n) ->
  forall i, 0 <= i < zden ZL n mod M64 -> m (Z_to_bv 64 (zden ZL b mod M64 + k + i)) = Some (Z_to_bv 8 0).
Proof.
  intros segs G ZL E' m b k n Hg Hb Hvb Hvn Hz HK i Hi. apply andb_prop in Hz as [Hzb Hzn].
  destruct HK as [_ HZ].
  assert (EB : edenot E' b = edenot (mkEZ ZL) b) by (symmetry; exact (SP.edenot_gagree G (mkEZ ZL) E' b Hg Hb Hvb)).
  assert (EN : edenot E' n = edenot (mkEZ ZL) n) by (symmetry; exact (SP.edenot_gagree G (mkEZ ZL) E' n Hg Hb Hvn)).
  specialize (HZ i). unfold estart, elenZ in HZ. cbn [a_base a_off] in HZ. rewrite EB, EN in HZ.
  rewrite !u_zden in HZ by assumption.
  apply HZ. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma kx_wr_g : forall segs G ZL E' m b k n, SP.gagree G (mkEZ ZL) E' -> eb (mkEZ ZL) = eb E' ->
  expr_vars_lt G b = true -> expr_vars_lt G n = true -> (zok b && zok n)%bool = true ->
  kentry_ok segs E' m (KWr (SA b k) n) ->
  wr_at segs m (zden ZL b mod M64 + k) (zden ZL n mod M64).
Proof.
  intros segs G ZL E' m b k n Hg Hb Hvb Hvn Hz HK. apply andb_prop in Hz as [Hzb Hzn].
  destruct HK as [Hfl HS].
  assert (EB : edenot E' b = edenot (mkEZ ZL) b) by (symmetry; exact (SP.edenot_gagree G (mkEZ ZL) E' b Hg Hb Hvb)).
  assert (EN : edenot E' n = edenot (mkEZ ZL) n) by (symmetry; exact (SP.edenot_gagree G (mkEZ ZL) E' n Hg Hb Hvn)).
  unfold flat, estart, elenZ in Hfl, HS. cbn [a_base a_off] in Hfl, HS. rewrite EB, EN in Hfl, HS. rewrite !u_zden in Hfl, HS by assumption.
  destruct Hfl as (F1 & F2 & F3 & F4).
  split; [lia|]. split; [lia|]. intros i Hi.
  specialize (HS i 1%nat ltac:(lia) ltac:(lia)). cbn [store_ok] in HS. unfold wa.
  destruct (wview segs m (Z_to_bv 64 (zden ZL b mod M64 + k + i))); [discriminate | discriminate].
Qed.

(* [comment removed for export] *)
Lemma img_sh_pres_W : forall (AI : AMallocIface) LB SP W m m', (forall iv, In iv client_ranges -> In iv (aci AI)) ->
  img_sh m -> aheap_pres_W (aci AI) LB SP W m m' -> (forall a, 0x7fff8000 <= a < 0x7fff8000 + 0xce200 -> outside W a) -> img_sh m'.
Proof.
  intros AI LB SP W m m' HCI HI HP HO. unfold img_sh in *. apply Forall_forall. intros [lo hi] Hin.
  pose proof (proj1 (Forall_forall _ _) HI _ Hin) as HT. pose proof (img_tabs_bounds lo hi Hin) as B.
  unfold tab_sh in *. cbn [fst snd] in *.
  eapply aheap_pres_W_rw_cells; [exact HP | exact HT | |].
  - right; right. right; left.
    exists (lo, hi). split; [apply HCI; unfold client_ranges; apply in_or_app; right; exact Hin|].
    cbn [fst snd cells_size csize]. rewrite ?Nat.add_0_r. rewrite shad_div. unfold ASHOFF. rewrite Z2Nat.id by (Z.div_mod_to_equations; lia).
    Z.div_mod_to_equations. lia.
  - intros a Ha. apply HO. cbn [cells_size csize] in Ha. rewrite ?Nat.add_0_r, Z2Nat.id in Ha by (Z.div_mod_to_equations; lia).
    rewrite shad_div in Ha. unfold ASHOFF in Ha. Z.div_mod_to_equations. lia.
Qed.
Lemma fmin_pres_W : forall (AI : AMallocIface) LB SP W m m', (forall iv, In iv client_ranges -> In iv (aci AI)) ->
  rt_fmin m -> aheap_pres_W (aci AI) LB SP W m m' -> (forall a, AFMIN <= a < AFMIN + 4 -> outside W a) -> rt_fmin m'.
Proof.
  intros AI LB SP W m m' HCI HF HP HO. unfold rt_fmin in *.
  eapply aheap_pres_W_rw_cells; [exact HP | exact HF | |].
  - left; right; left. exists (0x1174c0, 0x1174c4). split; [apply HCI; unfold client_ranges; cbn [In app]; tauto | cbn; unfold AFMIN; lia].
  - exact HO.
Qed.
Lemma shlen_d8 : forall l, shlen l = l / 8.
Proof. intros l. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma blk_granule : forall (AI : AMallocIface) L RNG st LB m p A n g, AHEAP AI L RNG st LB m -> In (HB p A n) LB -> 0 <= g -> 8 * g < n ->
  m (Z_to_bv 64 (shad A + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? n then 0 else n - 8 * g)).
Proof.
  intros AI L RNG st LB m p A n g AH HIN Hg Hn.
  destruct (AI_block AI _ _ _ _ _ _ _ _ AH HIN) as (_ & _ & _ & _ & BSH & _). exact (BSH g Hg Hn).
Qed.
(* [comment removed for export] *)
Lemma bytes1_of : forall m A b, 0x671000 <= A -> A + 1 <= M64 -> m (Z_to_bv 64 A) = Some b -> bytes_at bsegs m A [b].
Proof.
  intros m A b H1 H2 H. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. assert (i = 0%nat) as -> by lia.
  cbn [nth_error]. rewrite Z.add_0_r. unfold wa. rewrite ref_mrd_overlay by (rewrite u_Z_to_bv, Z.mod_small by lia; lia). exact H.
Qed.
Lemma le1_small : forall x, 0 <= x < 256 -> word_to_le_bytes 1 (Z_to_bv 64 x) = [Z_to_bv 8 x].
Proof.
  intros x Hx. unfold word_to_le_bytes. cbn [Z_to_le_bytes]. rewrite u_Z_to_bv, Z.mod_small by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma lb_remove_id : forall q LB, ~ In q (hb_ids LB) -> lb_remove q LB = LB.
Proof.
  intros q LB. induction LB as [|b LB IH]; intros H; [reflexivity|].
  unfold lb_remove in *. destruct b as [k A n]. destruct k as [q'|c].
  - destruct (N.eqb_spec q' q) as [->|Hne].
    + exfalso. apply H. cbn. left. reflexivity.
    + rewrite filter_cons, decide_True.
      * f_equal. apply IH. intros Hin. apply H. cbn. right. exact Hin.
      * cbn [ab_kind abkind_eqb]. apply N.eqb_neq in Hne. rewrite Hne. exact I.
  - rewrite filter_cons, decide_True; [f_equal; apply IH; exact H | cbn; exact I].
Qed.
End CANSEC.
