(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Mem RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common Require PropExec.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.VCommon Require Import FastWord.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie AxLazy AxLin AxVal AxBytes AxImg AxMem AxRng AxZZ AxScan AxState AxSys AxAcct AxMeasure AxGrant AxEntryS AxModelRel.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AxA Require Import AxExport.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Section ExportI.
Variable segs : list Segment.
Variable pc0 : N.
Hypothesis Himg : img_ok segs pc0 = true.
Variable fs0 : Fs.Fs.
Variable LIM : Z.
Variable ρ : valuation.
Variable B : AST.
Variable ms : machine_state.
Variable model : Model.
Hypothesis HR : R segs amodel (MR segs fs0 ρ) LIM ρ B (mkCfg ms model).
Variable A' : list (Z * Z).

Local Notation mX := (AxExport.mX ms model A').
Local Notation vis := (AxExport.vis model A').

Let Hlow : segs_low segs := img_low segs pc0 Himg.
Let HM : MR segs fs0 ρ (a_model B) model := r_model _ _ _ _ _ _ _ HR.
Let Hsat : sat ρ (a_facts B) := r_sat _ _ _ _ _ _ _ HR.

(* [comment removed for export] *)
Lemma maps_not_segs (z : Z) : inl (vm_maps (m_vmmaps model)) z -> ~ in_segs segs z.
Proof.
  intros [p [Hp Hz]] Hs. destruct (in_segs_reserved segs Hlow z Hs) as [q [Hq Hzq]].
  rewrite <- (mr_res segs fs0 ρ _ model HM) in Hq.
  pose proof (mr_disj segs fs0 ρ _ model HM p q Hp Hq) as D. unfold iv_disj in D. lia.
Qed.

(* [comment removed for export] *)
Definition atop_hi_ok : bool :=
  match lrange (a_facts B) (am_atop (a_model B)) with Some (lo, _) => ls_beg <=? lo | None => false end.

Theorem ex_mem_inv : atop_hi_ok = true -> Mem.mem_inv segs mX.
Proof.
  intros Hat a. unfold Mem.mem_ok_at. apply andb_true_intro. split.
  - unfold Mem.seg_addr. destruct (find_segment segs (bv_unsigned a) 1) as [sg|] eqn:Ef; [|reflexivity].
    destruct (find_segment_at' segs _ sg Ef) as [HIn Hr]. pose proof (Hlow sg HIn) as Hl. apply Z.ltb_lt. unfold Mem.UTOP, ls_beg in *. lia.
  - destruct (mX a) as [b|] eqn:Em; [|reflexivity].
    unfold AxExport.mX, mrestrict in Em. destruct (RzCPS.HID A' model a) eqn:Eh; [discriminate Em|].
    unfold RzCPS.HID in Eh. apply orb_false_iff in Eh as [_ Eh]. apply Z.leb_gt in Eh.
    apply andb_true_intro. split; [|apply Z.ltb_lt; unfold Mem.UTOP; lia].
    apply negb_true_iff. unfold Mem.ro_addr.
    destruct (find_segment segs (bv_unsigned a) 1) as [sg|] eqn:Ef; [|reflexivity].
    destruct (find_segment_at' segs _ sg Ef) as [HIn Hr]. pose proof (Hlow sg HIn) as Hl.
    assert (Hs : in_segs segs (bv_unsigned a)) by (exists sg; split; assumption).
    pose proof (r_cov _ _ _ _ _ _ _ HR a ltac:(cbn [cfg_ms]; rewrite Em; discriminate)) as Hc. cbn [cfg_model] in Hc.
    destruct Hc as [[_ Hro]|[Hc|Hc]].
    + unfold ro_at in Hro. rewrite Ef in Hro. exact Hro.
    + exfalso. unfold atop_hi_ok in Hat. destruct (lrange (a_facts B) (am_atop (a_model B))) as [[lo hi]|] eqn:El; [|discriminate Hat].
      apply Z.leb_le in Hat. pose proof (lrange_sound ρ _ _ Hsat _ El) as Xr. cbn [fst snd] in Xr.
      rewrite (mr_atop segs fs0 ρ _ model HM) in Hc. lia.
    + exfalso. exact (maps_not_segs _ Hc Hs).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition img_rg (Rq : region) : option (nat * Segment) :=
  match rg_kind Rq with
  | KImg _ i => match nth_error segs i with
                | Some sg => if (match rg_ts Rq with [] => true | _ => false end) &&& (wZ (rg_bo Rq) =? Z.of_N (seg_base sg))
                                &&& (to_Z (rg_n Rq) <=? Z.of_N (seg_size sg)) then Some (i, sg) else None
                | None => None
                end
  | _ => None
  end.

(* [comment removed for export] *)
Definition xb_lit_eqb (a b : xb) : bool := match a, b with BL c1, BL c2 => (c1 =? c2)%uint63 | _, _ => false end.

Lemma xb_lit_eqb_eq (a b : xb) : xb_lit_eqb a b = true -> a = b.
Proof. destruct a, b; try discriminate. cbn [xb_lit_eqb]. intros H. apply Uint63.eqb_spec in H. subst. reflexivity. Qed.

Definition bytes_dflt (Rq : region) (x : Z) (n : nat) : bool :=
  forallb (fun i => let y := of_Z (x + Z.of_nat i) in xb_lit_eqb (rbyte segs Rq y) (default_byte segs (rg_kind Rq) y)) (seq 0 n).

Definition pristine_ok (Rq : region) (x n : Z) : bool :=
  match img_rg Rq with
  | Some _ => rng_all (fun (_ : Z) (_ : cell) => false) (rg_d Rq) (rg_cells Rq) (x / 8) ((x + n - 1) / 8)
              ||| ((n <=? 65536) &&& bytes_dflt Rq x (Z.to_nat n))
  | None => false
  end.

Theorem export_pristine (Rq : region) (x n : Z) : In Rq (a_mem B) -> pristine_ok Rq x n = true -> 0 <= x -> x + n <= to_Z (rg_n Rq) ->
  vis (rbase ρ Rq + x) (rbase ρ Rq + x + n) ->
  forall a, rbase ρ Rq + x <= a < rbase ρ Rq + x + n -> Mem.mrd segs mX (wz a) = Common.PropExec.seg_rom segs (wz a).
Proof.
  intros HIn Hok Hx Hfit Hvis a Ha. change (Common.PropExec.seg_rom segs (wz a)) with (VCommon.PropExec.seg_rom segs (wz a)). unfold pristine_ok in Hok. destruct (img_rg Rq) as [[i sg]|] eqn:Ei; [|discriminate Hok].
  unfold img_rg in Ei. destruct (rg_kind Rq) as [| | |w i0|ph] eqn:Ek; try discriminate Ei.
  destruct (nth_error segs i0) as [sg0|] eqn:En; [|discriminate Ei].
  destruct (rg_ts Rq) as [|t0 tr] eqn:Ets; [|discriminate Ei]. cbv iota in Ei.
  destruct ((wZ (rg_bo Rq) =? Z.of_N (seg_base sg0)) &&& (to_Z (rg_n Rq) <=? Z.of_N (seg_size sg0))) eqn:Eg; [|discriminate Ei].
  injection Ei as <- <-. apply land_true in Eg as [G1 G2]. apply Z.eqb_eq in G1. apply Z.leb_le in G2.
  pose proof (r_mem _ _ _ _ _ _ _ HR) as [Hrok HF]. cbn [cfg_ms] in HF, Hrok.
  destruct (regions_ok_in ρ _ Rq Hrok HIn) as (W1 & W2 & W3 & _).
  assert (He : is_entry Rq = false) by (unfold is_entry; rewrite Ek; reflexivity).
  assert (Eb : rbase ρ Rq = Z.of_N (seg_base sg0)).
  { unfold rbase, smod. rewrite Ets. cbn [teval]. rewrite Z.add_0_l, Z.mod_small by apply wZ_range. exact G1. }
  set (y := of_Z (a - rbase ρ Rq)). assert (Ey : to_Z y = a - rbase ρ Rq) by (unfold y; apply phi_of_Z_small; lia).
  assert (Ea : rbase ρ Rq + to_Z y = a) by lia.
  destruct (export_byte segs fs0 LIM ρ B ms model HR A' Rq y HIn He ltac:(lia) ltac:(rewrite Ea; apply Hvis; lia)) as [[b [Hb Hxb]] _].
  rewrite Ea in Hb. rewrite Hb.
  (* [comment removed for export] *)
  assert (Hrb : rbyte segs Rq y = default_byte segs (rg_kind Rq) y).
  { apply lor_true in Hok as [Hok|Hok].
    - unfold rbyte, get_cell_opt. destruct (iget (rg_d Rq) (rg_cells Rq) (y >> 3)%uint63) as [c|] eqn:Eg; [|reflexivity]. exfalso.
      pose proof (rng_all_iget (fun (_ : Z) (_ : cell) => false) _ _ _ _ (y >> 3)%uint63 c Hok) as Y. cbv beta in Y.
      assert (Hk : x / 8 <= to_Z (y >> 3)%uint63 <= (x + n - 1) / 8) by (rewrite phi_lsr3; split; apply Z.div_le_mono; lia).
      specialize (Y Hk (key_small Rq y W3 ltac:(lia)) Eg). discriminate Y.
    - apply land_true in Hok as [_ Hby]. unfold bytes_dflt in Hby. rewrite forallb_forall in Hby.
      specialize (Hby (Z.to_nat (a - rbase ρ Rq - x)) ltac:(apply in_seq; lia)). cbv zeta in Hby.
      replace (of_Z (x + Z.of_nat (Z.to_nat (a - rbase ρ Rq - x)))) with y in Hby by (unfold y; f_equal; lia).
      exact (xb_lit_eqb_eq _ _ Hby). }
  rewrite Hrb, Ek in Hxb. cbn [default_byte] in Hxb.
  destruct (seg_ok1_facts sg0 (img_ok_seg segs pc0 sg0 Himg (nth_error_In _ _ En))) as (c & Hc & Hsz & Hl & Hrd & _ & _ & Hscan).
  destruct (img_ok_parts segs pc0 Himg) as (_ & Hpw & _).
  assert (Hnz : to_Z (of_Z (Z.of_N (seg_size sg0))) = Z.of_N (seg_size sg0)) by (apply phi_of_Z_small; lia).
  pose proof (scanI_sound c 64 0%uint63 _ ltac:(rewrite Hnz; change (to_Z 0%uint63) with 0; lia) Hscan (to_Z y) ltac:(rewrite Hnz; lia)) as Hfb.
  change (to_Z 0%uint63) with 0 in Hfb. rewrite Z.add_0_l, of_to_Z in Hfb.
  destruct (fimg_c c y) as [ib|] eqn:Efc; [|congruence].
  assert (Efi : fimg_i segs i0 y = Some ib) by (unfold fimg_i; rewrite En, Hc; exact Efc).
  rewrite Efi in Hxb. rewrite (xb_lit ρ ib b Hxb).
  pose proof (find_seg_pw segs Hpw i0 sg0 (Z.of_N (seg_base sg0) + to_Z y) En ltac:(lia)) as Hf.
  pose proof (fimg_i_rom segs i0 y ib sg0 En Efi Hf Hrd ltac:(unfold ls_beg in Hl; lia)) as Hrom.
  replace (Z.of_N (seg_base sg0) + to_Z y) with a in Hrom by lia. unfold wz. rewrite Hrom. reflexivity.
Qed.

End ExportI.
