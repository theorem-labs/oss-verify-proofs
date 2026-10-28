(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import GDesc RT_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxToolkit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXB Require Import HxaInit HxaImage HxaInv HxaHooks HxaImgShCert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ush_byte (n off : Z) : Z :=
  if off <? n / 8 then 0 else if (off =? n / 8) && negb (n mod 8 =? 0) then n mod 8 else -1.

Lemma ush_byte_ok (n off v : Z) : 0 <= n -> 0 <= off -> ush_byte n off = v -> 0 <= v ->
  nth_error (ushadow n) (Z.to_nat off) = Some (Z_to_bv 8 v).
Proof.
  intros Hn Hoff E Hv. unfold ush_byte in E. unfold ushadow. assert (H8 : 0 <= n / 8) by (apply Z.div_pos; lia).
  destruct (Z.ltb_spec off (n / 8)) as [L|L].
  - subst v. rewrite nth_error_app1 by (rewrite repeat_length; lia). apply nth_error_repeat. lia.
  - destruct (Z.eqb_spec off (n / 8)) as [Eo|Eo]; [|cbn [andb] in E; lia]. destruct (Z.eqb_spec (n mod 8) 0) as [E0|E0]; [cbn in E; lia|].
    cbn [andb negb] in E. subst v. rewrite nth_error_app2 by (rewrite repeat_length; lia). rewrite repeat_length, Eo, Nat.sub_diag. reflexivity.
Qed.

Definition in_ranges_b (l : list (Z * Z)) (a : Z) : bool := existsb (fun rg => (fst rg <=? a) && (a <? snd rg)) l.

Lemma in_ranges_b_spec (l : list (Z * Z)) (a : Z) : in_ranges_b l a = true <-> in_ranges l a.
Proof.
  unfold in_ranges_b, in_ranges. rewrite existsb_exists. split.
  - intros ([lo hi] & Hin & H). apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists lo, hi. cbn [fst snd] in *. auto.
  - intros (lo & hi & Hin & H). exists (lo, hi). split; [exact Hin|]. cbn [fst snd]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Definition acc_static_b (a : Z) : bool :=
  in_ranges_b CLIENT_STATIC a && negb (in_ranges_b RT_STATIC a)
  && negb ((0x5e7460 <=? a) && (a <? 0x6a0320)) && negb ((0x5e6660 <=? a) && (a <? 0x5e7140)) && negb ((0xbd6080 <=? a) && (a <? 0xbda540)).

Lemma acc_static_b_ok (a : Z) : acc_static_b a = true ->
  client_static a /\ ~ (0x5e7460 <= a < 0x6a0320) /\ ~ (0x5e6660 <= a < 0x5e7140) /\ ~ (0xbd6080 <= a < 0xbda540).
Proof.
  unfold acc_static_b. intros H. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  split; [split; [apply in_ranges_b_spec; exact H1 | intros X; apply in_ranges_b_spec in X; rewrite X in H2; discriminate]|].
  repeat split; intros [X1 X2]; [apply negb_true_iff in H3 as Y | apply negb_true_iff in H4 as Y | apply negb_true_iff in H5 as Y];
    apply andb_false_iff in Y as [Y|Y]; [apply Z.leb_gt in Y | apply Z.ltb_ge in Y | apply Z.leb_gt in Y | apply Z.ltb_ge in Y | apply Z.leb_gt in Y | apply Z.ltb_ge in Y]; lia.
Qed.

(* [comment removed for export] *)
Definition byte_why_ok (k j : Z) (w : nat) (z : Z) : bool :=
  let s := IMGSH_LO + 8 * k + j in
  match w with
  | O => (z =? 0) && forallb (fun i => acc_static_b ((s - SHB) * 8 + i)) [0; 1; 2; 3; 4; 5; 6; 7]
  | Datatypes.S gi =>
      match nth_error GDESC gi with
      | Some g => (0 <=? s - shad (gd_beg g)) && (ush_byte (gd_size g) (s - shad (gd_beg g)) =? z) && (0 <=? z) && (0 <=? gd_size g) && (0 <=? gd_beg g)
      | None => false
      end
  end.

Fixpoint assoc_k (k : Z) (l : list (Z * list (Z * nat))) : list (Z * nat) :=
  match l with [] => [] | (k', e) :: l' => if k' =? k then e else assoc_k k l' end.

Definition cell_why_ok (CERT : list (Z * list (Z * nat))) (k : Z) (c : HxMem.cell) : bool :=
  match c with
  | CW w km =>
      let e := assoc_k k CERT in
      forallb (fun j => negb (Z.testbit (to_Z km) j) || existsb (fun jw => (fst jw =? j) && byte_why_ok k j (snd jw) (byteZ (wZ w) j)) e) [0; 1; 2; 3; 4; 5; 6; 7]
  | CP _ _ => false
  end.

Definition cells_check (f : Z -> HxMem.cell -> bool) (T : itrie HxMem.cell) : bool :=
  iall (fun _ : HxMem.cell => false) (imapo (fun k v => if f k v then None else Some v) T 0 1).

Lemma cells_check_ok (f : Z -> HxMem.cell -> bool) (d : nat) (T : itrie HxMem.cell) : cells_check f T = true ->
  forall k c, to_Z k < 2 ^ Z.of_nat d -> iget d T k = Some c -> f (to_Z k) c = true.
Proof.
  intros Hc k c Hk G. destruct (f (to_Z k) c) eqn:Ef; [reflexivity|]. exfalso.
  pose proof (iget_imapo (fun k v => if f k v then None else Some v) d T 0 1 k) as E. rewrite G in E.
  pose proof (to_Z_bounded k) as Bk. rewrite Z.add_0_l, Z.mul_1_l in E. rewrite Z.mod_small in E by lia.
  rewrite Ef in E. pose proof (iall_iget (fun _ : HxMem.cell => false) d _ k c Hc E). discriminate.
Qed.

Lemma imgsh_checked : cells_check (cell_why_ok IMGSH_CERT) (rg_cells RG_IMGSH) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma assoc_k_in (k : Z) (l : list (Z * list (Z * nat))) (x : Z * nat) : In x (assoc_k k l) -> True.
Proof. auto. Qed.

Section ImgShOk.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Section Gen.
Variable RGS : region.
Variable CERT : list (Z * list (Z * nat)).
Hypothesis IMGSH_abs : rg_abs RGS = Some 2147459072%uint63.
Hypothesis IMGSH_size : to_Z (rg_size RGS) = 1563136.
Hypothesis IMGSH_al : to_Z (rg_al RGS) = 3.
Hypothesis IMGSH_wr : rg_wr RGS = false.
Hypothesis IMGSH_dflt : rg_dflt RGS = DUnk.
Hypothesis IMGSH_d : rg_d RGS = 18%nat.
Hypothesis RGS_checked : cells_check (cell_why_ok CERT) (rg_cells RGS) = true.

Theorem imgsh_region_ok : forall (Σ : rts RT) (m : word -> option byte) (rho : valuation) (t : int), ART RT Σ m -> region_ok bsegs rho t RGS m.
Proof.
  intros Σ m rho t HART. unfold region_ok, rbase. rewrite IMGSH_abs, IMGSH_size, IMGSH_al, IMGSH_wr, IMGSH_d.
  change (to_Z 2147459072%uint63) with IMGSH_LO.
  split; [unfold IMGSH_LO; lia|]. split; [unfold IMGSH_LO, two63; lia|]. split; [lia|]. split; [cbn; lia|]. split; [cbn; lia|]. split; [lia|].
  split; [reflexivity|].
  intros i Hi.
  pose proof (af_img_shadow RT AF _ _ HART) as (_ & _ & Hmap). change (shad 65536) with IMGSH_LO in Hmap. change (shad SEGTOP_A) with IMGSH_HI in Hmap.
  destruct (Hmap (IMGSH_LO + i) ltac:(unfold IMGSH_LO, IMGSH_HI; lia)) as [_ [b Hb]].
  exists b. split; [exact Hb|]. split; [|discriminate].
  unfold rg_kb, rd_cell. rewrite IMGSH_d, IMGSH_dflt.
  assert (Ek : to_Z (of_Z (i / 8)) = i / 8) by (apply of_Z_small; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  destruct (iget 18 (rg_cells RGS) (of_Z (i / 8))) as [c|] eqn:Ec; [|cbn [dflt_cell cell_kb]; change (to_Z 0%uint63) with 0; rewrite Z.bits_0; exact I].
  pose proof (cells_check_ok (cell_why_ok CERT) 18 _ RGS_checked (of_Z (i / 8)) c ltac:(rewrite Ek; change (2 ^ Z.of_nat 18) with 262144; apply Z.div_lt_upper_bound; lia) Ec) as Hc.
  rewrite Ek in Hc. destruct c as [w km|]; [|discriminate Hc]. cbn [cell_why_ok] in Hc. cbn [cell_kb].
  destruct (Z.testbit (to_Z km) (i mod 8)) eqn:Ebit; [|exact I]. cbn [kb_ok].
  assert (Hj : In (i mod 8) [0; 1; 2; 3; 4; 5; 6; 7]).
  { pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as Hm. cbn [In]. lia. }
  pose proof (proj1 (forallb_forall _ _) Hc (i mod 8) Hj) as Hcj. cbv beta in Hcj. rewrite Ebit in Hcj. cbn [negb orb] in Hcj.
  apply existsb_exists in Hcj as ([j' w'] & _ & Hjw). cbn [fst snd] in Hjw. apply andb_prop in Hjw as [Ej Hwhy]. apply Z.eqb_eq in Ej. subst j'.
  set (z := byteZ (wZ w) (i mod 8)) in *. pose proof (byteZ_range (wZ w) (i mod 8)) as Hz. fold z in Hz.
  assert (Es : IMGSH_LO + 8 * (i / 8) + i mod 8 = IMGSH_LO + i) by (pose proof (Z.div_mod i 8 ltac:(lia)); lia).
  unfold byte_why_ok in Hwhy. cbv zeta in Hwhy. rewrite Es in Hwhy.
  destruct w' as [|gi].
  - (* [comment removed for export] *)
    apply andb_prop in Hwhy as [Ez Hst]. apply Z.eqb_eq in Ez. rewrite Ez.
    set (a := (IMGSH_LO + i - SHB) * 8) in *.
    assert (Hacc : acc bsegs m a 8).
    { apply (af_acc_static RT AF _ _ a 8 HART); [unfold a, IMGSH_LO, SHB; lia|]. intros i0 Hi0. apply acc_static_b_ok.
      apply (proj1 (forallb_forall _ _) Hst i0). cbn [In]. lia. }
    pose proof (acc_granule_zero m a ltac:(unfold a; apply Z.mod_mul; lia) Hacc) as E0.
    assert (Esh : shad a = IMGSH_LO + i) by (unfold shad, a; rewrite Z.div_mul by lia; lia).
    rewrite Esh, Hb in E0. injection E0 as ->. reflexivity.
  - (* [comment removed for export] *)
    destruct (nth_error GDESC gi) as [g|] eqn:Eg; [|discriminate Hwhy].
    apply andb_prop in Hwhy as [Hwhy H5]. apply andb_prop in Hwhy as [Hwhy H4]. apply andb_prop in Hwhy as [Hwhy H3]. apply andb_prop in Hwhy as [H1 H2].
    apply Z.leb_le in H1, H3, H4, H5. apply Z.eqb_eq in H2.
    pose proof (af_lib_sh RT AF _ _ g HART (nth_error_In _ _ Eg)) as Hsh.
    pose proof (ush_byte_ok (gd_size g) (IMGSH_LO + i - shad (gd_beg g)) z H4 H1 H2 H3) as Hn.
    assert (Hlen : IMGSH_LO + i - shad (gd_beg g) < Z.of_nat (length (ushadow (gd_size g)))).
    { assert (X : nth_error (ushadow (gd_size g)) (Z.to_nat (IMGSH_LO + i - shad (gd_beg g))) <> None) by congruence. apply nth_error_Some in X. lia. }
    pose proof (bytes_at_mrd m (shad (gd_beg g)) _ (IMGSH_LO + i - shad (gd_beg g)) Hsh ltac:(lia)) as E.
    replace (shad (gd_beg g) + (IMGSH_LO + i - shad (gd_beg g))) with (IMGSH_LO + i) in E by lia.
    rewrite Hb, Hn in E. injection E as ->. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
Qed.

End Gen.

Theorem IMGSH_OK : forall (Σ : rts RT) (m : word -> option byte) (rho : valuation) (t : int), ART RT Σ m -> region_ok bsegs rho t RG_IMGSH m.
Proof. exact (imgsh_region_ok RG_IMGSH IMGSH_CERT eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl imgsh_checked). Qed.

End ImgShOk.
