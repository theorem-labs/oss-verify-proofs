(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec ITree Nodes PlacementSearch.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AcctCore ExecF ModelX MmXfer.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ITreeA NodesA NodesSil.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude Dispatch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Lemma iv_overlap_sym : forall a1 n1 a2 n2, iv_overlap a1 n1 a2 n2 = iv_overlap a2 n2 a1 n1.
Proof. intros. unfold iv_overlap. apply andb_comm. Qed.

Lemma iv_overlap_apart : forall a1 n1 a2 n2 : word,
  bv_unsigned a1 + bv_unsigned n1 <= bv_unsigned a2 \/ bv_unsigned a2 + bv_unsigned n2 <= bv_unsigned a1 ->
  iv_overlap a1 n1 a2 n2 = false.
Proof. intros a1 n1 a2 n2 H. unfold iv_overlap. apply andb_false_iff. destruct H; [right|left]; apply Z.ltb_ge; lia. Qed.

(* [comment removed for export] *)
Lemma In_maps_subtract : forall maps (b s : word) lo hi,
  In (b, s) maps -> 0 < bv_unsigned s -> lo <= hi ->
  bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b ->
  In (b, s) (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] r IH]; intros b s lo hi Hin S0 LH AP; [contradiction|].
  cbn [maps_subtract]. apply in_or_app. destruct Hin as [E|Hin]; [left| right; apply IH; assumption].
  injection E as -> ->. unfold iv_subtract. cbv zeta.
  pose proof (bv_unsigned_in_range 64 b) as Rb. pose proof (bv_unsigned_in_range 64 s) as Rs.
  destruct AP as [AP|AP].
  - rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite app_nil_r. left.
    rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [app]. left.
    rewrite Z.max_l by lia. replace (bv_unsigned b + bv_unsigned s - bv_unsigned b) with (bv_unsigned s) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma region_free_maps_subtract : forall l (b s : word) lo hi,
  0 <= lo -> hi < 2^64 ->
  region_free l b s = true -> region_free (maps_subtract l lo hi) b s = true.
Proof.
  induction l as [|[a sz] r IH]; intros b s lo hi L0 H64 RF; [reflexivity|].
  cbn [region_free] in RF. apply andb_prop in RF as [O RF]. apply negb_true_iff in O.
  cbn [maps_subtract]. apply region_free_intro. intros x y Hin. apply in_app_or in Hin as [Hin|Hin].
  - unfold iv_subtract in Hin. cbv zeta in Hin.
    pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 sz) as Rz.
    change (bv_modulus 64) with (2^64) in Ra, Rz.
    unfold iv_overlap in O |- *. apply andb_false_iff in O.
    apply in_app_or in Hin as [Hin|Hin].
    + destruct (Z.ltb_spec (bv_unsigned a) lo); [|contradiction]. destruct Hin as [E|[]]. injection E as <- <-.
      rewrite unsigned_lit by lia. apply andb_false_iff. destruct O as [O|O]; apply Z.ltb_ge in O; [left|right]; apply Z.ltb_ge; lia.
    + destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [|contradiction]. destruct Hin as [E|[]]. injection E as <- <-.
      rewrite !unsigned_lit by lia. apply andb_false_iff. destruct O as [O|O]; apply Z.ltb_ge in O; [left|right]; apply Z.ltb_ge; lia.
  - exact (region_free_In _ _ _ _ _ (IH b s lo hi L0 H64 RF) Hin).
Qed.

Lemma In_map_remove : forall maps (b s a : word), In (b, s) maps -> b <> a -> In (b, s) (map_remove maps a).
Proof.
  intros maps b s a Hin NE. unfold map_remove. apply filter_In. split; [exact Hin|]. cbn [fst].
  apply negb_true_iff. destruct (bv_eqb b a) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. contradiction.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition shE (h : VmMaps) (b s : word) : Prop :=
  In (b, s) (vm_maps h) /\ region_free (vm_noaccess h) b s = true /\ region_free (vm_reserved h) b s = true.

Lemma m_vmmaps_destroyed : forall a n h m, m_vmmaps (with_mmap_destroyed a n h m) = h.
Proof. reflexivity. Qed.

Lemma check_munmap_shE : forall a l eff m m' evs (b s : word),
  Mmap.check_munmap a l eff m = CheckOk m' evs ->
  shE (m_vmmaps m) b s -> 0 < bv_unsigned s ->
  (bv_unsigned a + page_round_up_Z (bv_unsigned l) <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned a) ->
  shE (m_vmmaps m') b s.
Proof.
  intros a l eff m m' evs b s H (HI & HN & HR) S0 AP. unfold Mmap.check_munmap in H.
  destruct (negb (bv_unsigned a mod page_size =? 0) || w_is0 l) eqn:G1.
  { apply check_ret_only_ok_iff in H as (_ & <- & _). repeat split; assumption. }
  cbv zeta in H. destruct (TASK_SIZE <? bv_unsigned a + page_round_up_Z (bv_unsigned l)) eqn:G2.
  { apply check_ret_only_ok_iff in H as (_ & <- & _). repeat split; assumption. }
  apply Z.ltb_ge in G2. unfold TASK_SIZE in G2.
  apply orb_false_iff in G1 as [_ W0]. unfold w_is0 in W0.
  assert (L0 : 0 < bv_unsigned l).
  { pose proof (bv_unsigned_in_range 64 l) as R. destruct (Z.eq_dec (bv_unsigned l) 0) as [E|E]; [|lia].
    exfalso. assert (l = Z_to_bv 64 0) as -> by (apply bv_eq; rewrite E; reflexivity).
    rewrite (proj2 (bv_eqb_eq _ _) eq_refl) in W0. discriminate. }
  pose proof (page_round_up_Z_ge (bv_unsigned l)) as RU.
  pose proof (bv_unsigned_in_range 64 a) as Ra. change (bv_modulus 64) with (2^64) in Ra.
  assert (UN : bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned l))) = page_round_up_Z (bv_unsigned l))
    by (apply unsigned_lit; lia).
  destruct (map_has (vm_maps (m_vmmaps m)) a (Z_to_bv 64 (page_round_up_Z (bv_unsigned l)))) eqn:G3.
  - destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (w_is0 r && listNN_eqb us [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned l)))]); [|discriminate].
    injection H as <- _. rewrite m_vmmaps_destroyed. cbn [vm_maps vm_noaccess vm_reserved]. split; [|split].
    + apply In_map_remove; [exact HI|]. intros ->. lia.
    + apply region_free_maps_subtract; [lia| rewrite UN; lia| exact HN].
    + exact HR.
  - destruct (munmap_free_ok (m_vmmaps m) a (page_round_up_Z (bv_unsigned l))); [|discriminate].
    apply check_ret_only_ok_iff in H as (_ & <- & _). repeat split; assumption.
Qed.

Lemma m_vmmaps_with_vmmaps : forall h m, m_vmmaps (with_vmmaps h m) = h.
Proof. reflexivity. Qed.

Ltac crush_eq H :=
  repeat (cbv zeta beta iota in H;
          lazymatch type of H with
          | CheckReject = CheckOk _ _ => discriminate H
          | CheckUnmodeled = CheckOk _ _ => discriminate H
          | check_ret_only _ _ _ _ = CheckOk _ _ => apply check_ret_only_ok_iff in H as (_ & <- & _)
          | (if ?x then _ else _) = _ => destruct x eqn:?
          | (match ?x with _ => _ end) = _ => destruct x eqn:?
          end).

Ltac split_andb :=
  repeat match goal with
  | H : _ && _ = true |- _ => apply andb_prop in H; destruct H
  end.

Ltac prep_arith :=
  repeat match goal with
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : negb _ = false |- _ => apply negb_false_iff in H
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  end; unfold two_pow_64 in *.

(* [comment removed for export] *)
Ltac ov_false HI :=
  first [ (* [comment removed for export] *)
          match goal with
          | RF : region_free (_ ++ _) ?X ?N = true |- iv_overlap ?b ?s ?X ?N = false =>
              rewrite iv_overlap_sym; apply (region_free_In _ _ _ _ _ RF); apply in_or_app; right; exact HI
          end
        | apply iv_overlap_apart; lia ].

Lemma check_mmap_shE : forall a l p f d off eff m m' evs (b s : word),
  Mmap.check_mmap a l p f d off eff m = CheckOk m' evs ->
  shE (m_vmmaps m) b s -> 0 < bv_unsigned s ->
  (bv_unsigned a = 0 \/ bv_unsigned a + page_round_up_Z (bv_unsigned l) <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned a) ->
  shE (m_vmmaps m') b s.
Proof.
  intros a l p f d off eff m m' evs b s H (HI & HN & HR) S0 AP. unfold Mmap.check_mmap in H.
  pose proof (bv_unsigned_in_range 64 a) as Ra. change (bv_modulus 64) with (2^64) in Ra.
  pose proof (bv_unsigned_in_range 64 l) as Rl. change (bv_modulus 64) with (2^64) in Rl.
  pose proof (page_round_up_Z_ge (bv_unsigned l)) as RU.
  crush_eq H.
  all: try solve [repeat split; assumption].
  all: injection H as <- _.
  all: rewrite ?vmmaps_with_mmap_replacement, ?vmmaps_with_mmap_backing, ?m_vmmaps_destroyed, ?m_vmmaps_with_vmmaps.
  all: unfold mmap_fixed_rw_next, mmap_fixed_destroyed_next, mmap_fixed_rw_span_next, mmap_fixed_noaccess_span_next.
  all: split_andb; prep_arith.
  all: try (assert (UN : bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned l))) = page_round_up_Z (bv_unsigned l))
              by (apply unsigned_lit; lia)).
  all: split; [| split; [| exact HR]]; cbn [vm_maps vm_noaccess].
  all: try solve [ exact HI | right; exact HI
                 | apply In_maps_subtract; [exact HI| lia| rewrite ?UN; lia| rewrite ?UN; lia]
                 | right; apply In_maps_subtract; [exact HI| lia| rewrite ?UN; lia| rewrite ?UN; lia] ].
  all: try solve [ exact HN
                 | apply region_free_maps_subtract; [lia| rewrite ?UN; lia| exact HN]
                 | cbn [region_free]; apply andb_true_intro; split;
                   [ apply negb_true_iff; rewrite ?UN; ov_false HI
                   | first [ exact HN | apply region_free_maps_subtract; [lia| rewrite ?UN; lia| exact HN] ] ] ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ShInv.
Variable SHM : list (Z * Z).

#[using="Type"] Lemma sh_entry_shE : forall h e, sh_entry_ok h e <->
  (0 <= fst e /\ 0 < snd e /\ fst e + snd e < 2^64 /\ shE h (Z_to_bv 64 (fst e)) (Z_to_bv 64 (snd e))).
Proof. intros h e. unfold sh_entry_ok, shE. tauto. Qed.

#[using="Type"] Lemma check_mmap_shinv : forall a l p f d off eff m m' evs,
  Mmap.check_mmap a l p f d off eff m = CheckOk m' evs -> shinv SHM m ->
  (bv_unsigned a = 0 \/ apart_sh SHM (bv_unsigned a) (page_round_up_Z (bv_unsigned l))) ->
  shinv SHM m'.
Proof.
  intros a l p f d off eff m m' evs H SH AP. unfold shinv in *. apply Forall_forall. intros e He.
  pose proof (proj1 (Forall_forall _ _) SH e He) as OK. apply sh_entry_shE in OK as (B0 & S0 & BS & E).
  apply sh_entry_shE. split; [exact B0|]. split; [exact S0|]. split; [exact BS|].
  eapply check_mmap_shE; [exact H| exact E| rewrite unsigned_lit by lia; lia|].
  destruct AP as [AP|AP]; [left; exact AP| right].
  pose proof (proj1 (Forall_forall _ _) AP e He) as X. cbv beta in X. rewrite !unsigned_lit by lia. lia.
Qed.

#[using="Type"] Lemma check_munmap_shinv : forall a l eff m m' evs,
  Mmap.check_munmap a l eff m = CheckOk m' evs -> shinv SHM m ->
  apart_sh SHM (bv_unsigned a) (page_round_up_Z (bv_unsigned l)) ->
  shinv SHM m'.
Proof.
  intros a l eff m m' evs H SH AP. unfold shinv in *. apply Forall_forall. intros e He.
  pose proof (proj1 (Forall_forall _ _) SH e He) as OK. apply sh_entry_shE in OK as (B0 & S0 & BS & E).
  apply sh_entry_shE. split; [exact B0|]. split; [exact S0|]. split; [exact BS|].
  eapply check_munmap_shE; [exact H| exact E| rewrite unsigned_lit by lia; lia|].
  pose proof (proj1 (Forall_forall _ _) AP e He) as X. cbv beta in X. rewrite !unsigned_lit by lia. lia.
Qed.

End ShInv.
