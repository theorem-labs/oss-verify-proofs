(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Mem Cells Step Frame Exec MState.
From OSSVerify.Proofs.openssl.ct.lib.Common Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxQuery.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Forall2_kb_map (rho : valuation) (f : nat -> kb) (bs : list byte) : forall (n s : nat),
  (forall i b, nth_error bs i = Some b -> kb_ok rho (f (s + i)%nat) b) -> length bs = n ->
  Forall2 (kb_ok rho) (map f (seq s n)) bs.
Proof.
  revert bs. induction bs as [|b bs IH]; intros n s H Hl; destruct n as [|n]; try discriminate; cbn [seq map]; constructor.
  - specialize (H 0%nat b eq_refl). rewrite Nat.add_0_r in H. exact H.
  - apply IH; [|cbn in Hl; lia]. intros i b' Hi. replace (S s + i)%nat with (s + S i)%nat by lia. apply H. exact Hi.
Qed.

Lemma kbs_Z_intro (rho : valuation) (n : nat) (z : Z) : 0 <= z -> Forall2 (kb_ok rho) (kbs_Z n z) (Z_to_le_bytes n z).
Proof.
  intros Hz. unfold kbs_Z. apply Forall2_kb_map; [|apply length_Z_to_le_bytes]. intros i b Hi. cbn [Nat.add kb_ok].
  assert (Hlt : (i < n)%nat) by (rewrite <- (length_Z_to_le_bytes n z); apply nth_error_Some; congruence).
  rewrite (nth_Z_to_le_bytes n z i Hz Hlt) in Hi. injection Hi as <-. apply byte_of_unsigned.
Qed.

Lemma kbs_ptr_intro (rho : valuation) (tag : int) (A : Z) : rho tag = A -> 0 <= A < 2 ^ 64 ->
  Forall2 (kb_ok rho) (kbs_ptr tag) (le8 (Z_to_bv 64 A)).
Proof.
  intros Er HA. unfold kbs_ptr. apply Forall2_kb_map; [|apply length_le8]. intros i b Hi. cbn [Nat.add kb_ok].
  assert (Ep : bv_unsigned (pword rho tag w_zero) = A).
  { unfold pword. change (wZ w_zero) with 0. rewrite Z.add_0_r, Er, Z_to_bv_unsigned. apply bv_wrap_small. exact HA. }
  rewrite Ep. unfold le8, word_to_le_bytes in Hi. rewrite Z_to_bv_unsigned, bv_wrap_small in Hi by exact HA.
  assert (Hlt : (i < 8)%nat) by (rewrite <- (length_Z_to_le_bytes 8 A); apply nth_error_Some; congruence).
  rewrite (nth_Z_to_le_bytes 8 A i ltac:(lia) Hlt) in Hi. injection Hi as <-. apply byte_of_unsigned.
Qed.

Lemma kbs_bytes_intro (rho : valuation) : forall zs : list Z, Forall (fun z => 0 <= z < 256) zs ->
  Forall2 (kb_ok rho) (kbs_bytes zs) (map (Z_to_bv 8) zs).
Proof.
  induction 1 as [|z zs Hz _ IH]; cbn [kbs_bytes map]; constructor; [|exact IH].
  cbn [kb_ok]. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hz.
Qed.

Lemma kbs_any_intro (rho : valuation) : forall bs : list byte, Forall2 (kb_ok rho) (kbs_any (length bs)) bs.
Proof. induction bs as [|b bs IH]; cbn [kbs_any repeat length]; constructor; [exact I | exact IH]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Learn.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition fact : Type := (Z * list kb)%type.

Definition fact_holds (rho : valuation) (m : word -> option byte) (B : Z) (f : fact) : Prop :=
  exists bs, Forall2 (kb_ok rho) (snd f) bs /\ bytes_at segs m (B + fst f) bs.

Definition fact_covers (k : kb) (i : Z) (f : fact) : bool :=
  (fst f <=? i) && match nth_error (snd f) (Z.to_nat (i - fst f)) with Some k' => kb_leb k k' | None => false end.

(* [comment removed for export] *)
Definition byte_learnt (rg : region) (fs : list fact) (i : Z) : bool :=
  match rg_kb segs rg i with
  | KU => true
  | k => existsb (fact_covers k i) fs
  end.

Fixpoint learn_check (rg : region) (fs : list fact) (off : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => byte_learnt rg fs off && learn_check rg fs (off + 1) n'
  end.

Lemma learn_check_at (rg : region) (fs : list fact) : forall (n : nat) (off i : Z),
  learn_check rg fs off n = true -> off <= i < off + Z.of_nat n -> byte_learnt rg fs i = true.
Proof.
  induction n as [|n IH]; intros off i H Hi; [lia|]. cbn [learn_check] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec i off) as [->|Hne]; [exact H1|]. apply (IH (off + 1) i H2). lia.
Qed.

Lemma Forall2_nth_l {A B : Type} (P : A -> B -> Prop) : forall (l : list A) (l' : list B) (i : nat) (a : A),
  Forall2 P l l' -> nth_error l i = Some a -> exists b, nth_error l' i = Some b /\ P a b.
Proof.
  induction l as [|x l IH]; intros l' i a H Hi; [destruct i; discriminate|]. inversion H as [|? y ? l2 Hxy Hr]; subst.
  destruct i as [|i]; cbn in Hi |- *; [injection Hi as <-; exists y; auto | exact (IH l2 i a Hr Hi)].
Qed.

Theorem region_ok_learn_gen (rho : valuation) (t : int) (rg : region) (m : word -> option byte) (fs : list fact) :
  (0 <= rbase rho t rg /\ (0 < rbase rho t rg \/ to_Z (rg_al rg) = 0)) -> rbase rho t rg + to_Z (rg_size rg) < two63 -> to_Z (rg_size rg) < 2 ^ 62 ->
  to_Z (rg_size rg) <= 8 * 2 ^ Z.of_nat (rg_d rg) -> Z.of_nat (rg_d rg) <= 59 -> to_Z (rg_al rg) < 63 -> rbase rho t rg mod 2 ^ to_Z (rg_al rg) = 0 ->
  (forall i, 0 <= i < to_Z (rg_size rg) -> exists b, mrd segs m (wa (rbase rho t rg + i)) = Some b) ->
  (rg_wr rg = true -> forall i, 0 <= i < to_Z (rg_size rg) -> wview segs m (wa (rbase rho t rg + i)) <> None) ->
  Forall (fact_holds rho m (rbase rho t rg)) fs ->
  learn_check rg fs 0 (Z.to_nat (to_Z (rg_size rg))) = true ->
  region_ok segs rho t rg m.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 Hmap Hwr Hfs Hck. unfold region_ok. repeat (split; [assumption|]).
  intros i Hi. destruct (Hmap i Hi) as [b Eb]. exists b. split; [exact Eb|]. split; [|intros Hw; exact (Hwr Hw i Hi)].
  pose proof (learn_check_at rg fs _ 0 i Hck ltac:(lia)) as Hl. unfold byte_learnt in Hl.
  assert (Hk : rg_kb segs rg i = KU \/ existsb (fact_covers (rg_kb segs rg i) i) fs = true) by (destruct (rg_kb segs rg i); auto).
  destruct Hk as [->|Hk]; [exact I|]. apply existsb_exists in Hk as (f & Hf & Hc). unfold fact_covers in Hc.
  apply andb_prop in Hc as [Hlo Hc]. apply Z.leb_le in Hlo.
  destruct (nth_error (snd f) (Z.to_nat (i - fst f))) as [k'|] eqn:Ek; [|discriminate].
  pose proof (proj1 (Forall_forall _ _) Hfs f Hf) as (bs & HF & (_ & _ & Hb)).
  destruct (Forall2_nth_l _ _ _ _ _ HF Ek) as (b' & Eb' & Kb').
  assert (Hlt : (Z.to_nat (i - fst f) < length bs)%nat) by (apply nth_error_Some; congruence).
  specialize (Hb _ Hlt). rewrite Z2Nat.id in Hb by lia. replace (rbase rho t rg + fst f + (i - fst f)) with (rbase rho t rg + i) in Hb by lia.
  rewrite Eb, Eb' in Hb. injection Hb as ->. exact (kb_leb_ok rho _ _ b' Hc Kb').
Qed.

Theorem region_ok_learn (rho : valuation) (t : int) (rg : region) (m : word -> option byte) (fs : list fact) :
  0 < rbase rho t rg -> rbase rho t rg + to_Z (rg_size rg) < two63 -> to_Z (rg_size rg) < 2 ^ 62 ->
  to_Z (rg_size rg) <= 8 * 2 ^ Z.of_nat (rg_d rg) -> Z.of_nat (rg_d rg) <= 59 -> to_Z (rg_al rg) < 63 -> rbase rho t rg mod 2 ^ to_Z (rg_al rg) = 0 ->
  (forall i, 0 <= i < to_Z (rg_size rg) -> exists b, mrd segs m (wa (rbase rho t rg + i)) = Some b) ->
  (rg_wr rg = true -> forall i, 0 <= i < to_Z (rg_size rg) -> wview segs m (wa (rbase rho t rg + i)) <> None) ->
  Forall (fact_holds rho m (rbase rho t rg)) fs ->
  learn_check rg fs 0 (Z.to_nat (to_Z (rg_size rg))) = true ->
  region_ok segs rho t rg m.
Proof. intros H0. apply region_ok_learn_gen. split; [lia | left; exact H0]. Qed.

(* [comment removed for export] *)
Lemma find_segment_In : forall (sgs : list Segment) (a n : Z) (sg : Segment), find_segment sgs a n = Some sg -> In sg sgs.
Proof.
  induction sgs as [|s0 sgs IH]; intros a n sg H; cbn [find_segment] in H; [discriminate|].
  destruct (_ && _); [injection H as <-; left; reflexivity | right; exact (IH a n sg H)].
Qed.

Lemma wview_mrd (m : word -> option byte) (a : word) :
  (forall sg, In sg segs -> seg_writable sg = true -> seg_readable sg = true) ->
  wview segs m a <> None -> exists b, mrd segs m a = Some b.
Proof.
  intros Hrd Hw. unfold mrd. unfold wview in Hw. destruct (m a) as [b|]; [exists b; reflexivity|].
  unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
  destruct (find_segment segs (bv_unsigned a) 1) as [sg|] eqn:E; [|exfalso; apply Hw; reflexivity].
  destruct (seg_writable sg) eqn:W; [|exfalso; apply Hw; reflexivity].
  rewrite (Hrd sg (find_segment_In segs _ _ sg E) W). change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base sg)))) as [b|]; [exists b; reflexivity | exfalso; apply Hw; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma bytes_at_mapped (m : word -> option byte) (A : Z) (bs : list byte) :
  bytes_at segs m A bs -> forall i, 0 <= i < Z.of_nat (length bs) -> exists b, mrd segs m (wa (A + i)) = Some b.
Proof.
  intros (_ & _ & Hb) i Hi. specialize (Hb (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in Hb by lia.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [exists b; exact Hb|]. apply nth_error_None in E. lia.
Qed.

(* [comment removed for export] *)
Definition num_ok (B : Z) (rg : region) : bool :=
  (0 <? B) && (B + to_Z (rg_size rg) <? two63) && (to_Z (rg_size rg) <? 2 ^ 62) && (to_Z (rg_size rg) <=? 8 * 2 ^ Z.of_nat (rg_d rg))
  && (Z.of_nat (rg_d rg) <=? 59) && (to_Z (rg_al rg) <? 63) && (B mod 2 ^ to_Z (rg_al rg) =? 0).

(* [comment removed for export] *)
Lemma static_region_ok (rho : valuation) (t : int) (rg : region) (m : word -> option byte) (lo : int) (ks : list kb) (bs : list byte) :
  rg_abs rg = Some lo -> rg_wr rg = false -> num_ok (to_Z lo) rg = true ->
  Forall2 (kb_ok rho) ks bs -> bytes_at segs m (to_Z lo) bs -> Z.of_nat (length bs) = to_Z (rg_size rg) ->
  learn_check rg [(0, ks)] 0 (Z.to_nat (to_Z (rg_size rg))) = true ->
  region_ok segs rho t rg m.
Proof.
  intros Ea Ew Hn HF Hb Hl Hck. unfold num_ok in Hn.
  apply andb_prop in Hn as [Hn N7]. apply andb_prop in Hn as [Hn N6]. apply andb_prop in Hn as [Hn N5]. apply andb_prop in Hn as [Hn N4].
  apply andb_prop in Hn as [Hn N3]. apply andb_prop in Hn as [N1 N2].
  apply Z.ltb_lt in N1, N2, N3, N6. apply Z.leb_le in N4, N5. apply Z.eqb_eq in N7.
  assert (Eb : rbase rho t rg = to_Z lo) by (unfold rbase; rewrite Ea; reflexivity).
  apply (region_ok_learn rho t rg m [(0, ks)]); rewrite ?Eb; try assumption.
  - intros i Hi. apply (bytes_at_mapped m (to_Z lo) bs Hb). lia.
  - intros X. rewrite Ew in X. discriminate.
  - constructor; [|constructor]. exists bs. cbn [fst snd]. rewrite Z.add_0_r. split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition dir_in (rho : valuation) (M : mem) (L : list (Z * Z)) : Prop :=
  forall t rg, mget M t = Some rg -> In (rbase rho t rg, rbase rho t rg + to_Z (rg_size rg)) L.

Lemma dir_in_empty (rho : valuation) : dir_in rho IEmpty [].
Proof. intros t rg G. unfold mget in G. destruct (_ <? _)%uint63; [rewrite iget_empty in G|]; discriminate. Qed.

Lemma Rmem_add_sep (rho : valuation) (M : mem) (t : int) (rg : region) (m : word -> option byte) (L : list (Z * Z)) :
  Rmem segs rho M m -> dir_in rho M L -> mget M t = None -> to_Z t < to_Z TAGLIM -> region_ok segs rho t rg m ->
  Forall (fun iv => rbase rho t rg + to_Z (rg_size rg) <= fst iv \/ snd iv <= rbase rho t rg) L ->
  Rmem segs rho (mset M t rg) m /\ dir_in rho (mset M t rg) ((rbase rho t rg, rbase rho t rg + to_Z (rg_size rg)) :: L).
Proof.
  intros [HR Hsep] Hd Hfresh Ht Hok HL. split; [split|].
  - intros t2 rg2 G. destruct (mget_mset_cases M t t2 rg rg2 Ht G) as [[-> ->]|[_ G2]]; [exact Hok | exact (HR t2 rg2 G2)].
  - apply (regions_sep_new rho M t rg Hsep Hfresh Ht). intros t2 rg2 G2.
    exact (proj1 (Forall_forall _ _) HL _ (Hd t2 rg2 G2)).
  - intros t2 rg2 G. destruct (mget_mset_cases M t t2 rg rg2 Ht G) as [[-> ->]|[_ G2]]; [left; reflexivity | right; exact (Hd t2 rg2 G2)].
Qed.

(* [comment removed for export] *)
Definition dir_inw (rho : valuation) (M : mem) (L : list (Z * Z * bool)) : Prop :=
  forall t rg, mget M t = Some rg -> In (rbase rho t rg, rbase rho t rg + to_Z (rg_size rg), rg_wr rg) L.

Lemma dir_inw_empty (rho : valuation) : dir_inw rho IEmpty [].
Proof. intros t rg G. unfold mget in G. destruct (_ <? _)%uint63; [rewrite iget_empty in G|]; discriminate. Qed.

Lemma Rmem_add_sepw (rho : valuation) (M : mem) (t : int) (rg : region) (m : word -> option byte) (L : list (Z * Z * bool)) :
  Rmem segs rho M m -> dir_inw rho M L -> mget M t = None -> to_Z t < to_Z TAGLIM -> region_ok segs rho t rg m ->
  Forall (fun e => rg_wr rg = true \/ snd e = true ->
                   rbase rho t rg + to_Z (rg_size rg) <= fst (fst e) \/ snd (fst e) <= rbase rho t rg) L ->
  Rmem segs rho (mset M t rg) m /\ dir_inw rho (mset M t rg) ((rbase rho t rg, rbase rho t rg + to_Z (rg_size rg), rg_wr rg) :: L).
Proof.
  intros [HR Hsep] Hd Hfresh Ht Hok HL. split; [split|].
  - intros t2 rg2 G. destruct (mget_mset_cases M t t2 rg rg2 Ht G) as [[-> ->]|[_ G2]]; [exact Hok | exact (HR t2 rg2 G2)].
  - apply (regions_sep_new_wr rho M t rg Hsep Hfresh Ht). intros t2 rg2 G2 Hw.
    exact (proj1 (Forall_forall _ _) HL _ (Hd t2 rg2 G2) Hw).
  - intros t2 rg2 G. destruct (mget_mset_cases M t t2 rg rg2 Ht G) as [[-> ->]|[_ G2]]; [left; reflexivity | right; exact (Hd t2 rg2 G2)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Silent.
Variable rho : valuation.
Variable M0 : mem.                       (* [comment removed for export] *)
Variable W : list ivl.                   (* [comment removed for export] *)
Variable m0 : word -> option byte.       (* [comment removed for export] *)
Variable F0 : bvmap 5 word.
Variable fc0 : bv 32.

Definition CInv (S : sstate) (ms : machine_state) : Prop :=
  same_dirs M0 (s_mem S) /\ munch W m0 (ms_mem ms) /\ wmono segs m0 (ms_mem ms) /\ mem_inv segs (ms_mem ms)
  /\ ms_fregs ms = F0 /\ ms_fcsr ms = fc0 /\ ms_rom ms = seg_rom segs /\ regs_nf (ms_regs ms).

(* [comment removed for export] *)
Hypothesis W_ok : forall t rg, mget M0 t = Some rg -> rg_wr rg = true ->
  inside W (rbase rho t rg) (to_Z (rg_size rg)).

Lemma inside_sub : forall (W' : list ivl) (a n a' n' : Z), inside W' a n -> a <= a' -> a' + n' <= a + n -> inside W' a' n'.
Proof.
  induction W' as [|[lo hi] W' IH]; cbn [inside]; intros a n a' n' H Ha Hn; [exact H|].
  destruct H as [H|H]; [left; lia | right; exact (IH a n a' n' H Ha Hn)].
Qed.

(* [comment removed for export] *)
Lemma CInv_pres (S S' : sstate) (ms ms' : machine_state) :
  CInv S ms -> R segs rho S ms ->
  ms_fregs ms' = ms_fregs ms -> ms_fcsr ms' = ms_fcsr ms -> ms_rom ms' = ms_rom ms ->
  same_dirs (s_mem S) (s_mem S') -> mem_step rho (s_mem S) (ms_mem ms) (ms_mem ms') -> regs_step (ms_regs ms) (ms_regs ms') ->
  CInv S' ms'.
Proof.
  intros (Hd & MU & WM & MI & Hfr & Hfc & Hro & Hnf) HR Ef Ec Eo Hd' Hm Hrs.
  unfold CInv. rewrite Ef, Ec, Eo. split; [exact (same_dirs_trans _ _ _ Hd Hd')|].
  assert (Hregs : regs_nf (ms_regs ms')) by exact (regs_nf_step _ _ Hnf Hrs).
  destruct Hm as [->|(t & rg & off & bs & Eg & Hw & Em & Hoff)]; [auto 10|]. rewrite Em.
  pose proof HR as (_ & _ & _ & _ & [HRg _]).
  destruct (HRg t rg Eg) as (B0 & B1 & B2 & _ & _ & _ & _ & Hby).
  pose proof (to_Z_bounded off) as Bo. pose proof (to_Z_bounded (rg_size rg)) as Bs. unfold two63 in B1.
  assert (WR : wr_at segs (ms_mem ms) (rbase rho t rg) (to_Z (rg_size rg))).
  { split; [lia|]. split; [lia|]. intros i Hi. destruct (Hby i Hi) as (b & _ & _ & Hwv). exact (Hwv Hw). }
  (* [comment removed for export] *)
  specialize (Hd t). rewrite Eg in Hd. destruct (mget M0 t) as [rg0|] eqn:Eg0; [|contradiction].
  pose proof (rbase_same_dir rho t rg0 rg Hd) as Eb. destruct Hd as (_ & Es & _ & Ewr & _).
  pose proof (W_ok t rg0 Eg0 ltac:(congruence)) as Hin. rewrite <- Eb, <- Es in Hin.
  split; [|split; [|split; [|auto]]].
  - apply munch_write; [exact MU | lia | lia |]. eapply inside_sub; [exact Hin | lia | lia].
  - apply wmono_write. exact WM.
  - apply mem_inv_store; [exact MI|]. apply (wr_at_store_ok segs (ms_mem ms) (rbase rho t rg) (to_Z (rg_size rg)) (to_Z off) (length bs) WR); lia.
Qed.

Theorem CInv_step : step_pres segs rho CInv.
Proof.
  intros S S' ms ms' HC HRn HRn' Hst Ef Ec Eo Hd' Hm Hrs Enx Eabs.
  exact (CInv_pres S S' ms ms' HC (Rn_R segs rho S ms HRn) Ef Ec Eo Hd' Hm Hrs).
Qed.

End Silent.

End Learn.
