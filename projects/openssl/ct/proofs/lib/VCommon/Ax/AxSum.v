(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxWordsInt AxAcct.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec FastWord FastWordSem StoreOk.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLazy AxLin AxRel AxVal AxBytes AxMem AxMemC AxZZ AxBg AxState AxFetchFast AsanWLazy AsanWBase AsanSBase.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require AxScan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma word_lit_w (w : word) (z : Z) : bv_unsigned w = z -> w = Z_to_bv 64 z.
Proof. intros <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma ri_zero (r : reg) : (ri r =? 0)%uint63 = (bv_unsigned r =? 0).
Proof.
  destruct (eqbP (ri r) 0%uint63) as [E|E]; rewrite phi_ri in E; change (to_Z 0%uint63) with 0 in E.
  - symmetry. apply Z.eqb_eq. exact E.
  - symmetry. apply Z.eqb_neq. exact E.
Qed.

Lemma aget_zero (m m' : aregs) (r : reg) : bv_unsigned r = 0 -> aget m (ri r) = aget m' (ri r).
Proof. intros H. unfold aget. rewrite ri_zero, (proj2 (Z.eqb_eq _ _) H). reflexivity. Qed.

Lemma aget_aset_same (m : aregs) (r : reg) (v : xv) : bv_unsigned r <> 0 -> aget (aset m (ri r) v) (ri r) = v.
Proof. intros H. rewrite aget_aset, (proj2 (Z.eqb_neq _ _) H), Z.eqb_refl. reflexivity. Qed.

Lemma aget_aset_other (m : aregs) (rd r : reg) (v : xv) : bv_unsigned rd <> bv_unsigned r -> aget (aset m (ri rd) v) (ri r) = aget m (ri r).
Proof.
  intros H. rewrite aget_aset, (proj2 (Z.eqb_neq _ _) H).
  destruct (bv_unsigned r =? 0) eqn:E; [unfold aget; rewrite ri_zero, E; reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Definition clob (CL : list reg) (regs : aregs) : aregs := fold_right (fun r m => aset m (ri r) XT) regs CL.

Lemma clob_out (CL : list reg) (regs : aregs) (r : reg) : ~ In r CL -> bv_unsigned r <> 0 -> aget (clob CL regs) (ri r) = aget regs (ri r).
Proof.
  intros Hn H0. induction CL as [|c CL IH]; [reflexivity|]. cbn [clob fold_right]. fold (clob CL regs).
  rewrite aget_aset, (proj2 (Z.eqb_neq _ _) H0).
  destruct (Z.eqb_spec (bv_unsigned c) (bv_unsigned r)) as [E|E]; [exfalso; apply Hn; left; apply bv_eq; exact E|].
  apply IH. intros X. apply Hn. right. exact X.
Qed.

Lemma clob_in' (CL : list reg) (regs : aregs) (r : reg) : In r CL -> bv_unsigned r <> 0 -> aget (clob CL regs) (ri r) = XT.
Proof.
  intros Hin H0. induction CL as [|c CL IH]; [destruct Hin|]. cbn [clob fold_right]. fold (clob CL regs).
  rewrite aget_aset, (proj2 (Z.eqb_neq _ _) H0).
  destruct (Z.eqb_spec (bv_unsigned c) (bv_unsigned r)) as [E|E]; [reflexivity|].
  apply IH. destruct Hin as [X|X]; [exfalso; apply E; rewrite X; reflexivity | exact X].
Qed.

Lemma In_reg_dec (r : reg) (CL : list reg) : {In r CL} + {~ In r CL}.
Proof. apply in_dec. intros x y. destruct (decide (x = y)) as [E|E]; [left | right]; exact E. Qed.

Section Regs.
Variable ρ : valuation.

(* [comment removed for export] *)
Lemma RRegs_frame (regs regs' : aregs) (ms ms' : machine_state) (CL : list reg) :
  RRegs ρ regs ms -> (forall r, ~ In r CL -> rg ms' r = rg ms r) ->
  (forall r, ~ In r CL -> aget regs' (ri r) = aget regs (ri r)) ->
  (forall r, In r CL -> xv_val ρ (aget regs' (ri r)) (rg ms' r)) ->
  RRegs ρ regs' ms'.
Proof.
  intros HR Hk Ha Hc r. destruct (In_reg_dec r CL) as [Hin|Hn]; [exact (Hc r Hin)|].
  rewrite (Ha r Hn), (Hk r Hn). exact (HR r).
Qed.

Lemma RRegs_clob (regs : aregs) (ms ms' : machine_state) (CL : list reg) :
  RRegs ρ regs ms -> (forall r, ~ In r CL -> rg ms' r = rg ms r) -> (forall r, In r CL -> bv_unsigned r <> 0) ->
  RRegs ρ (clob CL regs) ms'.
Proof.
  intros HR Hk H0. apply (RRegs_frame regs (clob CL regs) ms ms' CL HR Hk).
  - intros r Hn. destruct (Z.eq_dec (bv_unsigned r) 0) as [E|E]; [apply aget_zero; exact E | apply clob_out; assumption].
  - intros r Hin. rewrite (clob_in' CL regs r Hin (H0 r Hin)). exact I.
Qed.

End Regs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Mem.
Variable segs : list Segment.

Lemma RMem_pw (ρ : valuation) (A : list region) (m m' : word -> option byte) :
  (forall x, m' x = m x) -> RMem segs ρ A m -> RMem segs ρ A m'.
Proof.
  intros Hpw [Hok HR]. split; [exact Hok|]. rewrite Forall_forall in *. intros R HIn.
  apply (RRegion_mframe segs ρ m m' R (regions_ok_in ρ A R Hok HIn)); [intros z _; apply Hpw | exact (HR R HIn)].
Qed.

(* [comment removed for export] *)
Lemma hs_ok_out' (ρ : valuation) (A A' : list region) (m m' : word -> option byte) :
  Forall2 same_fields A A' -> (hs_old ρ A m -> forall z, in_ss z -> m' (wz z) = m (wz z)) -> hs_ok ρ A m -> hs_ok ρ A' m'.
Proof.
  intros HF Hss0 Hhs. apply (hs_ok_geom ρ A A' m' HF). destruct Hhs as [Hpl|Hold]; [left; exact Hpl | right].
  pose proof (Hss0 Hold) as Hss. destruct Hold as (P1 & P2 & P3 & P4).
  split; [exact P1|]. split; [intros z Hz Hm; rewrite (Hss z Hz); exact (P2 z Hz Hm)|].
  split.
  - destruct P3 as [P3|P3]; [left | right]; intros z Hz; rewrite (Hss z (or_introl Hz)); exact (P3 z Hz).
  - destruct P4 as [P4|P4]; [left | right]; intros z Hz; rewrite (Hss z (or_intror Hz)); exact (P4 z Hz).
Qed.

Lemma hs_ok_out (ρ : valuation) (A A' : list region) (m m' : word -> option byte) :
  Forall2 same_fields A A' -> (forall z, in_ss z -> m' (wz z) = m (wz z)) -> hs_ok ρ A m -> hs_ok ρ A' m'.
Proof. intros HF Hss. exact (hs_ok_out' ρ A A' m m' HF (fun _ => Hss)). Qed.

Lemma hs_ok_pw (ρ : valuation) (A : list region) (m m' : word -> option byte) :
  (forall x, m' x = m x) -> hs_ok ρ A m -> hs_ok ρ A m'.
Proof.
  intros Hpw. apply hs_ok_out; [|intros z _; apply Hpw].
  clear. induction A as [|R A IH]; constructor; [repeat split | exact IH].
Qed.

Lemma mem_cov_pw (model : Model) (m m' : word -> option byte) : (forall x, m' x = m x) -> mem_cov segs model m -> mem_cov segs model m'.
Proof. intros Hpw H x Hx. rewrite Hpw in Hx. exact (H x Hx). Qed.

Lemma na_ok_pw (ρ : valuation) (A : list region) (model : Model) (m m' : word -> option byte) :
  (forall x, m' x = m x) -> na_ok segs ρ A model m -> na_ok segs ρ A model m'.
Proof. intros Hpw (N1 & N2 & N3). split; [intros x Hx; rewrite Hpw in Hx; exact (N1 x Hx) | split; assumption]. Qed.

(* [comment removed for export] *)
Lemma a_store_BT_havoc (ρ : valuation) (A A' : list region) (m m' : word -> option byte) (v : xv) (a : bv 64) (n : nat) :
  RMem segs ρ A m -> xv_val ρ v a -> (1 <= n)%nat -> Z.of_nat n < 2 ^ 40 -> a_store segs A v (repeat BT n) = Some A' ->
  (forall x : word, ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n) -> m' x = m x) ->
  mem_grows m m' -> RMem segs ρ A' m'.
Proof.
  intros HM Hv Hn1 Hn Hst Hfr Hg.
  refine (proj2 (a_store_sound_gen segs ρ A A' m m' v a (repeat BT n) HM Hv ltac:(rewrite repeat_length; exact Hn1)
                   ltac:(rewrite repeat_length; exact Hn) Hst ltac:(rewrite repeat_length; exact Hfr) _)).
  intros i Hi. rewrite repeat_length in Hi.
  assert (Hnth : nth i (repeat BT n) BT = BT) by (apply nth_repeat).
  destruct (m' (wz (bv_unsigned a + Z.of_nat i))) as [b|] eqn:E'.
  - left. exists b. split; [reflexivity|]. rewrite Hnth. exact I.
  - right. split; [|exact Hnth]. destruct (m (wz (bv_unsigned a + Z.of_nat i))) as [b0|] eqn:E0; [|reflexivity].
    exfalso. apply (Hg (wz (bv_unsigned a + Z.of_nat i))); [rewrite E0; discriminate | exact E'].
Qed.

(* [comment removed for export] *)
Lemma a_store_BT_sound (ρ : valuation) (A A' : list region) (m : word -> option byte) (v : xv) (a : bv 64) (bs : list byte) :
  RMem segs ρ A m -> xv_val ρ v a -> (1 <= length bs < 1000)%nat -> a_store segs A v (repeat BT (length bs)) = Some A' ->
  store_ok segs m a (length bs) = true /\ RMem segs ρ A' (write_to_mem m a bs).
Proof.
  intros HM Hv Hn Hst.
  pose proof (a_store_sound segs ρ A A' m v a (repeat BT (length bs)) bs HM Hv ltac:(rewrite repeat_length; exact Hn)) as H.
  rewrite repeat_length in H. apply H; [|exact Hst].
  clear. induction bs as [|b bs IH]; cbn [length repeat]; constructor; [exact I | exact IH].
Qed.

End Mem.

(* [comment removed for export] *)
Definition cell_lit (segs : list Segment) (mem : list region) (a v : Z) : bool :=
  match a_load segs mem (XL (wofZ a)) 8 with
  | Some l => match all_lit l with Some bs => (wZ (lit_load SZ8 true bs) =? v) | None => false end
  | None => false
  end.

Lemma cell_lit_sound (segs : list Segment) (ρ : valuation) (A : list region) (m : word -> option byte) (a v : Z) :
  RMem segs ρ A m -> 0 <= a < 2 ^ 64 -> cell_lit segs A a v = true -> cell8 segs m a v.
Proof.
  intros HM Ha H. unfold cell_lit in H.
  destruct (a_load segs A (XL (wofZ a)) 8) as [l|] eqn:El; [|discriminate].
  destruct (all_lit l) as [ibs|] eqn:Ea; [|discriminate]. apply Z.eqb_eq in H.
  assert (Hv : xv_val ρ (XL (wofZ a)) (Z_to_bv 64 a)).
  { cbn [xv_val]. rewrite wZ_wofZ, Z_to_bv_unsigned. reflexivity. }
  destruct (a_load_sound segs ρ A m _ _ 8 l HM Hv ltac:(lia) El) as [bs [Hrd HF]].
  exists bs. split; [exact Hrd|]. apply word_lit_w. rewrite <- H.
  pose proof (a_load_length segs A _ 8 l El) as Hl. apply all_lit_map in Ea. subst l. rewrite length_map in Hl.
  apply lit_load_sound; [exact Hl|].
  clear -HF. revert bs HF. induction ibs as [|i r IH]; intros bs HF; inversion HF; subst; constructor; [assumption | apply IH; assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma model_backing_fields (model : Model) (pages : list word) :
  m_halted (with_vm_backing (m_vm_lazy model) pages model) = m_halted model /\
  vm_limit (m_vmmaps (with_vm_backing (m_vm_lazy model) pages model)) = vm_limit (m_vmmaps model).
Proof. destruct model as [fd [maps lazy mat] io fs proc lim tm]. split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition in_seg (segs : list Segment) (a : Z) : bool :=
  existsb (fun sg => (Z.of_N (seg_base sg) <=? a) && (a + 8 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs.

Lemma no_lazy_img (segs : list Segment) (Hlow : segs_low segs) (model : Model) (a n : Z) :
  vm_reserved (m_vmmaps model) = segments_reserved segs ->
  (forall p q, In p (m_vm_lazy model) -> In q (vm_reserved (m_vmmaps model)) -> iv_disj (bas p) (bas p + bsz p) q) ->
  in_seg segs a = true -> no_lazy model a (a + Z.min n 8).
Proof.
  intros Hres Hlz Hin. unfold in_seg in Hin. apply existsb_exists in Hin as [sg [HIn Hc]].
  apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2. pose proof (Hlow sg HIn) as Hl. unfold ls_beg in Hl.
  destruct (Z_lt_le_dec 0 (Z.min n 8)) as [Hpos|Hpos]; [|intros p z _ Hz; lia].
  apply (no_lazy_in_segment model segs sg a (a + Z.min n 8)); [|exact HIn|lia|lia|lia|lia].
  intros p q Hp Hq. rewrite <- Hres in Hq. destruct (Hlz p q Hp Hq) as [X|X]; unfold bas, bsz in X; [left | right]; lia.
Qed.

(* [comment removed for export] *)
Definition in_segn (segs : list Segment) (a n : Z) : bool :=
  lexists (fun sg => (Z.of_N (seg_base sg) <=? a) &&& (a + n <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs.

Lemma in_segn_low (segs : list Segment) (a n : Z) : segs_low segs -> in_segn segs a n = true -> 0 <= a /\ a + n <= ls_beg.
Proof.
  intros Hlow H. apply lexists_exists in H as [sg [HIn Hc]]. apply land_true in Hc as [C1 C2].
  apply Z.leb_le in C1. apply Z.leb_le in C2. pose proof (Hlow sg HIn). lia.
Qed.

Lemma no_lazy_imgn (segs : list Segment) (Hlow : segs_low segs) (model : Model) (a n : Z) :
  vm_reserved (m_vmmaps model) = segments_reserved segs ->
  (forall p q, In p (m_vm_lazy model) -> In q (vm_reserved (m_vmmaps model)) -> iv_disj (bas p) (bas p + bsz p) q) ->
  in_segn segs a n = true -> no_lazy model a (a + n).
Proof.
  intros Hres Hlz Hin. apply lexists_exists in Hin as [sg [HIn Hc]]. apply land_true in Hc as [C1 C2].
  apply Z.leb_le in C1. apply Z.leb_le in C2. pose proof (Hlow sg HIn) as Hl. unfold ls_beg in Hl.
  destruct (Z_lt_le_dec 0 n) as [Hpos|Hpos]; [|intros p z _ Hz; lia].
  apply (no_lazy_in_segment model segs sg a (a + n)); [|exact HIn|lia|lia|lia|lia].
  intros p q Hp Hq. rewrite <- Hres in Hq. destruct (Hlz p q Hp Hq) as [X|X]; unfold bas, bsz in X; [left | right]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition same_addr (s : store) (ts : terms) (o : w64) (ts' : terms) (o' : w64) : bool :=
  (teqb ts ts' &&& w_eqb o o') |||
  (let f := canon_form s ts o in let g := canon_form s ts' o' in teqb (fst f) (fst g) &&& w_eqb (snd f) (snd g)).

Lemma same_addr_sound (ρ : valuation) (s : store) (ts : terms) (o : w64) (ts' : terms) (o' : w64) :
  sat ρ s -> same_addr s ts o ts' o' = true -> smod ρ ts o = smod ρ ts' o'.
Proof.
  intros Hs H. unfold same_addr in H. apply lor_true in H as [H|H]; apply land_true in H as [H1 H2].
  - apply teqb_eq in H1. rewrite w_eqb_spec in H2. apply Z.eqb_eq in H2. apply wZ_inj in H2. subst. reflexivity.
  - apply teqb_eq in H1. rewrite w_eqb_spec in H2. apply Z.eqb_eq in H2. apply wZ_inj in H2.
    rewrite <- (canon_form_sound ρ s ts o Hs), <- (canon_form_sound ρ s ts' o' Hs), H1, H2. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_firstn' (segs : list Segment) (m : word -> option byte) : forall (n : nat) (a : word) (bs : list byte) (k : nat),
  rdn segs m a n = Some bs -> (k <= n)%nat -> rdn segs m a k = Some (firstn k bs).
Proof.
  induction n as [|n IH]; intros a bs k H Hk.
  - assert (k = 0%nat) by lia. subst k. reflexivity.
  - destruct k as [|k]; [reflexivity|]. cbn [rdn] in *.
    destruct (match m a with Some b => Some b | None => seg_rom segs a end) as [b|]; [|discriminate].
    destruct (rdn segs m (a + 1)%bv n) as [r|] eqn:Er; [|discriminate]. injection H as <-.
    rewrite (IH _ r k Er ltac:(lia)). reflexivity.
Qed.

Lemma skipn_nth_cons {X : Type} (i : nat) (l : list X) (d : X) : (i < length l)%nat -> skipn i l = nth i l d :: skipn (S i) l.
Proof.
  revert l. induction i as [|i IH]; intros [|x l] H; cbn [length] in H; try lia; [reflexivity|].
  cbn [skipn nth]. apply IH. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lr_ge (s : store) (f : lin) (c : Z) : bool :=
  match lrange s f with Some (lo, _) => c <=? lo | None => false end.

Lemma lr_ge_sound (ρ : valuation) (s : store) (f : lin) (c : Z) : sat ρ s -> lr_ge s f c = true -> c <= leval ρ f.
Proof.
  intros Hs H. unfold lr_ge in H. destruct (lrange s f) as [[lo hi]|] eqn:E; [|discriminate]. apply Z.leb_le in H.
  pose proof (lrange_sound ρ s f Hs _ E) as X. cbn [fst snd] in X. lia.
Qed.

(* [comment removed for export] *)
Definition rprove_q (d : nat) (s : store) (f : lin) (c : Z) : bool :=
  match lrange s f with
  | Some (lo, hi) => if c <=? lo then true else if hi <? c then false else rprove d s f c
  | None => rprove d s f c
  end.

Lemma rprove_q_sound (ρ : valuation) (s : store) (d : nat) (f : lin) (c : Z) : sat ρ s -> rprove_q d s f c = true -> c <= leval ρ f.
Proof.
  intros Hs H. unfold rprove_q in H. destruct (lrange s f) as [[lo hi]|] eqn:E; [|exact (rprove_sound ρ s d f c Hs H)].
  destruct (c <=? lo) eqn:E1.
  - apply Z.leb_le in E1. pose proof (lrange_sound ρ s f Hs _ E) as X. cbn [fst snd] in X. lia.
  - destruct (hi <? c); [discriminate | exact (rprove_sound ρ s d f c Hs H)].
Qed.

(* [comment removed for export] *)
Definition lr_in (s : store) (f : lin) (lo hi : Z) : bool :=
  match lrange s f with Some (l, h) => (lo <=? l) &&& (h <=? hi) | None => false end.

Lemma lr_in_sound (ρ : valuation) (s : store) (f : lin) (lo hi : Z) : sat ρ s -> lr_in s f lo hi = true -> lo <= leval ρ f <= hi.
Proof.
  intros Hs H. unfold lr_in in H. destruct (lrange s f) as [[l h]|] eqn:E; [|discriminate]. apply land_true in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. pose proof (lrange_sound ρ s f Hs _ E) as X. cbn [fst snd] in X. lia.
Qed.

(* [comment removed for export] *)
Definition mem_hole1 (f : lin) (n : Z) (fc : fact) : bool :=
  fc_hole fc &&& teqb (snd (fc_f fc)) (snd f)
  &&& (fc_lo fc + (fst f - fst (fc_f fc)) + n + 8 <=? 0x7fff8000) &&& (0x10007fff8000 <=? fc_hi fc + (fst f - fst (fc_f fc))).

Definition mem_hole (s : store) (f : lin) (n : Z) : bool :=
  match lrange s f with
  | Some (lo, hi) => (0 <=? lo) &&& (hi + n + 8 <=? 2 ^ 47) &&& lexists (mem_hole1 f n) (st_facts s)
  | None => false
  end.

Lemma mem_hole_sound (ρ : valuation) (s : store) (f : lin) (n : Z) : sat ρ s -> mem_hole s f n = true ->
  (0x10007fff8000 <= leval ρ f /\ leval ρ f + n + 8 <= 2 ^ 47) \/ (0 <= leval ρ f /\ leval ρ f + n + 8 <= 0x7fff8000).
Proof.
  intros Hs H. unfold mem_hole in H. destruct (lrange s f) as [[lo hi]|] eqn:E; [|discriminate].
  apply land_true in H as [H Hex]. apply land_true in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (lrange_sound ρ s f Hs _ E) as X. cbn [fst snd] in X.
  apply lexists_exists in Hex as [fc [Hin Hfc]]. unfold mem_hole1 in Hfc.
  apply land_true in Hfc as [Hfc H4]. apply land_true in Hfc as [Hfc H3]. apply land_true in Hfc as [Hh Ht].
  apply Z.leb_le in H3. apply Z.leb_le in H4. apply teqb_eq in Ht.
  destruct Hs as [_ Hfs]. rewrite Forall_forall in Hfs. pose proof (Hfs fc Hin) as Hsat. unfold fact_sat in Hsat. rewrite Hh in Hsat.
  assert (El : leval ρ f = leval ρ (fc_f fc) + (fst f - fst (fc_f fc))) by (unfold leval; rewrite Ht; ring).
  destruct Hsat as [Hl|Hr]; [right|left]; lia.
Qed.

(* [comment removed for export] *)
Definition hole_far1 (a : lin) (n : Z) (fc : fact) : bool :=
  fc_hole fc &&& teqb (snd (fc_f fc)) (snd a)
  &&& (fc_lo fc + (fst a - fst (fc_f fc)) <=? - n) &&& (n <=? fc_hi fc + (fst a - fst (fc_f fc))).

Definition hole_far (s : store) (a : lin) (n : Z) : bool := lexists (hole_far1 a n) (st_facts s).

Lemma hole_far_sound (ρ : valuation) (s : store) (a : lin) (n : Z) : sat ρ s -> hole_far s a n = true -> leval ρ a <= - n \/ n <= leval ρ a.
Proof.
  intros Hs H. unfold hole_far in H. apply lexists_exists in H as [fc [Hin Hfc]]. unfold hole_far1 in Hfc.
  apply land_true in Hfc as [Hfc H4]. apply land_true in Hfc as [Hfc H3]. apply land_true in Hfc as [Hh Ht].
  apply Z.leb_le in H3. apply Z.leb_le in H4. apply teqb_eq in Ht.
  destruct Hs as [_ Hfs]. rewrite Forall_forall in Hfs. pose proof (Hfs fc Hin) as Hsat. unfold fact_sat in Hsat. rewrite Hh in Hsat.
  assert (El : leval ρ a = leval ρ (fc_f fc) + (fst a - fst (fc_f fc))) by (unfold leval; rewrite Ht; ring).
  destruct Hsat as [Hl|Hr]; [left|right]; lia.
Qed.

(* [comment removed for export] *)
Definition in_app_mem (s : store) (f : lin) (n : Z) : bool :=
  lr_in s f 0x10007fff8000 (2 ^ 47 - n - 8) ||| lr_in s f 0 (0x7fff8000 - n - 8) ||| mem_hole s f n
  ||| rbetween 2 s f 0x10007fff8000 (2 ^ 47 - n - 8) ||| rbetween 2 s f 0 (0x7fff8000 - n - 8).

Lemma in_app_mem_sound (ρ : valuation) (s : store) (f : lin) (n : Z) : sat ρ s -> in_app_mem s f n = true ->
  (0x10007fff8000 <= leval ρ f /\ leval ρ f + n + 8 <= 2 ^ 47) \/ (0 <= leval ρ f /\ leval ρ f + n + 8 <= 0x7fff8000).
Proof.
  intros Hs H. unfold in_app_mem in H.
  apply lor_true in H as [H|H]; [apply lor_true in H as [H|H]; [apply lor_true in H as [H|H]; [apply lor_true in H as [H|H]|]|]|].
  - pose proof (lr_in_sound ρ s f _ _ Hs H). left. lia.
  - pose proof (lr_in_sound ρ s f _ _ Hs H). right. lia.
  - exact (mem_hole_sound ρ s f n Hs H).
  - pose proof (rbetween_sound ρ s 2 _ _ _ Hs H). left. lia.
  - pose proof (rbetween_sound ρ s 2 _ _ _ Hs H). right. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint irange_all {X : Type} (f : Z -> X -> bool) (d : nat) (t : itrie X) (k : Z) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c => match iget d t (of_Z k) with Some v => f k v | None => true end &&& irange_all f d t (k + 1) c
  end.

Lemma irange_all_iget {X : Type} (f : Z -> X -> bool) (d : nat) (t : itrie X) : forall (cnt : nat) (k j : Z) (v : X),
  irange_all f d t k cnt = true -> k <= j < k + Z.of_nat cnt -> iget d t (of_Z j) = Some v -> f j v = true.
Proof.
  induction cnt as [|c IH]; intros k j v H Hj Hg; [lia|]. cbn [irange_all] in H. apply land_true in H as [H1 H2].
  destruct (Z.eq_dec j k) as [->|Hne].
  - rewrite Hg in H1. exact H1.
  - apply (IH (k + 1) j v H2); [lia | exact Hg].
Qed.

(* [comment removed for export] *)
Definition keys_all {X : Type} (f : Z -> X -> bool) (d : nat) (t : itrie X) (k0 k1 : Z) : bool :=
  if k1 - k0 <? 16384 then irange_all f d t k0 (Z.to_nat (k1 - k0 + 1)) else AxScan.iall_key f t 0 1.

Lemma keys_all_iget {X : Type} (f : Z -> X -> bool) (d : nat) (t : itrie X) (k0 k1 : Z) (k : int) (v : X) :
  keys_all f d t k0 k1 = true -> k0 <= to_Z k <= k1 -> to_Z k < 2 ^ Z.of_nat d -> iget d t k = Some v -> f (to_Z k) v = true.
Proof.
  intros H Hk Hd Hg. unfold keys_all in H. destruct (k1 - k0 <? 16384).
  - apply (irange_all_iget f d t _ k0 (to_Z k) v H); [lia | rewrite of_to_Z; exact Hg].
  - pose proof (AxScan.iall_key_iget f d t 0 1 k v H Hg) as Y. pose proof (to_Z_bounded k).
    rewrite Z.mod_small in Y by lia. rewrite Z.add_0_l, Z.mul_1_l in Y. exact Y.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition words_ok_f (segs : list Segment) (base : Z) (ws : list (Z * Z)) : bool := AxWordsInt.words_ok_i segs base ws.

Lemma words_ok_f_eq (segs : list Segment) (base : Z) (ws : list (Z * Z)) : words_ok_f segs base ws = true -> words_ok segs base ws = true.
Proof. exact (AxWordsInt.words_ok_i_ok segs base ws). Qed.
