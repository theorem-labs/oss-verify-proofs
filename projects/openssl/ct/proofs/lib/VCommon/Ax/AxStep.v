(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie ExBytes.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require ExLoad.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLazy AxLin AxRel AxKb AxVal AxVal32 AxBytes AxMem AxMemC AxZZ AxBg AxState AxAcc AxMat AxAmo.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Inductive ares (M : Type) : Type :=
| ANext (A : astate M)
| AFork (l : list (astate M))
| AEcall (A : astate M)          (* [comment removed for export] *)
| AStuck (code : Z) (A : astate M)
| AFloor (r : int) (k : Z).
Arguments ANext {M}.
Arguments AFork {M}.
Arguments AEcall {M}.
Arguments AStuck {M}.
Arguments AFloor {M}.

Definition w_not1 : w64 := W true 9223372036854775806%uint63.

(* [comment removed for export] *)
Definition renorm_regs (s : store) (m : aregs) : aregs := imap (canon_v s) m.

Lemma aget_renorm (s : store) (m : aregs) (r : int) : aget (renorm_regs s m) r = canon_v s (aget m r).
Proof.
  unfold aget, renorm_regs. destruct (r =? 0)%uint63; [reflexivity|]. rewrite iget_imap.
  destruct (iget 5 m r); reflexivity.
Qed.

Lemma RRegs_renorm (ρ : valuation) (s : store) (m : aregs) (ms : machine_state) :
  sat ρ s -> RRegs ρ m ms -> RRegs ρ (renorm_regs s m) ms.
Proof. intros Hs H r. rewrite aget_renorm. apply canon_v_sound; [exact Hs | exact (H r)]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shares_var (ts1 ts2 : terms) : bool := lexists (fun p => lexists (fun q => (fst p =? fst q)%uint63) ts2) ts1.

Definition hole_ok (s : store) (nf : fact) (fc : fact) : bool :=
  match snd (fc_f fc) with
  | _ :: _ :: _ => match rel3 1 s [nf] (fst (fc_f fc)) (snd (fc_f fc)) with
                   | Some (lo, hi) => negb ((fc_lo fc <? lo) &&& (hi <? fc_hi fc))
                   | None => true
                   end
  | _ => true
  end.

Definition holes_ok (s : store) (d : lin) (lo hi : Z) : bool :=
  match snd d with
  | _ :: _ :: _ =>
      let nf := Fact d lo hi false in
      lforall (fun fc => if fc_hole fc then (if shares_var (snd d) (snd (fc_f fc)) then hole_ok s nf fc else true) else true) (st_facts s)
  | _ => true
  end.

Lemma holes_ok_sat (ρ : valuation) (s : store) (d : lin) (lo hi : Z) : sat ρ s -> lo <= leval ρ d <= hi -> holes_ok s d lo hi = true.
Proof.
  intros Hs Hd. unfold holes_ok. destruct (snd d) as [|q1 [|q2 q0]] eqn:Ed; try reflexivity. rewrite <- Ed.
  assert (Hnf : fact_sat ρ (Fact d lo hi false)) by exact Hd.
  apply lforall_intro. intros fc HIn.
  destruct (fc_hole fc) eqn:Eh; [|reflexivity]. destruct (shares_var (snd d) (snd (fc_f fc))); [|reflexivity]. unfold hole_ok.
  destruct (snd (fc_f fc)) as [|p1 [|p2 r0]] eqn:Ets; try reflexivity.
  destruct (rel3 1 s [Fact d lo hi false] (fst (fc_f fc)) (p1 :: p2 :: r0)) as [[l0 h0]|] eqn:El; [|reflexivity].
  pose proof (rel3_sound ρ s 1 Hs [Fact d lo hi false] (fst (fc_f fc)) (p1 :: p2 :: r0) ltac:(constructor; [exact Hnf | constructor]) _ El) as Hrg.
  cbn [fst snd] in Hrg.
  pose proof (proj1 (Forall_forall _ _) (proj2 Hs) fc HIn) as Hf. unfold fact_sat in Hf. rewrite Eh in Hf. unfold leval in Hf. rewrite Ets in Hf.
  apply negb_true_iff. destruct (fc_lo fc <? l0) eqn:E1; [|reflexivity]. apply Z.ltb_lt in E1.
  apply Z.ltb_ge. lia.
Qed.

Definition feasible (s : store) (d : lin) : bool :=
  match lrange s d with Some (lo, hi) => (lo <=? hi) &&& holes_ok s d lo hi | None => true end.

Lemma feasible_sat (ρ : valuation) (s : store) (d : lin) : sat ρ s -> feasible s d = true.
Proof.
  intros Hs. unfold feasible. destruct (lrange s d) as [[lo hi]|] eqn:E; [|reflexivity].
  pose proof (lrange_sound ρ s d Hs _ E) as H. cbn [fst snd] in H.
  apply land_intro; [apply Z.leb_le; lia | exact (holes_ok_sat ρ s d lo hi Hs H)].
Qed.

(* [comment removed for export] *)
Definition resv_store (r : rsv) : rsv := match r with RNone => RNone | _ => RUnk end.

(* [comment removed for export] *)
Definition need_floor (s : store) (x : xv) (k : Z) : bool :=
  match x with
  | XS _ _ => match xform s x with
              | Some f => match lshr s f k with None => true | Some _ => false end
              | None => false
              end
  | _ => false
  end.

(* [comment removed for export] *)
Definition align_bits (imm : w64) : option Z :=
  if wh imm then low_mask_bits (two64 - 1 - wZ imm) else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint hole_ne (fs : list fact) (c : Z) (ts : terms) : bool :=
  match fs with
  | [] => false
  | Fact (cf, tf) lo hi true :: r => (teqb tf ts &&& (lo <? cf - c) &&& (cf - c <? hi)) ||| hole_ne r c ts
  | _ :: r => hole_ne r c ts
  end.

Lemma hole_ne_sound (ρ : valuation) (fs : list fact) (c : Z) (ts : terms) :
  Forall (fact_sat ρ) fs -> hole_ne fs c ts = true -> c + teval ρ ts <> 0.
Proof.
  induction fs as [|[[cf tf] lo hi ho] r IH]; intros Hfs H; [discriminate|].
  inversion Hfs as [|? ? Hf Hr]; subst. cbn [hole_ne] in H. destruct ho; [|exact (IH Hr H)].
  apply lor_true in H as [H|H]; [|exact (IH Hr H)].
  apply land_true in H as [H H3]. apply land_true in H as [H1 H2]. apply teqb_eq in H1. subst tf.
  apply Z.ltb_lt in H2. apply Z.ltb_lt in H3.
  unfold fact_sat, leval in Hf. cbn [fc_hole fc_f fc_lo fc_hi fst snd] in Hf. lia.
Qed.

Definition rel_ne (s : store) (f g : lin) : bool :=
  hole_ne (st_facts s) (fst (lsub f g)) (snd (lsub f g)) ||| hole_ne (st_facts s) (fst (lsub g f)) (snd (lsub g f))
  ||| rprove 1 s (lsub g f) 1 ||| rprove 1 s (lsub f g) 1.

(* [comment removed for export] *)
Fixpoint hrefine_n (n : nat) (fs : list fact) (ts : terms) (c : Z) (i : ivl) : ivl :=
  match n with
  | O => i
  | S n' => let i' := hrefine fs ts c i in
            if (fst i' =? fst i) &&& (snd i' =? snd i) then i else hrefine_n n' fs ts c i'
  end.

Lemma hrefine_n_sound (ρ : valuation) (fs : list fact) (ts : terms) (c : Z) : Forall (fact_sat ρ) fs ->
  forall n i, fst i <= c + teval ρ ts <= snd i -> fst (hrefine_n n fs ts c i) <= c + teval ρ ts <= snd (hrefine_n n fs ts c i).
Proof.
  intros Hfs. induction n as [|n IH]; intros i Hi; cbn [hrefine_n]; [exact Hi|].
  destruct ((fst (hrefine fs ts c i) =? fst i) &&& (snd (hrefine fs ts c i) =? snd i)); [exact Hi|].
  apply IH. exact (hrefine_sound ρ fs ts c Hfs i Hi).
Qed.

Definition lrange_deep (s : store) (g : lin) : option ivl :=
  match lrange s g with
  | Some i => Some (match snd g with [] => i | ts => hrefine_n 6 (st_facts s) ts (fst g) i end)
  | None => None
  end.

Lemma lrange_deep_sound (ρ : valuation) (s : store) (g : lin) :
  sat ρ s -> forall i, lrange_deep s g = Some i -> fst i <= leval ρ g <= snd i.
Proof.
  intros Hs i H. unfold lrange_deep in H. destruct (lrange s g) as [j|] eqn:E; [|discriminate]. injection H as <-.
  pose proof (lrange_sound ρ s g Hs j E) as Hj. destruct (snd g) as [|t r] eqn:Eg; [exact Hj|].
  unfold leval in *. rewrite Eg in Hj |- *. exact (hrefine_n_sound ρ _ _ _ (proj2 Hs) 6 j Hj).
Qed.

(* [comment removed for export] *)
Definition deep_lt (s : store) (f g : lin) : bool :=
  match lrange_deep s f, lrange_deep s g with Some i, Some j => snd i <? fst j | _, _ => false end.
Definition deep_le (s : store) (f g : lin) : bool :=
  match lrange_deep s f, lrange_deep s g with Some i, Some j => snd i <=? fst j | _, _ => false end.

Lemma deep_lt_sound (ρ : valuation) (s : store) (f g : lin) : sat ρ s -> deep_lt s f g = true -> leval ρ f < leval ρ g.
Proof.
  intros Hs H. unfold deep_lt in H. destruct (lrange_deep s f) as [i|] eqn:Ei; [|discriminate]. destruct (lrange_deep s g) as [j|] eqn:Ej; [|discriminate].
  apply Z.ltb_lt in H. pose proof (lrange_deep_sound ρ s f Hs i Ei). pose proof (lrange_deep_sound ρ s g Hs j Ej). lia.
Qed.
Lemma deep_le_sound (ρ : valuation) (s : store) (f g : lin) : sat ρ s -> deep_le s f g = true -> leval ρ f <= leval ρ g.
Proof.
  intros Hs H. unfold deep_le in H. destruct (lrange_deep s f) as [i|] eqn:Ei; [|discriminate]. destruct (lrange_deep s g) as [j|] eqn:Ej; [|discriminate].
  apply Z.leb_le in H. pose proof (lrange_deep_sound ρ s f Hs i Ei). pose proof (lrange_deep_sound ρ s g Hs j Ej). lia.
Qed.

Definition rel_branch (s : store) (bc : branch_cond) (x y : xv) : option bool :=
  match xform s x, xform s y with
  | Some f, Some g =>
      match bc with
      | BC_LTU => if rprove 1 s (lsub g f) 1 then Some true else if rprove 1 s (lsub f g) 0 then Some false
                  else if deep_lt s f g then Some true else if deep_le s g f then Some false else None
      | BC_GEU => if rprove 1 s (lsub g f) 1 then Some false else if rprove 1 s (lsub f g) 0 then Some true
                  else if deep_lt s f g then Some false else if deep_le s g f then Some true else None
      | BC_EQ => if rel_ne s f g then Some false else None
      | BC_NE => if rel_ne s f g then Some true else None
      | _ => None
      end
  | _, _ => None
  end.

Definition a_branch_r (s : store) (bc : branch_cond) (x y : xv) : option bool :=
  match a_branch s bc x y with
  | Some b => Some b
  | None => rel_branch s bc x y
  end.

Lemma rel_branch_sound (ρ : valuation) (s : store) (bc : branch_cond) (x y : xv) (a b : bv 64) (r : bool) :
  sat ρ s -> xv_val ρ x a -> xv_val ρ y b -> rel_branch s bc x y = Some r -> r = branch_taken bc a b.
Proof.
  intros Hs Hx Hy H. unfold rel_branch in H.
  destruct (xform s x) as [f|] eqn:Ef; [|discriminate]. destruct (xform s y) as [g|] eqn:Eg; [|discriminate].
  pose proof (xform_sound ρ s x a f Hs Hx Ef) as Ha. pose proof (xform_sound ρ s y b g Hs Hy Eg) as Hb.
  assert (P1 : forall c, rprove 1 s (lsub g f) c = true -> c <= bv_unsigned b - bv_unsigned a).
  { intros c Hc. pose proof (rprove_sound ρ s 1 _ _ Hs Hc) as X. rewrite leval_lsub in X. lia. }
  assert (P2 : forall c, rprove 1 s (lsub f g) c = true -> c <= bv_unsigned a - bv_unsigned b).
  { intros c Hc. pose proof (rprove_sound ρ s 1 _ _ Hs Hc) as X. rewrite leval_lsub in X. lia. }
  assert (Pne : rel_ne s f g = true -> bv_unsigned a <> bv_unsigned b).
  { unfold rel_ne. intros E. apply lor_true in E as [E|E]; [apply lor_true in E as [E|E]; [apply lor_true in E as [E|E]|]|].
    - pose proof (hole_ne_sound ρ _ _ _ (proj2 Hs) E) as X. fold (leval ρ (lsub f g)) in X. rewrite leval_lsub in X. lia.
    - pose proof (hole_ne_sound ρ _ _ _ (proj2 Hs) E) as X. fold (leval ρ (lsub g f)) in X. rewrite leval_lsub in X. lia.
    - pose proof (P1 _ E). lia.
    - pose proof (P2 _ E). lia. }
  destruct bc; try discriminate; cbn [branch_taken]; unfold bv_ltu, bv_eqb.
  - destruct (rel_ne s f g) eqn:E; [|discriminate]. injection H as <-. symmetry. apply Z.eqb_neq. exact (Pne eq_refl).
  - destruct (rel_ne s f g) eqn:E; [|discriminate]. injection H as <-. symmetry. apply negb_true_iff, Z.eqb_neq. exact (Pne eq_refl).
  - destruct (rprove 1 s (lsub g f) 1) eqn:E1.
    + injection H as <-. pose proof (P1 _ E1). symmetry. apply Z.ltb_lt. lia.
    + destruct (rprove 1 s (lsub f g) 0) eqn:E2.
      * injection H as <-. pose proof (P2 _ E2). symmetry. apply Z.ltb_ge. lia.
      * destruct (deep_lt s f g) eqn:E3.
        -- injection H as <-. pose proof (deep_lt_sound ρ s f g Hs E3). symmetry. apply Z.ltb_lt. lia.
        -- destruct (deep_le s g f) eqn:E4; [|discriminate]. injection H as <-. pose proof (deep_le_sound ρ s g f Hs E4). symmetry. apply Z.ltb_ge. lia.
  - destruct (rprove 1 s (lsub g f) 1) eqn:E1.
    + injection H as <-. pose proof (P1 _ E1). symmetry. apply negb_false_iff, Z.ltb_lt. lia.
    + destruct (rprove 1 s (lsub f g) 0) eqn:E2.
      * injection H as <-. pose proof (P2 _ E2). symmetry. apply negb_true_iff, Z.ltb_ge. lia.
      * destruct (deep_lt s f g) eqn:E3.
        -- injection H as <-. pose proof (deep_lt_sound ρ s f g Hs E3). symmetry. apply negb_false_iff, Z.ltb_lt. lia.
        -- destruct (deep_le s g f) eqn:E4; [|discriminate]. injection H as <-. pose proof (deep_le_sound ρ s g f Hs E4). symmetry. apply negb_true_iff, Z.ltb_ge. lia.
Qed.

Lemma a_branch_r_sound (ρ : valuation) (s : store) (bc : branch_cond) (x y : xv) (a b : bv 64) (r : bool) :
  sat ρ s -> xv_val ρ x a -> xv_val ρ y b -> a_branch_r s bc x y = Some r -> r = branch_taken bc a b.
Proof.
  intros Hs Hx Hy H. unfold a_branch_r in H. destruct (a_branch s bc x y) as [r0|] eqn:E.
  - injection H as <-. exact (a_branch_sound ρ s bc x y a b r0 Hs Hx Hy E).
  - exact (rel_branch_sound ρ s bc x y a b r Hs Hx Hy H).
Qed.

(* [comment removed for export] *)
Definition and_floor (s : store) (x y : xv) : option Z :=
  match y with
  | XL m => match (match low_mask_bits (wZ m) with Some k => Some k | None => align_bits m end) with
            | Some k => if need_floor s x k then Some k else None
            | None => None
            end
  | _ => None
  end.

(* [comment removed for export] *)
Definition load_x (segs : list Segment) (s : store) (A : list region) (v : xv) (sz : msize) (sg : bool) : option xv :=
  match sz with
  | SZ8 => match a_loadw segs A v with
           | Some w => Some (XL w)
           | None => match a_load4 segs s A v 8 with Some l => Some (val_of_bytes s sz sg l) | None => None end
           end
  | _ => match a_load4 segs s A v (msz_n sz) with Some l => Some (val_of_bytes s sz sg l) | None => None end
  end.

Definition store_x (segs : list Segment) (s : store) (A : list region) (v : xv) (sz : msize) (x : xv) : option (list region) :=
  match sz, x with
  | SZ8, XL w => match a_storew A v w with Some A' => Some A' | None => a_store4 segs s A v (bytes_of sz x) end
  | _, XL w => match a_storek A v (msz_n sz) w with Some A' => Some A' | None => a_store4 segs s A v (bytes_of sz x) end
  | _, _ => a_store4 segs s A v (bytes_of sz x)
  end.

Lemma store_x_store4 (segs : list Segment) (s : store) (A A' : list region) (v : xv) (sz : msize) (x : xv) :
  store_x segs s A v sz x = Some A' -> a_store4 segs s A v (bytes_of sz x) = Some A'.
Proof.
  unfold store_x. destruct x as [w| | | | |]; try (destruct sz; exact (fun H => H)).
  assert (Hk : forall n, (1 <= n <= 8)%nat -> n = msz_n sz ->
            (match a_storek A v n w with Some A0 => Some A0 | None => a_store4 segs s A v (bytes_of sz (XL w)) end) = Some A' ->
            a_store4 segs s A v (bytes_of sz (XL w)) = Some A').
  { intros n Hn -> H. destruct (a_storek A v (msz_n sz) w) as [A0|] eqn:E; [|exact H]. injection H as <-.
    apply (a_storek_store segs) in E; [|exact Hn]. unfold a_store4, a_store3, a_store2. cbn [bytes_of]. rewrite E. reflexivity. }
  destruct sz; [exact (Hk 1%nat ltac:(lia) eq_refl) | exact (Hk 2%nat ltac:(lia) eq_refl) | exact (Hk 4%nat ltac:(lia) eq_refl) |].
  destruct (a_storew A v w) as [A0|] eqn:E; [|exact (fun H => H)]. intros H. injection H as <-.
  apply (a_storew_store segs) in E. change (bytes_of SZ8 (XL w)) with (wbytes w).
  unfold a_store4, a_store3, a_store2. rewrite E. reflexivity.
Qed.

Lemma load_x_sound (segs : list Segment) (ρ : valuation) (s : store) (A : list region) (m : word -> option byte) (v : xv) (a : bv 64)
    (sz : msize) (sg : bool) (x : xv) :
  segs_low segs -> sat ρ s -> RMem segs ρ A m -> hs_ok ρ A m -> xv_val ρ v a -> load_x segs s A v sz sg = Some x ->
  exists bs, rdn segs m a (msz_n sz) = Some bs /\ xv_val ρ x (load_word sz sg bs).
Proof.
  intros Hlow Hs HM Hhs Hv H.
  assert (Hgen : forall n, n = msz_n sz -> (match a_load4 segs s A v n with Some l => Some (val_of_bytes s sz sg l) | None => None end) = Some x ->
            exists bs, rdn segs m a (msz_n sz) = Some bs /\ xv_val ρ x (load_word sz sg bs)).
  { intros n -> H0. destruct (a_load4 segs s A v (msz_n sz)) as [l|] eqn:E; [|discriminate]. injection H0 as <-.
    destruct (a_load4_sound segs ρ s A m v a (msz_n sz) l Hlow Hs HM Hhs Hv ltac:(destruct sz; cbn; lia) E) as [bs [Hr Hf]].
    exists bs. split; [exact Hr|]. apply val_of_bytes_sound; [exact Hs | exact Hf | exact (a_load4_length segs _ _ _ _ _ E)]. }
  unfold load_x in H. destruct sz; try (exact (Hgen _ eq_refl H)).
  destruct (a_loadw segs A v) as [w|] eqn:Ew; [|exact (Hgen _ eq_refl H)]. injection H as <-.
  pose proof (a_loadw_load segs A v w Ew) as El.
  destruct (a_load_sound segs ρ A m v a 8 (wbytes w) HM Hv ltac:(lia) El) as [bs [Hr Hf]]. exists bs. split; [exact Hr|].
  pose proof (val_of_bytes_sound ρ s SZ8 sg (wbytes w) bs Hs Hf eq_refl) as X.
  change (val_of_bytes s SZ8 sg (wbytes w)) with (XL (ExLoad.w_of_bytes8 (map (w_byte w) (seq 0 8)))) in X.
  rewrite w_bytes8 in X. exact X.
Qed.

Section Exec.
Variable segs : list Segment.
Variable M : Type.
Variable LIM : Z.

Definition upd (A : astate M) (pc : w64) (regs : aregs) (resv : rsv) (mem : list region) : astate M :=
  AS pc regs resv mem (a_facts A) (a_model A) (a_budget A) (a_steps A + 1).

(* [comment removed for export] *)
Definition updm (A : astate M) (c : Z) (pc : w64) (regs : aregs) (resv : rsv) (mem : list region) : astate M :=
  AS pc regs resv mem (a_facts A) (a_model A) (a_budget A + c) (a_steps A + 1).

Definition with_facts (A : astate M) (pc : w64) (s : store) : astate M :=
  AS pc (renorm_regs s (a_regs A)) (a_resv A) (a_mem A) s (a_model A) (a_budget A) (a_steps A + 1).

(* [comment removed for export] *)
Definition rng_eq_fork (bc : branch_cond) (x y : xv) : bool :=
  match bc with
  | BC_EQ | BC_NE => match x, y with XR _ _, XL _ => true | XL _, XR _ _ => true | _, _ => false end
  | _ => false
  end.

Definition astep_d (A : astate M) (d : dinstr) : ares M :=
  let m := a_regs A in
  let s := a_facts A in
  let pc := a_pc A in
  let npc := w_add pc w_four in
  let next rd v := ANext (upd A npc (aset m rd v) (a_resv A) (a_mem A)) in
  if negb (pc_ok npc) then AStuck 1 A else
  match d with
  | DLui rd v => next rd (XL v)
  | DAuipc rd v => next rd (XL (w_add pc v))
  | DJal rd off =>
      let t := w_add pc off in
      if pc_ok t then ANext (upd A t (aset m rd (XL npc)) (a_resv A) (a_mem A)) else AStuck 2 A
  | DJalr rd rs1 off =>
      match aget m rs1 with
      | XL b => let t := w_and (w_add b off) w_not1 in
                if pc_ok t then ANext (upd A t (aset m rd (XL npc)) (a_resv A) (a_mem A)) else AStuck 3 A
      | _ => AStuck 10 A
      end
  | DBranch bc rs1 rs2 off =>
      let x := aget m rs1 in let y := aget m rs2 in
      let t := w_add pc off in
      if negb (pc_ok t) then AStuck 4 A else
      match a_branch_r s bc x y with
      | Some true => ANext (upd A t m (a_resv A) (a_mem A))
      | Some false => ANext (upd A npc m (a_resv A) (a_mem A))
      | None =>
          match a_fork s bc x y, xform s x, xform s y with
          | Some l, Some f, Some g =>
              let dd := lsub f g in
              match List.filter (fun p : store * bool => feasible (fst p) dd) l with
              | [p] => ANext (with_facts A (if snd p then t else npc) (fst p))
              | l' => AFork (map (fun p : store * bool => with_facts A (if snd p then t else npc) (fst p)) l')
              end
          | _, _, _ => if rng_eq_fork bc x y then AFork [with_facts A t s; with_facts A npc s] else AStuck 11 A
          end
      end
  | DLoad sz sg rd rs1 off =>
      if a_budget A + 8192 <=? LIM then
        match load_x segs s (a_mem A) (a_add s (aget m rs1) (XL off)) sz sg with
        | Some x => ANext (updm A 8192 npc (aset m rd x) (a_resv A) (a_mem A))
        | None => AStuck 12 A
        end
      else AStuck 13 A
  | DStore sz rs1 rs2 off =>
      if a_budget A + 8192 <=? LIM then
        match store_x segs s (a_mem A) (a_add s (aget m rs1) (XL off)) sz (aget m rs2) with
        | Some mem' => ANext (updm A 8192 npc m (resv_store (a_resv A)) mem')
        | None => AStuck 14 A
        end
      else AStuck 13 A
  | DOpImm op rd rs1 imm =>
      match op with
      | ALU_AND => match align_bits imm with
                   | Some k => if need_floor s (aget m rs1) k then AFloor rs1 k else next rd (a_alu64 s op (aget m rs1) (XL imm))
                   | None => next rd (a_alu64 s op (aget m rs1) (XL imm))
                   end
      | _ => next rd (a_alu64 s op (aget m rs1) (XL imm))
      end
  | DShiftImm op rd rs1 sh =>
      match op with
      | ALU_SRL => if need_floor s (aget m rs1) (wZ sh) then AFloor rs1 (wZ sh) else next rd (a_alu64 s op (aget m rs1) (XL sh))
      | _ => next rd (a_alu64 s op (aget m rs1) (XL sh))
      end
  | DOp op rd rs1 rs2 =>
      match op with
      | ALU_AND => match and_floor s (aget m rs1) (aget m rs2) with
                   | Some k => AFloor rs1 k
                   | None => match and_floor s (aget m rs2) (aget m rs1) with
                             | Some k => AFloor rs2 k
                             | None => next rd (a_alu64 s op (aget m rs1) (aget m rs2))
                             end
                   end
      | _ => next rd (a_alu64 s op (aget m rs1) (aget m rs2))
      end
  | DOpImm32 rd rs1 imm => next rd (a_alu32x s ALU_ADD (aget m rs1) (XL imm))
  | DShiftImm32 op rd rs1 sh => next rd (a_alu32x s op (aget m rs1) (XL sh))
  | DOp32 op rd rs1 rs2 => next rd (a_alu32x s op (aget m rs1) (aget m rs2))
  | DMul op rd rs1 rs2 => next rd (a_muldiv s op (aget m rs1) (aget m rs2))
  | DMul32 op rd rs1 rs2 => next rd (a_muldiv32 s op (aget m rs1) (aget m rs2))
  | DFence => ANext (upd A npc m (a_resv A) (a_mem A))
  | DLr wd rd rs1 =>
      let av := aget m rs1 in
      if a_budget A + 8192 <=? LIM then
        if a_aligned s wd av then
          match a_load4 segs s (a_mem A) av (amo_n wd) with
          | Some l => ANext (updm A 8192 npc (aset m rd (val_of_bytes s (match wd with AW => SZ4 | AD => SZ8 end) true l)) (RSome av) (a_mem A))
          | None => AStuck 20 A
          end
        else AStuck 21 A
      else AStuck 13 A
  | DSc wd rd rs1 rs2 =>
      let av := aget m rs1 in
      if a_budget A + 8192 <=? LIM then
        if a_aligned s wd av then
          match a_resv A with
          | RNone => ANext (upd A npc (aset m rd (XL w_one)) RNone (a_mem A))
          | RSome r =>
              if xv_same r av then
                match a_store4 segs s (a_mem A) av (bytes_of (match wd with AW => SZ4 | AD => SZ8 end) (aget m rs2)) with
                | Some mem' => ANext (updm A 8192 npc (aset m rd (XL w_zero)) RNone mem')
                | None => AStuck 25 A
                end
              else AStuck 26 A
          | RUnk => AStuck 27 A
          end
        else AStuck 24 A
      else AStuck 13 A
  | DAmo op wd rd rs1 rs2 =>
      let av := aget m rs1 in
      if a_budget A + 16384 <=? LIM then
        if a_aligned s wd av then
          match a_load4 segs s (a_mem A) av (amo_n wd) with
          | Some l =>
              let old := val_of_bytes s (match wd with AW => SZ4 | AD => SZ8 end) true l in
              let nb := match wd with AW => amo_bytes_w s op old (aget m rs2) | AD => amo_bytes_d s op old (aget m rs2) end in
              match a_store4 segs s (a_mem A) av nb with
              | Some mem' => ANext (updm A 16384 npc (aset m rd old) (resv_store (a_resv A)) mem')
              | None => AStuck 31 A
              end
          | None => AStuck 30 A
          end
        else AStuck 32 A
      else AStuck 13 A
  | DUnsupported => AStuck 49 A
  end.

End Exec.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wbv_not1 : wbv w_not1 = bv_not w1.
Proof. apply bv_eq. rewrite wbv_unsigned. rewrite bv_not_unsigned. reflexivity. Qed.

Section Sound.
Variable segs : list Segment.
Variable M : Type.
Variable MRρ : M -> Model -> Prop.
Variable LIM : Z.
Variable ρ : valuation.
Hypothesis MR_mat : forall am m pages, MRρ am m -> MRρ am (with_vm_backing (m_vm_lazy m) pages m).

Notation RR := (R segs M MRρ LIM ρ).

Lemma XL_w_of_bv (x : word) : xv_val ρ (XL (w_of_bv x)) x.
Proof. cbn [xv_val]. rewrite wZ_w_of_bv. reflexivity. Qed.

Lemma XL_val (v : w64) (x : word) : wbv v = x -> xv_val ρ (XL v) x.
Proof. intros <-. cbn [xv_val]. apply wbv_unsigned. Qed.

(* [comment removed for export] *)
Lemma R_build (A A' : astate M) (ms ms' : machine_state) (model model' : Model) :
  RR A (mkCfg ms model) ->
  ms_pc_val ms' = wbv (a_pc A') -> pc_ok (a_pc A') = true -> ms_svc_pending ms' = None ->
  RRegs ρ (a_regs A') ms' -> RResv ρ (a_resv A') (ms_resv ms') -> ms_rom ms' = ms_rom ms ->
  RMem segs ρ (a_mem A') (ms_mem ms') -> hs_ok ρ (a_mem A') (ms_mem ms') ->
  mem_cov segs model (ms_mem ms') -> comp_inv segs ρ (a_mem A') model -> na_ok segs ρ (a_mem A') model (ms_mem ms') ->
  a_model A' = a_model A -> sat ρ (a_facts A') ->
  ((model' = model /\ a_budget A <= a_budget A')
   \/ (exists pages, model' = with_vm_backing (m_vm_lazy model) pages model /\ vm_backing_used model' <= a_budget A')) ->
  RR A' (mkCfg ms' model').
Proof.
  intros HR Hpc Hok Hsvc Hregs Hres Hrom Hmem Hhs Hcov Hcomp Hna Hmod Hsat Hm.
  destruct HR as [Hpc0 Hal0 Hsvc0 Hregs0 Hres0 Hrom0 Hmem0 Hmod0 Hh0 [Hb0 Hl0] Hsat0 Hhs0 Hcov0 Hcomp0 Hna0].
  cbn [cfg_ms cfg_model] in *.
  destruct Hm as [[-> Hbud]|[pages [-> Hbud]]]; constructor; cbn [cfg_ms cfg_model]; try assumption.
  all: try (apply pc_ok_spec; exact Hok).
  all: try (rewrite Hrom; exact Hrom0).
  all: try (rewrite Hmod; first [exact Hmod0 | apply MR_mat; exact Hmod0]).
  - split; [lia | exact Hl0].
  - split; [exact Hbud | exact Hl0].
Qed.

(* [comment removed for export] *)
Lemma R_next_reg (A : astate M) (ms : machine_state) (model : Model) (rd : reg) (v : xv) (x pcw : word) (pc' : w64) :
  RR A (mkCfg ms model) -> pc_ok pc' = true -> pcw = wbv pc' -> xv_val ρ v x ->
  RR (upd M A pc' (aset (a_regs A) (ri rd) v) (a_resv A) (a_mem A)) (mkCfg (setx ms rd x pcw (ms_resv ms) (ms_mem ms)) model).
Proof.
  intros HR Hok Hpcw Hv. pose proof HR as [Hpc _ _ Hregs Hres _ Hmem _ _ _ Hsat Hhs Hcov Hcomp Hna].
  cbn [cfg_ms cfg_model] in *.
  apply (R_build A _ ms _ model model HR); cbn [upd a_pc a_regs a_resv a_mem a_model a_facts a_budget setx ms_pc_val ms_svc_pending ms_resv ms_rom ms_mem];
    try reflexivity; try assumption.
  all: first [ apply RRegs_set; assumption | left; split; [reflexivity | lia] ].
Qed.

Lemma R_next_noreg (A : astate M) (ms : machine_state) (model : Model) (pcw : word) (pc' : w64) :
  RR A (mkCfg ms model) -> pc_ok pc' = true -> pcw = wbv pc' ->
  RR (upd M A pc' (a_regs A) (a_resv A) (a_mem A)) (mkCfg (setx ms 0 w0 pcw (ms_resv ms) (ms_mem ms)) model).
Proof.
  intros HR Hok Hpcw. pose proof HR as [Hpc _ _ Hregs Hres _ Hmem _ _ _ Hsat Hhs Hcov Hcomp Hna].
  cbn [cfg_ms cfg_model] in *.
  apply (R_build A _ ms _ model model HR); cbn [upd a_pc a_regs a_resv a_mem a_model a_facts a_budget setx ms_pc_val ms_svc_pending ms_resv ms_rom ms_mem];
    try reflexivity; try assumption.
  all: first [ apply RRegs_set0; assumption | left; split; [reflexivity | lia] ].
Qed.

(* [comment removed for export] *)
Lemma R_next_facts (A : astate M) (ms : machine_state) (model : Model) (pcw : word) (pc' : w64) (s' : store) :
  RR A (mkCfg ms model) -> pc_ok pc' = true -> pcw = wbv pc' -> sat ρ s' ->
  RR (with_facts M A pc' s') (mkCfg (setx ms 0 w0 pcw (ms_resv ms) (ms_mem ms)) model).
Proof.
  intros HR Hok Hpcw Hs'. pose proof HR as [Hpc _ _ Hregs Hres _ Hmem _ _ _ Hsat Hhs Hcov Hcomp Hna].
  cbn [cfg_ms cfg_model] in *.
  apply (R_build A _ ms _ model model HR); cbn [with_facts a_pc a_regs a_resv a_mem a_model a_facts a_budget setx ms_pc_val ms_svc_pending ms_resv ms_rom ms_mem];
    try reflexivity; try assumption.
  all: first [ apply RRegs_renorm; [exact Hs'|]; apply RRegs_set0; assumption | left; split; [reflexivity | lia] ].
Qed.

Lemma sext32_imm (imm : bv 12) : xv_val32 ρ (XL (w_of_bv (sext 64 imm))) (sext 32 imm).
Proof.
  exists (sext 64 imm). split; [apply XL_w_of_bv|]. unfold sext. rewrite !bv_sign_extend_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 32 * 2 ^ 32). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_mod_divide; [reflexivity|]. exists (2 ^ 32). reflexivity.
Qed.

Lemma zext32_sh (shamt : bv 5) : xv_val32 ρ (XL (w_of_bv (zext 64 shamt))) (zext 32 shamt).
Proof.
  exists (zext 64 shamt). split; [apply XL_w_of_bv|]. unfold zext. rewrite !bv_zero_extend_unsigned' .
  pose proof (bv_unsigned_in_range 5 shamt) as Hs. change (bv_modulus 5) with 32 in Hs.
  unfold bv_wrap. change (bv_modulus 64) with (2^64). change (bv_modulus 32) with (2^32). change two32 with (2^32).
  rewrite !Z.mod_small; lia.
Qed.

(* [comment removed for export] *)
Lemma budget_step (A : astate M) (model : Model) (c : Z) (acc : list (word * nat)) :
  vm_backing_used model <= a_budget A -> vm_limit (m_vmmaps model) = LIM -> a_budget A + c <= LIM -> 4096 * acc_pages acc = c ->
  vm_backing_used model + 4096 * acc_pages acc <= vm_limit (m_vmmaps model).
Proof. intros. lia. Qed.

(* [comment removed for export] *)
Lemma R_mem_step (A : astate M) (ms ms' : machine_state) (model : Model) (c : Z) (acc : list (word * nat))
    (pc' : w64) (regs' : aregs) (resv' : rsv) (mem' : list region) :
  RR A (mkCfg ms model) -> a_budget A + c <= LIM -> 4096 * acc_pages acc = c ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' acc) ->
  ms_pc_val ms' = wbv pc' -> pc_ok pc' = true -> ms_svc_pending ms' = None ->
  RRegs ρ regs' ms' -> RResv ρ resv' (ms_resv ms') -> ms_rom ms' = ms_rom ms ->
  RMem segs ρ mem' (ms_mem ms') -> hs_ok ρ mem' (ms_mem ms') ->
  mem_cov segs model (ms_mem ms') -> comp_inv segs ρ mem' model -> na_ok segs ρ mem' model (ms_mem ms') ->
  exists ms1 model', mi_account_step segs ms model = MachineOk (ms1, model') /\ RR (updm M A c pc' regs' resv' mem') (mkCfg ms1 model').
Proof.
  intros HR Hc Hacc Hst Hpc Hok Hsvc Hregs Hres Hrom Hmem Hhs Hcov Hcomp Hna.
  pose proof HR as [_ _ _ _ _ _ _ _ _ [Hb Hl] Hsat _ _ _ _]. cbn [cfg_ms cfg_model] in *.
  destruct (account_acc segs ms ms' model acc Hst (budget_step A model c acc Hb Hl Hc Hacc)) as [pages [Ea Hu]].
  exists ms', (with_vm_backing (m_vm_lazy model) pages model). split; [exact Ea|].
  apply (R_build A _ ms ms' model _ HR); cbn [updm a_pc a_regs a_resv a_mem a_model a_facts a_budget]; try reflexivity; try assumption.
  right. exists pages. split; [reflexivity | lia].
Qed.

Lemma RResv_store (r : rsv) (a : word) (mr : option word) : RResv ρ r mr -> RResv ρ (resv_store r) (inval a mr).
Proof.
  destruct r; cbn [RResv resv_store]; try exact (fun _ => I).
  intros ->. reflexivity.
Qed.

Lemma msz_lt (sz : msize) : (1 <= msz_n sz < 1000)%nat.
Proof. destruct sz; cbn; lia. Qed.

Lemma amo_lt (wd : awidth) : (1 <= amo_n wd < 1000)%nat.
Proof. destruct wd; cbn; lia. Qed.

(* [comment removed for export] *)
Lemma store4_post (Hlow : segs_low segs) (A : astate M) (ms : machine_state) (model : Model) (v : xv) (a : word) (nb : list xb) (bs : list byte) (mem' : list region) :
  RR A (mkCfg ms model) -> xv_val ρ v a -> (1 <= length nb < 1000)%nat -> Forall2 (xb_bv ρ) nb bs ->
  a_store4 segs (a_facts A) (a_mem A) v nb = Some mem' ->
  store_ok segs (ms_mem ms) a (length bs) = true
  /\ RMem segs ρ mem' (write_to_mem (ms_mem ms) a bs) /\ hs_ok ρ mem' (write_to_mem (ms_mem ms) a bs)
  /\ mem_cov segs model (write_to_mem (ms_mem ms) a bs) /\ comp_inv segs ρ mem' model
  /\ na_ok segs ρ mem' model (write_to_mem (ms_mem ms) a bs).
Proof.
  intros HR Hv Hn Hf Es. pose proof HR as [_ _ _ _ _ _ Hmem _ _ _ Hsat Hhs Hcov Hcomp Hna]. cbn [cfg_ms cfg_model] in *.
  pose proof (Forall2_length Hf) as Hlen.
  destruct (a_store4_sound segs ρ (a_facts A) (a_mem A) mem' (ms_mem ms) v a nb bs Hlow Hsat Hmem Hhs Hv Hn Hf Es) as [Hok [Hmem' Hhs']].
  pose proof (a_store4_fields segs (a_facts A) (a_mem A) mem' v nb Es) as HF.
  rewrite Hlen in Hok.
  split; [exact Hok|]. split; [exact Hmem'|]. split; [exact Hhs'|].
  split; [exact (mem_cov_write segs model (ms_mem ms) a bs Hcov Hok)|].
  split; [exact (comp_inv_geom segs ρ (a_mem A) mem' model HF Hcomp)|].
  apply (na_ok_geom segs ρ (a_mem A) mem' model _ HF). exact (na_ok_write segs ρ (a_mem A) model (ms_mem ms) a bs Hna Hok).
Qed.

Hypothesis Hlow : segs_low segs.

Ltac pc4 Hpc := rewrite wbv_add, Hpc, wbv_four; reflexivity.

Theorem astep_d_next_sound (A A' : astate M) (ms : machine_state) (model : Model) (w : bv 32) (i : instr) :
  RR A (mkCfg ms model) -> fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
  astep_d segs M LIM A (dec i) = ANext A' ->
  exists ms' model', mi_account_step segs ms model = MachineOk (ms', model') /\ RR A' (mkCfg ms' model').
Proof.
  intros HR Hf He Hd Hst. pose proof HR as [Hpc Hal Hsvc Hregs Hres Hrom Hmem Hmod Hh [Hb Hl] Hsat Hhs Hcov Hcomp Hna].
  cbn [cfg_ms cfg_model] in *.
  unfold astep_d in Hst. destruct (pc_ok (w_add (a_pc A) w_four)) eqn:Hnpc; cbn [negb] in Hst; [|discriminate].
  assert (Hnone : forall ms', RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
            RR A' (mkCfg ms' model) -> exists ms1 model', mi_account_step segs ms model = MachineOk (ms1, model') /\ RR A' (mkCfg ms1 model')).
  { intros ms' Hacc HR'. exists ms', model. split; [exact (account_none segs ms ms' model Hacc) | exact HR']. }
  destruct i; cbn [dec] in Hst; try discriminate.
  - (* [comment removed for export] *)
    injection Hst as <-. apply (Hnone _ (acc_Lui segs ms w 4 rd imm Hf He Hd)).
    apply R_next_reg; [exact HR | exact Hnpc | pc4 Hpc | apply XL_w_of_bv].
  - (* [comment removed for export] *)
    injection Hst as <-. apply (Hnone _ (acc_Auipc segs ms w 4 rd imm Hf He Hd)).
    apply R_next_reg; [exact HR | exact Hnpc | pc4 Hpc |]. apply XL_val. rewrite wbv_add, Hpc, wbv_w_of_bv. reflexivity.
  - (* [comment removed for export] *)
    destruct (pc_ok (w_add (a_pc A) (w_of_bv (sext 64 imm)))) eqn:Ht; [|discriminate]. injection Hst as <-.
    apply (Hnone _ (acc_Jal segs ms w 4 rd imm Hf He Hd)).
    apply R_next_reg; [exact HR | exact Ht | rewrite wbv_add, Hpc, wbv_w_of_bv; reflexivity |]. apply XL_val. pc4 Hpc.
  - (* [comment removed for export] *)
    destruct (aget (a_regs A) (ri rs1)) as [b| | | | |] eqn:Eb; try discriminate.
    destruct (pc_ok (w_and (w_add b (w_of_bv (sext 64 imm))) w_not1)) eqn:Ht; [|discriminate]. injection Hst as <-.
    apply (Hnone _ (acc_Jalr segs ms w 4 rd rs1 imm Hf He Hd)).
    assert (Hbv : rg ms rs1 = wbv b) by (specialize (Hregs rs1); rewrite Eb in Hregs; apply xv_XL in Hregs; exact Hregs).
    apply R_next_reg; [exact HR | exact Ht | rewrite wbv_and, wbv_add, wbv_w_of_bv, wbv_not1, Hbv; reflexivity |]. apply XL_val. pc4 Hpc.
  - (* [comment removed for export] *)
    destruct (pc_ok (w_add (a_pc A) (w_of_bv (sext 64 imm)))) eqn:Ht; cbn [negb] in Hst; [|discriminate].
    assert (Etk : (ms_pc_val ms + sext 64 imm)%bv = wbv (w_add (a_pc A) (w_of_bv (sext 64 imm)))) by (rewrite wbv_add, Hpc, wbv_w_of_bv; reflexivity).
    assert (Ent : (ms_pc_val ms + Z_to_bv 64 4)%bv = wbv (w_add (a_pc A) w_four)) by (pc4 Hpc).
    apply (Hnone _ (acc_Branch segs ms w 4 c rs1 rs2 imm Hf He Hd)).
    destruct (a_branch_r (a_facts A) c (aget (a_regs A) (ri rs1)) (aget (a_regs A) (ri rs2))) as [bt|] eqn:Eb.
    + pose proof (a_branch_r_sound ρ (a_facts A) c _ _ (rg ms rs1) (rg ms rs2) bt Hsat (Hregs rs1) (Hregs rs2) Eb) as Hbt.
      rewrite <- Hbt. destruct bt; injection Hst as <-; apply R_next_noreg; assumption.
    + destruct (a_fork (a_facts A) c (aget (a_regs A) (ri rs1)) (aget (a_regs A) (ri rs2))) as [l|] eqn:Efk; [|destruct (rng_eq_fork _ _ _); discriminate].
      destruct (xform (a_facts A) (aget (a_regs A) (ri rs1))) as [f|] eqn:Exf; [|destruct (rng_eq_fork _ _ _); discriminate].
      destruct (xform (a_facts A) (aget (a_regs A) (ri rs2))) as [g|] eqn:Exg; [|destruct (rng_eq_fork _ _ _); discriminate].
      destruct (a_fork_sound ρ (a_facts A) c _ _ (rg ms rs1) (rg ms rs2) l Hsat (Hregs rs1) (Hregs rs2) Efk) as [s' [r [Hin [Hs' Hr]]]].
      assert (Hin' : In (s', r) (List.filter (fun p : store * bool => feasible (fst p) (lsub f g)) l)).
      { apply filter_In. split; [exact Hin | exact (feasible_sat ρ s' _ Hs')]. }
      destruct (List.filter (fun p : store * bool => feasible (fst p) (lsub f g)) l) as [|p [|q rest]]; try discriminate.
      injection Hst as <-. destruct Hin' as [->|[]]. cbn [fst snd]. rewrite <- Hr.
      destruct r; apply R_next_facts; assumption.
  - (* [comment removed for export] *)
    destruct (a_budget A + 8192 <=? LIM) eqn:Ebud; [|discriminate]. apply Z.leb_le in Ebud.
    destruct (load_x segs (a_facts A) (a_mem A) (a_add (a_facts A) (aget (a_regs A) (ri rs1)) (XL (w_of_bv (sext 64 imm)))) sz signed)
      as [xl|] eqn:Eb; [|discriminate]. injection Hst as <-.
    pose proof (a_add_sound ρ (a_facts A) _ _ _ _ Hsat (Hregs rs1) (XL_w_of_bv (sext 64 imm))) as Hadd.
    destruct (load_x_sound segs ρ (a_facts A) (a_mem A) (ms_mem ms) _ _ sz signed xl Hlow Hsat Hmem Hhs Hadd Eb) as [bs [Hr Hxl]].
    apply (R_mem_step A ms _ model 8192 _ _ _ _ _ HR Ebud (f_equal (Z.mul 4096) (acc_pages_one _ (msz_n sz) ltac:(destruct sz; cbn; lia)))
             (acc_Load segs ms w 4 sz signed rd rs1 imm bs Hf He Hd Hr));
      cbn [setx ms_pc_val ms_svc_pending ms_resv ms_rom ms_mem]; try reflexivity; try assumption.
    + pc4 Hpc.
    + apply RRegs_set; [exact Hregs | exact Hxl].
  - (* [comment removed for export] *)
    destruct (a_budget A + 8192 <=? LIM) eqn:Ebud; [|discriminate]. apply Z.leb_le in Ebud.
    destruct (store_x segs (a_facts A) (a_mem A) (a_add (a_facts A) (aget (a_regs A) (ri rs1)) (XL (w_of_bv (sext 64 imm)))) sz (aget (a_regs A) (ri rs2)))
      as [mem'|] eqn:Es0; [|discriminate]. injection Hst as <-. pose proof (store_x_store4 segs _ _ _ _ _ _ Es0) as Es.
    pose proof (a_add_sound ρ (a_facts A) _ _ _ _ Hsat (Hregs rs1) (XL_w_of_bv (sext 64 imm))) as Hadd.
    pose proof (bytes_of_sound ρ sz _ (rg ms rs2) (Hregs rs2)) as Hf2.
    pose proof (bytes_of_length sz (aget (a_regs A) (ri rs2))) as Hlen.
    assert (Hlb : length (store_bytes sz (rg ms rs2)) = msz_n sz) by (rewrite <- (Forall2_length Hf2); exact Hlen).
    destruct (store4_post Hlow A ms model _ _ _ _ mem' HR Hadd ltac:(rewrite Hlen; apply msz_lt) Hf2 Es) as (Hok & Hmem' & Hhs' & Hcov' & Hcomp' & Hna').
    rewrite Hlb in Hok.
    apply (R_mem_step A ms _ model 8192 _ _ _ _ _ HR Ebud (f_equal (Z.mul 4096) (acc_pages_one _ (msz_n sz) ltac:(destruct sz; cbn; lia)))
             (acc_Store segs ms w 4 sz rs1 rs2 imm Hf He Hd Hok));
      cbn [setx ms_pc_val ms_svc_pending ms_resv ms_rom ms_mem]; try reflexivity; try assumption.
    all: first [ pc4 Hpc | (apply RRegs_set0; exact Hregs) | (apply RResv_store; exact Hres) ].
  - (* [comment removed for export] *)
    assert (Hgen : ANext (upd M A (w_add (a_pc A) w_four) (aset (a_regs A) (ri rd) (a_alu64 (a_facts A) op (aget (a_regs A) (ri rs1)) (XL (w_of_bv (sext 64 imm))))) (a_resv A) (a_mem A)) = ANext A' ->
              exists ms1 model', mi_account_step segs ms model = MachineOk (ms1, model') /\ RR A' (mkCfg ms1 model')).
    { intros E. injection E as <-. apply (Hnone _ (acc_OpImm segs ms w 4 op rd rs1 imm Hf He Hd)).
      apply R_next_reg; [exact HR | exact Hnpc | pc4 Hpc |]. apply a_alu64_sound; [exact Hsat | exact (Hregs rs1) | apply XL_w_of_bv]. }
    destruct op; try exact (Hgen Hst).
    destruct (align_bits (w_of_bv (sext 64 imm))) as [k|]; [|exact (Hgen Hst)].
    destruct (need_floor (a_facts A) (aget (a_regs A) (ri rs1)) k); [discriminate | exact (Hgen Hst)].
  - (* [comment removed for export] *)
    assert (Hgen : ANext (upd M A (w_add (a_pc A) w_four) (aset (a_regs A) (ri rd) (a_alu64 (a_facts A) op (aget (a_regs A) (ri rs1)) (XL (w_of_bv (zext 64 shamt))))) (a_resv A) (a_mem A)) = ANext A' ->
              exists ms1 model', mi_account_step segs ms model = MachineOk (ms1, model') /\ RR A' (mkCfg ms1 model')).
    { intros E. injection E as <-. apply (Hnone _ (acc_ShiftImm segs ms w 4 op rd rs1 shamt Hf He Hd)).
      apply R_next_reg; [exact HR | exact Hnpc | pc4 Hpc |]. apply a_alu64_sound; [exact Hsat | exact (Hregs rs1) | apply XL_w_of_bv]. }
    destruct op; try exact (Hgen Hst).
    destruct (need_floor (a_facts A) (aget (a_regs A) (ri rs1)) (wZ (w_of_bv (zext 64 shamt)))); [discriminate | exact (Hgen Hst)].
  - (* [comment removed for export] *)
    assert (Hgen : ANext (upd M A (w_add (a_pc A) w_four) (aset (a_regs A) (ri rd) (a_alu64 (a_facts A) op (aget (a_regs A) (ri rs1)) (aget (a_regs A) (ri rs2)))) (a_resv A) (a_mem A)) = ANext A' ->
              exists ms1 model', mi_account_step segs ms model = MachineOk (ms1, model') /\ RR A' (mkCfg ms1 model')).
    { intros E. injection E as <-. apply (Hnone _ (acc_Op segs ms w 4 op rd rs1 rs2 Hf He Hd)).
      apply R_next_reg; [exact HR | exact Hnpc | pc4 Hpc |]. apply a_alu64_sound; [exact Hsat | exact (Hregs rs1) | exact (Hregs rs2)]. }
    destruct op; try exact (Hgen Hst).
    destruct (and_floor (a_facts A) (aget (a_regs A) (ri rs1)) (aget (a_regs A) (ri rs2))); [discriminate|].
    destruct (and_floor (a_facts A) (aget (a_regs A) (ri rs2)) (aget (a_regs A) (ri rs1))); [discriminate | exact (Hgen Hst)].
  - (* [comment removed for export] *)
    injection Hst as <-. apply (Hnone _ (acc_OpImm32 segs ms w 4 rd rs1 imm Hf He Hd)).
    apply R_next_reg; [exact HR | exact Hnpc | pc4 Hpc |].
    apply a_alu32x_sound; [exact Hsat | apply xv_val32_low32; exact (Hregs rs1) | apply sext32_imm].
  - (* [comment removed for export] *)
    injection Hst as <-. apply (Hnone _ (acc_ShiftImm32 segs ms w 4 op rd rs1 shamt Hf He Hd)).
    apply R_next_reg; [exact HR | exact Hnpc | pc4 Hpc |].
    apply a_alu32x_sound; [exact Hsat | apply xv_val32_low32; exact (Hregs rs1) | apply zext32_sh].
  - (* [comment removed for export] *)
    injection Hst as <-. apply (Hnone _ (acc_Op32 segs ms w 4 op rd rs1 rs2 Hf He Hd)).
    apply R_next_reg; [exact HR | exact Hnpc | pc4 Hpc |].
    apply a_alu32x_sound; [exact Hsat | apply xv_val32_low32; exact (Hregs rs1) | apply xv_val32_low32; exact (Hregs rs2)].
  - (* [comment removed for export] *)
    injection Hst as <-. apply (Hnone _ (acc_Fence segs ms w 4 fm pred succ rd rs1 Hf He Hd)).
    apply R_next_noreg; [exact HR | exact Hnpc | pc4 Hpc].
  - (* [comment removed for export] *)
    injection Hst as <-. apply (Hnone _ (acc_FenceI segs ms w 4 rd rs1 imm Hf He Hd)).
    apply R_next_noreg; [exact HR | exact Hnpc | pc4 Hpc].
  - (* [comment removed for export] *)
    injection Hst as <-. apply (Hnone _ (acc_Mul segs ms w 4 op rd rs1 rs2 Hf He Hd)).
    apply R_next_reg; [exact HR | exact Hnpc | pc4 Hpc |]. apply a_muldiv_sound; [exact Hsat | exact (Hregs rs1) | exact (Hregs rs2)].
  - (* [comment removed for export] *)
    injection Hst as <-. apply (Hnone _ (acc_Mul32 segs ms w 4 op rd rs1 rs2 Hf He Hd)).
    apply R_next_reg; [exact HR | exact Hnpc | pc4 Hpc |].
    apply a_muldiv32_sound; [exact Hsat | apply xv_val32_low32; exact (Hregs rs1) | apply xv_val32_low32; exact (Hregs rs2)].
  - (* [comment removed for export] *)
    destruct (a_budget A + 8192 <=? LIM) eqn:Ebud; [|discriminate]. apply Z.leb_le in Ebud.
    destruct (a_aligned (a_facts A) w0 (aget (a_regs A) (ri rs1))) eqn:Eal; [|discriminate].
    destruct (a_load4 segs (a_facts A) (a_mem A) (aget (a_regs A) (ri rs1)) (amo_n w0)) as [l|] eqn:Eb; [|discriminate]. injection Hst as <-.
    pose proof (a_aligned_sound ρ _ w0 _ _ Hsat (Hregs rs1) Eal) as Hali.
    destruct (a_load4_sound segs ρ (a_facts A) (a_mem A) (ms_mem ms) _ _ (amo_n w0) l Hlow Hsat Hmem Hhs (Hregs rs1) (amo_lt w0) Eb) as [bs [Hr Hf2]].
    pose proof (a_load4_length segs _ _ _ _ _ Eb) as Hlen.
    apply (R_mem_step A ms _ model 8192 _ _ _ _ _ HR Ebud (f_equal (Z.mul 4096) (acc_pages_one _ (amo_n w0) ltac:(destruct w0; cbn; lia)))
             (acc_Lr segs ms w 4 w0 aq rl rd rs1 bs Hf He Hd Hali Hr));
      cbn [setx ms_pc_val ms_svc_pending ms_resv ms_rom ms_mem]; try reflexivity; try assumption.
    + pc4 Hpc.
    + apply RRegs_set; [exact Hregs|].
      replace (lr_word w0 bs) with (load_word (match w0 with AW => SZ4 | AD => SZ8 end) true bs) by (destruct w0; reflexivity).
      apply val_of_bytes_sound; [exact Hsat | exact Hf2 | destruct w0; exact Hlen].
    + cbn [RResv]. exists (rg ms rs1). split; [reflexivity | exact (Hregs rs1)].
  - (* [comment removed for export] *)
    destruct (a_budget A + 8192 <=? LIM) eqn:Ebud; [|discriminate]. apply Z.leb_le in Ebud.
    destruct (a_aligned (a_facts A) w0 (aget (a_regs A) (ri rs1))) eqn:Eal; [|discriminate].
    pose proof (a_aligned_sound ρ _ w0 _ _ Hsat (Hregs rs1) Eal) as Hali.
    destruct (a_resv A) as [|rv|] eqn:Erv; [| |discriminate].
    + (* [comment removed for export] *)
      injection Hst as <-. cbn [RResv] in Hres.
      assert (Hsc : sc_ok (ms_resv ms) (rg ms rs1) = false) by (rewrite Hres; reflexivity).
      apply (Hnone _ (acc_Sc_fail segs ms w 4 w0 aq rl rd rs1 rs2 Hf He Hd Hali Hsc)).
      apply (R_build A _ ms _ model model HR); cbn [upd a_pc a_regs a_resv a_mem a_model a_facts a_budget setx ms_pc_val ms_svc_pending ms_resv ms_rom ms_mem];
        try reflexivity; try assumption.
      all: first [ pc4 Hpc | (apply RRegs_set; [exact Hregs | apply XL_val; reflexivity]) | (left; split; [reflexivity | lia]) ].
    + destruct (xv_same rv (aget (a_regs A) (ri rs1))) eqn:Esame; [|discriminate].
      destruct (a_store4 segs (a_facts A) (a_mem A) (aget (a_regs A) (ri rs1)) (bytes_of (match w0 with AW => SZ4 | AD => SZ8 end) (aget (a_regs A) (ri rs2))))
        as [mem'|] eqn:Es; [|discriminate]. injection Hst as <-.
      cbn [RResv] in Hres. destruct Hres as [ra [Era Hra]].
      pose proof (xv_same_sound ρ _ _ ra (rg ms rs1) Esame Hra (Hregs rs1)) as Eaddr. subst ra.
      assert (Hsc : sc_ok (ms_resv ms) (rg ms rs1) = true) by (rewrite Era; unfold sc_ok; apply Z.eqb_refl).
      set (SZ := match w0 with AW => SZ4 | AD => SZ8 end) in *.
      pose proof (bytes_of_sound ρ SZ _ (rg ms rs2) (Hregs rs2)) as Hf2.
      assert (Esc : sc_bytes w0 (rg ms rs2) = store_bytes SZ (rg ms rs2)) by (destruct w0; reflexivity).
      pose proof (bytes_of_length SZ (aget (a_regs A) (ri rs2))) as Hlen.
      assert (Hszn : msz_n SZ = amo_n w0) by (destruct w0; reflexivity).
      assert (Hlb : length (store_bytes SZ (rg ms rs2)) = amo_n w0) by (rewrite <- (Forall2_length Hf2), Hlen; exact Hszn).
      destruct (store4_post Hlow A ms model _ _ _ _ mem' HR (Hregs rs1) ltac:(rewrite Hlen; apply msz_lt) Hf2 Es) as (Hok & Hmem' & Hhs' & Hcov' & Hcomp' & Hna').
      rewrite Hlb in Hok.
      apply (R_mem_step A ms _ model 8192 _ _ _ _ _ HR Ebud (f_equal (Z.mul 4096) (acc_pages_one _ (amo_n w0) ltac:(destruct w0; cbn; lia)))
               (acc_Sc_ok segs ms w 4 w0 aq rl rd rs1 rs2 Hf He Hd Hali Hsc Hok));
        cbn [setx ms_pc_val ms_svc_pending ms_resv ms_rom ms_mem]; try reflexivity; try (rewrite Esc; assumption); try assumption.
      * pc4 Hpc.
      * apply RRegs_set; [exact Hregs | apply XL_val; reflexivity].
  - (* [comment removed for export] *)
    destruct (a_budget A + 16384 <=? LIM) eqn:Ebud; [|discriminate]. apply Z.leb_le in Ebud.
    destruct (a_aligned (a_facts A) w0 (aget (a_regs A) (ri rs1))) eqn:Eal; [|discriminate].
    pose proof (a_aligned_sound ρ _ w0 _ _ Hsat (Hregs rs1) Eal) as Hali.
    destruct (a_load4 segs (a_facts A) (a_mem A) (aget (a_regs A) (ri rs1)) (amo_n w0)) as [l|] eqn:Eb; [|discriminate].
    destruct (a_load4_sound segs ρ (a_facts A) (a_mem A) (ms_mem ms) _ _ (amo_n w0) l Hlow Hsat Hmem Hhs (Hregs rs1) (amo_lt w0) Eb) as [bs [Hr Hf2]].
    pose proof (a_load4_length segs _ _ _ _ _ Eb) as Hlen.
    destruct w0.
    + (* [comment removed for export] *)
      cbn [amo_n] in *.
      destruct (a_store4 segs (a_facts A) (a_mem A) (aget (a_regs A) (ri rs1)) (amo_bytes_w (a_facts A) op (val_of_bytes (a_facts A) SZ4 true l) (aget (a_regs A) (ri rs2))))
        as [mem'|] eqn:Es; [|discriminate]. injection Hst as <-.
      set (old32 := bv_extract 0 32 (le_bytes_to_word bs)) in *.
      pose proof (amo_bytes_w_sound ρ (a_facts A) op (val_of_bytes (a_facts A) SZ4 true l) _ old32 (rg ms rs2) Hsat
                    (val_of_bytes_sound ρ (a_facts A) SZ4 true l bs Hsat Hf2 Hlen) (Hregs rs2)) as Hnb.
      assert (Hnl : length (amo_bytes_w (a_facts A) op (val_of_bytes (a_facts A) SZ4 true l) (aget (a_regs A) (ri rs2))) = 4%nat)
        by (rewrite (Forall2_length Hnb); apply length_Z_to_le_bytes).
      destruct (store4_post Hlow A ms model _ _ _ _ mem' HR (Hregs rs1) ltac:(rewrite Hnl; lia) Hnb Es) as (Hok & Hmem' & Hhs' & Hcov' & Hcomp' & Hna').
      rewrite length_Z_to_le_bytes in Hok.
      apply (R_mem_step A ms _ model 16384 _ _ _ _ _ HR Ebud (f_equal (Z.mul 4096) (acc_pages_two _ _ 4 4 ltac:(lia) ltac:(lia)))
               (acc_Amo_w segs ms w 4 op aq rl rd rs1 rs2 bs Hf He Hd Hali Hr Hok));
        cbn [setx ms_pc_val ms_svc_pending ms_resv ms_rom ms_mem]; try reflexivity; try assumption.
      * pc4 Hpc.
      * apply RRegs_set; [exact Hregs|]. exact (val_of_bytes_sound ρ (a_facts A) SZ4 true l bs Hsat Hf2 Hlen).
      * apply RResv_store. exact Hres.
    + (* [comment removed for export] *)
      cbn [amo_n] in *.
      destruct (a_store4 segs (a_facts A) (a_mem A) (aget (a_regs A) (ri rs1)) (amo_bytes_d (a_facts A) op (val_of_bytes (a_facts A) SZ8 true l) (aget (a_regs A) (ri rs2))))
        as [mem'|] eqn:Es; [|discriminate]. injection Hst as <-.
      pose proof (val_of_bytes_sound ρ (a_facts A) SZ8 true l bs Hsat Hf2 Hlen) as Hold. cbn [load_word] in Hold.
      pose proof (amo_bytes_d_sound ρ (a_facts A) op _ _ _ (rg ms rs2) Hsat Hold (Hregs rs2)) as Hnb.
      assert (Hnl : length (amo_bytes_d (a_facts A) op (val_of_bytes (a_facts A) SZ8 true l) (aget (a_regs A) (ri rs2))) = 8%nat)
        by (rewrite (Forall2_length Hnb); apply length_Z_to_le_bytes).
      destruct (store4_post Hlow A ms model _ _ _ _ mem' HR (Hregs rs1) ltac:(rewrite Hnl; lia) Hnb Es) as (Hok & Hmem' & Hhs' & Hcov' & Hcomp' & Hna').
      rewrite length_Z_to_le_bytes in Hok.
      apply (R_mem_step A ms _ model 16384 _ _ _ _ _ HR Ebud (f_equal (Z.mul 4096) (acc_pages_two _ _ 8 8 ltac:(lia) ltac:(lia)))
               (acc_Amo_d segs ms w 4 op aq rl rd rs1 rs2 bs Hf He Hd Hali Hr Hok));
        cbn [setx ms_pc_val ms_svc_pending ms_resv ms_rom ms_mem]; try reflexivity; try assumption.
      * pc4 Hpc.
      * apply RRegs_set; [exact Hregs | exact Hold].
      * apply RResv_store. exact Hres.
Qed.

Theorem astep_d_fork_sound (A : astate M) (l : list (astate M)) (ms : machine_state) (model : Model) (w : bv 32) (i : instr) :
  RR A (mkCfg ms model) -> fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
  astep_d segs M LIM A (dec i) = AFork l ->
  exists ms' model', mi_account_step segs ms model = MachineOk (ms', model') /\ exists A', In A' l /\ RR A' (mkCfg ms' model').
Proof.
  intros HR Hf He Hd Hst. pose proof HR as [Hpc Hal Hsvc Hregs Hres Hrom Hmem Hmod Hh [Hb Hl] Hsat Hhs Hcov Hcomp Hna].
  cbn [cfg_ms cfg_model] in *.
  unfold astep_d in Hst. destruct (pc_ok (w_add (a_pc A) w_four)) eqn:Hnpc; cbn [negb] in Hst; [|discriminate].
  destruct i; cbn [dec] in Hst; try discriminate.
  - destruct (pc_ok (w_add (a_pc A) (w_of_bv (sext 64 imm)))); discriminate.
  - destruct (aget (a_regs A) (ri rs1)) as [b| | | | |]; try discriminate. destruct (pc_ok (w_and (w_add b (w_of_bv (sext 64 imm))) w_not1)); discriminate.
  - (* [comment removed for export] *)
    destruct (pc_ok (w_add (a_pc A) (w_of_bv (sext 64 imm)))) eqn:Ht; cbn [negb] in Hst; [|discriminate].
    assert (Etk : (ms_pc_val ms + sext 64 imm)%bv = wbv (w_add (a_pc A) (w_of_bv (sext 64 imm)))) by (rewrite wbv_add, Hpc, wbv_w_of_bv; reflexivity).
    assert (Ent : (ms_pc_val ms + Z_to_bv 64 4)%bv = wbv (w_add (a_pc A) w_four)) by (rewrite wbv_add, Hpc, wbv_four; reflexivity).
    destruct (a_branch_r (a_facts A) c (aget (a_regs A) (ri rs1)) (aget (a_regs A) (ri rs2))) as [[|]|] eqn:Eb; try discriminate.
    assert (Hplain : (if rng_eq_fork c (aget (a_regs A) (ri rs1)) (aget (a_regs A) (ri rs2))
                      then AFork [with_facts M A (w_add (a_pc A) (w_of_bv (sext 64 imm))) (a_facts A); with_facts M A (w_add (a_pc A) w_four) (a_facts A)]
                      else AStuck 11 A) = AFork l ->
              exists ms' model', mi_account_step segs ms model = MachineOk (ms', model') /\ exists A', In A' l /\ RR A' (mkCfg ms' model')).
    { intros Hp. destruct (rng_eq_fork _ _ _); [|discriminate Hp]. injection Hp as <-.
      exists (setx ms 0 w0 (if branch_taken c (rg ms rs1) (rg ms rs2) then ms_pc_val ms + sext 64 imm else ms_pc_val ms + Z_to_bv 64 4)%bv (ms_resv ms) (ms_mem ms)), model.
      split; [exact (account_none segs ms _ model (acc_Branch segs ms w 4 c rs1 rs2 imm Hf He Hd))|].
      destruct (branch_taken c (rg ms rs1) (rg ms rs2)).
      - eexists. split; [left; reflexivity|]. apply R_next_facts; assumption.
      - eexists. split; [right; left; reflexivity|]. apply R_next_facts; assumption. }
    destruct (a_fork (a_facts A) c (aget (a_regs A) (ri rs1)) (aget (a_regs A) (ri rs2))) as [l0|] eqn:Efk; [|exact (Hplain Hst)].
    destruct (xform (a_facts A) (aget (a_regs A) (ri rs1))) as [f|] eqn:Exf; [|exact (Hplain Hst)].
    destruct (xform (a_facts A) (aget (a_regs A) (ri rs2))) as [g|] eqn:Exg; [|exact (Hplain Hst)].
    destruct (a_fork_sound ρ (a_facts A) c _ _ (rg ms rs1) (rg ms rs2) l0 Hsat (Hregs rs1) (Hregs rs2) Efk) as [s' [r [Hin [Hs' Hr]]]].
    assert (Hin' : In (s', r) (List.filter (fun p : store * bool => feasible (fst p) (lsub f g)) l0)).
    { apply filter_In. split; [exact Hin | exact (feasible_sat ρ s' _ Hs')]. }
    set (F := fun p : store * bool => with_facts M A (if snd p then w_add (a_pc A) (w_of_bv (sext 64 imm)) else w_add (a_pc A) w_four) (fst p)) in *.
    assert (El : l = map F (List.filter (fun p : store * bool => feasible (fst p) (lsub f g)) l0)).
    { destruct (List.filter (fun p : store * bool => feasible (fst p) (lsub f g)) l0) as [|p [|q rest]]; try discriminate; injection Hst as <-; reflexivity. }
    exists (setx ms 0 w0 (if branch_taken c (rg ms rs1) (rg ms rs2) then ms_pc_val ms + sext 64 imm else ms_pc_val ms + Z_to_bv 64 4)%bv (ms_resv ms) (ms_mem ms)), model.
    split; [exact (account_none segs ms _ model (acc_Branch segs ms w 4 c rs1 rs2 imm Hf He Hd))|].
    exists (F (s', r)). split; [rewrite El; apply in_map; exact Hin'|].
    unfold F. cbn [fst snd]. rewrite <- Hr. destruct r; apply R_next_facts; assumption.
  - destruct (a_budget A + 8192 <=? LIM); [|discriminate]. destruct (load_x _ _ _ _ _ _); discriminate.
  - destruct (a_budget A + 8192 <=? LIM); [|discriminate]. destruct (store_x _ _ _ _ _ _); discriminate.
  - destruct op; try discriminate. destruct (align_bits _); [|discriminate]. destruct (need_floor _ _ _); discriminate.
  - destruct op; try discriminate. destruct (need_floor _ _ _); discriminate.
  - destruct op; try discriminate. destruct (and_floor _ _ _); [discriminate|]. destruct (and_floor _ _ _); discriminate.
  - destruct (a_budget A + 8192 <=? LIM); [|discriminate]. destruct (a_aligned _ _ _); [|discriminate]. destruct (a_load4 _ _ _ _ _); discriminate.
  - destruct (a_budget A + 8192 <=? LIM); [|discriminate]. destruct (a_aligned _ _ _); [|discriminate].
    destruct (a_resv A); try discriminate. destruct (xv_same _ _); [|discriminate]. destruct (a_store4 _ _ _ _ _); discriminate.
  - destruct (a_budget A + 16384 <=? LIM); [|discriminate]. destruct (a_aligned _ _ _); [|discriminate].
    destruct (a_load4 _ _ _ _ _); [|discriminate]. destruct (a_store4 _ _ _ _ _); discriminate.
Qed.

(* [comment removed for export] *)
Lemma astep_d_no_ecall (A B : astate M) (d : dinstr) : astep_d segs M LIM A d <> AEcall B.
Proof.
  unfold astep_d. destruct (negb (pc_ok (w_add (a_pc A) w_four))); [discriminate|].
  destruct d; try discriminate.
  - destruct (pc_ok _); discriminate.
  - destruct (aget (a_regs A) rs1) as [b| | | | |]; try discriminate. destruct (pc_ok (w_and (w_add b off) w_not1)); discriminate.
  - destruct (negb (pc_ok _)); [discriminate|]. destruct (a_branch_r _ _ _ _) as [[|]|]; try discriminate.
    destruct (a_fork _ _ _ _); [|destruct (rng_eq_fork _ _ _); discriminate]. destruct (xform _ _); [|destruct (rng_eq_fork _ _ _); discriminate]. destruct (xform _ _); [|destruct (rng_eq_fork _ _ _); discriminate].
    destruct (List.filter _ _) as [|p [|q r]]; discriminate.
  - destruct (_ <=? LIM); [|discriminate]. destruct (load_x _ _ _ _ _ _); discriminate.
  - destruct (_ <=? LIM); [|discriminate]. destruct (store_x _ _ _ _ _ _); discriminate.
  - destruct op; try discriminate. destruct (align_bits _); [|discriminate]. destruct (need_floor _ _ _); discriminate.
  - destruct op; try discriminate. destruct (need_floor _ _ _); discriminate.
  - destruct op; try discriminate. destruct (and_floor _ _ _); [discriminate|]. destruct (and_floor _ _ _); discriminate.
  - destruct (_ <=? LIM); [|discriminate]. destruct (a_aligned _ _ _); [|discriminate]. destruct (a_load4 _ _ _ _ _); discriminate.
  - destruct (_ <=? LIM); [|discriminate]. destruct (a_aligned _ _ _); [|discriminate].
    destruct (a_resv A); try discriminate. destruct (xv_same _ _); [|discriminate]. destruct (a_store4 _ _ _ _ _); discriminate.
  - destruct (_ <=? LIM); [|discriminate]. destruct (a_aligned _ _ _); [|discriminate].
    destruct (a_load4 _ _ _ _ _); [|discriminate]. destruct (a_store4 _ _ _ _ _); discriminate.
Qed.

End Sound.

(* [comment removed for export] *)
Definition nomem (d : dinstr) : bool :=
  match d with
  | DLui _ _ | DAuipc _ _ | DJal _ _ | DJalr _ _ _ | DBranch _ _ _ _ | DLoad _ _ _ _ _ | DOpImm _ _ _ _ | DShiftImm _ _ _ _ | DOp _ _ _ _
  | DOpImm32 _ _ _ | DShiftImm32 _ _ _ _ | DOp32 _ _ _ _ | DMul _ _ _ _ | DMul32 _ _ _ _ | DFence => true
  | _ => false
  end.

Lemma astep_d_nomem (segs : list Segment) (M : Type) (LIM : Z) (A A' : astate M) (d : dinstr) :
  nomem d = true -> astep_d segs M LIM A d = ANext A' -> a_mem A' = a_mem A /\ a_model A' = a_model A.
Proof.
  intros Hn H. unfold astep_d in H. destruct (negb (pc_ok (w_add (a_pc A) w_four))); [discriminate|].
  destruct d; cbn [nomem] in Hn; try discriminate Hn.
  1-2: injection H as <-; split; reflexivity.
  - destruct (pc_ok _); [|discriminate]. injection H as <-. split; reflexivity.
  - destruct (aget (a_regs A) rs1) as [b| | | | |]; try discriminate. destruct (pc_ok _); [|discriminate]. injection H as <-. split; reflexivity.
  - destruct (negb (pc_ok _)); [discriminate|]. destruct (a_branch_r _ _ _ _) as [[|]|].
    1-2: injection H as <-; split; reflexivity.
    destruct (a_fork _ _ _ _) as [l|]; [|destruct (rng_eq_fork _ _ _); discriminate]. destruct (xform _ _); [|destruct (rng_eq_fork _ _ _); discriminate]. destruct (xform _ _); [|destruct (rng_eq_fork _ _ _); discriminate].
    destruct (List.filter _ l) as [|p [|q r]]; try discriminate. injection H as <-. split; reflexivity.
  - destruct (_ <=? LIM); [|discriminate]. destruct (load_x _ _ _ _ _ _); [|discriminate]. injection H as <-. split; reflexivity.
  - destruct op; try (injection H as <-; split; reflexivity).
    destruct (align_bits _); [|injection H as <-; split; reflexivity]. destruct (need_floor _ _ _); [discriminate|]. injection H as <-. split; reflexivity.
  - destruct op; try (injection H as <-; split; reflexivity). destruct (need_floor _ _ _); [discriminate|]. injection H as <-. split; reflexivity.
  - destruct op; try (injection H as <-; split; reflexivity).
    destruct (and_floor _ _ _); [discriminate|]. destruct (and_floor _ _ _); [discriminate|]. injection H as <-. split; reflexivity.
  - injection H as <-. split; reflexivity.
  - injection H as <-. split; reflexivity.
  - injection H as <-. split; reflexivity.
  - injection H as <-. split; reflexivity.
  - injection H as <-. split; reflexivity.
  - injection H as <-. split; reflexivity.
Qed.

Lemma astep_d_fork_mem (segs : list Segment) (M : Type) (LIM : Z) (A : astate M) (d : dinstr) (l : list (astate M)) :
  astep_d segs M LIM A d = AFork l -> forall A', In A' l -> a_mem A' = a_mem A /\ a_model A' = a_model A.
Proof.
  intros H. unfold astep_d in H. destruct (negb (pc_ok (w_add (a_pc A) w_four))); [discriminate|].
  destruct d; try discriminate.
  - destruct (pc_ok _); discriminate.
  - destruct (aget (a_regs A) rs1) as [b| | | | |]; try discriminate. destruct (pc_ok _); discriminate.
  - destruct (negb (pc_ok _)); [discriminate|]. destruct (a_branch_r _ _ _ _) as [[|]|]; try discriminate.
    assert (Hplain : forall t0 n0 : w64, (if rng_eq_fork bc (aget (a_regs A) rs1) (aget (a_regs A) rs2) then AFork [with_facts M A t0 (a_facts A); with_facts M A n0 (a_facts A)] else AStuck 11 A) = AFork l ->
              forall A', In A' l -> a_mem A' = a_mem A /\ a_model A' = a_model A).
    { intros t0 n0 Hp. destruct (rng_eq_fork _ _ _); [|discriminate Hp]. injection Hp as <-. intros A' [<-|[<-|[]]]; split; reflexivity. }
    destruct (a_fork _ _ _ _) as [l0|]; [|exact (Hplain _ _ H)]. destruct (xform _ _); [|exact (Hplain _ _ H)]. destruct (xform _ _); [|exact (Hplain _ _ H)].
    destruct (List.filter _ l0) as [|p [|q r]] eqn:Ef; try discriminate.
    + injection H as <-. intros A' [].
    + intros A' HIn.
      assert (Hl : l = map (fun p0 : store * bool => with_facts M A (if snd p0 then w_add (a_pc A) off else w_add (a_pc A) w_four) (fst p0)) (p :: q :: r))
        by (injection H as <-; reflexivity).
      rewrite Hl in HIn. apply in_map_iff in HIn as [x [<- _]]. split; reflexivity.
  - destruct (_ <=? LIM); [|discriminate]. destruct (load_x _ _ _ _ _ _); discriminate.
  - destruct (_ <=? LIM); [|discriminate]. destruct (store_x _ _ _ _ _ _); discriminate.
  - destruct op; try discriminate. destruct (align_bits _); [|discriminate]. destruct (need_floor _ _ _); discriminate.
  - destruct op; try discriminate. destruct (need_floor _ _ _); discriminate.
  - destruct op; try discriminate. destruct (and_floor _ _ _); [discriminate|]. destruct (and_floor _ _ _); discriminate.
  - destruct (_ <=? LIM); [|discriminate]. destruct (a_aligned _ _ _); [|discriminate]. destruct (a_load4 _ _ _ _ _); discriminate.
  - destruct (_ <=? LIM); [|discriminate]. destruct (a_aligned _ _ _); [|discriminate].
    destruct (a_resv A); try discriminate. destruct (xv_same _ _); [|discriminate]. destruct (a_store4 _ _ _ _ _); discriminate.
  - destruct (_ <=? LIM); [|discriminate]. destruct (a_aligned _ _ _); [|discriminate].
    destruct (a_load4 _ _ _ _ _); [|discriminate]. destruct (a_store4 _ _ _ _ _); discriminate.
Qed.

(* [comment removed for export] *)
Lemma astep_d_model (segs : list Segment) (M : Type) (LIM : Z) (A : astate M) (d : dinstr) :
  match astep_d segs M LIM A d with
  | ANext A' => a_model A' = a_model A
  | AFork l => forall A', In A' l -> a_model A' = a_model A
  | _ => True
  end.
Proof.
  unfold astep_d. destruct (negb (pc_ok (w_add (a_pc A) w_four))); [exact I|].
  destruct d; try reflexivity; try exact I.
  - destruct (pc_ok _); [reflexivity | exact I].
  - destruct (aget (a_regs A) rs1) as [b| | | | |]; try exact I. destruct (pc_ok _); [reflexivity | exact I].
  - destruct (negb (pc_ok _)); [exact I|]. destruct (a_branch_r _ _ _ _) as [[|]|]; try reflexivity.
    assert (Hplain : forall t0 n0 : w64, match (if rng_eq_fork bc (aget (a_regs A) rs1) (aget (a_regs A) rs2) then AFork [with_facts M A t0 (a_facts A); with_facts M A n0 (a_facts A)] else AStuck 11 A) with
                                         | ANext A' => a_model A' = a_model A | AFork l => forall A', In A' l -> a_model A' = a_model A | _ => True end).
    { intros t0 n0. destruct (rng_eq_fork _ _ _); [|exact I]. intros A' [<-|[<-|[]]]; reflexivity. }
    destruct (a_fork _ _ _ _) as [l|]; [|apply Hplain]. destruct (xform _ _); [|apply Hplain]. destruct (xform _ _); [|apply Hplain].
    destruct (List.filter _ l) as [|p [|q r]]; try reflexivity.
    + intros A' [].
    + intros A' HIn. apply in_map_iff in HIn as [x [<- _]]. reflexivity.
  - destruct (_ <=? LIM); [|exact I]. destruct (load_x _ _ _ _ _ _); [reflexivity | exact I].
  - destruct (_ <=? LIM); [|exact I]. destruct (store_x _ _ _ _ _ _); [reflexivity | exact I].
  - destruct op; try reflexivity. destruct (align_bits _); [|reflexivity]. destruct (need_floor _ _ _); [exact I | reflexivity].
  - destruct op; try reflexivity. destruct (need_floor _ _ _); [exact I | reflexivity].
  - destruct op; try reflexivity. destruct (and_floor _ _ _); [exact I|]. destruct (and_floor _ _ _); [exact I | reflexivity].
  - destruct (_ <=? LIM); [|exact I]. destruct (a_aligned _ _ _); [|exact I]. destruct (a_load4 _ _ _ _ _); [reflexivity | exact I].
  - destruct (_ <=? LIM); [|exact I]. destruct (a_aligned _ _ _); [|exact I].
    destruct (a_resv A); try reflexivity; try exact I. destruct (xv_same _ _); [|exact I]. destruct (a_store4 _ _ _ _ _); [reflexivity | exact I].
  - destruct (_ <=? LIM); [|exact I]. destruct (a_aligned _ _ _); [|exact I].
    destruct (a_load4 _ _ _ _ _); [|exact I]. destruct (a_store4 _ _ _ _ _); [reflexivity | exact I].
Qed.
