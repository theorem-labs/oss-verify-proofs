(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxFold FxRgs FxFacts FxSubst.

Module AcShift.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec FxLin FxCore FxSound FxSubst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition vshift (n : positive) (E : valu) : valu := fun y => E (n + y)%positive.
Definition tshift (n : positive) (t : list (positive * Z)) : list (positive * Z) :=
  List.map (fun p => ((n + fst p)%positive, snd p)) t.
Definition lshift (n : positive) (l : lin) : lin := LIN (l_c l) (tshift n (l_t l)).
Definition bshift (n : positive) (v : bval) : bval := match v with BK b => BK b | BV l j => BV (lshift n l) j end.
Definition fshift (n : positive) (f : fact) : fact :=
  match f with
  | FCond c a b tk => FCond c (lshift n a) (lshift n b) tk
  | FRange l lo hi => FRange (lshift n l) lo hi
  | FMod l k r => FMod (lshift n l) k r
  | FBits l m v => FBits (lshift n l) m v
  | FByte x v j => FByte (lshift n x) (lshift n v) j
  | FBytes x bs => FBytes (lshift n x) (List.map (fun p => (lshift n (fst p), snd p)) bs)
  end.
Definition rshift (n : positive) (R : region) : region :=
  RG (lshift n (rg_base R)) (lshift n (rg_size R)) (rg_kind R) (tmap (bshift n) (rg_cont R)).
Definition rsv_shift (n : positive) (r : rsv) : rsv := match r with RAt l => RAt (lshift n l) | _ => r end.
Definition sst_shift (n : positive) (P : sst) : sst :=
  SST (s_pc P) (tmap (lshift n) (s_regs P)) (List.map (rshift n) (s_rgs P)) (List.map (fshift n) (s_facts P))
      (n + s_next P)%positive (rsv_shift n (s_resv P)).

(* [comment removed for export] *)
Lemma tsum_shift : forall n E t, tsum E (tshift n t) = tsum (vshift n E) t.
Proof. intros n E t. induction t as [|[x c] t IH]; cbn [tshift List.map tsum fst snd]; [reflexivity|]. rewrite <- IH. reflexivity. Qed.
Lemma lden_shift : forall n E l, lden E (lshift n l) = lden (vshift n E) l.
Proof. intros n E [c t]. unfold lden, lz, lshift. cbn [l_c l_t]. rewrite tsum_shift. reflexivity. Qed.
Lemma bden_shift : forall n E v, bden E (bshift n v) = bden (vshift n E) v.
Proof. intros n E [b|l j]; cbn [bshift bden]; [reflexivity | rewrite lden_shift; reflexivity]. Qed.
Lemma rget_shift : forall n R k, rget (tmap (lshift n) R) k = lshift n (rget R k).
Proof.
  intros n R k. unfold rget. destruct k as [p|p|]; [| |reflexivity]; rewrite tget_tmap; destruct (tget _ R); reflexivity.
Qed.
Lemma rsz_shift : forall n E R, rsz E (rshift n R) = rsz (vshift n E) R.
Proof. intros n E R. unfold rsz, rshift. cbn [rg_size]. rewrite lden_shift. reflexivity. Qed.
Lemma base_shift : forall n E R, lden E (rg_base (rshift n R)) = lden (vshift n E) (rg_base R).
Proof. intros n E R. unfold rshift. cbn [rg_base]. apply lden_shift. Qed.

Lemma regs_ok_shift : forall n E R regs, regs_ok E (tmap (lshift n) R) regs <-> regs_ok (vshift n E) R regs.
Proof.
  intros n E R regs. unfold regs_ok. split; intros H r; rewrite (H r); rewrite rget_shift, lden_shift; reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma rg_ok_shift : forall n E m R, rg_ok segs E m (rshift n R) <-> rg_ok segs (vshift n E) m R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n E m R. unfold rg_ok. rewrite rsz_shift, base_shift. cbn [rg_kind rshift rg_cont].
  split; intros (H1 & H2 & H3 & H4); (split; [exact H1|]); (split; [exact H2|]); split.
  - intros i Hi. specialize (H3 i Hi). destruct (rg_kind R); try exact H3;
      (destruct H3 as [H3a H3b]; split; [exact H3a|]; intros Hn; apply H3b; rewrite tget_tmap, Hn; reflexivity).
  - intros p v Hp. destruct (H4 p (bshift n v)) as [Ha Hb]; [rewrite tget_tmap, Hp; reflexivity|].
    split; [exact Ha|]. rewrite bden_shift in Hb. exact Hb.
  - intros i Hi. specialize (H3 i Hi). destruct (rg_kind R); try exact H3;
      (destruct H3 as [H3a H3b]; split; [exact H3a|]; intros Hn; apply H3b; rewrite tget_tmap in Hn;
       destruct (tget (okey i) (rg_cont R)); [discriminate | reflexivity]).
  - intros p v Hp. rewrite tget_tmap in Hp. destruct (tget p (rg_cont R)) as [v0|] eqn:E0; [|discriminate].
    cbn [option_map] in Hp. injection Hp as <-. destruct (H4 p v0 E0) as [Ha Hb]. split; [exact Ha|].
    rewrite bden_shift. exact Hb.
Qed.

#[using="Type"] Lemma rg_disj_shift : forall n E R1 R2, rg_disj E (rshift n R1) (rshift n R2) <-> rg_disj (vshift n E) R1 R2.
Proof. LiaFast.lf_pins LiaFast.u0. intros n E R1 R2. unfold rg_disj. rewrite !base_shift, !rsz_shift. tauto. Qed.

#[using="Type"] Lemma rgs_disj_shift : forall n E rgs, rgs_disj E (List.map (rshift n) rgs) <-> rgs_disj (vshift n E) rgs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n E rgs. induction rgs as [|R rs IH]; cbn [List.map rgs_disj]; [tauto|]. rewrite IH.
  rewrite Forall_map. split; intros [H1 H2]; split; try exact H2;
    (eapply Forall_impl; [|exact H1]); intros R' HR'; apply rg_disj_shift; exact HR'.
Qed.

#[using="Type"] Lemma fact_ok_shift : forall n E f, fact_ok E (fshift n f) <-> fact_ok (vshift n E) f.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n E [c a b tk|l lo hi|l k r|l m v|x v j|x bs]; cbn [fshift fact_ok]; rewrite ?lden_shift; try tauto.
  rewrite length_map.
  assert (Hn : forall i, nth i (List.map (fun p => (lshift n (fst p), snd p)) bs) (lconst 0, 0) = (lshift n (fst (nth i bs (lconst 0, 0))), snd (nth i bs (lconst 0, 0)))).
  { intros i. change (lconst 0, 0) with ((fun p : lin * Z => (lshift n (fst p), snd p)) (lconst 0, 0)) at 1. rewrite map_nth. reflexivity. }
  split; intros H i Hi; specialize (H i Hi); rewrite ?Hn in *; cbn [fst snd] in *; rewrite ?lden_shift in *; exact H.
Qed.

#[using="Type"] Lemma rsv_ok_shift : forall n E r v, rsv_ok E (rsv_shift n r) v <-> rsv_ok (vshift n E) r v.
Proof. LiaFast.lf_pins LiaFast.u0. intros n E [|l|] v; cbn [rsv_shift rsv_ok]; rewrite ?lden_shift; tauto. Qed.

#[using="Type"] Theorem sden0_shift : forall n E P ms, sden0 segs E (sst_shift n P) ms <-> sden0 segs (vshift n E) P ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n E P ms. unfold sden0, sst_shift. cbn [s_pc s_regs s_rgs s_facts s_resv].
  rewrite regs_ok_shift, rsv_ok_shift, rgs_disj_shift, !Forall_map.
  assert (HG : Forall (fun R => rg_ok segs E (ms_mem ms) (rshift n R)) (s_rgs P) <-> Forall (rg_ok segs (vshift n E) (ms_mem ms)) (s_rgs P)).
  { split; intros H; (eapply Forall_impl; [|exact H]); intros R HR; apply rg_ok_shift; exact HR. }
  assert (HF : Forall (fun f => fact_ok E (fshift n f)) (s_facts P) <-> Forall (fact_ok (vshift n E)) (s_facts P)).
  { split; intros H; (eapply Forall_impl; [|exact H]); intros f Hf; apply fact_ok_shift; exact Hf. }
  rewrite HG, HF. tauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem sden_shift_fwd : forall n E P ms, state_wf P = true -> sden0 segs E (sst_shift n P) ms -> sden segs (vshift n E) P ms.
Proof. LiaFast.lf_pins LiaFast.u0. intros n E P ms Hw H. apply sden0_sden; [exact Hw|]. apply sden0_shift. exact H. Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem sden_shift_bwd : forall n E E1 L ms, sden segs E1 L ms -> agree (s_next L) E1 (vshift n E) ->
  sden0 segs E (sst_shift n L) ms.
Proof. LiaFast.lf_pins LiaFast.u0. intros n E E1 L ms H Ha. apply sden0_shift. exact (H _ Ha). Qed.
End WithSegs.

(* [comment removed for export] *)
Lemma lwf_shift : forall n m l, lwf m l = true -> lwf (n + m) (lshift n l) = true.
Proof.
  intros n m [c t] H. unfold lwf, lshift in *. cbn [l_t] in *. unfold tshift.
  rewrite forallb_forall in *. intros [x k] Hx. apply in_map_iff in Hx as ([y k'] & Hy & Hin). cbn [fst snd] in Hy. injection Hy as <- <-.
  specialize (H _ Hin). cbn in H. apply Pos.ltb_lt in H. apply Pos.ltb_lt. lia.
Qed.
Lemma lwf_shift_ge : forall n l, forallb (fun p => Pos.leb n (fst p)) (l_t (lshift n l)) = true.
Proof.
  intros n [c t]. unfold lshift, tshift. cbn [l_t]. rewrite forallb_forall. intros [x k] Hx.
  apply in_map_iff in Hx as ([y k'] & Hy & _). cbn [fst snd] in Hy. injection Hy as <- _. cbn [fst]. apply Pos.leb_le. lia.
Qed.
(* [comment removed for export] *)
End AcShift.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition is_bare (l : lin) : option positive :=
  match l with LIN 0 [(x, 1)] => Some x | _ => None end.
Definition bind_bare (lp ls : lin) (σ : tree lin) : tree lin :=
  match is_bare lp with
  | Some y => match tget y σ with Some _ => σ | None => tset y ls σ end
  | None => σ
  end.
Fixpoint match_regs_n (Rs RP : tree lin) (k : nat) (σ : tree lin) : tree lin :=
  match k with
  | O => σ
  | S k' => match_regs_n Rs RP k' (bind_bare (rget RP (Pos.of_succ_nat k)) (rget Rs (Pos.of_succ_nat k)) σ)
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ldivz (d : lin) (k : Z) : option lin :=
  let ok := (Z.eqb (Z.rem (sgn64 (l_c d)) k) 0 && forallb (fun '(_, c) => Z.eqb (Z.rem (sgn64 c) k) 0) (l_t d))%bool in
  if ok then Some (LIN (w64 (Z.quot (sgn64 (l_c d)) k)) (List.map (fun '(x, c) => (x, w64 (Z.quot (sgn64 c) k))) (l_t d))) else None.
Definition bind_lin (lp ls : lin) (σ : tree lin) : tree lin :=
  let unb := List.filter (fun '(x, _) => match tget x σ with Some _ => false | None => true end) (l_t lp) in
  match unb with
  | [(y, k)] =>
      let rest := LIN (l_c lp) (List.filter (fun '(x, _) => match tget x σ with Some _ => true | None => false end) (l_t lp)) in
      let d := lsub ls (lsubst σ rest) in
      if Z.eqb k 1 then tset y d σ
      else match ldivz d (sgn64 k) with Some q => if Z.eqb (sgn64 k) 0 then σ else tset y q σ | None => σ end
  | _ => σ
  end.
(* [comment removed for export] *)
Definition bind_any (lp ls : lin) (σ : tree lin) : tree lin :=
  match is_bare lp with Some _ => bind_bare lp ls σ | None => bind_lin lp ls σ end.
(* [comment removed for export] *)
Fixpoint match_rgs (rs rp : list region) (σ : tree lin) : tree lin :=
  match rs, rp with
  | R :: rs', R' :: rp' => match_rgs rs' rp' (bind_lin (rg_size R') (rg_size R) (bind_any (rg_base R') (rg_base R) σ))
  | _, _ => σ
  end.
Fixpoint match_regs_lin (Rs RP : tree lin) (k : nat) (σ : tree lin) : tree lin :=
  match k with
  | O => σ
  | S k' => match_regs_lin Rs RP k' (bind_lin (rget RP (Pos.of_succ_nat k)) (rget Rs (Pos.of_succ_nat k)) σ)
  end.
(* [comment removed for export] *)
Fixpoint bind_cont_acc (cs cp : tree bval) (k : positive -> positive) (σ : tree lin) : tree lin :=
  match cp with
  | TEmpty => σ
  | TNode l v r =>
      let σ1 := match v with
                | Some (BV lp j) => match is_bare lp, tget (k xH) cs with
                                    | Some _, Some (BV ls j') => if Z.eqb j j' then bind_bare lp ls σ else σ
                                    | _, _ => σ
                                    end
                | _ => σ
                end in
      bind_cont_acc cs r (fun p => k (xI p)) (bind_cont_acc cs l (fun p => k (xO p)) σ1)
  end.
Definition bind_cont (cs cp : tree bval) (σ : tree lin) : tree lin := bind_cont_acc cs cp (fun p => p) σ.
Fixpoint match_cont (rs rp : list region) (σ : tree lin) : tree lin :=
  match rs, rp with
  | R :: rs', R' :: rp' => match_cont rs' rp' (bind_cont (rg_cont R) (rg_cont R') σ)
  | _, _ => σ
  end.
Definition match_st (s P : sst) : tree lin :=
  let σ1 := match_cont (s_rgs s) (s_rgs P) (match_rgs (s_rgs s) (s_rgs P) (match_regs_n (s_regs s) (s_regs P) 31 TEmpty)) in
  match_regs_lin (s_regs s) (s_regs P) 31 (match_regs_lin (s_regs s) (s_regs P) 31 σ1).

(* [comment removed for export] *)
Fixpoint regs_ent_n (Rs RP : tree lin) (σ : tree lin) (k : nat) : bool :=
  match k with
  | O => true
  | S k' => (lin_eqb (rget Rs (Pos.of_succ_nat k)) (lsubst σ (rget RP (Pos.of_succ_nat k))) && regs_ent_n Rs RP σ k')%bool
  end.
Definition bval_eqb (a b : bval) : bool :=
  match a, b with BK x, BK y => Z.eqb x y | BV l j, BV l' j' => (lin_eqb l l' && Z.eqb j j')%bool | _, _ => false end.
(* [comment removed for export] *)
Definition bval_ent (a b : bval) : bool :=
  if bval_eqb a b then true else
  match a, b with
  | BK x, BV l j => match is_const l with Some c => Z.eqb (x mod 256) (Z.shiftr c (8 * j) mod 256) | None => false end
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition rkind_le (a b : rkind) : bool :=
  match a, b with RW, RW | RO, RO | RZ, RZ | RZ, RW | RI, RI | RI, RW | RT, RT => true | _, _ => false end.
(* [comment removed for export] *)
Definition rz_extra_ok (Rs RP : region) : bool :=
  match rg_kind RP with
  | RZ => tforall2 (fun v ov => match ov with Some _ => true | None => bval_eqb v (BK 0) end) (rg_cont Rs) (rg_cont RP)
  | RI => tforall2 (fun v ov => match ov with Some _ => true | None => false end) (rg_cont Rs) (rg_cont RP)
  | _ => true
  end.
(* [comment removed for export] *)
Definition rz_cell_ok (Rs : region) (p : positive) (v : bval) : bool :=
  match rg_kind Rs, is_const (rg_size Rs) with
  | RZ, Some z => (bval_eqb v (BK 0) && Z.ltb (Zpos p - 1) z)%bool
  | _, _ => false
  end.
(* [comment removed for export] *)
Fixpoint id_on (σ : tree lin) (t : list (positive * Z)) : bool :=
  match t with
  | [] => true
  | (x, _) :: t' => match tget x σ with
                    | None => id_on σ t'
                    | Some l' => if lin_eqb l' (lvar x) then id_on σ t' else false
                    end
  end.
Definition cell_ent (σ : tree lin) (v' v : bval) : bool :=
  match v with
  | BV l _ => if id_on σ (l_t l) then (if bval_eqb v' v then true else bval_ent v' (bsubst σ v)) else bval_ent v' (bsubst σ v)
  | BK _ => bval_ent v' (bsubst σ v)
  end.
Definition cells_ent (Rs RP : region) (σ : tree lin) : bool :=
  if tforall2 (fun v ov => match ov with Some v' => cell_ent σ v' v | None => false end) (rg_cont RP) (rg_cont Rs) then true
  else tforall (fun p v => match tget p (rg_cont Rs) with Some v' => cell_ent σ v' v | None => rz_cell_ok Rs p v end) (rg_cont RP).
Definition rg_ent (Rs RP : region) (σ : tree lin) : bool :=
  (lin_eqb (rg_base Rs) (lsubst σ (rg_base RP)) && lin_eqb (rg_size Rs) (lsubst σ (rg_size RP)) && rkind_le (rg_kind Rs) (rg_kind RP) &&
   cells_ent Rs RP σ &&
   rz_extra_ok Rs RP)%bool.
Fixpoint rgs_ent (rs rp : list region) (σ : tree lin) : bool :=
  match rs, rp with
  | [], [] => true
  | R :: rs', R' :: rp' => (rg_ent R R' σ && rgs_ent rs' rp' σ)%bool
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition fact_implied (fs : list fact) (f : fact) : bool :=
  if existsb (fact_eqb f) fs then true else
  match f with
  | FCond c a b tk => match ev_br fs c a b with Some tk' => Bool.eqb tk tk' | None => false end
  | FRange l lo hi => if (let '(lo', hi') := irange fs l in (Z.leb lo lo' && Z.leb hi' hi)%bool) then true else
                      (let '(lo', hi') := irange_x fs l in (Z.leb lo lo' && Z.leb hi' hi)%bool)
  | FMod l k r => match lowb fs l k with
                  | Some r' => Z.eqb r r'
                  | None => (Z.eqb r 0 && Z.leb 0 k && Z.leb k (lalign fs l))%bool
                  end
  | FBits l m v => let t := tn_of fs l in (Z.eqb (Z.land (fst t) m) m && Z.eqb (Z.land (snd t) m) v)%bool
  | FByte x v j => existsb (fun g => match g with FByte x' v' j' => (lin_eqb x x' && lin_eqb v v' && Z.eqb j j')%bool | _ => false end) fs
  | FBytes _ _ => false
  end%bool.
Definition facts_ent (fs fp : list fact) (σ : tree lin) : bool := forallb (fun f => fact_implied fs (fsubst σ f)) fp.
Definition rsv_ent (rs rp : rsv) (σ : tree lin) : bool :=
  match rp, rs with
  | RUnk, _ => true
  | RNone, RNone => true
  | RAt l, RAt l' => lin_eqb l' (lsubst σ l)
  | _, _ => false
  end.
Definition entails (s P : sst) (σ : tree lin) : bool :=
  (Z.eqb (s_pc s) (s_pc P) && regs_ent_n (s_regs s) (s_regs P) σ 31 && rgs_ent (s_rgs s) (s_rgs P) σ &&
   facts_ent (s_facts s) (s_facts P) σ && rsv_ent (s_resv s) (s_resv P) σ)%bool.

(* [comment removed for export] *)
Lemma regs_ent_n_spec : forall Rs RP σ k, regs_ent_n Rs RP σ k = true -> forall i, (1 <= i <= k)%nat ->
  rget Rs (Pos.of_succ_nat i) = lsubst σ (rget RP (Pos.of_succ_nat i)).
Proof.
  intros Rs RP σ k. induction k as [|k IH]; intros H i Hi; [lia|].
  cbn [regs_ent_n] in H. apply andb_prop in H as [H1 H2]. destruct (Nat.eq_dec i (S k)) as [->|Hne].
  - apply lin_eqb_eq. exact H1.
  - apply IH; [exact H2 | lia].
Qed.

Lemma regs_ent_ok : forall E Rs RP σ regs, regs_ok E Rs regs -> regs_ent_n Rs RP σ 31 = true -> regs_ok (ecomp E σ) RP regs.
Proof.
  intros E Rs RP σ regs HR H r. rewrite (HR r). destruct (decide (r = 0%bv)) as [->|Hr0]; [reflexivity|].
  destruct (rkey_succ r Hr0) as (k & Hk & Ek). rewrite Ek. rewrite (regs_ent_n_spec _ _ _ _ H k Hk). apply lden_lsubst.
Qed.

Lemma bval_eqb_eq : forall a b, bval_eqb a b = true -> a = b.
Proof.
  intros [x|l j] [y|l' j'] H; cbn in H; try discriminate.
  - apply Z.eqb_eq in H. subst. reflexivity.
  - apply andb_prop in H as [H1 H2]. apply lin_eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.
Lemma bval_ent_den : forall E a b, bval_ent a b = true -> bden E a = bden E b.
Proof.
  intros E a b H. unfold bval_ent in H. destruct (bval_eqb a b) eqn:He; [rewrite (bval_eqb_eq _ _ He); reflexivity|].
  destruct a as [x|la ja]; [|discriminate]. destruct b as [y|l j]; [discriminate|]. destruct (is_const l) as [c|] eqn:Hc; [|discriminate].
  apply Z.eqb_eq in H. destruct (is_const_sound E l c Hc) as [Hl Hr]. cbn [bden]. rewrite Hl.
  rewrite Z_to_bv_unsigned. unfold bv_wrap at 1, bv_modulus. change (2 ^ Z.of_N 64) with two64. rewrite (Z.mod_small c) by exact Hr.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. exact H.
Qed.
Lemma id_on_tsum : forall E σ t, id_on σ t = true -> tsum (ecomp E σ) t = tsum E t.
Proof.
  intros E σ t. induction t as [|[x k] t IH]; cbn [id_on tsum]; intros H; [reflexivity|].
  assert (Hx : ecomp E σ x = E x /\ id_on σ t = true).
  { unfold ecomp, svar. destruct (tget x σ) as [l'|]; [|split; [apply lden_lvar | exact H]].
    destruct (lin_eqb l' (lvar x)) eqn:El; [|discriminate]. apply lin_eqb_eq in El. subst l'. split; [apply lden_lvar | exact H]. }
  destruct Hx as [Hx Ht]. unfold vz. rewrite Hx, (IH Ht). reflexivity.
Qed.
Lemma cell_ent_den : forall E σ v' v, cell_ent σ v' v = true -> bden E v' = bden E (bsubst σ v).
Proof.
  intros E σ v' v H. destruct v as [b|l j]; cbn [cell_ent] in H; [exact (bval_ent_den E _ _ H)|].
  destruct (id_on σ (l_t l)) eqn:Hid; [|exact (bval_ent_den E _ _ H)].
  destruct (bval_eqb v' (BV l j)) eqn:Hb; [|exact (bval_ent_den E _ _ H)].
  apply bval_eqb_eq in Hb. subst v'. rewrite bden_bsubst. cbn [bden].
  assert (Hl : lden (ecomp E σ) l = lden E l) by (unfold lden, lz; rewrite (id_on_tsum E σ (l_t l) Hid); reflexivity).
  rewrite Hl. reflexivity.
Qed.

Lemma rg_ent_parts : forall Rs RP σ, rg_ent Rs RP σ = true ->
  rg_base Rs = lsubst σ (rg_base RP) /\ rg_size Rs = lsubst σ (rg_size RP) /\ rkind_le (rg_kind Rs) (rg_kind RP) = true /\
  (forall p v, tget p (rg_cont RP) = Some v ->
     (exists v', tget p (rg_cont Rs) = Some v' /\ forall E, bden E v' = bden E (bsubst σ v)) \/
     (tget p (rg_cont Rs) = None /\ rz_cell_ok Rs p v = true)) /\
  rz_extra_ok Rs RP = true.
Proof.
  intros Rs RP σ H. unfold rg_ent in H.
  apply andb_prop in H as [H Hz]. apply andb_prop in H as [H Hc]. apply andb_prop in H as [H Hk]. apply andb_prop in H as [Hb Hs].
  split; [apply lin_eqb_eq; exact Hb|]. split; [apply lin_eqb_eq; exact Hs|]. split; [exact Hk|]. split; [|exact Hz].
  intros p v Hp. unfold cells_ent in Hc.
  destruct (tforall2 (fun v ov => match ov with Some v' => cell_ent σ v' v | None => false end) (rg_cont RP) (rg_cont Rs)) eqn:Hf.
  - pose proof (tforall2_spec _ _ _ Hf p v Hp) as Hv. cbn beta in Hv.
    destruct (tget p (rg_cont Rs)) as [v'|]; [|discriminate]. left. exists v'. split; [reflexivity|]. intros E. exact (cell_ent_den E _ _ _ Hv).
  - pose proof (tforall_spec _ _ Hc p v Hp) as Hv. cbn beta in Hv.
    destruct (tget p (rg_cont Rs)) as [v'|].
    + left. exists v'. split; [reflexivity|]. intros E. exact (cell_ent_den E _ _ _ Hv).
    + right. split; [reflexivity | exact Hv].
Qed.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma rg_ent_ok : forall E m Rs RP σ, rg_ok segs E m Rs -> rg_ent Rs RP σ = true -> rg_ok segs (ecomp E σ) m RP.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m Rs RP σ HR H. destruct (rg_ent_parts _ _ _ H) as (Hb & Hs & Hk & Hc & Hz).
  unfold rg_ok, rsz in *. rewrite <- !lden_lsubst, <- Hb, <- Hs. destruct HR as (H1 & H2 & H3 & H4).
  split; [exact H1|]. split; [exact H2|]. split.
  - intros i Hi. specialize (H3 i Hi). unfold rz_extra_ok in Hz.
    destruct (rg_kind Rs) eqn:Hks; destruct (rg_kind RP) eqn:Hkp; cbn in Hk; try discriminate; try exact H3.
    + exact (proj1 H3).
    + split; [exact (proj1 H3)|]. intros Hnt.
      destruct (tget (okey i) (rg_cont Rs)) as [v|] eqn:Ht.
      * pose proof (tforall2_spec _ _ _ Hz _ _ Ht) as Hv. cbn beta in Hv. rewrite Hnt in Hv. apply bval_eqb_eq in Hv. subst v.
        pose proof (Pos2Z.is_pos (okey i)). destruct (H4 _ _ Ht) as [_ Hrd].
        rewrite okey_pos in Hrd by lia. exact Hrd.
      * exact (proj2 H3 eq_refl).
    + exact (proj1 H3).
    + split; [exact (proj1 H3)|]. intros Hnt.
      destruct (tget (okey i) (rg_cont Rs)) as [v|] eqn:Ht.
      * pose proof (tforall2_spec _ _ _ Hz _ _ Ht) as Hv. cbn beta in Hv. rewrite Hnt in Hv. discriminate.
      * exact (proj2 H3 eq_refl).
  - intros p v Hp. destruct (Hc p v Hp) as [(v' & Hv' & Hbd) | [Hnone Hzc]].
    + destruct (H4 p v' Hv') as [Hp1 Hp2]. split; [exact Hp1|].
      rewrite <- bden_bsubst, <- Hbd. exact Hp2.
    + (* [comment removed for export] *)
      unfold rz_cell_ok in Hzc. destruct (rg_kind Rs) eqn:Hks; try discriminate.
      destruct (is_const (rg_size Rs)) as [z|] eqn:Hcz; [|discriminate].
      apply andb_prop in Hzc as [Hv0 Hlt]. apply bval_eqb_eq in Hv0. subst v. apply Z.ltb_lt in Hlt.
      destruct (is_const_sound E _ z Hcz) as [Hden Hr].
      assert (Hsz : bv_unsigned (lden E (rg_size Rs)) = z) by (rewrite Hden; apply u_small64; lia).
      pose proof (Pos2Z.is_pos p) as Hpp.
      split; [rewrite Hsz; exact Hlt|].
      assert (Hi : 0 <= Zpos p - 1 < bv_unsigned (lden E (rg_size Rs))) by (rewrite Hsz; lia).
      specialize (H3 (Zpos p - 1) Hi). cbn beta iota in H3. destruct H3 as [_ H3z].
      assert (Hok : okey (Zpos p - 1) = p) by (unfold okey; replace (Zpos p - 1 + 1) with (Zpos p) by lia; reflexivity).
      rewrite Hok in H3z. rewrite (H3z Hnone). reflexivity.
Qed.

#[using="Type"] Lemma rgs_ent_ok : forall E m rs rp σ, Forall (rg_ok segs E m) rs -> rgs_ent rs rp σ = true -> Forall (rg_ok segs (ecomp E σ) m) rp.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m rs. induction rs as [|R rs IH]; intros [|R' rp] σ HF H; cbn [rgs_ent] in H; try discriminate; [constructor|].
  apply andb_prop in H as [H1 H2]. inversion HF as [|? ? HR HF']; subst.
  constructor; [exact (rg_ent_ok _ _ _ _ _ HR H1) | exact (IH rp σ HF' H2)].
Qed.

#[using="Type"] Lemma rgs_ent_in : forall rs rp σ R', rgs_ent rs rp σ = true -> In R' rp -> exists R, In R rs /\ rg_ent R R' σ = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction rs as [|R rs IH]; intros [|R0 rp] σ R' H Hin; cbn [rgs_ent] in H; try discriminate; [destruct Hin|].
  apply andb_prop in H as [H1 H2]. destruct Hin as [->|Hin].
  - exists R. split; [left; reflexivity | exact H1].
  - destruct (IH rp σ R' H2 Hin) as (Rx & HRx & Hx). exists Rx. split; [right; exact HRx | exact Hx].
Qed.

#[using="Type"] Lemma rgs_ent_disj : forall E rs rp σ, rgs_disj E rs -> rgs_ent rs rp σ = true -> rgs_disj (ecomp E σ) rp.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E rs. induction rs as [|R rs IH]; intros [|R' rp] σ Hd H; cbn [rgs_ent] in H; try discriminate; [exact I|].
  apply andb_prop in H as [H1 H2]. destruct Hd as [Hx Hrs]. split; [|exact (IH rp σ Hrs H2)].
  apply Forall_forall. intros R'' HR''. destruct (rgs_ent_in rs rp σ R'' H2 HR'') as (Rx & HRx & HRxe).
  rewrite Forall_forall in Hx. pose proof (Hx Rx HRx) as Hdx.
  destruct (rg_ent_parts _ _ _ H1) as (Hb1 & Hs1 & _ & _ & _). destruct (rg_ent_parts _ _ _ HRxe) as (Hb2 & Hs2 & _ & _ & _).
  unfold rg_disj, rsz in *. rewrite <- !lden_lsubst, <- Hb1, <- Hb2, <- Hs1, <- Hs2. exact Hdx.
Qed.

#[using="Type"] Lemma bc_eqb_eq : forall a b, bc_eqb a b = true -> a = b.
Proof. LiaFast.lf_pins LiaFast.u0. intros [] [] H; cbn in H; try discriminate; reflexivity. Qed.
#[using="Type"] Lemma lzs_eqb_eq : forall a b, lzs_eqb a b = true -> a = b.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction a as [|[x j] a IH]; intros [|[y k] b] H; cbn [lzs_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply lin_eqb_eq in H1. apply Z.eqb_eq in H2. subst. f_equal. exact (IH b H3).
Qed.
#[using="Type"] Lemma fact_eqb_eq : forall f g, fact_eqb f g = true -> f = g.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros [c a b tk|l lo hi|l k r|l m v|x v j|x bs] [c' a' b' tk'|l' lo' hi'|l' k' r'|l' m' v'|x' v' j'|x' bs'] H; cbn [fact_eqb] in H; try discriminate.
  6: { apply andb_prop in H as [H1 H2]. apply lin_eqb_eq in H1. apply lzs_eqb_eq in H2. subst. reflexivity. }
  - apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply bc_eqb_eq in H1. apply lin_eqb_eq in H2, H3. apply Bool.eqb_prop in H4. subst. reflexivity.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply lin_eqb_eq in H1. apply Z.eqb_eq in H2, H3. subst. reflexivity.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply lin_eqb_eq in H1. apply Z.eqb_eq in H2, H3. subst. reflexivity.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply lin_eqb_eq in H1. apply Z.eqb_eq in H2, H3. subst. reflexivity.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply lin_eqb_eq in H1, H2. apply Z.eqb_eq in H3. subst. reflexivity.
Qed.
#[using="Type"] Lemma fact_implied_ok : forall E fs f, Forall (fact_ok E) fs -> fact_implied fs f = true -> fact_ok E f.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs f HF H. unfold fact_implied in H. destruct (existsb (fact_eqb f) fs) eqn:Hex.
  { apply existsb_exists in Hex as (g & Hg & Heq). apply fact_eqb_eq in Heq. subst g. rewrite Forall_forall in HF. exact (HF _ Hg). }
  revert H. destruct f as [c a b tk|l lo hi|l k r|l m v|x v j|x bs]; intros H; cbn [fact_ok] in *.
  - destruct (ev_br fs c a b) as [tk'|] eqn:Hb; [|discriminate]. apply Bool.eqb_prop in H. subst tk'.
    exact (ev_br_sound E fs c a b tk HF Hb).
  - pose proof (irange_sound E fs l HF) as Hr. destruct (irange fs l) as [lo' hi'] eqn:Hir. cbn [fst snd] in Hr.
    destruct (Z.leb lo lo' && Z.leb hi' hi)%bool eqn:H0.
    + apply andb_prop in H0 as [H1 H2]. apply Z.leb_le in H1, H2. lia.
    + pose proof (irange_x_sound E fs l HF) as Hx. destruct (irange_x fs l) as [lo2 hi2]. cbn [fst snd] in Hx.
      apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. lia.
  - destruct (lowb fs l k) as [r'|] eqn:Hlb.
    + apply Z.eqb_eq in H. subst r'. exact (lowb_sound E fs l k r HF Hlb).
    + apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1]. apply Z.eqb_eq in H0. subst r.
      apply Z.leb_le in H1, H2. destruct (lalign_sound E fs l HF) as [Hb Hd].
      apply Z.mod_divide; [apply Z.pow_nonzero; lia|]. apply Z.divide_trans with (2 ^ lalign fs l); [apply pow2_divide_le; lia | exact Hd].
  - apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1, H2. pose proof (tn_of_ok E fs l HF) as Ht. unfold tn_ok in Ht.
    rewrite <- H1, Z.land_assoc, Ht, H2. reflexivity.
  - apply existsb_exists in H as (g & Hg & Heq). destruct g as [c a b tk|l lo hi|l k r|l m v'|x' v' j'|x' bs']; try discriminate.
    apply andb_prop in Heq as [Heq Hj]. apply andb_prop in Heq as [Hx Hv]. apply lin_eqb_eq in Hx, Hv. apply Z.eqb_eq in Hj. subst.
    rewrite Forall_forall in HF. exact (HF _ Hg).
  - discriminate.
Qed.

#[using="Type"] Lemma facts_ent_ok : forall E fs fp σ, Forall (fact_ok E) fs -> facts_ent fs fp σ = true -> Forall (fact_ok (ecomp E σ)) fp.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs fp σ HF H. apply Forall_forall. intros f Hf. unfold facts_ent in H. rewrite forallb_forall in H.
  apply fact_ok_fsubst. apply (fact_implied_ok E fs); [exact HF | exact (H f Hf)].
Qed.

#[using="Type"] Theorem entails_sound0 : forall E s P σ ms, sden0 segs E s ms -> entails s P σ = true -> sden0 segs (ecomp E σ) P ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E s P σ ms (Hpc & Hsvc & Hresv & HR & HG & HD & HF & Hfrm) H. unfold entails in H.
  apply andb_prop in H as [H Hv]. apply andb_prop in H as [H Hf]. apply andb_prop in H as [H Hg]. apply andb_prop in H as [Hp Hr].
  apply Z.eqb_eq in Hp.
  split; [rewrite Hpc, Hp; reflexivity|]. split; [exact Hsvc|].
  split; [unfold rsv_ent in Hv; destruct (s_resv P) as [|l|]; destruct (s_resv s) as [|l'|]; cbn [rsv_ok] in *; try discriminate; try exact I;
          [exact Hresv | apply lin_eqb_eq in Hv; rewrite Hresv, Hv, lden_lsubst; reflexivity]|].
  split; [exact (regs_ent_ok _ _ _ _ _ HR Hr)|]. split; [exact (rgs_ent_ok _ _ _ _ _ HG Hg)|].
  split; [exact (rgs_ent_disj _ _ _ _ HD Hg)|]. split; [exact (facts_ent_ok _ _ _ _ HF Hf) | exact Hfrm].
Qed.

#[using="Type"] Theorem entails_sden : forall E s P σ ms, sden0 segs E s ms -> entails s P σ = true -> state_wf P = true ->
  sden segs (ecomp E σ) P ms.
Proof. LiaFast.lf_pins LiaFast.u0. intros E s P σ ms H He Hw. apply sden0_sden; [exact Hw | exact (entails_sound0 E s P σ ms H He)]. Qed.

End WithSegs.
