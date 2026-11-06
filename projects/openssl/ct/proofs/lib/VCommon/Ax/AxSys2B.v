(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxAcct.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import FastWord FastWordSem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxBytes AxMem AxZZ AxState AxSys AxGrant.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxModelRel AxMRFix.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lin_al (k : Z) (f : lin) : bool := (fst f mod k =? 0) &&& lforall (fun p => snd p mod k =? 0) (snd f).

Lemma lin_al_sound (ρ : valuation) (k : Z) (f : lin) : 0 < k -> lin_al k f = true -> leval ρ f mod k = 0.
Proof.
  intros Hk H. unfold lin_al in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1.
  pose proof (lforall_forall _ _ H2) as H3. cbv beta in H3. clear H2. destruct f as [c ts]. unfold leval. cbn [fst snd] in *.
  assert (Ht : teval ρ ts mod k = 0).
  { induction ts as [|[x q] r IH]; [apply Z.mod_0_l; lia|]. cbn [teval fst snd].
    pose proof (H3 (x, q) (or_introl eq_refl)) as Hq. cbn [snd] in Hq. apply Z.eqb_eq in Hq.
    specialize (IH (fun p Hp => H3 p (or_intror Hp))).
    rewrite Z.add_mod, IH, Z.add_0_r, Z.mod_mod by lia. rewrite <- Z.mul_mod_idemp_l, Hq by lia. apply Z.mod_0_l. lia. }
  rewrite Z.add_mod, H1, Ht by lia. apply Z.mod_0_l. lia.
Qed.

Lemma lin_al_tdiv8 (f : lin) : lin_al 4096 f = true -> tdiv8_ok (snd f) = true.
Proof.
  intros H. unfold lin_al in H. apply andb_prop in H as [_ H2]. pose proof (lforall_forall _ _ H2) as H3. cbv beta in H3.
  unfold tdiv8_ok. apply lforall_intro. intros p Hp. specialize (H3 p Hp). apply Z.eqb_eq in H3. apply Z.eqb_eq.
  pose proof (Z.div_mod (snd p) 4096 ltac:(lia)) as D. rewrite H3 in D. rewrite D, Z.add_0_r.
  replace (4096 * (snd p / 4096)) with ((512 * (snd p / 4096)) * 8) by lia. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Definition ent_has (s : store) (f : lin) (n : Z) (e : aent) : bool :=
  match lrange s (lsub f (ae_base e)) with
  | Some (lo, hi) => (0 <=? lo) &&& (hi + n <=? ae_size e)
  | None => false
  end.

Lemma ent_has_sound (ρ : valuation) (s : store) (f : lin) (n : Z) (e : aent) :
  sat ρ s -> ent_has s f n e = true ->
  leval ρ (ae_base e) <= leval ρ f /\ leval ρ f + n <= leval ρ (ae_base e) + ae_size e.
Proof.
  intros Hs H. unfold ent_has in H. destruct (lrange s (lsub f (ae_base e))) as [[lo hi]|] eqn:E; [|discriminate H].
  pose proof (lrange_sound ρ s _ Hs _ E) as Hr. cbn [fst snd] in Hr. rewrite leval_lsub in Hr.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Fixpoint find_ent (s : store) (f : lin) (n : Z) (l : list aent) : option aent :=
  match l with
  | [] => None
  | e :: r => if ent_has s f n e then Some e else find_ent s f n r
  end.

Lemma find_ent_spec (s : store) (f : lin) (n : Z) (l : list aent) (e : aent) :
  find_ent s f n l = Some e -> In e l /\ ent_has s f n e = true.
Proof.
  induction l as [|x r IH]; cbn [find_ent]; [discriminate|]. destruct (ent_has s f n x) eqn:E.
  - intros H. injection H as <-. split; [left; reflexivity | exact E].
  - intros H. destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.

(* [comment removed for export] *)
Definition exp_miss (s : store) (f : lin) (n : Z) (e0 : aent) (x : aent * lin * Z) : bool :=
  if aent_eqb (fst (fst x)) e0 then
    match lrange s (lsub f (snd (fst x))) with
    | Some (lo, hi) => (hi + n <=? 0) ||| (snd x <=? lo)
    | None => false
    end
  else true.

Lemma exp_miss_sound (ρ : valuation) (s : store) (f : lin) (n : Z) (e0 : aent) (exps : list (aent * lin * Z)) (z : Z) :
  sat ρ s -> lforall (exp_miss s f n e0) exps = true -> leval ρ f <= z < leval ρ f + n -> ~ in_exp ρ exps e0 z.
Proof.
  intros Hs H Hz [x [Hx [He Hr]]]. pose proof (lforall_forall _ _ H x Hx) as Hm. unfold exp_miss in Hm.
  rewrite He, aent_eqb_refl in Hm. destruct (lrange s (lsub f (snd (fst x)))) as [[lo hi]|] eqn:E; [|discriminate Hm].
  pose proof (lrange_sound ρ s _ Hs _ E) as Hl. cbn [fst snd] in Hl. rewrite leval_lsub in Hl.
  apply orb_prop in Hm as [Hm|Hm]; apply Z.leb_le in Hm; lia.
Qed.

(* [comment removed for export] *)
Definition no_exp (e0 : aent) (exps : list (aent * lin * Z)) : bool := lforall (fun x => negb (aent_eqb (fst (fst x)) e0)) exps.

Lemma no_exp_sound (e0 : aent) (exps : list (aent * lin * Z)) : no_exp e0 exps = true -> forall x, In x exps -> fst (fst x) <> e0.
Proof.
  intros H x Hx E. pose proof (lforall_forall _ _ H x Hx) as Hn. cbv beta in Hn. rewrite E, aent_eqb_refl in Hn. discriminate Hn.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ss_wit (s : store) (A : list region) : bool := has_wit s ls_beg ls_end A &&& has_wit s hs_beg hs_hi A.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fix_shape (A : AST) (prot : Z) : option (Z * bool) :=
  let r := a_regs A in
  match xlit (aget r 11%uint63), xlit (aget r 12%uint63), xlit (aget r 13%uint63), xlit (aget r 15%uint63) with
  | Some len, Some p, Some flags, Some off =>
      if (0 <? len) &&& (len <? 70368744177664) &&& (off =? 0) &&& (p =? prot) &&& ((flags =? 50) ||| (flags =? 16434))
      then Some (page_round_up_Z len, flags =? 16434) else None
  | _, _, _, _ => None
  end.

(* [comment removed for export] *)
Definition len_shape (A : AST) : option Z :=
  match xlit (aget (a_regs A) 11%uint63) with
  | Some len => if (0 <? len) &&& (len <? 70368744177664) then Some (page_round_up_Z len) else None
  | None => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition expose_ok (A : AST) (f : lin) (nZ : Z) (e0 : aent) : bool :=
  let am := a_model A in
  let s := a_facts A in
  ae_na e0 &&& var_ent e0 &&& am_shadow am &&& lin_al 4096 f &&& (0 <=? fst f) &&& (fst f <? 9223372036854775808)
  &&& eb_above s (am_atop am) (a_mem A) &&& ss_wit s (a_mem A) &&& lforall (fun R => (0 <? to_Z (rg_n R))) (a_mem A).

(* [comment removed for export] *)
Definition expose_next (A : AST) (regs : aregs) (f : lin) (nZ : Z) (e0 : aent) (budget : Z) : AST :=
  with_model A (npc A) regs
    (zero_rg (snd f) (wofZ (fst f)) nZ :: comp_rg (snd f) (wofZ (fst f)) nZ :: a_mem A)
    (a_facts A) (add_exp (a_model A) e0 f nZ) budget.

Definition sys_fix_rw (LIM : Z) (A : AST) : option (list AST) :=
  let am := a_model A in
  let s := a_facts A in
  match fix_shape A 3, xform s (aget (a_regs A) 10%uint63) with
  | Some (nZ, lz), Some f =>
      match find_ent s f nZ (am_maps am) with
      | Some e0 =>
          if expose_ok A f nZ e0 &&& lforall (exp_miss s f nZ e0) (am_exp am) &&& (a_budget A + (if lz then 0 else nZ) <=? LIM)
             &&& (negb lz ||| (65536 <=? ae_size e0))      (* [comment removed for export] *)
          then Some [expose_next A (aset (a_regs A) reg_a0 (aget (a_regs A) reg_a0)) f nZ e0 (a_budget A + (if lz then 0 else nZ))]
          else None
      | None => None
      end
  | _, _ => None
  end.

Definition sys_mprotect2 (LIM : Z) (A : AST) : option (list AST) :=
  let am := a_model A in
  let s := a_facts A in
  match len_shape A, xlit (aget (a_regs A) 12%uint63), xform s (aget (a_regs A) 10%uint63) with
  | Some nZ, Some 3, Some f =>
      match find_ent s f nZ (am_maps am) with
      | Some e0 =>
          if expose_ok A f nZ e0 &&& no_exp e0 (am_exp am) &&& (a_budget A + nZ <=? LIM)
          then Some [expose_next A (aset (a_regs A) reg_a0 (XL w_zero)) f nZ e0 (a_budget A + nZ)]
          else None
      | None => None
      end
  | _, _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sh_region (s : store) (f : lin) (n : Z) (R : region) : option region :=
  if negb (is_shadow R) then Some R else
  if is_empty (rg_cells R) then Some R else
  match lrange s (lsub (wS (rg_bo R), rg_ts R) f) with
  | Some (lo, hi) =>
      if negb ((- 4611686018427387904 <? lo) &&& (hi <? 4611686018427387904)) then None else
      if (hi + to_Z (rg_n R) <=? 0) ||| (n <=? lo) then Some R                      (* [comment removed for export] *)
      else if (0 <=? lo) &&& (hi + to_Z (rg_n R) <=? n) then Some (with_cells R IEmpty)  (* [comment removed for export] *)
      else None
  | None => None
  end.

Fixpoint sh_regions (s : store) (f : lin) (n : Z) (A : list region) : option (list region) :=
  match A with
  | [] => Some []
  | R :: A' => match sh_region s f n R, sh_regions s f n A' with Some R', Some l => Some (R' :: l) | _, _ => None end
  end.

(* [comment removed for export] *)
Definition in_shadow (s : store) (f : lin) (n : Z) : bool :=
  match lrange s f with
  | Some (lo, hi) => ((ls_beg <=? lo) &&& (hi + n <=? ls_end)) ||| ((hs_beg <=? lo) &&& (hi + n <=? hs_hi))
  | None => false
  end.

Definition sys_fix_sh (LIM : Z) (A : AST) : option (list AST) :=
  let am := a_model A in
  let s := a_facts A in
  match fix_shape A 3, xform s (aget (a_regs A) 10%uint63) with
  | Some (nZ, lz), Some f =>
      match find_ent s f nZ (am_maps am) with
      | Some e0 =>
          if negb (ae_na e0) &&& am_shadow am &&& lin_al 4096 f &&& in_shadow s f nZ &&& ss_wit s (a_mem A)
             &&& (a_budget A + (if lz then 0 else nZ) <=? LIM)
             &&& (negb lz ||| (65536 <=? ae_size e0)) &&& (negb (AxLz.lzfull e0) ||| lz)   (* [comment removed for export] *)
          then match sh_regions s f nZ (a_mem A) with
               | Some mem' => Some [with_model A (npc A) (aset (a_regs A) reg_a0 (aget (a_regs A) reg_a0)) mem' s am
                                      (a_budget A + (if lz then 0 else nZ))]
               | None => None
               end
          else None
      | None => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rg_at (ts : terms) (o : w64) (k : rkind) (R : region) : bool :=
  teqb (rg_ts R) ts &&& w_eqb (rg_bo R) o &&& is_empty (rg_cells R) &&&
  match rg_kind R, k with KZero, KZero => true | KShadow, KShadow => true | _, _ => false end.

Fixpoint find_at (ts : terms) (o : w64) (k : rkind) (A : list region) (j : nat) : option (nat * region) :=
  match A with
  | [] => None
  | R :: A' => if rg_at ts o k R then Some (j, R) else find_at ts o k A' (S j)
  end.

Definition sys_fix_none (A : AST) : option (list AST) :=
  let am := a_model A in
  let s := a_facts A in
  match fix_shape A 0, xform s (aget (a_regs A) 10%uint63) with
  | Some (nZ, lz), Some f =>
      match find_ent s f nZ (am_maps am) with
      | Some e0 =>
          let ts := snd f in
          let o := wofZ (fst f) in
          match find_at ts o KZero (a_mem A) 0, find_at (tdiv8 ts) (wofZ (wS o / 8 + sh_off)) KShadow (a_mem A) 0 with
          | Some (i, R), Some (j, C) =>
              let nR := to_Z (rg_n R) in
              if negb (ae_na e0) &&& lin_al 4096 f &&& eb_above s (am_atop am) (a_mem A)
                 &&& (nZ <? nR) &&& (nR <? 140737488355328) &&& (nR mod 8 =? 0)
                 &&& (to_Z (rg_n C) =? nR / 8) &&& (0 <=? fst f) &&& (fst f + nR <? 9223372036854775808)
                 &&& lforall (fun R => (0 <? to_Z (rg_n R))) (a_mem A)
                 &&& (negb lz ||| (65536 <=? ae_size e0)) &&& negb (AxLz.lzfull e0)       (* [comment removed for export] *)
              then
                let o' := wofZ (fst f + nZ) in
                let mem' := replace_nth (replace_nth (a_mem A) i (zero_rg ts o' (nR - nZ))) j (comp_rg ts o' (nR - nZ)) in
                Some [with_model A (npc A) (aset (a_regs A) reg_a0 (aget (a_regs A) reg_a0)) mem' s am (a_budget A)]
              else None
          | _, _ => None
          end
      | None => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint find_exact (f : lin) (n : Z) (l : list aent) : option aent :=
  match l with
  | [] => None
  | e :: r => if lin_eqb (ae_base e) f &&& (ae_size e =? n) then Some e else find_exact f n r
  end.

Lemma find_exact_spec (f : lin) (n : Z) (l : list aent) (e : aent) :
  find_exact f n l = Some e -> In e l /\ ae_base e = f /\ ae_size e = n.
Proof.
  induction l as [|x r IH]; cbn [find_exact]; [discriminate|]. destruct (lin_eqb (ae_base x) f &&& (ae_size x =? n)) eqn:E.
  - intros H. injection H as <-. apply andb_prop in E as [E1 E2]. apply lin_eqb_eq in E1. apply Z.eqb_eq in E2.
    split; [left; reflexivity | split; assumption].
  - intros H. destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.

(* [comment removed for export] *)
Definition rg_is (ts : terms) (o : w64) (n : Z) (R : region) : bool :=
  teqb (rg_ts R) ts &&& w_eqb (rg_bo R) o &&& (to_Z (rg_n R) =? n) &&&
  match rg_kind R with KZero | KUnk => true | _ => false end.

(* [comment removed for export] *)
Definition cp_is (ts : terms) (o : w64) (n : Z) (C : region) : bool := rg_at ts o KShadow C &&& (to_Z (rg_n C) =? n).

Definition sys_munmap2 (A : AST) : option (list AST) :=
  let am := a_model A in
  let s := a_facts A in
  match len_shape A, xform s (aget (a_regs A) 10%uint63) with
  | Some nZ, Some f =>
      match find_exact f nZ (am_maps am) with
      | Some e0 =>
          if var_ent e0 &&& am_shadow am &&& lin_al 4096 f &&& eb_above s (am_atop am) (a_mem A) then
            if ae_na e0 then
              if no_exp e0 (am_exp am)
              then Some [with_model A (npc A) (aset (a_regs A) reg_a0 (XL w_zero)) (a_mem A) s (del_ent am e0) (a_budget A)]
              else None
            else
              let ts := snd f in
              let o := wofZ (fst f) in
              let isR := rg_is ts o nZ in
              let isC := cp_is (tdiv8 ts) (wofZ (wS o / 8 + sh_off)) (nZ / 8) in
              if (0 <=? fst f) &&& (fst f + nZ <? 9223372036854775808) &&& lexists isR (a_mem A) &&& lexists isC (a_mem A)
              then Some [with_model A (npc A) (aset (a_regs A) reg_a0 (XL w_zero))
                           (List.filter (fun X => negb (isR X) &&& negb (isC X)) (a_mem A)) s (del_ent am e0) (a_budget A)]
              else None
          else None
      | None => None
      end
  | _, _ => None
  end.
