(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import AX2. Import AX2S.

Module SSR.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition t63 : Z := 2 ^ 63.
Definition t64 : Z := 2 ^ 64.
Definition t31 : Z := 2 ^ 31.

(* [comment removed for export] *)
Definition in64 (lo hi : Z) : bool := if Z.leb (- t63) lo then Z.ltb hi t63 else false.
(* [comment removed for export] *)
Definition in32 (lo hi : Z) : bool := if Z.leb (- t31) lo then Z.ltb hi t31 else false.

(* [comment removed for export] *)
Fixpoint terms_eqb (a b : list (Z * expr)) : bool :=
  match a, b with
  | [], [] => true
  | (k, x) :: a', (k', y) :: b' => if Z.eqb k k' then (if expr_eqb x y then terms_eqb a' b' else false) else false
  | _, _ => false
  end.

(* [comment removed for export] *)
Record sfact : Type := SF { sf_ts : list (Z * expr); sf_c : Z; sf_lo : Z; sf_hi : Z }.

Fixpoint mk_tab (kn : list kentry) : list sfact :=
  match kn with
  | [] => []
  | KRange f l h :: r => let L := lin_of f in SF (snd L) (fst L) l h :: mk_tab r
  | _ :: r => mk_tab r
  end.

(* [comment removed for export] *)
Definition fact_iv (c l h ce : Z) : option (Z * Z) :=
  if Z.leb 0 l then
    if Z.leb l h then
      if Z.ltb h t64 then
        let d := (t63 - c + ce) mod t64 in
        let k := (l + d) / t64 in
        if Z.eqb k ((h + d) / t64) then Some (l + d - k * t64 - t63, h + d - k * t64 - t63) else None
      else None
    else None
  else None.

Definition iv_meet (acc : option (Z * Z)) (lo hi : Z) : option (Z * Z) :=
  match acc with Some (a, b) => Some (Z.max a lo, Z.min b hi) | None => Some (lo, hi) end.

(* [comment removed for export] *)
Fixpoint tab_find (T : list sfact) (ce : Z) (ts : list (Z * expr)) (acc : option (Z * Z)) : option (Z * Z) :=
  match T with
  | [] => acc
  | SF ts' c l h :: r =>
      if terms_eqb ts' ts then
        match fact_iv c l h ce with
        | Some (lo, hi) => tab_find r ce ts (iv_meet acc lo hi)
        | None => tab_find r ce ts acc
        end
      else tab_find r ce ts acc
  end.

Definition tab_lookup (T : list sfact) (e : expr) : option (Z * Z) :=
  let L := lin_of e in
  match snd L with
  | [] => None
  | ts => tab_find T (fst L) ts None
  end.

(* [comment removed for export] *)
Definition erange_fb (kn : list kentry) (e : expr) : option (Z * Z) :=
  match erange kn e with
  | Some (lo, hi) =>
      if Z.ltb hi t63 then (if Z.leb 0 lo then Some (lo, hi) else None)
      else if Z.leb t63 lo then (if Z.ltb hi t64 then Some (lo - t64, hi - t64) else None)
      else None
  | None => None
  end.

Definition siv_add (a b : option (Z * Z)) : option (Z * Z) :=
  match a, b with
  | Some (al, ah), Some (bl, bh) => if in64 (al + bl) (ah + bh) then Some (al + bl, ah + bh) else None
  | _, _ => None
  end.

Definition siv_sub (a b : option (Z * Z)) : option (Z * Z) :=
  match a, b with
  | Some (al, ah), Some (bl, bh) => if in64 (al - bh) (ah - bl) then Some (al - bh, ah - bl) else None
  | _, _ => None
  end.

Definition min4 (a b c d : Z) : Z := Z.min (Z.min a b) (Z.min c d).
Definition max4 (a b c d : Z) : Z := Z.max (Z.max a b) (Z.max c d).

(* [comment removed for export] *)
Definition prod_iv (al ah bl bh : Z) : Z * Z :=
  (min4 (al * bl) (al * bh) (ah * bl) (ah * bh), max4 (al * bl) (al * bh) (ah * bl) (ah * bh)).

Definition siv_mul (a b : option (Z * Z)) : option (Z * Z) :=
  match a, b with
  | Some (al, ah), Some (bl, bh) => let '(lo, hi) := prod_iv al ah bl bh in if in64 lo hi then Some (lo, hi) else None
  | _, _ => None
  end.

Definition siv_mulw (a b : option (Z * Z)) : option (Z * Z) :=
  match a, b with
  | Some (al, ah), Some (bl, bh) => let '(lo, hi) := prod_iv al ah bl bh in if in32 lo hi then Some (lo, hi) else None
  | _, _ => None
  end.

Definition siv_sll (a : option (Z * Z)) (s : Z) : option (Z * Z) :=
  match a with
  | Some (al, ah) => let lo := al * 2 ^ s in let hi := ah * 2 ^ s in if in64 lo hi then Some (lo, hi) else None
  | None => None
  end.

Definition siv_sra (a : option (Z * Z)) (s : Z) : option (Z * Z) :=
  match a with
  | Some (al, ah) => Some (Z.shiftr al s, Z.shiftr ah s)
  | None => None
  end.

(* [comment removed for export] *)
Definition siv_srl (s : Z) : option (Z * Z) := if Z.leb 1 s then (if Z.leb s 63 then Some (0, 2 ^ (64 - s) - 1) else None) else None.
(* [comment removed for export] *)
Definition siv_srlr (ra : option (Z * Z)) (s : Z) : option (Z * Z) :=
  match ra with
  | Some (lo, hi) => if Z.leb 0 lo then (if Z.leb 1 s then (if Z.leb s 63 then Some (lo / 2 ^ s, hi / 2 ^ s) else None) else None)
                     else siv_srl s
  | None => siv_srl s
  end.
Definition siv_andl (m : Z) : option (Z * Z) := let m' := m mod t64 in if Z.ltb m' t63 then Some (0, m') else None.

Definition siv_w (r : option (Z * Z)) : option (Z * Z) :=
  match r with
  | Some (lo, hi) => if in32 lo hi then Some (lo, hi) else None
  | None => None
  end.

Definition siv_sllw (a : option (Z * Z)) (s : Z) : option (Z * Z) :=
  match a with
  | Some (al, ah) => let lo := al * 2 ^ s in let hi := ah * 2 ^ s in if in32 lo hi then Some (lo, hi) else None
  | None => None
  end.

Definition siv_sraw (a : option (Z * Z)) (s : Z) : option (Z * Z) :=
  match a with
  | Some (al, ah) => if in32 al ah then Some (Z.shiftr al s, Z.shiftr ah s) else None
  | None => None
  end.

(* [comment removed for export] *)
Definition siv_sext (a : option (Z * Z)) (n : nat) : option (Z * Z) :=
  match a with
  | Some (al, ah) =>
      if Nat.leb 1 n then
        if Nat.leb n 8 then
          let hw := 2 ^ (8 * Z.of_nat n - 1) in
          if Z.leb (- hw) al then (if Z.ltb ah hw then Some (al, ah) else None) else None
        else None
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition siv_zext (a : option (Z * Z)) (n : nat) : option (Z * Z) :=
  if Nat.ltb n 8 then
    let w := 2 ^ (8 * Z.of_nat n) in
    match a with
    | Some (al, ah) => if Z.leb 0 al then (if Z.ltb ah w then Some (al, ah) else Some (0, w - 1)) else Some (0, w - 1)
    | None => Some (0, w - 1)
    end
  else None.

(* [comment removed for export] *)
Definition iv_meet_o (a b : option (Z * Z)) : option (Z * Z) :=
  match a, b with
  | Some (l1, h1), Some (l2, h2) => Some (Z.max l1 l2, Z.min h1 h2)
  | Some r, None => Some r
  | None, r => r
  end.

(* [comment removed for export] *)
Fixpoint sr (T : list sfact) (kn : list kentry) (e : expr) {struct e} : option (Z * Z) :=
  match tab_lookup T e with
  | Some (lo, hi) =>
      if Z.ltb (hi - lo) (2 ^ 32) then Some (lo, hi) else
      iv_meet_o (Some (lo, hi))
      (match
        (match e with
         | ELit z => let v := z mod t64 in Some (if Z.leb t63 v then v - t64 else v, if Z.leb t63 v then v - t64 else v)
         | EAlu ALU_ADD a b => siv_add (sr T kn a) (sr T kn b)
         | EAlu ALU_SUB a b => siv_sub (sr T kn a) (sr T kn b)
         | EAlu ALU_SLL a (ELit s) => siv_sll (sr T kn a) (s mod 64)
         | EAlu ALU_SRA a (ELit s) => siv_sra (sr T kn a) (s mod 64)
         | EAlu ALU_SRL a (ELit s) => siv_srlr (sr T kn a) (s mod 64)
         | EAlu ALU_AND a (ELit m) => siv_andl m
         | EAlu ALU_SLTU _ _ => Some (0, 1)
         | EAlu ALU_SLT _ _ => Some (0, 1)
         | EMd M_MUL a b => siv_mul (sr T kn a) (sr T kn b)
         | EAluw ALU_ADD a b => siv_w (siv_add (sr T kn a) (sr T kn b))
         | EAluw ALU_SUB a b => siv_w (siv_sub (sr T kn a) (sr T kn b))
         | EAluw ALU_SLL a (ELit s) => siv_sllw (sr T kn a) (s mod 32)
         | EAluw ALU_SRA a (ELit s) => siv_sraw (sr T kn a) (s mod 32)
         | EMdw M_MUL a b => siv_mulw (sr T kn a) (sr T kn b)
         | EExt true O n a => siv_sext (sr T kn a) n
         | EExt false O n a => siv_zext (sr T kn a) n
         | _ => None
         end) with
      | Some r => Some r
      | None => erange_fb kn e
      end)
  | None =>
    match
      (match e with
       | ELit z => let v := z mod t64 in Some (if Z.leb t63 v then v - t64 else v, if Z.leb t63 v then v - t64 else v)
       | EAlu ALU_ADD a b => siv_add (sr T kn a) (sr T kn b)
       | EAlu ALU_SUB a b => siv_sub (sr T kn a) (sr T kn b)
       | EAlu ALU_SLL a (ELit s) => siv_sll (sr T kn a) (s mod 64)
       | EAlu ALU_SRA a (ELit s) => siv_sra (sr T kn a) (s mod 64)
       | EAlu ALU_SRL a (ELit s) => siv_srlr (sr T kn a) (s mod 64)
       | EAlu ALU_AND a (ELit m) => siv_andl m
       | EAlu ALU_SLTU _ _ => Some (0, 1)
       | EAlu ALU_SLT _ _ => Some (0, 1)
       | EMd M_MUL a b => siv_mul (sr T kn a) (sr T kn b)
       | EAluw ALU_ADD a b => siv_w (siv_add (sr T kn a) (sr T kn b))
       | EAluw ALU_SUB a b => siv_w (siv_sub (sr T kn a) (sr T kn b))
       | EAluw ALU_SLL a (ELit s) => siv_sllw (sr T kn a) (s mod 32)
       | EAluw ALU_SRA a (ELit s) => siv_sraw (sr T kn a) (s mod 32)
       | EMdw M_MUL a b => siv_mulw (sr T kn a) (sr T kn b)
       | EExt true O n a => siv_sext (sr T kn a) n
       | EExt false O n a => siv_zext (sr T kn a) n
       | _ => None
       end) with
    | Some r => Some r
    | None => erange_fb kn e
    end
  end.

Definition srange (kn : list kentry) (e : expr) : option (Z * Z) := sr (mk_tab kn) kn e.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma t63_eq : t63 = 2 ^ 63. Proof. reflexivity. Qed.
Lemma t64_eq : t64 = 2 ^ 64. Proof. reflexivity. Qed.
Lemma t31_eq : t31 = 2 ^ 31. Proof. reflexivity. Qed.

Lemma in64_ok : forall lo hi, in64 lo hi = true -> - 2 ^ 63 <= lo /\ hi < 2 ^ 63.
Proof. intros lo hi H. unfold in64 in H. destruct (Z.leb_spec (- t63) lo); [|discriminate]. apply Z.ltb_lt in H. rewrite t63_eq in *. lia. Qed.
Lemma in32_ok : forall lo hi, in32 lo hi = true -> - 2 ^ 31 <= lo /\ hi < 2 ^ 31.
Proof. intros lo hi H. unfold in32 in H. destruct (Z.leb_spec (- t31) lo); [|discriminate]. apply Z.ltb_lt in H. rewrite t31_eq in *. lia. Qed.

(* [comment removed for export] *)
Lemma s_range : forall w : word, - 2 ^ 63 <= bv_signed w < 2 ^ 63.
Proof. intros w. pose proof (bv_signed_in_range 64 w ltac:(lia)) as H. change (bv_half_modulus 64) with (2 ^ 63) in H. exact H. Qed.

Lemma s_eqm : forall w : word, eqm (bv_signed w) (bv_unsigned w).
Proof.
  intros w. unfold bv_signed, bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
  pose proof (Z.div_mod (bv_unsigned w + 2 ^ 63) (2 ^ 64) ltac:(lia)) as H.
  exists (- ((bv_unsigned w + 2 ^ 63) / 2 ^ 64)). lia.
Qed.

Lemma s_of_eqm : forall (w : word) v, eqm (bv_unsigned w) v -> - 2 ^ 63 <= v < 2 ^ 63 -> bv_signed w = v.
Proof.
  intros w v [q Hq] Hv. unfold bv_signed. rewrite Hq.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
  replace (v + q * 2 ^ 64 + 2 ^ 63) with ((v + 2 ^ 63) + q * 2 ^ 64) by lia. rewrite Z.mod_add by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma s_u_nonneg : forall w : word, 0 <= bv_signed w -> bv_unsigned w = bv_signed w.
Proof.
  intros w H. pose proof (s_range w). pose proof (u64_range w). destruct (s_eqm w) as [q Hq].
  assert (q = 0) by nia. subst q. lia.
Qed.

Lemma eqm_small_eq : forall a b, eqm a b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a = b.
Proof. intros a b [q H] Ha Hb. assert (q = 0) by nia. subst q. lia. Qed.

(* [comment removed for export] *)
Lemma swrap32_eqm : forall a b, (exists q, a = b + q * 2 ^ 32) -> bv_swrap 32 a = bv_swrap 32 b.
Proof.
  intros a b [q H]. subst a. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  replace (b + q * 2 ^ 32 + 2 ^ 31) with ((b + 2 ^ 31) + q * 2 ^ 32) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma swrap32_id : forall v, - 2 ^ 31 <= v < 2 ^ 31 -> bv_swrap 32 v = v.
Proof. intros v Hv. apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia. Qed.
Lemma swrap64_id : forall v, - 2 ^ 63 <= v < 2 ^ 63 -> bv_swrap 64 v = v.
Proof. intros v Hv. apply bv_swrap_small. change (bv_half_modulus 64) with (2 ^ 63). lia. Qed.
Lemma s_lit : forall z, bv_signed (Z_to_bv 64 z) = bv_swrap 64 z.
Proof. intros z. rewrite Z_to_bv_signed. reflexivity. Qed.
Lemma eqm_to32 : forall a b, eqm a b -> exists q, a = b + q * 2 ^ 32.
Proof. intros a b [q H]. exists (q * 2 ^ 32). lia. Qed.

(* [comment removed for export] *)
Lemma s_w32 : forall t, bv_signed (Z_to_bv 64 (bv_swrap 32 t)) = bv_swrap 32 t.
Proof.
  intros t. rewrite s_lit. apply swrap64_id. pose proof (bv_swrap_in_range 32 t ltac:(lia)) as H.
  change (bv_half_modulus 32) with (2 ^ 31) in H. lia.
Qed.

Section Sound.
Variable segs : list Segment.
Variable E : env.
Variable M : word -> option byte.
Variable kn : list kentry.
Hypothesis Hkn : know_ok segs E M kn.

Definition sE (e : expr) : Z := bv_signed (edenot E e).

Definition iv_ok (e : expr) (r : option (Z * Z)) : Prop :=
  match r with Some (lo, hi) => lo <= sE e <= hi | None => True end.

Lemma terms_eqb_eq : forall a b, terms_eqb a b = true -> a = b.
Proof.
  induction a as [|[k x] a IH]; intros [|[k' y] b] H; cbn in H; try discriminate; [reflexivity|].
  destruct (Z.eqb_spec k k'); [|discriminate]. destruct (expr_eqb x y) eqn:Hxy; [|discriminate].
  apply expr_eqb_eq in Hxy. subst. f_equal. apply IH. exact H.
Qed.

(* [comment removed for export] *)
Definition tab_ok (T : list sfact) : Prop :=
  Forall (fun F => exists f, lin_of f = (sf_c F, sf_ts F) /\ sf_lo F <= bv_unsigned (edenot E f) <= sf_hi F) T.

Lemma mk_tab_ok : tab_ok (mk_tab kn).
Proof.
  unfold tab_ok. induction kn as [|K r IH]; cbn [mk_tab]; [constructor|].
  apply Forall_cons_iff in Hkn as [HK Hr].
  destruct K; try (apply IH; exact Hr).
  constructor; [|apply IH; exact Hr]. cbn [sf_c sf_ts sf_lo sf_hi]. exists e. split; [destruct (lin_of e); reflexivity|].
  cbn in HK. lia.
Qed.

Lemma fact_iv_sound : forall c l h ce uf se t lo hi,
  eqm uf (c + t) -> eqm se (ce + t) -> l <= uf <= h -> - 2 ^ 63 <= se < 2 ^ 63 ->
  fact_iv c l h ce = Some (lo, hi) -> lo <= se <= hi.
Proof.
  intros c l h ce uf se t lo hi Hf He Hu Hs H. unfold fact_iv in H. rewrite t64_eq, t63_eq in H.
  destruct (Z.leb_spec 0 l) as [G1|G1]; [|discriminate]. destruct (Z.leb_spec l h) as [G2|G2]; [|discriminate].
  destruct (Z.ltb_spec h (2 ^ 64)) as [G3|G3]; [|discriminate].
  remember ((2 ^ 63 - c + ce) mod 2 ^ 64) as d eqn:Hdd.
  remember ((l + d) / 2 ^ 64) as k eqn:Hkk.
  destruct (Z.eqb_spec k ((h + d) / 2 ^ 64)) as [Hk|Hk]; [|discriminate]. injection H as <- <-.
  assert (Hd : 0 <= d < 2 ^ 64) by (subst d; apply Z.mod_pos_bound; lia).
  assert (Hl1 : k * 2 ^ 64 <= l + d).
  { pose proof (Z.mul_div_le (l + d) (2 ^ 64) ltac:(lia)) as Q. rewrite <- Hkk in Q. lia. }
  assert (Hh1 : h + d < (k + 1) * 2 ^ 64).
  { pose proof (Z.mul_succ_div_gt (h + d) (2 ^ 64) ltac:(lia)) as Q. rewrite <- Hk in Q. lia. }
  assert (Hc : eqm (se + 2 ^ 63) (uf + d - k * 2 ^ 64)).
  { destruct Hf as [q1 Q1]. destruct He as [q2 Q2]. pose proof (Z.div_mod (2 ^ 63 - c + ce) (2 ^ 64) ltac:(lia)) as Hm.
    rewrite <- Hdd in Hm. exists (q2 - q1 + (2 ^ 63 - c + ce) / 2 ^ 64 + k). lia. }
  pose proof (eqm_small_eq _ _ Hc ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma tab_find_sound : forall T e ce ts acc lo hi, tab_ok T -> eqm (bv_unsigned (edenot E e)) (ce + tden E ts) ->
  (forall a b, acc = Some (a, b) -> a <= sE e <= b) ->
  tab_find T ce ts acc = Some (lo, hi) -> lo <= sE e <= hi.
Proof.
  induction T as [|[ts' c l h] T IH]; intros e ce ts acc lo hi HT He Hacc H; cbn [tab_find] in H; [exact (Hacc lo hi H)|].
  unfold tab_ok in HT. apply Forall_cons_iff in HT as [HF HT].
  destruct (terms_eqb ts' ts) eqn:Hts; [|exact (IH e ce ts acc lo hi HT He Hacc H)].
  apply terms_eqb_eq in Hts. subst ts'.
  destruct (fact_iv c l h ce) as [[lo' hi']|] eqn:Hf; [|exact (IH e ce ts acc lo hi HT He Hacc H)].
  apply (IH e ce ts (iv_meet acc lo' hi') lo hi HT He); [|exact H].
  cbn [sf_c sf_ts sf_lo sf_hi] in HF. destruct HF as (f & Hlf & Hb).
  pose proof (lin_of_sound E f) as Hl. rewrite Hlf in Hl. unfold lden in Hl. cbn [fst snd] in Hl.
  assert (B : lo' <= sE e <= hi').
  { apply (fact_iv_sound c l h ce (bv_unsigned (edenot E f)) (sE e) (tden E ts) lo' hi'); [| | lia | apply s_range | exact Hf].
    - apply eqm_sym. exact Hl.
    - eapply eqm_trans; [apply s_eqm | exact He]. }
  intros a b Hab. unfold iv_meet in Hab. destruct acc as [[a0 b0]|].
  - injection Hab as <- <-. specialize (Hacc a0 b0 eq_refl). lia.
  - injection Hab as <- <-. exact B.
Qed.

Lemma tab_lookup_sound : forall T e lo hi, tab_ok T -> tab_lookup T e = Some (lo, hi) -> lo <= sE e <= hi.
Proof.
  intros T e lo hi HT H. unfold tab_lookup in H. pose proof (lin_of_sound E e) as Hl. unfold lden in Hl.
  destruct (lin_of e) as [c ts] eqn:Hle. cbn [fst snd] in *. destruct ts as [|t ts]; [discriminate|].
  apply (tab_find_sound T e c (t :: ts) None lo hi HT); [apply eqm_sym; exact Hl | intros a b Hab; discriminate Hab | exact H].
Qed.

(* [comment removed for export] *)
Lemma eqm_mul : forall a a' b b', eqm a a' -> eqm b b' -> eqm (a * b) (a' * b').
Proof. intros a a' b b' [q H] [r H']. exists (q * b + a' * r). subst. ring. Qed.

Lemma mul_le_max : forall a b x y, a <= x <= b -> x * y <= Z.max (a * y) (b * y) /\ Z.min (a * y) (b * y) <= x * y.
Proof. intros a b x y Hx. destruct (Z.le_ge_cases 0 y); split; nia. Qed.

Lemma mul_le_max' : forall a b c y, a <= y <= b -> c * y <= Z.max (c * a) (c * b) /\ Z.min (c * a) (c * b) <= c * y.
Proof. intros a b c y Hy. destruct (Z.le_ge_cases 0 c); split; nia. Qed.

Lemma prod_iv_ok : forall al ah bl bh x y lo hi, al <= x <= ah -> bl <= y <= bh -> prod_iv al ah bl bh = (lo, hi) -> lo <= x * y <= hi.
Proof.
  intros al ah bl bh x y lo hi Hx Hy H. unfold prod_iv in H. injection H as <- <-. unfold min4, max4.
  destruct (mul_le_max al ah x y Hx) as [H1 H2].
  destruct (mul_le_max' bl bh al y Hy) as [H3 H4]. destruct (mul_le_max' bl bh ah y Hy) as [H5 H6].
  split; lia.
Qed.

Lemma iv_by : forall e r v, (forall lo hi, r = Some (lo, hi) -> sE e = v /\ lo <= v <= hi) -> iv_ok e r.
Proof. intros e [[lo hi]|] v H; cbn; [|exact I]. destruct (H lo hi eq_refl) as [-> Hb]. exact Hb. Qed.

Lemma siv_add_ok : forall a b ra rb, iv_ok a ra -> iv_ok b rb -> iv_ok (EAlu ALU_ADD a b) (siv_add ra rb).
Proof.
  intros a b [[al ah]|] [[bl bh]|] Ha Hb; cbn [siv_add]; try exact I. cbn in Ha, Hb.
  destruct (in64 (al + bl) (ah + bh)) eqn:Hr; [|exact I]. apply in64_ok in Hr. cbn. unfold sE in *. cbn [edenot].
  rewrite (s_of_eqm _ (bv_signed (edenot E a) + bv_signed (edenot E b))); [lia| |lia].
  eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; apply eqm_sym; apply s_eqm.
Qed.

Lemma siv_sub_ok : forall a b ra rb, iv_ok a ra -> iv_ok b rb -> iv_ok (EAlu ALU_SUB a b) (siv_sub ra rb).
Proof.
  intros a b [[al ah]|] [[bl bh]|] Ha Hb; cbn [siv_sub]; try exact I. cbn in Ha, Hb.
  destruct (in64 (al - bh) (ah - bl)) eqn:Hr; [|exact I]. apply in64_ok in Hr. cbn. unfold sE in *. cbn [edenot].
  rewrite (s_of_eqm _ (bv_signed (edenot E a) - bv_signed (edenot E b))); [lia| |lia].
  eapply eqm_trans; [apply u_sub_eqm|].
  replace (bv_signed (edenot E a) - bv_signed (edenot E b)) with (bv_signed (edenot E a) + (-1) * bv_signed (edenot E b)) by lia.
  replace (bv_unsigned (edenot E a) - bv_unsigned (edenot E b)) with (bv_unsigned (edenot E a) + (-1) * bv_unsigned (edenot E b)) by lia.
  apply eqm_add; [apply eqm_sym; apply s_eqm|]. apply eqm_mul_l. apply eqm_sym; apply s_eqm.
Qed.

Lemma siv_mul_ok : forall a b ra rb, iv_ok a ra -> iv_ok b rb -> iv_ok (EMd M_MUL a b) (siv_mul ra rb).
Proof.
  intros a b [[al ah]|] [[bl bh]|] Ha Hb; cbn [siv_mul]; try exact I. cbn in Ha, Hb.
  destruct (prod_iv al ah bl bh) as [lo hi] eqn:Hp.
  destruct (in64 lo hi) eqn:Hr; [|exact I]. apply in64_ok in Hr.
  pose proof (prod_iv_ok al ah bl bh _ _ lo hi Ha Hb Hp) as Hpb. cbn. unfold sE in *. cbn [edenot].
  rewrite (s_of_eqm _ (bv_signed (edenot E a) * bv_signed (edenot E b))); [lia| |lia].
  eapply eqm_trans; [apply u_mul_eqm|]. apply eqm_mul; apply eqm_sym; apply s_eqm.
Qed.

Lemma siv_sll_ok : forall a s ra, iv_ok a ra -> iv_ok (EAlu ALU_SLL a (ELit s)) (siv_sll ra (s mod 64)).
Proof.
  intros a s [[al ah]|] Ha; cbn [siv_sll]; [|exact I]. cbn in Ha.
  destruct (in64 (al * 2 ^ (s mod 64)) (ah * 2 ^ (s mod 64))) eqn:Hr; [|exact I]. apply in64_ok in Hr. cbn.
  assert (Hp : 0 < 2 ^ (s mod 64)) by (apply Z.pow_pos_nonneg; [lia|apply Z.mod_pos_bound; lia]).
  unfold sE in *. cbn [edenot].
  rewrite (s_of_eqm _ (bv_signed (edenot E a) * 2 ^ (s mod 64))); [nia| |nia].
  eapply eqm_trans; [apply u_sll_eqm|]. apply eqm_sym. rewrite Z.mul_comm. apply eqm_mul_l. apply s_eqm.
Qed.

Lemma shiftr_mono : forall x y k, 0 <= k -> x <= y -> Z.shiftr x k <= Z.shiftr y k.
Proof. intros x y k Hk Hxy. rewrite !Z.shiftr_div_pow2 by lia. apply Z.div_le_mono; [apply Z.pow_pos_nonneg; lia | exact Hxy]. Qed.

Lemma shiftr_range : forall x k n, 0 <= k -> - 2 ^ n <= x < 2 ^ n -> 0 <= n -> - 2 ^ n <= Z.shiftr x k < 2 ^ n.
Proof.
  intros x k n Hk Hx Hn. rewrite Z.shiftr_div_pow2 by lia. assert (Hp : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  split.
  - apply Z.div_le_lower_bound; [lia|]. assert (1 <= 2 ^ k) by lia. nia.
  - apply Z.div_lt_upper_bound; [lia|]. assert (1 <= 2 ^ k) by lia. nia.
Qed.

Lemma siv_sra_ok : forall a s ra, iv_ok a ra -> iv_ok (EAlu ALU_SRA a (ELit s)) (siv_sra ra (s mod 64)).
Proof.
  intros a s [[al ah]|] Ha; cbn [siv_sra]; [|exact I]. cbn in Ha. cbn.
  assert (Hk : 0 <= s mod 64) by (apply Z.mod_pos_bound; lia).
  unfold sE in *. cbn [edenot]. rewrite alu_sra. unfold v_sra. rewrite s_lit.
  assert (Hs : bv_unsigned (Z_to_bv 64 s) mod 64 = s mod 64).
  { rewrite u_lit64a. apply Z.mod_mod_divide. exists (2 ^ 58). reflexivity. }
  rewrite Hs. pose proof (s_range (edenot E a)) as Hr.
  rewrite swrap64_id by (apply (shiftr_range _ _ 63); lia).
  split; apply shiftr_mono; lia.
Qed.

Lemma siv_w_add_ok : forall a b ra rb, iv_ok a ra -> iv_ok b rb -> iv_ok (EAluw ALU_ADD a b) (siv_w (siv_add ra rb)).
Proof.
  intros a b [[al ah]|] [[bl bh]|] Ha Hb; cbn [siv_add siv_w]; try exact I. cbn in Ha, Hb.
  destruct (in64 (al + bl) (ah + bh)) eqn:Hr; [|exact I]. cbn [siv_w].
  destruct (in32 (al + bl) (ah + bh)) eqn:Hr32; [|exact I]. apply in32_ok in Hr32. cbn. unfold sE in *. cbn [edenot].
  rewrite w_addw. unfold v_addw. rewrite s_w32.
  rewrite (swrap32_eqm _ (bv_signed (edenot E a) + bv_signed (edenot E b))).
  - rewrite swrap32_id by lia. lia.
  - apply eqm_to32. apply eqm_add; apply eqm_sym; apply s_eqm.
Qed.

Lemma siv_w_sub_ok : forall a b ra rb, iv_ok a ra -> iv_ok b rb -> iv_ok (EAluw ALU_SUB a b) (siv_w (siv_sub ra rb)).
Proof.
  intros a b [[al ah]|] [[bl bh]|] Ha Hb; cbn [siv_sub siv_w]; try exact I. cbn in Ha, Hb.
  destruct (in64 (al - bh) (ah - bl)) eqn:Hr; [|exact I]. cbn [siv_w].
  destruct (in32 (al - bh) (ah - bl)) eqn:Hr32; [|exact I]. apply in32_ok in Hr32. cbn. unfold sE in *. cbn [edenot].
  rewrite w_subw. unfold v_subw. rewrite s_w32.
  rewrite (swrap32_eqm _ (bv_signed (edenot E a) - bv_signed (edenot E b))).
  - rewrite swrap32_id by lia. lia.
  - apply eqm_to32.
    replace (bv_signed (edenot E a) - bv_signed (edenot E b)) with (bv_signed (edenot E a) + (-1) * bv_signed (edenot E b)) by lia.
    replace (bv_unsigned (edenot E a) - bv_unsigned (edenot E b)) with (bv_unsigned (edenot E a) + (-1) * bv_unsigned (edenot E b)) by lia.
    apply eqm_add; [apply eqm_sym; apply s_eqm|]. apply eqm_mul_l. apply eqm_sym; apply s_eqm.
Qed.

Lemma u_mod32 : forall s, bv_unsigned (Z_to_bv 64 s) mod 32 = s mod 32.
Proof. intros s. rewrite u_lit64a. apply Z.mod_mod_divide. exists (2 ^ 59). reflexivity. Qed.

Lemma siv_sllw_ok : forall a s ra, iv_ok a ra -> iv_ok (EAluw ALU_SLL a (ELit s)) (siv_sllw ra (s mod 32)).
Proof.
  intros a s [[al ah]|] Ha; cbn [siv_sllw]; [|exact I]. cbn in Ha.
  destruct (in32 (al * 2 ^ (s mod 32)) (ah * 2 ^ (s mod 32))) eqn:Hr; [|exact I]. apply in32_ok in Hr. cbn.
  assert (Hk : 0 <= s mod 32) by (apply Z.mod_pos_bound; lia).
  assert (Hp : 0 < 2 ^ (s mod 32)) by (apply Z.pow_pos_nonneg; lia).
  unfold sE in *. cbn [edenot]. rewrite w_sllw. unfold v_sllw. rewrite s_w32, u_mod32.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (swrap32_eqm _ (bv_signed (edenot E a) * 2 ^ (s mod 32))).
  - rewrite swrap32_id by nia. nia.
  - apply eqm_to32. apply eqm_mul_r. apply eqm_sym; apply s_eqm.
Qed.

Lemma siv_sraw_ok : forall a s ra, iv_ok a ra -> iv_ok (EAluw ALU_SRA a (ELit s)) (siv_sraw ra (s mod 32)).
Proof.
  intros a s [[al ah]|] Ha; cbn [siv_sraw]; [|exact I]. cbn in Ha.
  destruct (in32 al ah) eqn:Hr; [|exact I]. apply in32_ok in Hr. cbn.
  assert (Hk : 0 <= s mod 32) by (apply Z.mod_pos_bound; lia).
  unfold sE in *. cbn [edenot]. rewrite w_sraw. unfold v_sraw. rewrite s_w32, u_mod32.
  rewrite (swrap32_eqm (bv_unsigned (edenot E a)) (bv_signed (edenot E a)))
    by (apply eqm_to32; apply eqm_sym; apply s_eqm).
  rewrite (swrap32_id (bv_signed (edenot E a))) by lia.
  rewrite swrap32_id by (apply (shiftr_range _ _ 31); lia).
  split; apply shiftr_mono; lia.
Qed.

Lemma siv_mulw_ok : forall a b ra rb, iv_ok a ra -> iv_ok b rb -> iv_ok (EMdw M_MUL a b) (siv_mulw ra rb).
Proof.
  intros a b [[al ah]|] [[bl bh]|] Ha Hb; cbn [siv_mulw]; try exact I. cbn in Ha, Hb.
  destruct (prod_iv al ah bl bh) as [lo hi] eqn:Hp.
  destruct (in32 lo hi) eqn:Hr; [|exact I]. apply in32_ok in Hr.
  pose proof (prod_iv_ok al ah bl bh _ _ lo hi Ha Hb Hp) as Hpb. cbn. unfold sE in *. cbn [edenot].
  rewrite w_mulw. unfold v_mulw. rewrite s_w32.
  rewrite (swrap32_eqm _ (bv_signed (edenot E a) * bv_signed (edenot E b))).
  - rewrite swrap32_id by lia. lia.
  - apply eqm_to32. apply eqm_mul; apply eqm_sym; apply s_eqm.
Qed.

Lemma swrapn_eqm : forall (n : N) a b, (n <= 64)%N -> eqm a b -> bv_swrap n a = bv_swrap n b.
Proof.
  intros n a b Hn [q H]. subst a. unfold bv_swrap, bv_wrap.
  assert (Hm : 2 ^ 64 = 2 ^ (64 - Z.of_N n) * bv_modulus n).
  { unfold bv_modulus. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  replace (b + q * 2 ^ 64 + bv_half_modulus n) with ((b + bv_half_modulus n) + (q * 2 ^ (64 - Z.of_N n)) * bv_modulus n)
    by (rewrite Hm; ring).
  rewrite Z.mod_add by (pose proof (bv_modulus_pos n); lia). reflexivity.
Qed.

Lemma siv_sext_ok : forall a n ra, iv_ok a ra -> iv_ok (EExt true 0 n a) (siv_sext ra n).
Proof.
  intros a n [[al ah]|] Ha; cbn [siv_sext]; [|exact I]. cbn in Ha.
  destruct (Nat.leb_spec 1 n); [|exact I]. destruct (Nat.leb_spec n 8); [|exact I].
  destruct (Z.leb_spec (- 2 ^ (8 * Z.of_nat n - 1)) al); [|exact I]. destruct (Z.ltb_spec ah (2 ^ (8 * Z.of_nat n - 1))); [|exact I].
  cbn. unfold sE in *. cbn [edenot]. unfold ext_val, ext_Z.
  change (8 * Z.of_nat 0) with 0. rewrite Z.pow_0_r, Z.div_1_r.
  assert (Hw : 2 ^ (8 * Z.of_nat n) = bv_modulus (8 * N.of_nat n)) by (unfold bv_modulus; f_equal; lia).
  rewrite Hw. fold (bv_wrap (8 * N.of_nat n) (bv_unsigned (edenot E a))). rewrite bv_swrap_wrap.
  rewrite (swrapn_eqm _ (bv_unsigned (edenot E a)) (bv_signed (edenot E a))) by (lia || (apply eqm_sym; apply s_eqm)).
  assert (Hh : bv_half_modulus (8 * N.of_nat n) = 2 ^ (8 * Z.of_nat n - 1)).
  { unfold bv_half_modulus, bv_modulus. replace (Z.of_N (8 * N.of_nat n)) with (8 * Z.of_nat n - 1 + 1) by lia.
    rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r. apply Z.div_mul. lia. }
  assert (Hp : 2 ^ (8 * Z.of_nat n - 1) <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia).
  rewrite bv_swrap_small by (rewrite Hh; lia). rewrite s_lit, swrap64_id by lia. lia.
Qed.

Lemma siv_zext_ok : forall a n ra, iv_ok a ra -> iv_ok (EExt false 0 n a) (siv_zext ra n).
Proof.
  intros a n ra Ha. unfold siv_zext. destruct (Nat.ltb_spec n 8); [|exact I].
  assert (Hw0 : 0 < 2 ^ (8 * Z.of_nat n)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hw1 : 2 ^ (8 * Z.of_nat n) <= 2 ^ 56) by (apply Z.pow_le_mono_r; lia).
  assert (Hv : sE (EExt false 0 n a) = bv_unsigned (edenot E a) mod 2 ^ (8 * Z.of_nat n)).
  { unfold sE. cbn [edenot]. unfold ext_val, ext_Z. change (8 * Z.of_nat 0) with 0. rewrite Z.pow_0_r, Z.div_1_r.
    rewrite s_lit. apply swrap64_id. pose proof (Z.mod_pos_bound (bv_unsigned (edenot E a)) (2 ^ (8 * Z.of_nat n)) Hw0). lia. }
  pose proof (Z.mod_pos_bound (bv_unsigned (edenot E a)) (2 ^ (8 * Z.of_nat n)) Hw0) as Hm.
  destruct ra as [[al ah]|]; cbn in Ha.
  - destruct (Z.leb_spec 0 al); [destruct (Z.ltb_spec ah (2 ^ (8 * Z.of_nat n)))|]; cbn; rewrite Hv; try lia.
    rewrite s_u_nonneg by (unfold sE in Ha; lia). unfold sE in Ha. rewrite Z.mod_small by lia. lia.
  - cbn. rewrite Hv. lia.
Qed.

Lemma lit_ok : forall z, iv_ok (ELit z)
  (Some (if Z.leb t63 (z mod t64) then z mod t64 - t64 else z mod t64, if Z.leb t63 (z mod t64) then z mod t64 - t64 else z mod t64)).
Proof.
  intros z. cbn. rewrite t63_eq, t64_eq. unfold sE. cbn [edenot].
  pose proof (Z.mod_pos_bound z (2 ^ 64) ltac:(lia)) as Hm.
  destruct (Z.leb_spec (2 ^ 63) (z mod 2 ^ 64)).
  - rewrite (s_of_eqm _ (z mod 2 ^ 64 - 2 ^ 64)); [lia| |lia].
    rewrite u_lit64a. exists 1. lia.
  - rewrite (s_of_eqm _ (z mod 2 ^ 64)); [lia| |lia].
    rewrite u_lit64a. exists 0. lia.
Qed.

Lemma erange_fb_ok : forall e, iv_ok e (erange_fb kn e).
Proof.
  intros e. unfold erange_fb. destruct (erange kn e) as [[lo hi]|] eqn:Hr; [|exact I].
  pose proof (erange_sound segs E M kn e lo hi Hkn Hr) as Hb. rewrite t63_eq, t64_eq.
  destruct (Z.ltb_spec hi (2 ^ 63)).
  - destruct (Z.leb_spec 0 lo); [|exact I]. cbn. unfold sE.
    rewrite (s_of_eqm _ (bv_unsigned (edenot E e))); [lia|apply eqm_refl|lia].
  - destruct (Z.leb_spec (2 ^ 63) lo); [|exact I]. destruct (Z.ltb_spec hi (2 ^ 64)); [|exact I]. cbn. unfold sE.
    rewrite (s_of_eqm _ (bv_unsigned (edenot E e) - 2 ^ 64)); [lia| exists 1; lia |lia].
Qed.

Lemma pick_ok : forall e r, iv_ok e r -> iv_ok e (match r with Some r' => Some r' | None => erange_fb kn e end).
Proof. intros e [r|] H; [exact H | apply erange_fb_ok]. Qed.

Lemma iv_meet_o_ok : forall e a b, iv_ok e a -> iv_ok e b -> iv_ok e (iv_meet_o a b).
Proof. intros e [[l1 h1]|] [[l2 h2]|] Ha Hb; cbn in *; try exact I; try exact Ha; try exact Hb; lia. Qed.

Lemma siv_srl_ok : forall a s, iv_ok (EAlu ALU_SRL a (ELit s)) (siv_srl (s mod 64)).
Proof.
  intros a s. unfold siv_srl. set (s' := s mod 64).
  destruct (Z.leb 1 s') eqn:C1; [|exact I]. destruct (Z.leb s' 63) eqn:C2; [|exact I]. apply Z.leb_le in C1, C2. cbn.
  unfold sE. cbn [edenot]. rewrite alu_srl. unfold v_srl. rewrite u_lit64a.
  assert (Hs : s mod 2 ^ 64 mod 64 = s') by (unfold s'; apply Z.mod_mod_divide; exists (2 ^ 58); reflexivity).
  rewrite Hs. pose proof (u64_range (edenot E a)) as R.
  assert (V : 0 <= Z.shiftr (bv_unsigned (edenot E a)) s' <= 2 ^ (64 - s') - 1).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
    assert (bv_unsigned (edenot E a) / 2 ^ s' < 2 ^ (64 - s')); [|lia].
    apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (s' + (64 - s')) with 64 by lia. lia. }
  assert (P : 2 ^ (64 - s') <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia).
  rewrite s_lit. rewrite swrap64_id by lia. lia.
Qed.

Lemma siv_srlr_ok : forall a s ra, iv_ok a ra -> iv_ok (EAlu ALU_SRL a (ELit s)) (siv_srlr ra (s mod 64)).
Proof.
  intros a s ra Ha. unfold siv_srlr. destruct ra as [[lo hi]|]; [|apply siv_srl_ok].
  destruct (Z.leb 0 lo) eqn:C0; [|apply siv_srl_ok]. apply Z.leb_le in C0.
  set (s' := s mod 64).
  destruct (Z.leb 1 s') eqn:C1; [|exact I]. destruct (Z.leb s' 63) eqn:C2; [|exact I]. apply Z.leb_le in C1, C2.
  cbn in Ha |- *. unfold sE in *. cbn [edenot]. rewrite alu_srl. unfold v_srl. rewrite u_lit64a.
  assert (Hs : s mod 2 ^ 64 mod 64 = s') by (unfold s'; apply Z.mod_mod_divide; exists (2 ^ 58); reflexivity).
  rewrite Hs. pose proof (u64_range (edenot E a)) as R.
  assert (Hu : bv_unsigned (edenot E a) = bv_signed (edenot E a)) by (apply s_u_nonneg; lia).
  assert (V : 0 <= Z.shiftr (bv_unsigned (edenot E a)) s' <= 2 ^ (64 - s') - 1).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
    assert (bv_unsigned (edenot E a) / 2 ^ s' < 2 ^ (64 - s')); [|lia].
    apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (s' + (64 - s')) with 64 by lia. lia. }
  assert (P : 2 ^ (64 - s') <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia).
  rewrite s_lit. rewrite swrap64_id by lia. rewrite Z.shiftr_div_pow2 by lia.
  assert (Pp : 0 < 2 ^ s') by (apply Z.pow_pos_nonneg; lia).
  split; apply Z.div_le_mono; lia.
Qed.

Lemma land_le_r : forall a b, 0 <= b -> Z.land a b <= b.
Proof.
  intros a b Hb. rewrite Z.land_comm.
  assert (D : Z.land (Z.ldiff b a) (Z.land b a) = 0).
  { apply Z.bits_inj_0. intros n. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec.
    destruct (Z.testbit a n), (Z.testbit b n); reflexivity. }
  pose proof (Z.lor_ldiff_and b a) as E1. rewrite <- (Z.lxor_lor _ _ D), <- (Z.add_nocarry_lxor _ _ D) in E1.
  assert (0 <= Z.ldiff b a) by (rewrite Z.ldiff_land; apply Z.land_nonneg; left; exact Hb). lia.
Qed.

Lemma siv_andl_ok : forall a m, iv_ok (EAlu ALU_AND a (ELit m)) (siv_andl m).
Proof.
  intros a m. unfold siv_andl. rewrite t64_eq, t63_eq. destruct (Z.ltb (m mod 2 ^ 64) (2 ^ 63)) eqn:C; [|exact I].
  apply Z.ltb_lt in C. cbn. unfold sE. cbn [edenot]. rewrite alu_and. unfold v_and. rewrite u_lit64a.
  pose proof (u64_range (edenot E a)) as R. pose proof (Z.mod_pos_bound m (2 ^ 64) ltac:(lia)) as Rm.
  assert (L : 0 <= Z.land (bv_unsigned (edenot E a)) (m mod 2 ^ 64) <= m mod 2 ^ 64).
  { split; [apply Z.land_nonneg; lia | apply land_le_r; lia]. }
  rewrite s_lit. rewrite swrap64_id by lia. lia.
Qed.

Lemma slt01_ok : forall op a b, (op = ALU_SLTU \/ op = ALU_SLT) -> iv_ok (EAlu op a b) (Some (0, 1)).
Proof.
  intros op a b Hop. cbn. unfold sE. cbn [edenot].
  destruct Hop as [->| ->]; [rewrite alu_sltu; unfold v_sltu | rewrite alu_slt; unfold v_slt];
    match goal with |- context [if ?c then _ else _] => destruct c end; rewrite s_lit, swrap64_id by lia; lia.
Qed.

Lemma sr_sound : forall T e, tab_ok T -> iv_ok e (sr T kn e).
Proof.
  intros T e HT. induction e; cbn [sr];
    (destruct (tab_lookup T _) as [[l0 h0]|] eqn:Ht;
     [ pose proof (tab_lookup_sound _ _ _ _ HT Ht) as Hf0;
       destruct (Z.ltb (h0 - l0) (2 ^ 32)); [exact Hf0|]; apply iv_meet_o_ok; [exact Hf0|] | ]).
  all: try exact (lit_ok z).
  all: try apply erange_fb_ok.
  all: try (apply pick_ok; destruct op; try exact I;
            first [ apply siv_add_ok; assumption | apply siv_sub_ok; assumption
                  | destruct e2; try exact I; first [apply siv_sll_ok; assumption | apply siv_sra_ok; assumption
                                                    | apply siv_srlr_ok; assumption | apply siv_andl_ok]
                  | apply slt01_ok; auto
                  | apply siv_w_add_ok; assumption | apply siv_w_sub_ok; assumption
                  | destruct e2; try exact I; first [apply siv_sllw_ok; assumption | apply siv_sraw_ok; assumption]
                  | apply siv_mul_ok; assumption | apply siv_mulw_ok; assumption ]).
  all: try (apply pick_ok; destruct sx; destruct lo; try exact I; [apply siv_sext_ok | apply siv_zext_ok]; assumption).
Qed.

End Sound.

(* [comment removed for export] *)
Theorem srange_sound : forall segs E M kn e lo hi, know_ok segs E M kn -> srange kn e = Some (lo, hi) ->
  lo <= bv_signed (edenot E e) <= hi.
Proof.
  intros segs E M kn e lo hi Hkn H. pose proof (sr_sound segs E M kn Hkn (mk_tab kn) e (mk_tab_ok segs E M kn Hkn)) as S.
  unfold srange in H. rewrite H in S. exact S.
Qed.

Theorem srange_sound_u : forall segs E M kn e lo hi, know_ok segs E M kn -> srange kn e = Some (lo, hi) -> 0 <= lo ->
  lo <= bv_unsigned (edenot E e) <= hi.
Proof.
  intros segs E M kn e lo hi Hkn H Hlo. pose proof (srange_sound segs E M kn e lo hi Hkn H) as S.
  rewrite s_u_nonneg by lia. exact S.
Qed.

(* [comment removed for export] *)
Theorem srange_sound_addr : forall segs E M kn e k lo hi, know_ok segs E M kn -> srange kn e = Some (lo, hi) ->
  0 <= lo + k -> hi + k < 2 ^ 64 ->
  lo + k <= (bv_unsigned (edenot E e) + k) mod 2 ^ 64 <= hi + k /\ (bv_unsigned (edenot E e) + k) mod 2 ^ 64 = bv_signed (edenot E e) + k.
Proof.
  intros segs E M kn e k lo hi Hkn H H1 H2. pose proof (srange_sound segs E M kn e lo hi Hkn H) as S.
  assert (Hm : (bv_unsigned (edenot E e) + k) mod 2 ^ 64 = bv_signed (edenot E e) + k).
  { destruct (s_eqm (edenot E e)) as [q Hq]. rewrite (Z.mod_unique (bv_unsigned (edenot E e) + k) (2 ^ 64) (- q) (bv_signed (edenot E e) + k));
      [reflexivity | lia | lia]. }
  rewrite Hm. lia.
Qed.

End SSR.
