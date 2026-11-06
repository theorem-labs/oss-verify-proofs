(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXStepR KXExec KXSound KXFull KXBridge KXTac.
Import ListNotations.
Import KXS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Inductive ktree : Type :=
| KLeaf (ss : sym_state) (scs : list sidecond) (accs : list (saddr * nat))
| KFork (c : branch_cond) (a b : expr) (scs : list sidecond) (accs : list (saddr * nat)) (t1 t2 : ktree)
| KSplit (x : expr) (v : Z) (scs : list sidecond) (accs : list (saddr * nat)) (t1 t2 : ktree).
    (* [comment removed for export] *)

Fixpoint kt_next (t : ktree) : nat :=
  match t with
  | KLeaf ss _ _ => s_next ss
  | KFork _ _ _ _ _ t1 t2 => Nat.max (kt_next t1) (kt_next t2)
  | KSplit _ _ _ _ t1 t2 => Nat.max (kt_next t1) (kt_next t2)
  end.

(* [comment removed for export] *)
Definition tighten (kn : list kentry) (K : kentry) : kentry :=
  match K with
  | KRange e lo hi => match erange kn e with Some (lo0, hi0) => KRange e (Z.max lo lo0) (Z.min hi hi0) | None => K end
  | _ => K
  end.
Definition kn_enter (kn ks : list kentry) : list kentry := map (tighten kn) ks ++ kn.

(* [comment removed for export] *)
Definition kt_enter (ss : sym_state) (n : nat) (ks : list kentry) : sym_state :=
  SSR (s_pc ss) (s_regs ss) (s_log ss) (kn_enter (s_know ss) ks) (Nat.max (s_next ss) n) (s_resv ss).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition two64m1 : Z := 2^64 - 1.
Definition zwrap (z : Z) : Z := z mod 2^64.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rel_know (kn : list kentry) (lt : bool) (a b : expr) : list kentry :=
  match erange kn a, erange kn b with
  | Some (al, ah), Some (bl, bh) =>
      if (Z.leb 0 al && Z.leb 0 bl && Z.ltb ah (2^64) && Z.ltb bh (2^64))%bool then
        if lt then (if Z.leb 1 (bh - al) then [KRange (mkAlu ALU_SUB b a) 1 (bh - al)] else [])
        else (if Z.leb 0 (ah - bl) then [KRange (mkAlu ALU_SUB a b) 0 (ah - bl)] else [])
      else []
  | _, _ => []
  end.

Definition cmpu_know (kn : list kentry) (lt : bool) (a b : expr) : list kentry :=
  match a, b with
  | ELit _, ELit _ => []
  | _, ELit z => let c := zwrap z in
                 if lt then (if Z.ltb 0 c then [KRange a 0 (c - 1)] else []) else [KRange a c two64m1]
  | ELit z, _ => let c := zwrap z in
                 if lt then [KRange b (c + 1) two64m1] else [KRange b 0 c]
  | _, _ => rel_know kn lt a b
  end.

Definition eq_know (eq : bool) (a b : expr) : list kentry :=
  match a, b with
  | ELit _, ELit _ => []
  | _, ELit z => let c := zwrap z in
                 if eq then [KRange a c c] else (if Z.eqb c 0 then [KRange a 1 two64m1] else [])
  | ELit z, _ => let c := zwrap z in
                 if eq then [KRange b c c] else (if Z.eqb c 0 then [KRange b 1 two64m1] else [])
  | _, _ => []
  end.

(* [comment removed for export] *)
Definition small63 (kn : list kentry) (e : expr) : bool :=
  match e with
  | ELit z => Z.ltb (zwrap z) (2^63)
  | _ => match erange kn e with Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi (2^63))%bool | None => false end
  end.
Definition cmps_know (kn : list kentry) (lt : bool) (a b : expr) : list kentry :=
  match a, b with
  | ELit _, ELit _ => []
  | _, ELit 0 => if lt then [KRange a (2^63) two64m1] else [KRange a 0 (2^63 - 1)]
  | _, _ => if (small63 kn a && small63 kn b)%bool then cmpu_know kn lt a b else []
  end.

Definition br_know (kn : list kentry) (t : bool) (c : branch_cond) (a b : expr) : list kentry :=
  match c with
  | BC_EQ => eq_know t a b
  | BC_NE => eq_know (negb t) a b
  | BC_LTU => cmpu_know kn t a b
  | BC_GEU => cmpu_know kn (negb t) a b
  | BC_LT => cmps_know kn t a b
  | BC_GE => cmps_know kn (negb t) a b
  end.

(* [comment removed for export] *)
Definition vs_step (kn : list kentry) (x : expr) : Z := 2 ^ Z.min (Z.max 0 (ealign kn x)) 16.
Definition vs_first (lo s : Z) : Z := ((lo + s - 1) / s) * s.
Definition split_know (kn : list kentry) (t : bool) (x : expr) (v : Z) : list kentry :=
  if t then [KRange x v v] else
  match erange kn x with
  | Some (lo, hi) => let s := vs_step kn x in
                     if (Z.leb 0 lo && Z.eqb v (vs_first lo s))%bool then [KRange x (v + s) hi] else []
  | None => []
  end.

Lemma u_lit_wrap : forall E z, bv_unsigned (edenot E (ELit z)) = zwrap z.
Proof. intros. cbn [edenot]. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma zwrap_range : forall z, 0 <= zwrap z < 2^64.
Proof. intro z. unfold zwrap. apply Z.mod_pos_bound. lia. Qed.

Lemma u_range64 : forall w : word, 0 <= bv_unsigned w <= two64m1.
Proof. intro w. pose proof (kx_u64_range w). unfold two64m1. lia. Qed.

Section BrKnow.
Variable segs : list Segment.
Variable E : env.
Variable base : word -> option byte.

Lemma rel_know_ok : forall kn lt a b, know_ok segs E base kn ->
  Z.ltb (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b)) = lt ->
  Forall (kentry_ok segs E base) (rel_know kn lt a b).
Proof.
  intros kn lt a b HK H. unfold rel_know.
  destruct (erange kn a) as [[al ah]|] eqn:Ea; [|constructor].
  destruct (erange kn b) as [[bl bh]|] eqn:Eb; [|constructor].
  destruct (Z.leb 0 al && Z.leb 0 bl && Z.ltb ah (2^64) && Z.ltb bh (2^64))%bool eqn:C; [|constructor].
  repeat (apply andb_prop in C as [C ?]).
  repeat match goal with X : Z.leb _ _ = true |- _ => apply Z.leb_le in X | X : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in X end.
  pose proof (erange_sound segs E base kn a al ah HK Ea) as Ra. pose proof (erange_sound segs E base kn b bl bh HK Eb) as Rb.
  destruct lt; [apply Z.ltb_lt in H | apply Z.ltb_ge in H].
  - destruct (Z.leb 1 (bh - al)); [|constructor]. constructor; [|constructor]. cbn [kentry_ok].
    rewrite mkAlu_denot, u_sub64, Z.mod_small by lia. lia.
  - destruct (Z.leb 0 (ah - bl)); [|constructor]. constructor; [|constructor]. cbn [kentry_ok].
    rewrite mkAlu_denot, u_sub64, Z.mod_small by lia. lia.
Qed.

Lemma cmpu_know_ok : forall kn lt a b, know_ok segs E base kn ->
  Z.ltb (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b)) = lt ->
  Forall (kentry_ok segs E base) (cmpu_know kn lt a b).
Proof.
  intros kn lt a b HK H. pose proof (u_range64 (edenot E a)) as Ra. pose proof (u_range64 (edenot E b)) as Rb.
  assert (REL : Forall (kentry_ok segs E base) (rel_know kn lt a b)) by (apply rel_know_ok; assumption).
  unfold cmpu_know.
  destruct a as [za| | | | | | |], b as [zb| | | | | | |]; cbn beta iota; try apply Forall_nil; try exact REL; clear REL;
    try rewrite (u_lit_wrap E zb) in H; try rewrite (u_lit_wrap E za) in H;
    try pose proof (zwrap_range za); try pose proof (zwrap_range zb);
    (destruct lt; [apply Z.ltb_lt in H | apply Z.ltb_ge in H]);
    repeat match goal with |- context [if ?c then _ else _] => let Hc := fresh "Hc" in destruct c eqn:Hc end;
    try apply Forall_nil; (apply Forall_cons; [|apply Forall_nil]); cbn [kentry_ok]; unfold two64m1 in *; lia.
Qed.

Lemma eq_know_ok : forall eq a b, Z.eqb (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b)) = eq ->
  Forall (kentry_ok segs E base) (eq_know eq a b).
Proof.
  intros eq a b H. pose proof (u_range64 (edenot E a)) as Ra. pose proof (u_range64 (edenot E b)) as Rb.
  unfold eq_know.
  destruct a as [za| | | | | | |], b as [zb| | | | | | |]; cbn beta iota; try apply Forall_nil;
    try rewrite (u_lit_wrap E zb) in H; try rewrite (u_lit_wrap E za) in H;
    try pose proof (zwrap_range za); try pose proof (zwrap_range zb);
    (destruct eq; [apply Z.eqb_eq in H | apply Z.eqb_neq in H]);
    repeat match goal with |- context [if ?c then _ else _] => let Hc := fresh "Hc" in destruct c eqn:Hc; [apply Z.eqb_eq in Hc|] end;
    try apply Forall_nil; (apply Forall_cons; [|apply Forall_nil]); cbn [kentry_ok]; unfold two64m1 in *; lia.
Qed.

Lemma signed_lt0 : forall w : word, (bv_signed w <? 0) = (2^63 <=? bv_unsigned w).
Proof.
  intro w. pose proof (kx_u64_range w) as R. rewrite (zb_signed w).
  destruct (Z.ltb_spec (bv_unsigned w) (2^63)); destruct (Z.leb_spec (2^63) (bv_unsigned w)); try lia;
    first [apply Z.ltb_ge; lia | apply Z.ltb_lt; lia].
Qed.

Lemma small63_ok : forall kn e, know_ok segs E base kn -> small63 kn e = true -> bv_signed (edenot E e) = bv_unsigned (edenot E e).
Proof.
  intros kn e HK H. rewrite (zb_signed (edenot E e)).
  assert (R : bv_unsigned (edenot E e) < 2^63).
  { unfold small63 in H.
    assert (G : match erange kn e with Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi (2^63))%bool | None => false end = true ->
                bv_unsigned (edenot E e) < 2^63).
    { destruct (erange kn e) as [[lo hi]|] eqn:Er; [|discriminate]. intro C. apply andb_prop in C as [C0 C1].
      apply Z.ltb_lt in C1. pose proof (erange_sound segs E base kn e lo hi HK Er). lia. }
    destruct e; try exact (G H). rewrite u_lit_wrap. apply Z.ltb_lt in H. exact H. }
  destruct (Z.ltb_spec (bv_unsigned (edenot E e)) (2^63)); [reflexivity | lia].
Qed.

Lemma cmps_know_ok : forall kn lt a b, know_ok segs E base kn -> Z.ltb (bv_signed (edenot E a)) (bv_signed (edenot E b)) = lt ->
  Forall (kentry_ok segs E base) (cmps_know kn lt a b).
Proof.
  intros kn lt a b HK H. pose proof (kx_u64_range (edenot E a)) as Ra.
  assert (GEN : Forall (kentry_ok segs E base) (if (small63 kn a && small63 kn b)%bool then cmpu_know kn lt a b else [])).
  { destruct (small63 kn a && small63 kn b)%bool eqn:C; [|apply Forall_nil]. apply andb_prop in C as [Ca Cb].
    rewrite (small63_ok kn a HK Ca), (small63_ok kn b HK Cb) in H. apply cmpu_know_ok; [exact HK | exact H]. }
  unfold cmps_know.
  destruct a as [za| | | | | | |], b as [zb| | | | | | |]; cbn beta iota; try apply Forall_nil; try exact GEN;
    (destruct zb; try exact GEN); clear GEN;
    change (bv_signed (edenot E (ELit 0))) with 0 in H; rewrite signed_lt0 in H;
    (destruct lt; [apply Z.leb_le in H | apply Z.leb_gt in H]);
    (apply Forall_cons; [|apply Forall_nil]); cbn [kentry_ok]; unfold two64m1; lia.
Qed.

Lemma br_know_ok : forall kn t c a b, know_ok segs E base kn -> branch_taken c (edenot E a) (edenot E b) = t ->
  Forall (kentry_ok segs E base) (br_know kn t c a b).
Proof.
  intros kn t c a b HK H. destruct c; cbn [branch_taken br_know] in *; unfold bv_eqb, bv_ltu, bv_lts in H.
  - apply eq_know_ok. exact H.
  - apply eq_know_ok. rewrite <- H, negb_involutive. reflexivity.
  - apply cmps_know_ok; [exact HK | exact H].
  - apply cmps_know_ok; [exact HK | rewrite <- H, negb_involutive; reflexivity].
  - apply cmpu_know_ok; [exact HK | exact H].
  - apply cmpu_know_ok; [exact HK | rewrite <- H, negb_involutive; reflexivity].
Qed.

Lemma split_know_ok : forall kn t x v, know_ok segs E base kn -> (0 <= v < 2^64)%Z ->
  Z.eqb (bv_unsigned (edenot E x)) v = t -> Forall (kentry_ok segs E base) (split_know kn t x v).
Proof.
  intros kn t x v HK Hv H. unfold split_know. destruct t.
  - apply Z.eqb_eq in H. constructor; [cbn [kentry_ok]; lia | constructor].
  - apply Z.eqb_neq in H. destruct (erange kn x) as [[lo hi]|] eqn:Er; [|constructor].
    destruct (Z.leb 0 lo && Z.eqb v (vs_first lo (vs_step kn x)))%bool eqn:C; [|constructor].
    apply andb_prop in C as [C0 C1]. apply Z.leb_le in C0. apply Z.eqb_eq in C1.
    pose proof (erange_sound segs E base kn x lo hi HK Er) as [R1 R2].
    pose proof (ealign_sound segs E base kn x HK) as [[A0 A1] AD].
    set (u := bv_unsigned (edenot E x)) in *. set (s0 := vs_step kn x) in *.
    assert (S0 : 0 < s0) by (unfold s0, vs_step; apply Z.pow_pos_nonneg; lia).
    assert (SD : (s0 | u)).
    { eapply Z.divide_trans; [|exact AD]. unfold s0, vs_step.
      exists (2 ^ (ealign kn x - Z.min (Z.max 0 (ealign kn x)) 16)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    destruct SD as [q Hq].
    constructor; [|constructor]. cbn [kentry_ok]. fold u. split; [|exact R2].
    unfold vs_first in C1.
    assert (Q : (lo + s0 - 1) / s0 < q + 1).
    { apply Z.div_lt_upper_bound; [exact S0|]. nia. }
    assert (Q2 : (lo + s0 - 1) / s0 <> q) by (intro Hc; apply H; rewrite Hq, C1, Hc; reflexivity).
    rewrite C1, Hq. nia.
Qed.

Lemma kn_enter_ok : forall kn ks, know_ok segs E base kn -> Forall (kentry_ok segs E base) ks -> know_ok segs E base (kn_enter kn ks).
Proof.
  intros kn ks HK Hks. unfold kn_enter. apply Forall_app. split; [|exact HK].
  induction Hks as [|K ks HK1 _ IH]; cbn [map]; constructor; [|exact IH].
  destruct K; cbn [tighten]; try exact HK1.
  destruct (erange kn e) as [[lo0 hi0]|] eqn:Er; [|exact HK1].
  pose proof (erange_sound segs E base kn e lo0 hi0 HK Er). cbn [kentry_ok] in *. lia.
Qed.

End BrKnow.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_call (i : instr) : bool :=
  match i with
  | Jal rd _ => bv_eqb rd 1
  | Jalr rd _ _ => bv_eqb rd 1
  | _ => false
  end.

Definition bc_eqb (x y : branch_cond) : bool :=
  match x, y with
  | BC_EQ, BC_EQ | BC_NE, BC_NE | BC_LT, BC_LT | BC_GE, BC_GE | BC_LTU, BC_LTU | BC_GEU, BC_GEU => true
  | _, _ => false
  end.
Lemma bc_eqb_eq : forall x y, bc_eqb x y = true -> x = y.
Proof. intros [] []; cbn; intros; congruence. Qed.

Definition sc_is_br (t : bool) (scs : list sidecond) : option (branch_cond * expr * expr) :=
  match scs with
  | [SCBr t' c a b] => if Bool.eqb t t' then Some (c, a, b) else None
  | _ => None
  end.

Lemma sc_is_br_some : forall t scs c a b, sc_is_br t scs = Some (c, a, b) -> scs = [SCBr t c a b].
Proof.
  intros t scs c a b H. destruct scs as [|[t' c' a' b'| | | | | |] [|? ?]]; cbn [sc_is_br] in H; try discriminate H.
  destruct (Bool.eqb t t') eqn:Ht; [|discriminate H]. apply Bool.eqb_prop in Ht. subst t'. injection H as -> -> ->. reflexivity.
Qed.

(* [comment removed for export] *)
Definition in_img (kn : list kentry) (lo hi : Z) : bool :=
  existsb (fun K => match K with KImg l h => (Z.leb l lo && Z.leb hi h)%bool | _ => false end) kn.

Definition vs_count (kn : list kentry) (x : expr) : option (Z * Z) :=
  match x with
  | ELit _ => None
  | _ => match erange kn x with
         | Some (lo, hi) =>
             if Z.leb 0 lo then
               let s := vs_step kn x in let v := vs_first lo s in
               if (Z.leb v hi && Z.ltb v (2^64))%bool then Some (v, (hi - v) / s + 1) else None
             else None
         | None => None
         end
  end.

Fixpoint vs_best (kn : list kentry) (vmax : Z) (cands : list expr) (best : option (expr * Z * Z)) : option (expr * Z * Z) :=
  match cands with
  | [] => best
  | x :: r =>
      match vs_count kn x with
      | Some (v, c) =>
          if (Z.leb 2 c && Z.leb c vmax && match best with Some (_, _, c0) => Z.ltb c c0 | None => true end)%bool
          then vs_best kn vmax r (Some (x, v, c)) else vs_best kn vmax r best
      | None => vs_best kn vmax r best
      end
  end.

Definition split_hint (vmax : Z) (i : instr) (ss : sym_state) : option (expr * Z) :=
  if Z.leb vmax 1 then None else
  match i with
  | Load msz _ _ rs imm =>
      let kn := s_know ss in
      let a := to_saddrK (facts_of kn) (sr_get (s_regs ss) rs) (bv_signed imm) in
      match a_base a with
      | ELit _ => None
      | b => match erange kn b with
             | Some (lo, hi) =>
                 if in_img kn (lo + a_off a) (hi + a_off a + Z.of_nat (msize_bytes msz)) then
                   match vs_best kn vmax (nubE (subexprs b)) None with
                   | Some (x, v, _) => Some (x, v)
                   | None => None
                   end
                 else None
             | None => None
             end
      end
  | _ => None
  end.

Lemma vs_count_range : forall kn x v c, vs_count kn x = Some (v, c) -> 0 <= v < 2^64.
Proof.
  intros kn x v c H. unfold vs_count in H.
  assert (G : match erange kn x with
              | Some (lo, hi) =>
                  if Z.leb 0 lo then
                    if (Z.leb (vs_first lo (vs_step kn x)) hi && Z.ltb (vs_first lo (vs_step kn x)) (2^64))%bool
                    then Some (vs_first lo (vs_step kn x), (hi - vs_first lo (vs_step kn x)) / vs_step kn x + 1) else None
                  else None
              | None => None
              end = Some (v, c)) by (destruct x; try discriminate H; exact H).
  clear H. destruct (erange kn x) as [[lo hi]|]; [|discriminate G].
  destruct (Z.leb 0 lo) eqn:L0; [|discriminate G]. apply Z.leb_le in L0.
  destruct (Z.leb (vs_first lo (vs_step kn x)) hi && Z.ltb (vs_first lo (vs_step kn x)) (2^64))%bool eqn:L1; [|discriminate G].
  injection G as <- <-. apply andb_prop in L1 as [_ L2]. apply Z.ltb_lt in L2. split; [|exact L2].
  unfold vs_first. assert (0 < vs_step kn x) by (unfold vs_step; apply Z.pow_pos_nonneg; lia).
  apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia | lia].
Qed.

Lemma vs_best_range : forall kn vmax cands best,
  (forall y w c, best = Some (y, w, c) -> 0 <= w < 2^64) ->
  forall y w c, vs_best kn vmax cands best = Some (y, w, c) -> 0 <= w < 2^64.
Proof.
  intros kn vmax. induction cands as [|y0 r IH]; intros best Hbest y w c H; cbn [vs_best] in H; [exact (Hbest _ _ _ H)|].
  destruct (vs_count kn y0) as [[w0 c1]|] eqn:Hvc; [|exact (IH _ Hbest _ _ _ H)].
  destruct (Z.leb 2 c1 && Z.leb c1 vmax && match best with Some (_, _, c2) => Z.ltb c1 c2 | None => true end)%bool;
    [|exact (IH _ Hbest _ _ _ H)].
  refine (IH _ _ _ _ _ H). intros y1 w1 c2 Heq. injection Heq as <- <- <-. exact (vs_count_range kn y0 w0 c1 Hvc).
Qed.

Lemma split_hint_range : forall vmax i ss x v, split_hint vmax i ss = Some (x, v) -> 0 <= v < 2^64.
Proof.
  intros vmax i ss x v H. unfold split_hint in H. destruct (Z.leb vmax 1); [discriminate H|].
  destruct i; try discriminate H.
  set (a := to_saddrK (facts_of (s_know ss)) (sr_get (s_regs ss) rs1) (bv_signed imm)) in *.
  assert (G : match erange (s_know ss) (a_base a) with
              | Some (lo, hi) =>
                  if in_img (s_know ss) (lo + a_off a) (hi + a_off a + Z.of_nat (msize_bytes sz)) then
                    match vs_best (s_know ss) vmax (nubE (subexprs (a_base a))) None with
                    | Some (x, v, _) => Some (x, v)
                    | None => None
                    end
                  else None
              | None => None
              end = Some (x, v)) by (destruct (a_base a); try discriminate H; exact H).
  clear H. destruct (erange (s_know ss) (a_base a)) as [[lo hi]|]; [|discriminate G].
  destruct (in_img _ _ _); [|discriminate G].
  destruct (vs_best (s_know ss) vmax (nubE (subexprs (a_base a))) None) as [[[x0 v0] c0]|] eqn:Hb; [|discriminate G].
  injection G as <- <-. exact (vs_best_range _ _ _ None ltac:(intros; discriminate) _ _ _ Hb).
Qed.

Section Tree.
Variable segs : list Segment.
Variable vmax : Z.

Fixpoint kx_tree (fuel : nat) (first : bool) (stops : list Z) (scalls : bool) (ss : sym_state)
                 (acc : list sidecond) (accs : list (saddr * nat)) : ktree :=
  match fuel with
  | O => KLeaf ss acc accs
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then KLeaf ss acc accs else
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => KLeaf ss acc accs
      | Some w =>
          if is_ecall w then KLeaf ss acc accs else
          match decode_any w with
          | None => KLeaf ss acc accs
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then KLeaf ss acc accs else
              match split_hint vmax i ss with
              | Some (x, v) =>
                  let t1 := kx_tree f first stops scalls (kt_enter ss 0 (split_know (s_know ss) true x v)) [] [] in
                  let t2 := kx_tree f first stops scalls (kt_enter ss (kt_next t1) (split_know (s_know ss) false x v)) [] [] in
                  KSplit x v acc accs t1 t2
              | None =>
              match acc_sym (facts_of (s_know ss)) i ss with
              | None => KLeaf ss acc accs
              | Some la =>
                  match sym_step segs i ss scr_nil with
                  | SOk ss' scs _ =>
                      if s_clean ss' then
                        (if (scalls && is_call i)%bool then KLeaf ss' (sc_add scs acc) (la ++ accs)
                         else kx_tree f false stops scalls ss' (sc_add scs acc) (la ++ accs))
                      else KLeaf ss acc accs
                  | SStop =>
                      match sym_step segs i ss (SCR [true] [] []), sym_step segs i ss (SCR [false] [] []) with
                      | SOk sst scst _, SOk ssf scsf _ =>
                          match sc_is_br true scst, sc_is_br false scsf with
                          | Some (c, a, b), Some (c', a', b') =>
                              if (bc_eqb c c' && expr_eqb a a' && expr_eqb b b' && s_clean sst && s_clean ssf)%bool then
                                (* [comment removed for export] *)
                                let t1 := kx_tree f false stops scalls (kt_enter sst 0 (br_know (s_know ss) true c a b)) [] [] in
                                let t2 := kx_tree f false stops scalls (kt_enter ssf (kt_next t1) (br_know (s_know ss) false c a b)) [] [] in
                                KFork c a b acc (la ++ accs) t1 t2
                              else KLeaf ss acc accs
                          | _, _ => KLeaf ss acc accs
                          end
                      | _, _ => KLeaf ss acc accs
                      end
                  end
              end
              end
          end
      end
  end.

End Tree.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TreeSound.
Variable segs : list Segment.
Variable vmax : Z.
Variables (F : bvmap 5 word) (fc : bv 32).
Variable E : env.
Variable base rom : word -> option byte.
Variable RNG : footprint.

Variable MI0 : Prop.
Variable Q : machine_state -> Prop.

(* [comment removed for export] *)
Definition PO (scs' : list sidecond) (accs' : list (saddr * nat)) : Prop :=
  scs_denot segs base E scs' /\ Forall (accP E RNG) accs'.
Definition PC (ss' : sym_state) : Prop :=
  forall regs', regs_ok E (s_regs ss') regs' -> rfull regs' -> log_flat E (s_log ss') ->
     (MI0 -> mem_inv segs (mem_denot E base (s_log ss'))) ->
     evtF segs RNG Q (MS regs' F (Z_to_bv 64 (s_pc ss')) fc None (mem_denot E base (s_log ss')) rom).

Fixpoint kt_obl (t : ktree) : Prop :=
  match t with
  | KLeaf ss scs accs => PO scs accs /\ PC ss
  | KFork c a b scs accs t1 t2 =>
      PO scs accs /\
      (branch_taken c (edenot E a) (edenot E b) = true -> kt_obl t1) /\
      (branch_taken c (edenot E a) (edenot E b) = false -> kt_obl t2)
  | KSplit x v scs accs t1 t2 =>
      PO scs accs /\
      (branch_taken BC_EQ (edenot E x) (edenot E (ELit v)) = true -> kt_obl t1) /\
      (branch_taken BC_EQ (edenot E x) (edenot E (ELit v)) = false -> kt_obl t2)
  end.

Lemma split_eqb : forall x v t, (0 <= v < 2^64)%Z -> branch_taken BC_EQ (edenot E x) (edenot E (ELit v)) = t ->
  Z.eqb (bv_unsigned (edenot E x)) v = t.
Proof.
  intros x v t Hv H. cbn [branch_taken edenot] in H. unfold bv_eqb in H.
  rewrite Z_to_bv_unsigned, bv_wrap_small in H by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); exact Hv). exact H.
Qed.

(* [comment removed for export] *)
Lemma kx_tree_acc : forall fuel first stops scalls ss acc accs,
  kt_obl (kx_tree segs vmax fuel first stops scalls ss acc accs) -> PO acc accs.
Proof.
  induction fuel as [|f IH]; intros first stops scalls ss acc accs H; cbn [kx_tree] in H.
  - exact (proj1 H).
  - destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [exact (proj1 H)|].
    destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|]; [|exact (proj1 H)].
    destruct (is_ecall w); [exact (proj1 H)|].
    destruct (decode_any w) as [[i sz]|]; [|exact (proj1 H)].
    destruct (negb (Z.eqb sz 4)); [exact (proj1 H)|].
    destruct (split_hint vmax i ss) as [[x v]|]; [exact (proj1 H)|].
    destruct (acc_sym (facts_of (s_know ss)) i ss) as [la|]; [|exact (proj1 H)].
    destruct (sym_step segs i ss scr_nil) as [ss' scs scr'|].
    + destruct (s_clean ss'); [|exact (proj1 H)].
      assert (X : PO (sc_add scs acc) (la ++ accs)).
      { destruct (scalls && is_call i)%bool; [exact (proj1 H) | exact (IH _ _ _ _ _ _ H)]. }
      destruct X as [X1 X2]. split; [exact (proj2 (sc_add_denot segs base E scs acc X1)) | exact (proj2 (proj1 (Forall_app _ _ _) X2))].
    + destruct (sym_step segs i ss (SCR [true] [] [])) as [sst scst ?|]; [|exact (proj1 H)].
      destruct (sym_step segs i ss (SCR [false] [] [])) as [ssf scsf ?|]; [|exact (proj1 H)].
      destruct (sc_is_br true scst) as [[[c a] b]|]; [|exact (proj1 H)].
      destruct (sc_is_br false scsf) as [[[c' a'] b']|]; [|exact (proj1 H)].
      destruct (bc_eqb c c' && expr_eqb a a' && expr_eqb b b' && s_clean sst && s_clean ssf)%bool; [|exact (proj1 H)].
      cbn [kt_obl] in H. destruct H as [[X1 X2] _]. split; [exact X1 | exact (proj2 (proj1 (Forall_app _ _ _) X2))].
Qed.

Lemma kx_tree_sound : forall fuel first stops scalls ss acc accs,
  s_resv ss = None ->
  kt_obl (kx_tree segs vmax fuel first stops scalls ss acc accs) ->
  forall regs, regs_ok E (s_regs ss) regs -> rfull regs -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  (MI0 -> mem_inv segs (mem_denot E base (s_log ss))) ->
  evtF segs RNG Q (MS regs F (Z_to_bv 64 (s_pc ss)) fc None (mem_denot E base (s_log ss)) rom).
Proof.
  induction fuel as [|f IH]; intros first stops scalls ss acc accs Hc H regs Hr Hfu Hlf Hkn Hmi; cbn [kx_tree] in H.
  - destruct H as (_ & K). exact (K regs Hr Hfu Hlf Hmi).
  - assert (Hleaf : kt_obl (KLeaf ss acc accs) ->
              evtF segs RNG Q (MS regs F (Z_to_bv 64 (s_pc ss)) fc None (mem_denot E base (s_log ss)) rom)).
    { intros (_ & K). exact (K regs Hr Hfu Hlf Hmi). }
    destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [exact (Hleaf H)|].
    destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|] eqn:Hf; [|exact (Hleaf H)].
    destruct (is_ecall w) eqn:He; [exact (Hleaf H)|].
    destruct (decode_any w) as [[i sz]|] eqn:Hd; [|exact (Hleaf H)].
    destruct (Z.eqb sz 4) eqn:Hsz; cbn [negb] in H; [|exact (Hleaf H)].
    apply Z.eqb_eq in Hsz. subst sz.
    destruct (split_hint vmax i ss) as [[x v]|] eqn:Hsp.
    { (* [comment removed for export] *)
      pose proof (split_hint_range vmax i ss x v Hsp) as Hv.
      cbn [kt_obl] in H. destruct H as (_ & HT1 & HT2).
      destruct (branch_taken BC_EQ (edenot E x) (edenot E (ELit v))) eqn:C.
      - refine (IH _ _ _ (kt_enter ss 0 (split_know (s_know ss) true x v)) _ _ Hc (HT1 eq_refl) regs Hr Hfu Hlf _ Hmi).
        cbn [kt_enter s_know]. exact (kn_enter_ok segs E base _ _ Hkn (split_know_ok segs E base _ true x v Hkn Hv (split_eqb x v true Hv C))).
      - refine (IH _ _ _ (kt_enter ss _ (split_know (s_know ss) false x v)) _ _ Hc (HT2 eq_refl) regs Hr Hfu Hlf _ Hmi).
        cbn [kt_enter s_know]. exact (kn_enter_ok segs E base _ _ Hkn (split_know_ok segs E base _ false x v Hkn Hv (split_eqb x v false Hv C))). }
    destruct (acc_sym (facts_of (s_know ss)) i ss) as [la|] eqn:Ha; [|exact (Hleaf H)].
    destruct (sym_step segs i ss scr_nil) as [ss' scs scr'|] eqn:Hs.
    + destruct (s_clean ss') eqn:Hcl; [|exact (Hleaf H)]. apply s_clean_None in Hcl.
      assert (X : PO (sc_add scs acc) (la ++ accs)).
      { destruct (scalls && is_call i)%bool; [exact (proj1 H) | exact (kx_tree_acc _ _ _ _ _ _ _ H)]. }
      destruct X as [X1 X2].
      pose proof (proj1 (sc_add_denot segs base E scs acc X1)) as Hscs.
      pose proof (proj1 (proj1 (Forall_app _ _ _) X2)) as Hla.
      destruct (kx_step_sound segs F fc E base rom RNG ss regs i ss' scs scr_nil scr' w la Hf He Hd Hs Ha Hc Hcl Hscs Hla Hr Hfu Hlf Hkn)
        as (regs1 & Hstep & Hr1 & Hfu1 & Hlf1 & Hkn1 & Hmi1).
      eapply evtF_step; [exact Hstep|].
      destruct (scalls && is_call i)%bool.
      * destruct H as (_ & K). exact (K regs1 Hr1 Hfu1 Hlf1 (fun X => Hmi1 (Hmi X))).
      * exact (IH _ _ _ _ _ _ Hcl H regs1 Hr1 Hfu1 Hlf1 Hkn1 (fun X => Hmi1 (Hmi X))).
    + destruct (sym_step segs i ss (SCR [true] [] [])) as [sst scst scrt|] eqn:Hst; [|exact (Hleaf H)].
      destruct (sym_step segs i ss (SCR [false] [] [])) as [ssf scsf scrf|] eqn:Hsf; [|exact (Hleaf H)].
      destruct (sc_is_br true scst) as [[[c a] b]|] eqn:Bt; [|exact (Hleaf H)].
      destruct (sc_is_br false scsf) as [[[c' a'] b']|] eqn:Bf; [|exact (Hleaf H)].
      destruct (bc_eqb c c' && expr_eqb a a' && expr_eqb b b' && s_clean sst && s_clean ssf)%bool eqn:Hchk; [|exact (Hleaf H)].
      repeat (apply andb_prop in Hchk as [Hchk ?]).
      apply bc_eqb_eq in Hchk. subst c'.
      repeat match goal with X : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in X end. subst a' b'.
      repeat match goal with X : s_clean _ = true |- _ => apply s_clean_None in X end.
      apply sc_is_br_some in Bt, Bf. subst scst scsf.
      cbn [kt_obl] in H. destruct H as ([_ X2] & HT1 & HT2).
      pose proof (proj1 (proj1 (Forall_app _ _ _) X2)) as Hla.
      destruct (branch_taken c (edenot E a) (edenot E b)) eqn:C.
      * specialize (HT1 eq_refl).
        assert (Hscs : scs_denot segs base E [SCBr true c a b]) by (constructor; [exact C | constructor]).
        destruct (kx_step_sound segs F fc E base rom RNG ss regs i sst _ _ scrt w la Hf He Hd Hst Ha Hc ltac:(assumption) Hscs Hla Hr Hfu Hlf Hkn)
          as (regs1 & Hstep & Hr1 & Hfu1 & Hlf1 & Hkn1 & Hmi1).
        eapply evtF_step; [exact Hstep|].
        refine (IH _ _ _ (kt_enter sst 0 (br_know (s_know ss) true c a b)) _ _ _ HT1 regs1 Hr1 Hfu1 Hlf1 _ (fun X => Hmi1 (Hmi X))); [assumption|].
        cbn [kt_enter s_know]. exact (kn_enter_ok segs E base _ _ Hkn1 (br_know_ok segs E base (s_know ss) true c a b Hkn C)).
      * specialize (HT2 eq_refl).
        assert (Hscs : scs_denot segs base E [SCBr false c a b]) by (constructor; [exact C | constructor]).
        destruct (kx_step_sound segs F fc E base rom RNG ss regs i ssf _ _ scrf w la Hf He Hd Hsf Ha Hc ltac:(assumption) Hscs Hla Hr Hfu Hlf Hkn)
          as (regs1 & Hstep & Hr1 & Hfu1 & Hlf1 & Hkn1 & Hmi1).
        eapply evtF_step; [exact Hstep|].
        refine (IH _ _ _ (kt_enter ssf _ (br_know (s_know ss) false c a b)) _ _ _ HT2 regs1 Hr1 Hfu1 Hlf1 _ (fun X => Hmi1 (Hmi X))); [assumption|].
        cbn [kt_enter s_know]. exact (kn_enter_ok segs E base _ _ Hkn1 (br_know_ok segs E base (s_know ss) false c a b Hkn C)).
Qed.

End TreeSound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive vtree : Type :=
| VLeaf (pc : Z) (sr : list expr) (log : list sentry) (rest : list sidecond) (arest : list (saddr * nat))
| VFork (c : branch_cond) (a b : expr) (rest : list sidecond) (arest : list (saddr * nat)) (p1 p2 : vtree).

Fixpoint kt_scs (t : ktree) : list sidecond :=
  match t with
  | KLeaf _ scs _ => scs
  | KFork _ _ _ scs _ t1 t2 => scs ++ kt_scs t1 ++ kt_scs t2
  | KSplit _ _ scs _ t1 t2 => scs ++ kt_scs t1 ++ kt_scs t2
  end.

(* [comment removed for export] *)
Definition sc_rest (kn : list kentry) (rs : list zreg) (scs : list sidecond) : list sidecond :=
  List.filter (fun sc => negb (sc_auto kn rs sc)) scs.
Definition acc_rest (kn : list kentry) (ws : list zreg) (accs : list (saddr * nat)) : list (saddr * nat) :=
  List.filter (fun an => negb (acc_auto kn ws an)) accs.
Definition node_chk (kn : list kentry) (rs ws : list zreg) (scs rest : list sidecond) (accs arest : list (saddr * nat)) : bool :=
  forallb (fun sc => sc_auto kn rs sc || sc_memx sc rest) scs && forallb (fun an => acc_auto kn ws an || acc_mem an arest) accs.

Fixpoint kt_resid (kn : list kentry) (rs ws : list zreg) (t : ktree) : vtree :=
  match t with
  | KLeaf ss scs accs => VLeaf (s_pc ss) (s_regs ss) (s_log ss) (sc_rest kn rs scs) (acc_rest kn ws accs)
  | KFork c a b scs accs t1 t2 =>
      VFork c a b (sc_rest kn rs scs) (acc_rest kn ws accs)
            (kt_resid (kn_enter kn (br_know kn true c a b)) rs ws t1) (kt_resid (kn_enter kn (br_know kn false c a b)) rs ws t2)
  | KSplit x v scs accs t1 t2 =>
      VFork BC_EQ x (ELit v) (sc_rest kn rs scs) (acc_rest kn ws accs)
            (kt_resid (kn_enter kn (split_know kn true x v)) rs ws t1) (kt_resid (kn_enter kn (split_know kn false x v)) rs ws t2)
  end.

Fixpoint list_eqb {A : Type} (eqb : A -> A -> bool) (x y : list A) : bool :=
  match x, y with
  | [], [] => true
  | a :: x', b :: y' => eqb a b && list_eqb eqb x' y'
  | _, _ => false
  end.
Lemma list_eqb_eq : forall {A} (eqb : A -> A -> bool), (forall a b, eqb a b = true -> a = b) ->
  forall x y, list_eqb eqb x y = true -> x = y.
Proof.
  intros A eqb H. induction x as [|a x IH]; intros [|b y] E; cbn in E; try discriminate; [reflexivity|].
  apply andb_prop in E as [E1 E2]. rewrite (H _ _ E1), (IH _ E2). reflexivity.
Qed.
Definition sentry_eqb (x y : sentry) : bool :=
  saddr_eqb (e_addr x) (e_addr y) && Nat.eqb (e_width x) (e_width y) && expr_eqb (e_val x) (e_val y).
Lemma sentry_eqb_eq : forall x y, sentry_eqb x y = true -> x = y.
Proof.
  intros [a w v] [a' w' v'] E. unfold sentry_eqb in E. cbn [e_addr e_width e_val] in E.
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply saddr_eqb_eq in E1. apply Nat.eqb_eq in E2. apply expr_eqb_eq in E3. subst. reflexivity.
Qed.

Fixpoint kt_chk (kn : list kentry) (rs ws : list zreg) (t : ktree) (p : vtree) : bool :=
  match t, p with
  | KLeaf ss scs accs, VLeaf pc sr log rest arest =>
      Z.eqb (s_pc ss) pc && list_eqb expr_eqb (s_regs ss) sr && list_eqb sentry_eqb (s_log ss) log &&
      node_chk kn rs ws scs rest accs arest
  | KFork c a b scs accs t1 t2, VFork c' a' b' rest arest p1 p2 =>
      bc_eqb c c' && expr_eqb a a' && expr_eqb b b' &&
      node_chk kn rs ws scs rest accs arest &&
      kt_chk (kn_enter kn (br_know kn true c a b)) rs ws t1 p1 && kt_chk (kn_enter kn (br_know kn false c a b)) rs ws t2 p2
  | KSplit x v scs accs t1 t2, VFork c' a' b' rest arest p1 p2 =>
      bc_eqb BC_EQ c' && expr_eqb x a' && expr_eqb (ELit v) b' && Z.leb 0 v && Z.ltb v (2^64) &&
      node_chk kn rs ws scs rest accs arest &&
      kt_chk (kn_enter kn (split_know kn true x v)) rs ws t1 p1 && kt_chk (kn_enter kn (split_know kn false x v)) rs ws t2 p2
  | _, _ => false
  end.

Definition kt_init (pc : Z) (rz : list zexp) (kn : list kentry) (nz : nat) : sym_state :=
  SS pc (ELit 0 :: map zx rz) [] kn nz.

(* [comment removed for export] *)
Definition kt_chk_all (zs : list Z) (rz : list zexp) (zks : list zk) (rk : list kentry) (rs ws : list zreg)
                      (reads : list rdspec) (t : ktree) (r : vtree) : bool :=
  let nz := length zs in
  forallb (zwf nz) rz && rds_chk nz 0 reads && forallb (sc_rd_chk nz reads) (kt_scs t) && forallb (rk_chk (map zk_kentry zks) (zk_tfs zks) nz reads) rk
  && forallb (zk_wf nz) zks && forallb (zreg_wf nz) rs && forallb (zreg_wf nz) ws
  && kt_chk (map zk_kentry zks ++ rk) rs ws t r.

Section TreeGo.
Variable segs : list Segment.
Variables (F : bvmap 5 word) (fc : bv 32).

(* [comment removed for export] *)
Fixpoint kt_obl2 (E : env) (PO2 : list sidecond -> list (saddr * nat) -> Prop) (PC2 : Z -> list expr -> list sentry -> Prop) (p : vtree) : Prop :=
  match p with
  | VLeaf pc sr log rest arest => PO2 rest arest /\ PC2 pc sr log
  | VFork c a b rest arest p1 p2 =>
      PO2 rest arest /\
      (branch_taken c (edenot E a) (edenot E b) = true -> kt_obl2 E PO2 PC2 p1) /\
      (branch_taken c (edenot E a) (edenot E b) = false -> kt_obl2 E PO2 PC2 p2)
  end.

Lemma evt_evtF_top : forall (Q : machine_state -> Prop) ms, evt segs Q ms -> evtF segs (fun _ _ => True) Q ms.
Proof.
  intros Q ms (ms' & Hs & HQ). exists ms'. split; [|exact HQ]. clear HQ.
  induction Hs as [|a b c [Hsvc Hst] _ IH]; [constructor|]. econstructor; [|exact IH].
  split; [exact Hsvc|]. unfold RiscvSemantics.step in Hst.
  destruct (RiscvSemantics.step_accesses segs a) as [[v accs]| |]; cbn in Hst; try discriminate Hst.
  injection Hst as ->. exists accs. split; [reflexivity|]. apply Forall_forall. intros x _. exact I.
Qed.

Section WithE.
Variable m rom : word -> option byte.
Variable RNG : footprint.
Variable Q : machine_state -> Prop.
Variables (zs : list Z) (rs ws : list zreg) (reads : list rdspec).
Variable E : env.
Hypothesis HA : atoms_ok zs E.
Hypothesis HRD : reads_ok segs m (length zs) reads E.
Hypothesis HWR : forallb (zreg_wf (length zs)) rs = true.
Hypothesis HWW : forallb (zreg_wf (length zs)) ws = true.
Hypothesis HRS : Forall (zreg_prop segs m zs) rs.
Hypothesis HWS : Forall (zwin_prop RNG zs) ws.

Definition PO2 (rest : list sidecond) (arest : list (saddr * nat)) : Prop :=
  Forall (sc_resid segs m E) rest /\ Forall (accP E RNG) arest.
Definition PC2 (pc' : Z) (sr' : list expr) (log' : list sentry) : Prop :=
  log_flat E log' -> (mem_inv segs m -> mem_inv segs (mem_denot E m log')) ->
  evtF segs RNG Q (MS (kx_regs E sr') F (Z_to_bv 64 pc') fc None (mem_denot E m log') rom).

Lemma node_chk_sound : forall kn scs rest accs arest, know_ok segs E m kn ->
  forallb (sc_rd_chk (length zs) reads) scs = true ->
  node_chk kn rs ws scs rest accs arest = true -> PO2 rest arest -> PO segs E m RNG scs accs.
Proof.
  intros kn scs rest accs arest HK Hrd Hc [H1 H2]. unfold node_chk in Hc. apply andb_prop in Hc as [Hc1 Hc2]. split.
  - pose proof (kx_scs_bulk segs m zs E kn rs scs rest HA HK HWR HRS Hc1 H1) as Hall.
    unfold scs_denot. rewrite Forall_forall in *. rewrite forallb_forall in Hrd.
    intros sc Hin. exact (kx_readbase segs m _ reads E sc HRD (Hrd sc Hin) (Hall sc Hin)).
  - exact (kx_accs_bulk segs m RNG zs E kn ws accs arest HA HK HWW HWS Hc2 H2).
Qed.

Lemma kt_chk_sound : forall t r kn, know_ok segs E m kn ->
  forallb (sc_rd_chk (length zs) reads) (kt_scs t) = true ->
  kt_chk kn rs ws t r = true -> kt_obl2 E PO2 PC2 r ->
  kt_obl segs F fc E m rom RNG (mem_inv segs m) Q t.
Proof.
  induction t as [ss scs accs | c a b scs accs t1 IH1 t2 IH2 | x v scs accs t1 IH1 t2 IH2]; intros r kn HK Hrd Hc H;
    destruct r as [pc sr log rest arest | c' a' b' rest arest r1 r2]; cbn [kt_chk kt_obl2] in *;
    try discriminate Hc.
  - repeat (apply andb_prop in Hc as [Hc ?]).
    apply Z.eqb_eq in Hc.
    match goal with X : list_eqb expr_eqb _ _ = true |- _ => apply (list_eqb_eq expr_eqb expr_eqb_eq) in X; rename X into Hsr end.
    match goal with X : list_eqb sentry_eqb _ _ = true |- _ => apply (list_eqb_eq sentry_eqb sentry_eqb_eq) in X; rename X into Hlog end.
    destruct H as (H' & K). cbn [kt_obl kt_scs] in *. split.
    + exact (node_chk_sound kn scs rest accs arest HK Hrd ltac:(assumption) H').
    + intros regs' Hr Hfu Hlf Hmi. rewrite (regs_ok_full_eq E _ regs' Hr Hfu). rewrite Hc, Hsr, Hlog in *. exact (K Hlf Hmi).
  - repeat (apply andb_prop in Hc as [Hc ?]).
    apply bc_eqb_eq in Hc. subst c'.
    repeat match goal with X : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in X end. subst a' b'.
    cbn [kt_scs] in Hrd. rewrite !forallb_app in Hrd. apply andb_prop in Hrd as [Hrd0 Hrd]. apply andb_prop in Hrd as [Hrd1 Hrd2].
    destruct H as (H' & HT1 & HT2). cbn [kt_obl]. split; [exact (node_chk_sound kn scs rest accs arest HK Hrd0 ltac:(assumption) H')|].
    split; intro C.
    + apply (IH1 r1 (kn_enter kn (br_know kn true c a b))); [|assumption|assumption|exact (HT1 C)].
      exact (kn_enter_ok segs E m _ _ HK (br_know_ok segs E m kn true c a b HK C)).
    + apply (IH2 r2 (kn_enter kn (br_know kn false c a b))); [|assumption|assumption|exact (HT2 C)].
      exact (kn_enter_ok segs E m _ _ HK (br_know_ok segs E m kn false c a b HK C)).
  - repeat (apply andb_prop in Hc as [Hc ?]).
    apply bc_eqb_eq in Hc. subst c'.
    repeat match goal with X : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in X end. subst a' b'.
    assert (Hv : 0 <= v < 2^64) by (split; [apply Z.leb_le | apply Z.ltb_lt]; assumption).
    cbn [kt_scs] in Hrd. rewrite !forallb_app in Hrd. apply andb_prop in Hrd as [Hrd0 Hrd]. apply andb_prop in Hrd as [Hrd1 Hrd2].
    destruct H as (H' & HT1 & HT2). cbn [kt_obl]. split; [exact (node_chk_sound kn scs rest accs arest HK Hrd0 ltac:(assumption) H')|].
    split; intro C.
    + apply (IH1 r1 (kn_enter kn (split_know kn true x v))); [|assumption|assumption|exact (HT1 C)].
      exact (kn_enter_ok segs E m _ _ HK (split_know_ok segs E m kn true x v HK Hv (split_eqb E x v true Hv C))).
    + apply (IH2 r2 (kn_enter kn (split_know kn false x v))); [|assumption|assumption|exact (HT2 C)].
      exact (kn_enter_ok segs E m _ _ HK (split_know_ok segs E m kn false x v HK Hv (split_eqb E x v false Hv C))).
Qed.

End WithE.

Theorem kx_tree_evtF : forall RNG (Q : machine_state -> Prop) vmax fuel stops scalls zs rz xs zks rk pc m rom t r reads rs ws,
  kx_tree segs vmax fuel true stops scalls (kt_init pc rz (map zk_kentry zks ++ rk) (length zs)) [] [] = t ->
  kt_chk_all zs rz zks rk rs ws reads t r = true ->
  Forall2 (fun e x => x = Z_to_bv 64 (zden zs e)) rz xs ->
  Forall (zk_prop segs m zs) zks ->
  Forall (zreg_prop segs m zs) rs ->
  Forall (zwin_prop RNG zs) ws ->
  (forall E, kx_env_ok segs m zs reads E -> know_ok segs E m (map zk_kentry zks ++ rk) ->
     kt_obl2 E (PO2 m RNG E) (PC2 m rom RNG Q E) r) ->
  evtF segs RNG Q (MS (mkRl xs) F (Z_to_bv 64 pc) fc None m rom).
Proof.
  intros RNG Q vmax fuel stops scalls zs rz xs zks rk pc m rom t r reads rs ws Hex Hchk Hregs Hzk Hrs Hws K.
  unfold kt_chk_all in Hchk. repeat (apply andb_prop in Hchk as [Hchk ?]).
  pose proof (kx_env_exists segs m zs reads ltac:(assumption)) as HE.
  set (E := kx_env (kx_vals segs m (map (Z_to_bv 64) zs) reads)) in *.
  assert (Hkn : know_ok segs E m (map zk_kentry zks ++ rk)).
  { assert (Hk0 : know_ok segs E m (map zk_kentry zks)) by (apply (zks_ent segs m zs E zks (proj1 HE)); assumption).
    assert (Htf : Forall (tf_ok segs m E) (zk_tfs zks)) by (apply (zk_tfs_ok segs m zs E zks (proj1 HE)); assumption).
    apply Forall_app. split; [exact Hk0|].
    apply Forall_forall. intros K0 HK0.
    match goal with X : forallb (rk_chk _ _ _ _) rk = true |- _ =>
      rewrite forallb_forall in X; exact (rk_chk_ok segs m _ _ _ reads E K0 (proj2 HE) Hk0 Htf (X K0 HK0)) end. }
  pose proof (kt_chk_sound m rom RNG Q zs rs ws reads E (proj1 HE) (proj2 HE) ltac:(assumption) ltac:(assumption) Hrs Hws
                t r _ Hkn ltac:(assumption) ltac:(assumption) (K E HE Hkn)) as Hobl.
  rewrite <- Hex in Hobl.
  exact (kx_tree_sound segs vmax F fc E m rom RNG (mem_inv segs m) Q fuel true stops scalls
           (kt_init pc rz (map zk_kentry zks ++ rk) (length zs)) [] [] eq_refl Hobl
           (mkRl xs) (regs_ok_init zs E rz xs (proj1 HE) ltac:(assumption) Hregs) (rfull_mkRl xs) I Hkn (fun X => X)).
Qed.

(* [comment removed for export] *)
Definition PO1 (m : word -> option byte) (E : env) (rest : list sidecond) (arest : list (saddr * nat)) : Prop :=
  Forall (sc_resid segs m E) rest.
Definition PC1 (m rom : word -> option byte) (Q : machine_state -> Prop) (E : env) (pc' : Z) (sr' : list expr) (log' : list sentry) : Prop :=
  log_flat E log' -> (mem_inv segs m -> mem_inv segs (mem_denot E m log')) ->
  evt segs Q (MS (kx_regs E sr') F (Z_to_bv 64 pc') fc None (mem_denot E m log') rom).

Lemma kt_obl2_top : forall m rom Q E r,
  kt_obl2 E (PO1 m E) (PC1 m rom Q E) r -> kt_obl2 E (PO2 m (fun _ _ => True) E) (PC2 m rom (fun _ _ => True) Q E) r.
Proof.
  intros m rom Q E.
  assert (T : forall arest, Forall (accP E (fun _ _ => True)) arest) by (intro; apply Forall_forall; intros x _; exact I).
  induction r as [pc sr log rest arest | c a b rest arest r1 IH1 r2 IH2]; intros H; cbn [kt_obl2] in *.
  - destruct H as [H1 K]. split; [split; [exact H1 | apply T]|].
    intros Hlf Hmi. apply evt_evtF_top. exact (K Hlf Hmi).
  - destruct H as (H0 & H1 & H2). split; [split; [exact H0 | apply T]|]. split; intro C; [exact (IH1 (H1 C)) | exact (IH2 (H2 C))].
Qed.

Theorem kx_tree_evt : forall (Q : machine_state -> Prop) vmax fuel stops scalls zs rz xs zks rk pc m rom t r reads rs,
  kx_tree segs vmax fuel true stops scalls (kt_init pc rz (map zk_kentry zks ++ rk) (length zs)) [] [] = t ->
  kt_chk_all zs rz zks rk rs [] reads t r = true ->
  Forall2 (fun e x => x = Z_to_bv 64 (zden zs e)) rz xs ->
  Forall (zk_prop segs m zs) zks ->
  Forall (zreg_prop segs m zs) rs ->
  (forall E, kx_env_ok segs m zs reads E -> know_ok segs E m (map zk_kentry zks ++ rk) ->
     kt_obl2 E (PO1 m E) (PC1 m rom Q E) r) ->
  evt segs Q (MS (mkRl xs) F (Z_to_bv 64 pc) fc None m rom).
Proof.
  intros Q vmax fuel stops scalls zs rz xs zks rk pc m rom t r reads rs Hex Hchk Hregs Hzk Hrs K.
  apply (evtF_evt segs (fun _ _ => True)).
  apply (kx_tree_evtF (fun _ _ => True) Q vmax fuel stops scalls zs rz xs zks rk pc m rom t r reads rs [] Hex Hchk Hregs Hzk Hrs (Forall_nil _)).
  intros E HE HK. apply kt_obl2_top. exact (K E HE HK).
Qed.

End TreeGo.
