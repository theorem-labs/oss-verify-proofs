(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec StoreOk ShapeAlg AgentLib AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlanSound.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxOpt CxOptGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mem_addr (K : kentry) : option saddr :=
  match K with
  | KWord a _ _ | KZero a _ | KBlob a _ _ | KFill a _ _ | KUnk a _ | KWr a _ => Some a
  | _ => None
  end.
Definition set_addr (K : kentry) (a' : saddr) : kentry :=
  match K with
  | KWord _ w v => KWord a' w v
  | KZero _ n => KZero a' n
  | KBlob _ n k => KBlob a' n k
  | KFill _ n c => KFill a' n c
  | KUnk _ n => KUnk a' n
  | KWr _ n => KWr a' n
  | _ => K
  end.
(* [comment removed for export] *)
Definition resplit_ok (k : list kentry) (b' : expr) : bool :=
  let (b, c) := split_lit b' in
  match xlo k b, xhi k b with
  | Some lo, Some hi => (0 <=? lo + c) && (hi + c <? 2 ^ 64)
  | _, _ => false
  end.
Definition readdr (i : nat) (a a' : saddr) (k : list kentry) : option (list kentry) :=
  match nth_error k i with
  | Some K => match mem_addr K with
              | Some x => if saddr_eqb x a then Some (set_addr K a' :: k) else None
              | None => None
              end
  | None => None
  end.
Definition node_resplit (args : list expr) (cs : acs) : option acs :=
  match args with
  | [ELit i; b'; ELit off'] =>
      if resplit_ok (kn cs) b' then
        match readdr (Z.to_nat i) (to_saddr b' off') (SA b' off') (kn cs) with
        | Some k' => Some (set_kn cs k')
        | None => None
        end
      else None
  | _ => None
  end.

Definition node_band_end (A : atable) (args : list expr) (cs : acs) : option acs :=
  match args with
  | [EVar v] =>
      let k := kn cs in
      let b := escale 4096 (EVar v) in
      match find_zone_disj A k b, xhi2 k (EVar v) with
      | Some n2, Some hi =>
          if (Z.leb 0 (zone_lo A) && Z.leb (zone_lo A) (zone_hi A) && Z.ltb (zone_hi A) two64
              && Z.leb hi (2 ^ 51) && Z.ltb (4096 * hi) (zone_hi A) && flat_x k b 0 n2)%bool
          then Some (add_kn cs [KRange (eadd b n2) 0 (zone_lo A)])
          else None
      | _, _ => None
      end
  | _ => None
  end.

Fixpoint find_range (k : list kentry) (e : expr) : option (Z * Z) :=
  match k with
  | [] => None
  | KRange x lo hi :: r => if expr_eqb x e then Some (lo, hi) else find_range r e
  | _ :: r => find_range r e
  end.
Definition node_sumfact (args : list expr) (cs : acs) : option acs :=
  match args with
  | [e1; e2] =>
      match find_range (kn cs) e1, find_range (kn cs) e2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          if Z.ltb (hi1 + hi2) (2 ^ 64) then Some (add_kn cs [KRange (eadd e1 e2) (lo1 + lo2) (hi1 + hi2)]) else None
      | _, _ => None
      end
  | _ => None
  end.

Definition node_order_end (args : list expr) (cs : acs) : option acs :=
  match args with
  | [b1; b2] =>
      let k := kn cs in
      match find_disj k b1 b2 with
      | Some (c1, o1, n1, c2, o2, n2) =>
          let D := esub (eaddz c2 o2) (eaddz c1 o1) in
          match xlo2 k D, xhi2 k D, xhi2 k (eaddz c1 o1) with
          | Some lo, Some hi, Some h1 =>
              if (Z.leb 1 lo && Z.ltb (hi + h1) (2 ^ 64) && flat_x k c1 o1 n1 && flat_x k c2 o2 n2)%bool
              then Some (add_kn cs [KRange (esub D n1) 0 hi])
              else None
          | _, _, _ => None
          end
      | None => None
      end
  | _ => None
  end.

Definition optk_xn (A : atable) (LIMIT : Z) (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 49 then node_resplit args cs else if Nat.eqb id 52 then node_band_end A args cs
  else if Nat.eqb id 53 then node_sumfact args cs else if Nat.eqb id 54 then node_order_end args cs else opt_xn A LIMIT id args cs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition canon (K : kentry) : kentry :=
  match mem_addr K with Some a => set_addr K (to_saddr (a_base a) (a_off a)) | None => K end.
Definition needs_resplit (K : kentry) : bool := negb (kentry_eqb (canon K) K).
Fixpoint index_of (f : kentry -> bool) (l : list kentry) (i : nat) : option nat :=
  match l with [] => None | x :: r => if f x then Some i else index_of f r (Datatypes.S i) end.
(* [comment removed for export] *)
Fixpoint resplit_ops (tgt : list kentry) (cur : list kentry) : list (nat * expr * Z) * list kentry :=
  match tgt with
  | [] => ([], cur)
  | K :: r =>
      if needs_resplit K then
        match mem_addr K, index_of (kentry_eqb (canon K)) cur 0%nat with
        | Some a, Some i =>
            match readdr i (to_saddr (a_base a) (a_off a)) a cur with
            | Some cur' => let '(ops, c2) := resplit_ops r cur' in ((i, a_base a, a_off a) :: ops, c2)
            | None => resplit_ops r cur
            end
        | _, _ => resplit_ops r cur
        end
      else resplit_ops r cur
  end.
(* [comment removed for export] *)
Fixpoint drop_img_pads (p : plan) : plan :=
  match p with
  | PExt id a k => PExt id a (drop_img_pads k)
  | PFact (KImg _ _) k => drop_img_pads k
  | PFact K k => PFact K (drop_img_pads k)
  | _ => p
  end.
Definition hop_plan_k (A : atable) (LIMIT : Z) (S HS : acs) (h : nat) : plan :=
  let '(ops, k') := resplit_ops (kn HS) (kn S) in
  fold_right (fun o p => let '(i, b, off) := o in PExt 49 [ELit (Z.of_nat i); b; ELit off] p) (drop_img_pads (hop_plan A LIMIT (set_kn S k') HS h)) ops.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma estart_resplit : forall segs E M k b' off',
  know_ok segs E M k -> resplit_ok k b' = true ->
  estart E (SA b' off') = estart E (to_saddr b' off').
Proof.
  intros segs E M k b' off' HK H. unfold resplit_ok in H. unfold to_saddr.
  destruct (split_lit b') as [b c] eqn:Hs.
  destruct (xlo k b) as [lo|] eqn:Hlo; [|discriminate]. destruct (xhi k b) as [hi|] eqn:Hhi; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  pose proof (xlo_sound segs E M k b lo HK Hlo) as Gl. pose proof (xhi_sound segs E M k b hi HK Hhi) as Gh.
  unfold estart. cbn [a_base a_off]. rewrite (split_lit_denot E b' b c Hs).
  rewrite Z_to_bv_unsigned. rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
Qed.

Lemma flat_same : forall E a a' n, estart E a' = estart E a -> flat E a n -> flat E a' n.
Proof. intros E a a' n He [H1 [H2 [H3 H4]]]. unfold flat. rewrite He. repeat split; assumption. Qed.

Lemma adenot_same : forall E a a' n, estart E a' = estart E a -> flat E a n -> adenot E a' = adenot E a.
Proof.
  intros E a a' n He Hf. pose proof (flat_same E a a' n He Hf) as Hf'.
  apply bv_eq. rewrite (flat_u E a n Hf), (flat_u E a' n Hf'). exact He.
Qed.

Lemma kentry_ok_readdr : forall segs E M K a a',
  mem_addr K = Some a -> estart E a' = estart E a -> kentry_ok segs E M K -> kentry_ok segs E M (set_addr K a').
Proof.
  intros segs E M K a a' Hm He HK.
  destruct K; cbn [mem_addr] in Hm; try discriminate Hm; injection Hm as ->; cbn [set_addr kentry_ok] in *.
  - (* [comment removed for export] *) destruct HK as [Hw [Hf Hr]]. split; [exact Hw|]. split; [exact (flat_same _ _ _ _ He Hf)|].
    rewrite (adenot_same E a a' _ He Hf). exact Hr.
  - (* [comment removed for export] *) destruct HK as [Hf Hz]. split; [exact (flat_same _ _ _ _ He Hf)|]. rewrite He. exact Hz.
  - (* [comment removed for export] *) destruct HK as [Hf [Hl Hz]]. split; [exact (flat_same _ _ _ _ He Hf)|]. split; [exact Hl|]. rewrite He. exact Hz.
  - (* [comment removed for export] *) destruct HK as [Hf Hz]. split; [exact (flat_same _ _ _ _ He Hf)|]. rewrite He. exact Hz.
  - (* [comment removed for export] *) destruct HK as [Hf Hz]. split; [exact (flat_same _ _ _ _ He Hf)|]. rewrite He. exact Hz.
  - (* [comment removed for export] *) destruct HK as [Hf Hz]. split; [exact (flat_same _ _ _ _ He Hf)|]. rewrite He. exact Hz.
Qed.

Lemma saddr_eqb_eq : forall a b, saddr_eqb a b = true -> a = b.
Proof.
  intros [b1 o1] [b2 o2] H. unfold saddr_eqb in H. cbn [a_base a_off] in H. apply andb_prop in H as [H1 H2].
  apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

Lemma know_ok_readdr : forall segs E M i a a' k k',
  estart E a' = estart E a -> readdr i a a' k = Some k' -> know_ok segs E M k -> know_ok segs E M k'.
Proof.
  intros segs E M i a a' k k' He Hr HK. unfold readdr in Hr.
  destruct (nth_error k i) as [K|] eqn:Hn; [|discriminate Hr].
  destruct (mem_addr K) as [x|] eqn:Hm; [|discriminate Hr]. destruct (saddr_eqb x a) eqn:Hx; [|discriminate Hr].
  injection Hr as <-. apply saddr_eqb_eq in Hx. subst x.
  constructor; [|exact HK]. apply (kentry_ok_readdr segs E M K a a' Hm He).
  exact (proj1 (Forall_forall _ _) HK K (nth_error_In _ _ Hn)).
Qed.

Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.

Theorem node_resplit_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (node_resplit args).
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_resplit in Hn.
  destruct args as [|[i| | | | | | |] [|b' [|[off'| | | | | | |] [|]]]]; try discriminate Hn.
  destruct (resplit_ok (kn cs) b') eqn:Hok; [|discriminate Hn].
  destruct (readdr (Z.to_nat i) (to_saddr b' off') (SA b' off') (kn cs)) as [k'|] eqn:Hr; [|discriminate Hn].
  injection Hn as <-.
  assert (Hrefl : forall x, env_agree x E E) by (intros x; split; [intros; reflexivity | reflexivity]).
  apply (Hk E R FULL model (conj (Hrefl _) (Hrefl _))); [|reflexivity].
  apply cs_ok_set_kn; [exact HC|].
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  eapply know_ok_readdr; [|exact Hr|exact HK].
  exact (estart_resplit _ _ _ _ _ _ HK Hok).
Qed.

Theorem node_band_end_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (node_band_end A args).
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_band_end in Hn.
  destruct args as [|[| v | | | | | |] [|]]; try discriminate Hn.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (find_zone_disj A (kn cs) (escale 4096 (EVar v))) as [n2|] eqn:Hf; [|discriminate Hn].
  destruct (xhi2 (kn cs) (EVar v)) as [hi|] eqn:Hhi; [|discriminate Hn].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate Hn] end.
  injection Hn as <-.
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  repeat match goal with Hq : Z.leb _ _ = true |- _ => apply Z.leb_le in Hq end.
  repeat match goal with Hq : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hq end.
  match goal with Hq : flat_x _ _ _ _ = true |- _ => pose proof (flat_x_sound SEGS E _ (kn cs) _ _ _ HK Hq) as (F1 & F2 & F3) end.
  pose proof (xhi2_sound SEGS E _ (kn cs) (EVar v) hi HK Hhi) as Hv. cbn [edenot] in Hv.
  assert (Ub : bv_unsigned (edenot E (escale 4096 (EVar v))) = 4096 * bv_unsigned (ev E v)).
  { unfold escale. rewrite mkMd_denot. cbn [edenot]. rewrite u_mul64, u64_lit by lia. apply Z.mod_small. unfold two64 in *. pose proof (bv_unsigned_in_range _ (ev E v)). lia. }
  pose proof (proj1 (Forall_forall _ _) HK _ (find_zone_disj_In A (kn cs) _ n2 Hf)) as Hd. cbn [kentry_ok] in Hd.
  unfold en_zone, estart, elenZ in Hd, F1, F2. cbn [a_base a_off edenot] in Hd, F1, F2. rewrite Ub in Hd, F1, F2.
  rewrite !u64_lit in Hd by (unfold two64 in *; lia).
  assert (Hrefl : forall x, env_agree x E E) by (intros x; split; [intros; reflexivity | reflexivity]).
  apply (Hk E R FULL model (conj (Hrefl _) (Hrefl _))); [|reflexivity].
  unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK]. cbn [kentry_ok].
  unfold eadd. rewrite mkAlu_denot, u_add64, Ub.
  destruct Hd as [Hd|Hd]; [exfalso; lia|].
  rewrite Z.mod_small by (unfold two64 in *; pose proof (bv_unsigned_in_range _ (edenot E n2)); lia). lia.
Qed.

Lemma find_range_In : forall k e lo hi, find_range k e = Some (lo, hi) -> In (KRange e lo hi) k.
Proof.
  induction k as [|K r IH]; intros e lo hi H; cbn [find_range] in H; [discriminate|].
  destruct K; try (right; apply IH; exact H).
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc end; [|right; apply IH; exact H].
  apply expr_eqb_eq in Hc. injection H as <- <-. subst. left. reflexivity.
Qed.

Theorem node_sumfact_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (node_sumfact args).
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_sumfact in Hn.
  destruct args as [|e1 [|e2 [|]]]; try discriminate Hn.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (find_range (kn cs) e1) as [[lo1 hi1]|] eqn:H1; [|discriminate Hn].
  destruct (find_range (kn cs) e2) as [[lo2 hi2]|] eqn:H2; [|discriminate Hn].
  destruct (Z.ltb_spec (hi1 + hi2) (2 ^ 64)) as [Hlt|]; [|discriminate Hn].
  injection Hn as <-.
  pose proof (proj1 (Forall_forall _ _) HK _ (find_range_In _ _ _ _ H1)) as G1. pose proof (proj1 (Forall_forall _ _) HK _ (find_range_In _ _ _ _ H2)) as G2.
  cbn [kentry_ok] in G1, G2.
  assert (Hrefl : forall x, env_agree x E E) by (intros x; split; [intros; reflexivity | reflexivity]).
  apply (Hk E R FULL model (conj (Hrefl _) (Hrefl _))); [|reflexivity].
  unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK]. cbn [kentry_ok].
  unfold eadd. rewrite mkAlu_denot, u_add64.
  pose proof (bv_unsigned_in_range _ (edenot E e1)). pose proof (bv_unsigned_in_range _ (edenot E e2)).
  rewrite Z.mod_small by lia. lia.
Qed.

Theorem node_order_end_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (node_order_end args).
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_order_end in Hn.
  destruct args as [|b1 [|b2 [|]]]; try discriminate Hn.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (find_disj (kn cs) b1 b2) as [[[[[[c1 o1] n1] c2] o2] n2]|] eqn:Hf; [|discriminate Hn].
  set (D := esub (eaddz c2 o2) (eaddz c1 o1)) in *.
  destruct (xlo2 (kn cs) D) as [lo|] eqn:Hlo; [|discriminate Hn].
  destruct (xhi2 (kn cs) D) as [hi|] eqn:Hhi; [|discriminate Hn].
  destruct (xhi2 (kn cs) (eaddz c1 o1)) as [h1|] eqn:Hh1; [|discriminate Hn].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate Hn] end.
  injection Hn as <-.
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  apply Z.leb_le in Hc. match goal with Hq : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hq end.
  pose proof (flat_x_sound SEGS E _ (kn cs) c1 o1 n1 HK ltac:(assumption)) as (A1 & A2 & A3).
  pose proof (flat_x_sound SEGS E _ (kn cs) c2 o2 n2 HK ltac:(assumption)) as (B1 & B2 & B3).
  pose proof (xlo2_sound SEGS E _ (kn cs) D lo HK Hlo) as Ld. pose proof (xhi2_sound SEGS E _ (kn cs) D hi HK Hhi) as Hd.
  pose proof (xhi2_sound SEGS E _ (kn cs) (eaddz c1 o1) h1 HK Hh1) as H1.
  pose proof (find_disj_sound SEGS E _ (kn cs) b1 b2 c1 o1 n1 c2 o2 n2 HK Hf) as Hdisj.
  assert (Hrefl : forall x, env_agree x E E) by (intros x; split; [intros; reflexivity | reflexivity]).
  apply (Hk E R FULL model (conj (Hrefl _) (Hrefl _))); [|reflexivity].
  unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK]. cbn [kentry_ok].
  unfold D, esub, eaddz in *. rewrite !mkAlu_denot, !u_sub64, !u_add64 in *. cbn [edenot] in *. rewrite !u_lit64 in *.
  unfold estart, elenZ in *; cbn [a_base a_off] in *.
  pose proof (u64_range (edenot E c1)) as R1. pose proof (u64_range (edenot E c2)) as R2. pose proof (u64_range (edenot E n1)) as R3. pose proof (u64_range (edenot E n2)) as R4.
  unfold two64 in *.
  set (u1 := bv_unsigned (edenot E c1)) in *. set (u2 := bv_unsigned (edenot E c2)) in *.
  set (l1 := bv_unsigned (edenot E n1)) in *. set (l2 := bv_unsigned (edenot E n2)) in *.
  assert (E1 : (u1 + o1 mod 2 ^ 64) mod 2 ^ 64 = u1 + o1) by (rewrite Zplus_mod_idemp_r; apply Z.mod_small; lia).
  assert (E2 : (u2 + o2 mod 2 ^ 64) mod 2 ^ 64 = u2 + o2) by (rewrite Zplus_mod_idemp_r; apply Z.mod_small; lia).
  rewrite E1, E2 in *.
  assert (Hlt : u1 + o1 < u2 + o2).
  { destruct (Z_lt_le_dec (u1 + o1) (u2 + o2)) as [|Hge]; [assumption|exfalso].
    destruct (Z.eq_dec (u2 + o2) (u1 + o1)) as [Heq|Hne].
    - rewrite Heq, Z.sub_diag, Z.mod_0_l in Ld by lia. lia.
    - assert (Hm : (u2 + o2 - (u1 + o1)) mod 2 ^ 64 = 2 ^ 64 + (u2 + o2 - (u1 + o1))).
      { symmetry. apply (Z.mod_unique _ _ (-1)); lia. }
      rewrite Hm in Hd. lia. }
  destruct Hdisj as [Hdj|Hdj]; [|exfalso; lia].
  assert (Hm : (u2 + o2 - (u1 + o1)) mod 2 ^ 64 = u2 + o2 - (u1 + o1)) by (apply Z.mod_small; lia).
  rewrite Hm in *. rewrite Z.mod_small by lia. lia.
Qed.

Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis ZONE_ok : zone_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.

Theorem optk_xn_sound : ext_stmt SEGS A nx0 LIMIT (optk_xn A LIMIT) SINV argH ISP FS0.
Proof.
  intros id args. unfold optk_xn. destruct (Nat.eqb id 49); [apply node_resplit_sound|].
  destruct (Nat.eqb id 52); [apply node_band_end_sound|].
  destruct (Nat.eqb id 53); [apply node_sumfact_sound|].
  destruct (Nat.eqb id 54); [apply node_order_end_sound|].
  - apply (opt_xn_sound SEGS A nx0 LIMIT SINV argH ISP FS0 SHADOW_ok SEGS_in_hull HULL_ok ZONE_ok argH_high).
Qed.
End Sound.
