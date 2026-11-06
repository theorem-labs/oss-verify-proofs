(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec CatExec SeqExec StepTac ZStores.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma rc_rdn_wbytes_out_Z : forall segs bs m (zb za : Z) n,
  (0 <= za < 2^64 /\ za + Z.of_nat n <= 2^64 /\ 0 <= zb < 2^64 /\
   zb + Z.of_nat (length bs) <= 2^64 /\
   (za + Z.of_nat n <= zb \/ zb + Z.of_nat (length bs) <= za))%Z ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs bs m zb za n (Ha & Han & Hb & Hbn & Hd).
  apply rdn_wbytes_out; rewrite ?u_Z2bv by lia; lia.
Qed.
Lemma rc_lo_sub : forall lo d b : Z, (lo <= b - d)%Z -> (lo + d <= b)%Z.
Proof. intros; lia. Qed.

Inductive roff := OB | OS (o : roff) (k : Z) | OA (o : roff) (k : Z).
Fixpoint roden (b : Z) (o : roff) : Z := match o with OB => b | OS o' k => roden b o' - k | OA o' k => roden b o' + k end.
Inductive raddr := RA (z : Z) | RR (o : roff).
Definition rden (b : Z) (a : raddr) : Z := match a with RA z => z | RR o => roden b o end.
Definition rlo (lo : Z) (a : raddr) : Z := match a with RA z => z | RR o => roden lo o end.
Definition rhi (hi : Z) (a : raddr) : Z := match a with RA z => z | RR o => roden hi o end.
Definition risabs (a : raddr) : bool := match a with RA _ => true | _ => false end.
Definition rbefore (lo hi : Z) (x : raddr) (n : Z) (y : raddr) : bool :=
  if Bool.eqb (risabs x) (risabs y) then (rden 0 x + n <=? rden 0 y)%Z else (rhi hi x + n <=? rlo lo y)%Z.
Definition rrange (lo hi : Z) (a : raddr) (n : Z) : bool :=
  ((0 <=? rlo lo a) && (rhi hi a <? 2^64) && (rhi hi a + n <=? 2^64))%Z%bool.
(* [comment removed for export] *)
Definition rlay : Type := (raddr * list byte)%type.
Definition rl (a : raddr) (bs : list byte) : rlay := (a, bs).
Definition rmem : Type := word -> option byte.
Definition rword : Type := word.
Definition rlayer (lo hi : Z) (ra : raddr) (n : Z) (ly : rlay) : bool :=
  let len := Z.of_nat (length (snd ly)) in
  (rrange lo hi (fst ly) len && (rbefore lo hi ra n (fst ly) || rbefore lo hi (fst ly) len ra))%bool.
Fixpoint rcount (lo hi : Z) (ra : raddr) (n : Z) (l : list rlay) : nat :=
  match l with
  | [] => O
  | ly :: l' => if rlayer lo hi ra n ly then S (rcount lo hi ra n l') else O
  end.
Fixpoint rchain (b : Z) (m : word -> option byte) (l : list rlay) : word -> option byte :=
  match l with
  | [] => m
  | ly :: l' => wbytes (rchain b m l') (Z_to_bv 64 (rden b (fst ly))) (snd ly)
  end.
Lemma roden_shift : forall b o, roden b o = (b + roden 0 o)%Z.
Proof. intros b o. induction o as [|o IH k|o IH k]; cbn [roden]; lia. Qed.
Lemma rden_bounds : forall lo hi b a, (lo <= b)%Z -> (b <= hi)%Z -> (rlo lo a <= rden b a <= rhi hi a)%Z.
Proof.
  intros lo hi b [z|o] H1 H2; cbn [rlo rhi rden]; [lia|].
  pose proof (roden_shift lo o). pose proof (roden_shift b o). pose proof (roden_shift hi o). lia.
Qed.
Lemma rbefore_sound : forall lo hi b x n y, (lo <= b)%Z -> (b <= hi)%Z -> rbefore lo hi x n y = true -> (rden b x + n <= rden b y)%Z.
Proof.
  intros lo hi b x n y H1 H2 H. unfold rbefore in H.
  pose proof (rden_bounds lo hi b x H1 H2). pose proof (rden_bounds lo hi b y H1 H2).
  destruct x as [zx|ox], y as [zy|oy]; cbn [risabs Bool.eqb rden rlo rhi] in *; apply Z.leb_le in H;
    try pose proof (roden_shift b ox); try pose proof (roden_shift b oy); lia.
Qed.
Lemma rdn_rchain_out : forall segs m b lo hi l ra n M A,
  M = rchain b m l -> A = Z_to_bv 64 (rden b ra) -> (lo <= b)%Z -> (b <= hi)%Z ->
  (rrange lo hi ra (Z.of_nat n) && forallb (rlayer lo hi ra (Z.of_nat n)) l)%bool = true ->
  rdn segs M A n = rdn segs m A n.
Proof.
  intros segs m b lo hi l ra n M A -> -> H1 H2 H. apply andb_true_iff in H as [HR HL].
  pose proof (rden_bounds lo hi b ra H1 H2) as BR.
  unfold rrange in HR. apply andb_true_iff in HR as [HR HR3]. apply andb_true_iff in HR as [HR1 HR2].
  apply Z.leb_le in HR1. apply Z.ltb_lt in HR2. apply Z.leb_le in HR3.
  induction l as [|[a bs] l IH]; cbn [rchain forallb fst snd] in *; [reflexivity|].
  apply andb_true_iff in HL as [HA HL]. unfold rlayer in HA. cbn [fst snd] in HA.
  apply andb_true_iff in HA as [HAR HD].
  unfold rrange in HAR. apply andb_true_iff in HAR as [HAR HA3]. apply andb_true_iff in HAR as [HA1 HA2].
  apply Z.leb_le in HA1. apply Z.ltb_lt in HA2. apply Z.leb_le in HA3.
  pose proof (rden_bounds lo hi b a H1 H2) as BA.
  rewrite rc_rdn_wbytes_out_Z; [apply IH; exact HL|].
  apply orb_true_iff in HD. destruct HD as [HD|HD]; apply (rbefore_sound lo hi b _ _ _ H1 H2) in HD; lia.
Qed.

Ltac is_pos_lit' p := lazymatch p with xH => idtac | xO ?q => is_pos_lit' q | xI ?q => is_pos_lit' q end.
Ltac is_Z_lit' z := lazymatch z with Z0 => idtac | Zpos ?p => is_pos_lit' p | Zneg ?p => is_pos_lit' p end.
(* [comment removed for export] *)
Ltac roff_of bt z :=
  lazymatch z with
  | bt => constr:(OB)
  | (?x - ?k)%Z => let _ := match tt with _ => is_Z_lit' k end in let o := roff_of bt x in constr:(OS o k)
  | (?x + ?k)%Z => let _ := match tt with _ => is_Z_lit' k end in let o := roff_of bt x in constr:(OA o k)
  end.
Ltac raddr_of bt z :=
  match tt with
  | _ => let _ := match tt with _ => is_Z_lit' z end in constr:(RA z)
  | _ => let o := roff_of bt z in constr:(RR o)
  end.
(* [comment removed for export] *)
Ltac rbase_of_z z :=
  lazymatch z with
  | bv_unsigned ?B => constr:(bv_unsigned B)
  | (?x - _)%Z => rbase_of_z x
  | (?x + _)%Z => rbase_of_z x
  end.
Ltac rbase_chain M :=
  lazymatch M with
  | wbytes ?M' (Z_to_bv 64 ?z) _ =>
      match tt with
      | _ => rbase_of_z z
      | _ => rbase_chain M'
      end
  end.
(* [comment removed for export] *)
Ltac is_nat_lit' n := lazymatch n with O => idtac | S ?m => is_nat_lit' m end.
Ltac rbs_ok bs :=
  lazymatch bs with
  | word_to_le_bytes ?k _ => is_nat_lit' k
  | zeros ?k => is_nat_lit' k
  | @nil _ => idtac
  | @cons _ _ ?t => rbs_ok t
  end.
(* [comment removed for export] *)
Ltac rlayers bt M :=
  lazymatch M with
  | wbytes ?M' (Z_to_bv 64 ?z) ?bs =>
      match tt with
      | _ => let _ := match tt with _ => rbs_ok bs end in
             let a := raddr_of bt z in let l := rlayers bt M' in uconstr:(@cons rlay (rl a bs) l)
      | _ => uconstr:(@nil rlay)
      end
  | _ => uconstr:(@nil rlay)
  end.
(* [comment removed for export] *)
Ltac rfirstn j l :=
  lazymatch j with
  | O => uconstr:(@nil rlay)
  | S ?j' => lazymatch l with @cons _ ?x ?t => let r := rfirstn j' t in uconstr:(@cons rlay x r) end
  end.
Ltac rdrop j M :=
  lazymatch j with
  | O => M
  | S ?j' => lazymatch M with wbytes ?M' _ _ => rdrop j' M' end
  end.
(* [comment removed for export] *)
Ltac rb_lower B :=
  match goal with
  | H : (?lo <= bv_unsigned B)%Z |- _ => let _ := match tt with _ => is_Z_lit' lo end in constr:(H)
  | H : (?lo <= bv_unsigned B <= _)%Z |- _ => let _ := match tt with _ => is_Z_lit' lo end in constr:(proj1 H)
  | H : (?lo <= bv_unsigned B - ?d)%Z |- _ =>
      let _ := match tt with _ => is_Z_lit' lo; is_Z_lit' d end in constr:(rc_lo_sub lo d (bv_unsigned B) H)
  end.
Ltac rb_upper B :=
  match goal with
  | H : (bv_unsigned B <= ?hi)%Z |- _ => let _ := match tt with _ => is_Z_lit' hi end in constr:(H)
  | H : (_ <= bv_unsigned B <= ?hi)%Z |- _ => let _ := match tt with _ => is_Z_lit' hi end in constr:(proj2 H)
  end.

(* [comment removed for export] *)
Ltac peel_refl :=
  lazymatch goal with
  | |- context [rdn ?segs ?M (Z_to_bv 64 ?za) ?n] =>
      lazymatch M with
      | wbytes _ (Z_to_bv 64 za) _ => fail   (* [comment removed for export] *)
      | wbytes _ (Z_to_bv 64 _) _ => idtac
      end;
      is_nat_lit' n;
      let bt := match tt with
                | _ => rbase_of_z za
                | _ => rbase_chain M
                | _ => constr:(0%Z)
                end in
      let ra := raddr_of bt za in
      let lu := rlayers bt M in
      let lall := constr:(lu) in
      lazymatch bt with
      | 0%Z =>
          let j := eval lazy in (rcount 0 0 ra (Z.of_nat n) lall) in
          lazymatch j with O => fail | _ => idtac end;
          let l := rfirstn j lall in
          let m := rdrop j M in
          rewrite (rdn_rchain_out segs m 0%Z 0%Z 0%Z l ra n M (Z_to_bv 64 za)
                     (@eq_refl rmem M) (@eq_refl rword (Z_to_bv 64 za)) (Z.le_refl 0) (Z.le_refl 0) (@eq_refl bool true))
      | bv_unsigned ?B =>
          let pl := rb_lower B in
          let ph := rb_upper B in
          lazymatch type of pl with
          | (?lo <= _)%Z =>
              lazymatch type of ph with
              | (_ <= ?hi)%Z =>
                  let j := eval lazy in (rcount lo hi ra (Z.of_nat n) lall) in
                  lazymatch j with O => fail | _ => idtac end;
                  let l := rfirstn j lall in
                  let m := rdrop j M in
                  rewrite (rdn_rchain_out segs m bt lo hi l ra n M (Z_to_bv 64 za)
                             (@eq_refl rmem M) (@eq_refl rword (Z_to_bv 64 za)) pl ph (@eq_refl bool true))
              end
          end
      end
  end.
