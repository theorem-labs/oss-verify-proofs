(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExTrie ExBytes.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxBytes AxMem AxState AxEntryRel AxSys.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

Fixpoint xbs_eqb (l1 l2 : list xb) : bool :=
  match l1, l2 with
  | [], [] => true
  | a :: r1, b :: r2 =>
      (match a, b with
       | BL x, BL y => (x =? y)%uint63
       | BT, BT => true
       | BF t1 o1 i1, BF t2 o2 i2 => Nat.eqb i1 i2 &&& w_eqb o1 o2 &&& teqb t1 t2
       | _, _ => false
       end) &&& xbs_eqb r1 r2
  | _, _ => false
  end.

Definition xv_eqb (a b : xv) : bool :=
  match a, b with
  | XL x, XL y => w_eqb x y
  | XS t1 o1, XS t2 o2 => w_eqb o1 o2 &&& teqb t1 t2
  | XR l1 h1, XR l2 h2 => (l1 =? l2) &&& (h1 =? h2)
  | XK m1 v1, XK m2 v2 => w_eqb m1 m2 &&& w_eqb v1 v2
  | XB l1, XB l2 => xbs_eqb l1 l2
  | XT, XT => true
  | _, _ => false
  end.

Definition cell_eqb (c d : cell) : bool :=
  match c, d with
  | CW a, CW b => w_eqb a b
  | CB l1, CB l2 => xbs_eqb l1 l2
  | _, _ => false
  end.

Definition kind_eqb (k1 k2 : rkind) : bool :=
  match k1, k2 with
  | KZero, KZero | KShadow, KShadow | KUnk, KUnk => true
  | KImg w1 i1, KImg w2 i2 => Bool.eqb w1 w2 &&& Nat.eqb i1 i2
  | KEntry p1, KEntry p2 => (ph_addr p1 =? ph_addr p2)%N &&& (ph_ent p1 =? ph_ent p2)%N &&& (ph_num p1 =? ph_num p2)%N
  | _, _ => false
  end.

Definition fields_eqb (R1 R2 : region) : bool :=
  w_eqb (rg_bo R1) (rg_bo R2) &&& (rg_n R1 =? rg_n R2)%uint63 &&& Nat.eqb (rg_d R1) (rg_d R2)
  &&& kind_eqb (rg_kind R1) (rg_kind R2) &&& teqb (rg_ts R1) (rg_ts R2).

Definition rsv_join (a b : rsv) : rsv :=
  match a, b with
  | RNone, RNone => RNone
  | RSome x, RSome y => if xv_eqb x y then a else RUnk
  | _, _ => RUnk
  end.

Definition vjoin (sa sb : store) (a b : xv) : xv :=
  if xv_eqb a b then a else
  match xrange sa a, xrange sb b with
  | Some (l1, h1), Some (l2, h2) => mk_rng (Z.min l1 l2) (Z.max h1 h2)
  | _, _ => XT
  end.

Definition bjoin1 (a b : xb) : xb :=
  match a, b with
  | BL x, BL y => if (x =? y)%uint63 then a else BT
  | BF t1 o1 i1, BF t2 o2 i2 => if Nat.eqb i1 i2 &&& w_eqb o1 o2 &&& teqb t1 t2 then a else BT
  | _, _ => BT
  end.

Definition cjoin (c d : cell) : cell :=
  if cell_eqb c d then c else
  CB [bjoin1 (cbyte c 0) (cbyte d 0); bjoin1 (cbyte c 1) (cbyte d 1); bjoin1 (cbyte c 2) (cbyte d 2); bjoin1 (cbyte c 3) (cbyte d 3);
      bjoin1 (cbyte c 4) (cbyte d 4); bjoin1 (cbyte c 5) (cbyte d 5); bjoin1 (cbyte c 6) (cbyte d 6); bjoin1 (cbyte c 7) (cbyte d 7)].

Fixpoint rjoin (d : nat) (sa sb : store) (ta tb : itrie xv) : itrie xv :=
  match d with
  | O => match ta, tb with
         | ILeaf a, ILeaf b => ILeaf (vjoin sa sb a b)
         | ILeaf a, _ => ILeaf (vjoin sa sb a (XL w_zero))
         | _, ILeaf b => ILeaf (vjoin sa sb (XL w_zero) b)
         | _, _ => IEmpty
         end
  | S d' => match ta, tb with
            | IEmpty, IEmpty => IEmpty
            | _, _ => INode (rjoin d' sa sb (match ta with INode l _ => l | _ => IEmpty end) (match tb with INode l _ => l | _ => IEmpty end))
                            (rjoin d' sa sb (match ta with INode _ r => r | _ => IEmpty end) (match tb with INode _ r => r | _ => IEmpty end))
            end
  end.

Section WithSegs.
Variable segs : list Segment.

Fixpoint tjoin (kd : rkind) (d : nat) (ta tb : itrie cell) (acc w : int) : itrie cell :=
  match d with
  | O => match ta, tb with
         | ILeaf a, ILeaf b => ILeaf (cjoin a b)
         | ILeaf a, _ => ILeaf (cjoin a (default_cell segs kd acc))
         | _, ILeaf b => ILeaf (cjoin (default_cell segs kd acc) b)
         | _, _ => IEmpty
         end
  | S d' => match ta, tb with
            | IEmpty, IEmpty => IEmpty
            | _, _ => INode (tjoin kd d' (match ta with INode l _ => l | _ => IEmpty end) (match tb with INode l _ => l | _ => IEmpty end) acc (w << 1)%uint63)
                            (tjoin kd d' (match ta with INode _ r => r | _ => IEmpty end) (match tb with INode _ r => r | _ => IEmpty end) (acc + w)%uint63 (w << 1)%uint63)
            end
  end.

Fixpoint tjoin2 (kd : rkind) (d : nat) (ta tb : itrie cell) (acc w : int) : bool * itrie cell :=
  match d with
  | O => match ta, tb with
         | ILeaf a, ILeaf b => if cell_eqb a b then (true, ta) else (false, ILeaf (cjoin a b))
         | ILeaf a, _ => if cell_eqb a (default_cell segs kd acc) then (true, ta) else (false, ILeaf (cjoin a (default_cell segs kd acc)))
         | _, ILeaf b => (false, ILeaf (cjoin (default_cell segs kd acc) b))
         | _, _ => (false, IEmpty)
         end
  | S d' => match ta, tb with
            | IEmpty, IEmpty => (true, ta)
            | INode la ra, _ =>
                let (fl, l') := tjoin2 kd d' la (match tb with INode l _ => l | _ => IEmpty end) acc (w << 1)%uint63 in
                let (fr, r') := tjoin2 kd d' ra (match tb with INode _ r => r | _ => IEmpty end) (acc + w)%uint63 (w << 1)%uint63 in
                if fl then (if fr then (true, ta) else (false, INode l' r')) else (false, INode l' r')
            | _, _ => (false, INode (tjoin kd d' IEmpty (match tb with INode l _ => l | _ => IEmpty end) acc (w << 1)%uint63)
                                     (tjoin kd d' IEmpty (match tb with INode _ r => r | _ => IEmpty end) (acc + w)%uint63 (w << 1)%uint63))
            end
  end.

Lemma cjoin_same (c d : cell) : cell_eqb c d = true -> cjoin c d = c.
Proof. unfold cjoin. intros ->. reflexivity. Qed.

Lemma tjoin2_eq (kd : rkind) : forall (d : nat) (ta tb : itrie cell) (acc w : int),
  snd (tjoin2 kd d ta tb acc w) = tjoin kd d ta tb acc w /\ (fst (tjoin2 kd d ta tb acc w) = true -> tjoin kd d ta tb acc w = ta).
Proof.
  induction d as [|d IH]; intros ta tb acc w.
  - destruct ta as [|a|la ra], tb as [|b|lb rb]; cbn [tjoin2 tjoin fst snd]; try (split; [reflexivity | discriminate]).
    + destruct (cell_eqb a (default_cell segs kd acc)) eqn:E; cbn [fst snd]; [rewrite (cjoin_same _ _ E); split; reflexivity | split; [reflexivity | discriminate]].
    + destruct (cell_eqb a b) eqn:E; cbn [fst snd]; [rewrite (cjoin_same _ _ E); split; reflexivity | split; [reflexivity | discriminate]].
    + destruct (cell_eqb a (default_cell segs kd acc)) eqn:E; cbn [fst snd]; [rewrite (cjoin_same _ _ E); split; reflexivity | split; [reflexivity | discriminate]].
  - destruct ta as [|a|la ra].
    + destruct tb as [|b|lb rb]; cbn [tjoin2 tjoin fst snd]; split; first [reflexivity | discriminate].
    + destruct tb as [|b|lb rb]; cbn [tjoin2 tjoin fst snd]; split; first [reflexivity | discriminate].
    + cbn [tjoin2].
      destruct (IH la (match tb with INode l _ => l | _ => IEmpty end) acc (w << 1)%uint63) as [E1 F1].
      destruct (IH ra (match tb with INode _ r => r | _ => IEmpty end) (acc + w)%uint63 (w << 1)%uint63) as [E2 F2].
      destruct (tjoin2 kd d la (match tb with INode l _ => l | _ => IEmpty end) acc (w << 1)%uint63) as [fl l'].
      destruct (tjoin2 kd d ra (match tb with INode _ r => r | _ => IEmpty end) (acc + w)%uint63 (w << 1)%uint63) as [fr r'].
      cbn [fst snd] in *. subst l' r'.
      assert (Et : tjoin kd (S d) (INode la ra) tb acc w =
                   INode (tjoin kd d la (match tb with INode l _ => l | _ => IEmpty end) acc (w << 1)%uint63)
                         (tjoin kd d ra (match tb with INode _ r => r | _ => IEmpty end) (acc + w)%uint63 (w << 1)%uint63))
        by (destruct tb; reflexivity).
      rewrite Et. destruct fl, fr; cbn [fst snd]; split; try reflexivity; try discriminate.
      * rewrite (F1 eq_refl), (F2 eq_refl). reflexivity.
      * intros _. rewrite (F1 eq_refl), (F2 eq_refl). reflexivity.
Qed.

Definition regjoin (R1 R2 : region) : option region :=
  if fields_eqb R1 R2 then Some (with_cells R1 (snd (tjoin2 (rg_kind R1) (rg_d R1) (rg_cells R1) (rg_cells R2) 0 1))) else None.

Fixpoint mjoin (A B : list region) : option (list region) :=
  match A, B with
  | [], [] => Some []
  | R1 :: A', R2 :: B' => match regjoin R1 R2, mjoin A' B' with Some R, Some l => Some (R :: l) | _, _ => None end
  | _, _ => None
  end.

End WithSegs.

Fixpoint boxjoin (ta tb : itrie (Z * Z)) : itrie (Z * Z) :=
  match ta, tb with
  | ILeaf (l1, h1), ILeaf (l2, h2) => ILeaf (Z.min l1 l2, Z.max h1 h2)
  | INode a1 a2, INode b1 b2 => INode (boxjoin a1 b1) (boxjoin a2 b2)
  | _, _ => IEmpty
  end.

Definition lin_eqb' (f g : lin) : bool := (fst f =? fst g) &&& teqb (snd f) (snd g).

Fixpoint ffind (f : lin) (l : list fact) : option fact :=
  match l with
  | [] => None
  | fc :: r => if negb (fc_hole fc) &&& lin_eqb' f (fc_f fc) then Some fc else ffind f r
  end.

Definition hole_eqb (a b : fact) : bool :=
  fc_hole b &&& (fc_lo a =? fc_lo b) &&& (fc_hi a =? fc_hi b) &&& lin_eqb' (fc_f a) (fc_f b).

Definition hole_implied (sb : store) (fc : fact) : bool :=
  match lrange sb (fc_f fc) with
  | Some (lo, hi) => (hi <=? fc_lo fc) ||| (fc_hi fc <=? lo)
  | None => false
  end.

Definition fjoin1 (sb : store) (fc : fact) : option fact :=
  if fc_hole fc then (if lexists (hole_eqb fc) (st_facts sb) ||| hole_implied sb fc then Some fc else None) else
  match ffind (fc_f fc) (st_facts sb) with
  | Some fb => Some (Fact (fc_f fc) (Z.min (fc_lo fc) (fc_lo fb)) (Z.max (fc_hi fc) (fc_hi fb)) false)
  | None => match lrange sb (fc_f fc) with
            | Some (lo, hi) => Some (Fact (fc_f fc) (Z.min (fc_lo fc) lo) (Z.max (fc_hi fc) hi) false)
            | None => None
            end
  end.

Fixpoint fjoin (sb : store) (l : list fact) : list fact :=
  match l with
  | [] => []
  | fc :: r => match fjoin1 sb fc with Some f => f :: fjoin sb r | None => fjoin sb r end
  end.

Definition hole_cands : list int := map of_Z [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15].

Definition hjoin1 (sa sb : store) (x : int) : list fact :=
  match iget bdepth (st_box sa) x, iget bdepth (st_box sb) x with
  | Some (l1, h1), Some (l2, h2) =>
      if h1 + 1 <? l2 then [Fact (lvar x 1) h1 l2 true]
      else if h2 + 1 <? l1 then [Fact (lvar x 1) h2 l1 true] else []
  | _, _ => []
  end.

Definition hjoin (sa sb : store) : list fact := flat_map (hjoin1 sa sb) hole_cands.

Fixpoint hback (sa : store) (l : list fact) : list fact :=
  match l with
  | [] => []
  | fc :: r => if fc_hole fc &&& negb (lexists (hole_eqb fc) (st_facts sa)) &&& hole_implied sa fc then fc :: hback sa r else hback sa r
  end.

Definition fact_eqb (a b : fact) : bool :=
  Bool.eqb (fc_hole a) (fc_hole b) &&& (fc_lo a =? fc_lo b) &&& (fc_hi a =? fc_hi b) &&& lin_eqb' (fc_f a) (fc_f b).

Definition fj1 (sb : store) (fc : fact) : list fact := match fjoin1 sb fc with Some f => [f] | None => [] end.

Definition hback1 (sa : store) (fc : fact) : list fact :=
  if fc_hole fc &&& negb (lexists (hole_eqb fc) (st_facts sa)) &&& hole_implied sa fc then [fc] else [].

Fixpoint fzip (sa sb : store) (la lb : list fact) : list fact :=
  match la, lb with
  | fa :: ra, fb :: rb => if fact_eqb fa fb then fa :: fzip sa sb ra rb else fj1 sb fa ++ hback1 sa fb ++ fzip sa sb ra rb
  | _, _ => fjoin sb la ++ hback sa lb
  end.

Definition fjoin_fast (sa sb : store) : list fact :=
  let la := st_facts sa in let lb := st_facts sb in
  let na := length la in let nb := length lb in
  fjoin sb (firstn (na - nb) la) ++ hback sa (firstn (nb - na) lb) ++ fzip sa sb (skipn (na - nb) la) (skipn (nb - na) lb).

Definition sjoin (sa sb : store) : store :=
  ST (boxjoin (st_box sa) (st_box sb)) (hjoin sa sb ++ fjoin_fast sa sb).

Definition set_next (am : amodel) (nx : int) : amodel :=
  AM (am_maps am) (am_brk0 am) (am_brk am) (am_tid am) (am_shadow am) nx (am_atop am) (am_out am) (am_exp am) (am_fd am).

Definition xb_eqb1 (a b : xb) : bool := xbs_eqb [a] [b].

Definition piece_eqb (p q : piece) : bool :=
  match p, q with
  | PB a, PB b => xb_eqb1 a b
  | PS j, PS k => j =? k
  | _, _ => false
  end.

Fixpoint list_eqb {X : Type} (e : X -> X -> bool) (l1 l2 : list X) : bool :=
  match l1, l2 with
  | [], [] => true
  | a :: r1, b :: r2 => e a b &&& list_eqb e r1 r2
  | _, _ => false
  end.

Definition exp_eqb (x y : aent * lin * Z) : bool :=
  aent_eqb (fst (fst x)) (fst (fst y)) &&& lin_eqb (snd (fst x)) (snd (fst y)) &&& (snd x =? snd y).

Definition afd_eqb (f g : afd) : bool :=
  match f, g with
  | FDStd, FDStd | FDDir, FDDir => true
  | FDFile o1 a1 b1 c1, FDFile o2 a2 b2 c2 => lin_eqb o1 o2 &&& (a1 =? a2)%uint63 &&& (b1 =? b2)%uint63 &&& (c1 =? c2)%uint63
  | FDDone a1 b1 c1, FDDone a2 b2 c2 => (a1 =? a2)%uint63 &&& (b1 =? b2)%uint63 &&& (c1 =? c2)%uint63
  | _, _ => false
  end.

Definition opt_xv_eqb (a b : option xv) : bool :=
  match a, b with Some x, Some y => xv_eqb x y | None, None => true | _, _ => false end.

Definition model_eqb (a b : amodel) : bool :=
  Bool.eqb (am_shadow a) (am_shadow b) &&& opt_xv_eqb (am_tid a) (am_tid b) &&& lin_eqb (am_brk a) (am_brk b)
  &&& lin_eqb (am_brk0 a) (am_brk0 b) &&& lin_eqb (am_atop a) (am_atop b) &&& afd_eqb (am_fd a) (am_fd b)
  &&& list_eqb piece_eqb (am_out a) (am_out b) &&& list_eqb exp_eqb (am_exp a) (am_exp b)
  &&& list_eqb aent_eqb (am_maps a) (am_maps b).

Definition max_next (a b : int) : int := if (a <? b)%uint63 then b else a.

Definition ajoin_state (A B : astate amodel) (mem : list region) : astate amodel :=
  AS (a_pc A) (rjoin 5 (a_facts A) (a_facts B) (a_regs A) (a_regs B)) (rsv_join (a_resv A) (a_resv B)) mem
     (sjoin (a_facts A) (a_facts B)) (set_next (a_model A) (max_next (am_next (a_model A)) (am_next (a_model B))))
     (Z.max (a_budget A) (a_budget B)) (Z.max (a_steps A) (a_steps B)).

Definition ajoin (segs : list Segment) (A B : astate amodel) : option (astate amodel) :=
  if w_eqb (a_pc A) (a_pc B) &&& model_eqb (a_model A) (a_model B) then
    match mjoin segs (a_mem A) (a_mem B) with
    | Some mem => Some (ajoin_state A B mem)
    | None => None
    end
  else None.

Definition ajoin_nm (A B : astate amodel) : option (astate amodel) :=
  if w_eqb (a_pc A) (a_pc B) then Some (ajoin_state A B (a_mem A)) else None.
