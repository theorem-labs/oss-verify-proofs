(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool List FMapPositive.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Common Require Import FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bndiv.lib.HX Require Import HxVal HxSymDef.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mono := list Z.                 (* [comment removed for export] *)
Definition poly := list (mono * Z).        (* [comment removed for export] *)

Section Eval.
Variable gam : Z -> Z.

Fixpoint meval (m : mono) : Z := match m with [] => 1 | v :: m' => gam v * meval m' end.
Fixpoint peval (p : poly) : Z := match p with [] => 0 | (m, c) :: p' => c * meval m + peval p' end.

(* [comment removed for export] *)
Fixpoint mcmp (a b : mono) : comparison :=
  match a, b with
  | [], [] => Eq
  | [], _ :: _ => Lt
  | _ :: _, [] => Gt
  | x :: a', y :: b' => match Z.compare x y with Eq => mcmp a' b' | c => c end
  end.

Lemma mcmp_eq (a : mono) : forall b, mcmp a b = Eq -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  destruct (Z.compare_spec x y) as [->|L|L]; try discriminate. f_equal. exact (IH b H).
Qed.

(* [comment removed for export] *)
Fixpoint minsert (v : Z) (m : mono) : mono :=
  match m with
  | [] => [v]
  | x :: m' => if v <=? x then v :: m else x :: minsert v m'
  end.
Definition mmul (a b : mono) : mono := fold_right minsert b a.

Lemma meval_minsert (v : Z) (m : mono) : meval (minsert v m) = gam v * meval m.
Proof. induction m as [|x m IH]; cbn [minsert meval]; [reflexivity|]. destruct (v <=? x); cbn [meval]; [reflexivity|]. rewrite IH. ring. Qed.

Lemma meval_mmul (a b : mono) : meval (mmul a b) = meval a * meval b.
Proof. induction a as [|x a IH]; cbn [mmul fold_right meval]; [ring|]. fold (mmul a b). rewrite meval_minsert, IH. ring. Qed.

(* [comment removed for export] *)
Fixpoint pins (m : mono) (c : Z) (p : poly) : poly :=
  match p with
  | [] => if c =? 0 then [] else [(m, c)]
  | (m', c') :: p' =>
      match mcmp m m' with
      | Lt => if c =? 0 then p else (m, c) :: p
      | Eq => if c + c' =? 0 then p' else (m', c + c') :: p'
      | Gt => (m', c') :: pins m c p'
      end
  end.

Lemma peval_pins (m : mono) (c : Z) (p : poly) : peval (pins m c p) = c * meval m + peval p.
Proof.
  induction p as [|[m' c'] p IH]; cbn [pins].
  - destruct (Z.eqb_spec c 0) as [->|]; cbn [peval]; ring.
  - destruct (mcmp m m') eqn:E.
    + apply mcmp_eq in E. subst m'. destruct (Z.eqb_spec (c + c') 0) as [E0|]; cbn [peval]; [|ring].
      replace (c * meval m + (c' * meval m + peval p)) with ((c + c') * meval m + peval p) by ring. rewrite E0. ring.
    + destruct (Z.eqb_spec c 0) as [->|]; cbn [peval]; ring.
    + cbn [peval]. rewrite IH. ring.
Qed.

(* [comment removed for export] *)
Fixpoint padd (p : poly) : poly -> poly :=
  fix padd_aux (q : poly) : poly :=
    match p, q with
    | [], _ => q
    | _, [] => p
    | (m1, c1) :: p', (m2, c2) :: q' =>
        match mcmp m1 m2 with
        | Lt => (m1, c1) :: padd p' q
        | Gt => (m2, c2) :: padd_aux q'
        | Eq => if c1 + c2 =? 0 then padd p' q' else (m1, c1 + c2) :: padd p' q'
        end
    end.

Lemma peval_padd (p : poly) : forall q, peval (padd p q) = peval p + peval q.
Proof.
  induction p as [|[m1 c1] p IHp]; intros q; [destruct q; reflexivity|].
  induction q as [|[m2 c2] q IHq]; [cbn; ring|].
  cbn [padd]. destruct (mcmp m1 m2) eqn:E.
  - apply mcmp_eq in E. subst m2. destruct (Z.eqb_spec (c1 + c2) 0) as [E0|]; cbn [peval]; rewrite IHp; [|ring].
    replace (c1 * meval m1 + peval p + (c2 * meval m1 + peval q)) with ((c1 + c2) * meval m1 + (peval p + peval q)) by ring. rewrite E0. ring.
  - cbn [peval]. rewrite IHp. cbn [peval]. ring.
  - cbn [peval]. change ((fix padd_aux (q0 : poly) : poly := match q0 with
                          | [] => (m1, c1) :: p
                          | (m3, c3) :: q' => match mcmp m1 m3 with
                                              | Eq => if c1 + c3 =? 0 then padd p q' else (m1, c1 + c3) :: padd p q'
                                              | Lt => (m1, c1) :: padd p q0
                                              | Gt => (m3, c3) :: padd_aux q'
                                              end
                          end) q) with (padd ((m1, c1) :: p) q). rewrite IHq. cbn [peval]. ring.
Qed.

Definition pscale (k : Z) (p : poly) : poly := if k =? 0 then [] else map (fun mc => (fst mc, k * snd mc)) p.

Lemma peval_pscale (k : Z) (p : poly) : peval (pscale k p) = k * peval p.
Proof.
  unfold pscale. destruct (Z.eqb_spec k 0) as [->|_]; [cbn; ring|].
  induction p as [|[m c] p IH]; cbn [map peval fst snd]; [ring|]. rewrite IH. ring.
Qed.

Definition psub (p q : poly) : poly := padd p (pscale (-1) q).

Lemma peval_psub (p q : poly) : peval (psub p q) = peval p - peval q.
Proof. unfold psub. rewrite peval_padd, peval_pscale. ring. Qed.

(* [comment removed for export] *)
Definition pmul1 (m : mono) (c : Z) (q : poly) (acc : poly) : poly :=
  fold_right (fun mc a => pins (mmul m (fst mc)) (c * snd mc) a) acc q.
Definition pmul (p q : poly) : poly := fold_right (fun mc a => pmul1 (fst mc) (snd mc) q a) [] p.

Lemma peval_pmul1 (m : mono) (c : Z) (q acc : poly) : peval (pmul1 m c q acc) = c * meval m * peval q + peval acc.
Proof.
  unfold pmul1. induction q as [|[m2 c2] q IH]; cbn [fold_right peval fst snd]; [ring|]. rewrite peval_pins, meval_mmul, IH. ring.
Qed.

Lemma peval_pmul (p q : poly) : peval (pmul p q) = peval p * peval q.
Proof.
  unfold pmul. induction p as [|[m c] p IH]; cbn [fold_right peval fst snd]; [ring|]. rewrite peval_pmul1, IH. ring.
Qed.

Definition pconst (z : Z) : poly := if z =? 0 then [] else [([], z)].
Lemma peval_pconst (z : Z) : peval (pconst z) = z.
Proof. unfold pconst. destruct (Z.eqb_spec z 0) as [->|]; cbn; ring. Qed.

Definition pvar (v : Z) : poly := [([v], 1)].
Lemma peval_pvar (v : Z) : peval (pvar v) = gam v.
Proof. cbn. ring. Qed.

(* [comment removed for export] *)
Fixpoint pdecomp (d : Z) (p : poly) : poly * poly :=
  match p with
  | [] => ([], [])
  | (m, c) :: p' =>
      let (L, H) := pdecomp d p' in
      if c mod d =? 0 then (L, (m, c / d) :: H) else ((m, c) :: L, H)
  end.

Lemma peval_pdecomp (d : Z) (p : poly) : 0 < d -> peval p = peval (fst (pdecomp d p)) + d * peval (snd (pdecomp d p)).
Proof.
  intros Hd. induction p as [|[m c] p IH]; [cbn; ring|]. cbn [pdecomp peval].
  destruct (pdecomp d p) as [L H]. cbn [fst snd] in IH. destruct (Z.eqb_spec (c mod d) 0) as [E|E]; cbn [fst snd peval].
  - rewrite IH. assert (c = d * (c / d)) by (apply Z.div_exact; lia). rewrite H0 at 1. ring.
  - rewrite IH. ring.
Qed.

(* [comment removed for export] *)
Definition pmodc (d : Z) (p : poly) : poly :=
  fold_right (fun mc a => if snd mc mod d =? 0 then a else (fst mc, snd mc mod d) :: a) [] p.
Definition pdivc (d : Z) (p : poly) : option poly :=
  fold_right (fun mc a => match a with
                          | Some a' => if snd mc mod d =? 0 then Some ((fst mc, snd mc / d) :: a') else None
                          | None => None end) (Some []) p.

Lemma peval_pdivc (d : Z) (p q : poly) : 0 < d -> pdivc d p = Some q -> peval p = d * peval q.
Proof.
  intros Hd. revert q. induction p as [|[m c] p IH]; intros q H; cbn [pdivc fold_right] in H.
  - injection H as <-. cbn. ring.
  - fold (pdivc d p) in H. destruct (pdivc d p) as [a'|]; [|discriminate]. cbn [fst snd] in H.
    destruct (Z.eqb_spec (c mod d) 0) as [E|E]; [|discriminate]. injection H as <-. cbn [peval]. rewrite (IH a' eq_refl).
    assert (c = d * (c / d)) by (apply Z.div_exact; lia). rewrite H at 1. ring.
Qed.

End Eval.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition MW : Z := 18446744073709551616.     (* [comment removed for export] *)

Lemma bvu_range (x : bv 64) : 0 <= bv_unsigned x < MW.
Proof. pose proof (bv_unsigned_in_range 64 x) as H. exact H. Qed.

Lemma wrap64 (z : Z) : bv_wrap 64 z = z mod MW.
Proof. reflexivity. Qed.

Lemma alu_add_u (x y : bv 64) : bv_unsigned (alu64 ALU_ADD x y) = (bv_unsigned x + bv_unsigned y) mod MW.
Proof. unfold alu64, alu. rewrite bv_add_unsigned. apply wrap64. Qed.

Lemma alu_sltu_u (x y : bv 64) : bv_unsigned (alu64 ALU_SLTU x y) = if bv_unsigned x <? bv_unsigned y then 1 else 0.
Proof. unfold alu64, alu, bv_ltu. destruct (bv_unsigned x <? bv_unsigned y); reflexivity. Qed.

Lemma shamt_u (y : bv 64) : 0 <= bv_unsigned y < 64 -> bv_unsigned (bv_and y (Z_to_bv 64 63)) = bv_unsigned y.
Proof.
  intros H. rewrite bv_and_unsigned. change (bv_unsigned (Z_to_bv 64 63)) with (Z.ones 6). rewrite Z.land_ones by lia.
  apply Z.mod_small. change (2 ^ 6) with 64. lia.
Qed.

Lemma alu_sll_u (x y : bv 64) : 0 <= bv_unsigned y < 64 ->
  bv_unsigned (alu64 ALU_SLL x y) = (bv_unsigned x * 2 ^ bv_unsigned y) mod MW.
Proof. intros H. unfold alu64, alu. rewrite bv_shiftl_unsigned, (shamt_u y H), Z.shiftl_mul_pow2 by lia. apply wrap64. Qed.

Lemma alu_srl_u (x y : bv 64) : 0 <= bv_unsigned y < 64 ->
  bv_unsigned (alu64 ALU_SRL x y) = bv_unsigned x / 2 ^ bv_unsigned y.
Proof. intros H. unfold alu64, alu. rewrite bv_shiftr_unsigned, (shamt_u y H), Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma alu_and_u (x y : bv 64) : bv_unsigned (alu64 ALU_AND x y) = Z.land (bv_unsigned x) (bv_unsigned y).
Proof. unfold alu64, alu. apply bv_and_unsigned. Qed.

Lemma mul_u (x y : bv 64) : bv_unsigned (mul_div M_MUL x y) = (bv_unsigned x * bv_unsigned y) mod MW.
Proof. unfold mul_div. rewrite bv_mul_unsigned. apply wrap64. Qed.

(* [comment removed for export] *)
Lemma sltu_carry (xv Y T K : Z) : 0 <= xv < MW -> 0 <= Y < MW -> 0 <= T < MW -> xv + Y - T = MW * K ->
  (if T <? Y then 1 else 0) = K.
Proof.
  intros Hx HY HT E. unfold MW in *. assert (HK : K = 0 \/ K = 1) by lia.
  destruct HK as [->| ->]; destruct (Z.ltb_spec T Y); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ubmap := PositiveMap.t Z.
Definition vkey (v : Z) : positive := Z.to_pos (v + 1).

Definition ub_get (U : ubmap) (v : Z) : option Z := if v <? 0 then None else PositiveMap.find (vkey v) U.
Definition ub_set (U : ubmap) (v u : Z) : ubmap := PositiveMap.add (vkey v) u U.

Lemma vkey_inj (v v' : Z) : 0 <= v -> 0 <= v' -> vkey v = vkey v' -> v = v'.
Proof. unfold vkey. intros H H' E. apply (f_equal Z.pos) in E. rewrite !Z2Pos.id in E by lia. lia. Qed.

Section Bounds.
Variable gam : Z -> Z.

Definition ub_ok (U : ubmap) : Prop := forall v u, ub_get U v = Some u -> 0 <= gam v <= u.

Lemma ub_ok_empty : ub_ok (PositiveMap.empty Z).
Proof. intros v u H. unfold ub_get in H. destruct (v <? 0); [discriminate|]. rewrite PositiveMap.gempty in H. discriminate. Qed.

Lemma ub_ok_set (U : ubmap) (v u : Z) : ub_ok U -> 0 <= v -> 0 <= gam v <= u -> ub_ok (ub_set U v u).
Proof.
  intros HU Hv Hg v' u' H. unfold ub_get, ub_set in H. destruct (Z.ltb_spec v' 0) as [|Hv']; [discriminate|].
  destruct (Pos.eq_dec (vkey v) (vkey v')) as [E|E].
  - rewrite E, PositiveMap.gss in H. injection H as <-. apply vkey_inj in E; [subst v'; exact Hg | lia | lia].
  - rewrite PositiveMap.gso in H by (intros X; apply E; symmetry; exact X). apply HU. unfold ub_get.
    destruct (Z.ltb_spec v' 0); [lia | exact H].
Qed.

Fixpoint mub (U : ubmap) (m : mono) : option Z :=
  match m with
  | [] => Some 1
  | v :: m' => match ub_get U v, mub U m' with Some u, Some r => Some (u * r) | _, _ => None end
  end.

Fixpoint pub (U : ubmap) (p : poly) : option Z :=
  match p with
  | [] => Some 0
  | (m, c) :: p' => match mub U m, pub U p' with
                    | Some um, Some r => Some ((if 0 <? c then c * um else 0) + r)
                    | _, _ => None
                    end
  end.

Definition pnonneg (p : poly) : bool := forallb (fun mc => 0 <=? snd mc) p.

Lemma mub_ok (U : ubmap) (m : mono) (u : Z) : ub_ok U -> mub U m = Some u -> 0 <= meval gam m <= u.
Proof.
  intros HU. revert u. induction m as [|v m IH]; intros u H; cbn [mub meval] in *.
  - injection H as <-. lia.
  - destruct (ub_get U v) as [uv|] eqn:Ev; [|discriminate]. destruct (mub U m) as [r|]; [|discriminate]. injection H as <-.
    pose proof (HU v uv Ev). pose proof (IH r eq_refl). nia.
Qed.

Lemma pub_ok (U : ubmap) (p : poly) (u : Z) : ub_ok U -> pub U p = Some u -> peval gam p <= u.
Proof.
  intros HU. revert u. induction p as [|[m c] p IH]; intros u H; cbn [pub peval] in *.
  - injection H as <-. lia.
  - destruct (mub U m) as [um|] eqn:Em; [|discriminate]. destruct (pub U p) as [r|]; [|discriminate]. injection H as <-.
    pose proof (mub_ok U m um HU Em). pose proof (IH r eq_refl). destruct (Z.ltb_spec 0 c); nia.
Qed.

Lemma pnonneg_ok (U : ubmap) (p : poly) (u : Z) : ub_ok U -> pub U p = Some u -> pnonneg p = true -> 0 <= peval gam p.
Proof.
  intros HU. revert u. induction p as [|[m c] p IH]; intros u H Hn; cbn [pub peval pnonneg forallb snd] in *; [lia|].
  destruct (mub U m) as [um|] eqn:Em; [|discriminate]. destruct (pub U p) as [r|]; [|discriminate].
  apply andb_prop in Hn as [Hc Hn]. apply Z.leb_le in Hc. pose proof (mub_ok U m um HU Em). pose proof (IH r eq_refl Hn). nia.
Qed.

(* [comment removed for export] *)
Definition pnonpos (p : poly) : bool := forallb (fun mc => snd mc <=? 0) p.

Lemma pnonpos_ok (U : ubmap) (p : poly) (u : Z) : ub_ok U -> pub U p = Some u -> pnonpos p = true -> peval gam p <= 0.
Proof.
  intros HU. revert u. induction p as [|[m c] p IH]; intros u H Hn; cbn [pub peval pnonpos forallb snd] in *; [lia|].
  destruct (mub U m) as [um|] eqn:Em; [|discriminate]. destruct (pub U p) as [r|]; [|discriminate].
  apply andb_prop in Hn as [Hc Hn]. apply Z.leb_le in Hc. pose proof (mub_ok U m um HU Em). pose proof (IH r eq_refl Hn). nia.
Qed.

End Bounds.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record ninfo : Type := NI { n_poly : poly; n_ub : Z; n_add : option (sarg * sarg * poly * Z) }.
Definition nmap := PositiveMap.t ninfo.

Definition tkey (t : int) : positive := vkey (to_Z t).
Definition n_get (N : nmap) (t : int) : option ninfo := PositiveMap.find (tkey t) N.
Definition n_set (N : nmap) (t : int) (ni : ninfo) : nmap := PositiveMap.add (tkey t) ni N.

Lemma n_get_set (N : nmap) (t t' : int) (ni : ninfo) : n_get (n_set N t ni) t' = if (t =? t')%uint63 then Some ni else n_get N t'.
Proof.
  unfold n_get, n_set. destruct (eqbP t t') as [E|E].
  - apply to_Z_inj in E. subst t'. apply PositiveMap.gss.
  - apply PositiveMap.gso. intros X. apply E. pose proof (to_Z_bounded t). pose proof (to_Z_bounded t'). symmetry. apply vkey_inj; [lia | lia | exact X].
Qed.

Definition sarg_eqb (a b : sarg) : bool :=
  match a, b with AC x, AC y => w_eqb x y | AN s, AN t => (s =? t)%uint63 | _, _ => false end.

Lemma sarg_eqb_eq (a b : sarg) : sarg_eqb a b = true -> a = b.
Proof.
  destruct a as [x|s], b as [y|t]; cbn; intros H; try discriminate.
  - rewrite w_eqb_spec in H. apply Z.eqb_eq in H. apply wZ_inj in H. subst. reflexivity.
  - apply Uint63.eqb_spec in H. subst. reflexivity.
Qed.

(* [comment removed for export] *)
Definition vlo (t : int) : Z := 8 * to_Z t.
Definition vhi (t : int) : Z := 8 * to_Z t + 1.
Definition vadd (t : int) : Z := 8 * to_Z t + 2.
Definition vmul (t : int) : Z := 8 * to_Z t + 3.
Definition vsplit (t : int) : Z := 8 * to_Z t + 4.

Definition T32 : Z := 4294967296.

Definition arg_info (N : nmap) (a : sarg) : option (poly * Z) :=
  match a with
  | AC w => Some (pconst (wZ w), wZ w)
  | AN t => match n_get N t with Some ni => Some (n_poly ni, n_ub ni) | None => None end
  end.

(* [comment removed for export] *)
Definition split32 (U : ubmap) (N : nmap) (t : int) : option (poly * ubmap) :=
  match n_get N t with
  | Some ni =>
      match n_add ni with
      | Some (_, _, gp, su) => Some (psub (pvar (vsplit t)) (pscale T32 gp), ub_set U (vsplit t) (su / T32))
      | None => Some (pvar (vsplit t), ub_set U (vsplit t) (n_ub ni / T32))
      end
  | None => None
  end.

(* [comment removed for export] *)
Definition add_carry (N : nmap) (T y : sarg) : option poly :=
  match T with
  | AN tg => match n_get N tg with
             | Some ni => match n_add ni with
                          | Some (a', b', gp, _) => if sarg_eqb y a' || sarg_eqb y b' then Some gp else None
                          | None => None
                          end
             | None => None
             end
  | AC _ => None
  end.

(* [comment removed for export] *)
Definition lowhigh (U : ubmap) (N : nmap) (a : sarg) (pa : poly) (k : Z) : option (poly * poly * ubmap) :=
  let (L, H) := pdecomp (2 ^ k) pa in
  let dec := match pub U L with Some uL => pnonneg L && (uL <=? 2 ^ k - 1) | None => false end in
  if dec then Some (L, H, U)
  else if k =? 32 then
    match a with
    | AN tx => match split32 U N tx with
               | Some (q, U') => Some (psub pa (pscale T32 q), q, U')
               | None => None
               end
    | AC _ => None
    end
  else None.

Definition astep (st : ubmap * nmap) (nd : snode) : option (ubmap * nmap) :=
  let (U, N) := st in
  let t := sn_t nd in
  match arg_info N (sn_a nd), arg_info N (sn_b nd) with
  | Some (pa, ua), Some (pb, ubb) =>
      match sn_op nd with
      | SAlu ALU_ADD =>
          let s := padd pa pb in
          let su := ua + ubb in
          let u := match pub U s with Some x => Z.min x su | None => su end in
          if u <=? MW - 1 then Some (U, n_set N t (NI s u (Some (sn_a nd, sn_b nd, [], su))))
          else Some (ub_set U (vadd t) 1,
                     n_set N t (NI (psub s (pscale MW (pvar (vadd t)))) (MW - 1) (Some (sn_a nd, sn_b nd, pvar (vadd t), su))))
      | SAlu ALU_SLTU =>
          match add_carry N (sn_a nd) (sn_b nd) with
          | Some gp => Some (U, n_set N t (NI gp 1 None))
          | None =>
              let x := pmodc MW (psub pa pb) in
              match pdivc MW (psub (padd x pb) pa), pub U x with
              | Some K, Some ux => if pnonneg x && (ux <=? MW - 1) then Some (U, n_set N t (NI K 1 None)) else None
              | _, _ => None
              end
          end
      | SMul M_MUL =>
          let s := pmul pa pb in
          let u := ua * ubb in
          if u <=? MW - 1 then Some (U, n_set N t (NI s u None))
          else Some (ub_set U (vmul t) (u / MW), n_set N t (NI (psub s (pscale MW (pvar (vmul t)))) (MW - 1) None))
      | SAlu ALU_SRL =>
          match sn_b nd with
          | AC w => let k := wZ w in
                    if (0 <=? k) && (k <? 64) then
                      match lowhigh U N (sn_a nd) pa k with
                      | Some (_, q, U') => Some (U', n_set N t (NI q (ua / 2 ^ k) None))
                      | None => None
                      end
                    else None
          | AN _ => None
          end
      | SAlu ALU_SLL =>
          match sn_b nd with
          | AC w => let k := wZ w in
                    if (0 <=? k) && (k <? 64) then
                      if ua * 2 ^ k <=? MW - 1 then Some (U, n_set N t (NI (pscale (2 ^ k) pa) (ua * 2 ^ k) None))
                      else match lowhigh U N (sn_a nd) pa (64 - k) with
                           | Some (l, _, U') => Some (U', n_set N t (NI (pscale (2 ^ k) l) (MW - 1) None))
                           | None => None
                           end
                    else None
          | AN _ => None
          end
      | SAlu ALU_AND =>
          match sn_b nd with
          | AC w => let c := wZ w in let k := Z.log2 (c + 1) in
                    if (c + 1 =? 2 ^ k) && (0 <=? k) && (k <? 64) then
                      match lowhigh U N (sn_a nd) pa k with
                      | Some (l, _, U') => Some (U', n_set N t (NI l (Z.min ua c) None))
                      | None => None
                      end
                    else None
          | AN _ => None
          end
      | _ => None
      end
  | _, _ => None
  end.

Fixpoint arun (st : ubmap * nmap) (l : list snode) : option (ubmap * nmap) :=
  match l with
  | [] => Some st
  | nd :: l' => match astep st nd with Some st' => arun st' l' | None => None end
  end.

(* [comment removed for export] *)
Definition ainput (st : ubmap * nmap) (t : int) : ubmap * nmap :=
  let (U, N) := st in
  (ub_set (ub_set U (vlo t) (T32 - 1)) (vhi t) (T32 - 1),
   n_set N t (NI (padd (pvar (vlo t)) (pscale T32 (pvar (vhi t)))) (MW - 1) None)).

(* [comment removed for export] *)
Definition psum (N : nmap) (tags : list int) : option poly :=
  fold_right (fun t acc => match n_get N t, acc with
                           | Some ni, Some p => Some (padd (n_poly ni) (pscale MW p))
                           | _, _ => None
                           end) (Some []) tags.

(* [comment removed for export] *)
Definition mul_check (st : ubmap * nmap) (ta tb outs : list int) (top : Z) : bool :=
  let (U, N) := st in
  match psum N outs, psum N ta, psum N tb with
  | Some po, Some pa, Some pb =>
      let D := psub po (pmul pa pb) in
      match pub U D with
      | Some _ => pnonpos D && forallb (fun mc => snd mc mod top =? 0) D
      | None => false
      end
  | _, _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition aval (rho : valuation) (a : sarg) : Z := bv_unsigned (valw rho a).

Section Sound.
Variable rho : valuation.
Variable D : Z -> option snode.      (* [comment removed for export] *)

Notation av := (aval rho).

(* [comment removed for export] *)
Definition gam (v : Z) : Z :=
  let t := of_Z (v / 8) in
  let j := v mod 8 in
  if j =? 0 then rho t mod T32
  else if j =? 1 then rho t / T32
  else match D (v / 8) with
       | Some nd =>
           let x := av (sn_a nd) in
           let y := av (sn_b nd) in
           if j =? 2 then match sn_op nd with SAlu ALU_ADD => (x + y) / MW | _ => 0 end
           else if j =? 3 then match sn_op nd with SMul M_MUL => (x * y) / MW | _ => 0 end
           else match sn_op nd with SAlu ALU_ADD => (x + y) / T32 | _ => rho t / T32 end
       | None => rho t / T32
       end.

Lemma vdiv (t : int) (j : Z) : 0 <= j < 8 -> (8 * to_Z t + j) / 8 = to_Z t /\ (8 * to_Z t + j) mod 8 = j.
Proof. intros Hj. split; [symmetry; apply (Z.div_unique _ 8 _ j); lia | symmetry; apply (Z.mod_unique _ 8 (to_Z t) j); lia]. Qed.

Lemma gam_vlo (t : int) : gam (vlo t) = rho t mod T32.
Proof. unfold gam, vlo. replace (8 * to_Z t) with (8 * to_Z t + 0) by ring. destruct (vdiv t 0 ltac:(lia)) as [-> ->]. rewrite of_to_Z. reflexivity. Qed.

Lemma gam_vhi (t : int) : gam (vhi t) = rho t / T32.
Proof. unfold gam, vhi. destruct (vdiv t 1 ltac:(lia)) as [-> ->]. rewrite of_to_Z. reflexivity. Qed.

Lemma gam_vadd (t : int) (nd : snode) : D (to_Z t) = Some nd -> sn_op nd = SAlu ALU_ADD ->
  gam (vadd t) = (av (sn_a nd) + av (sn_b nd)) / MW.
Proof. intros HD Ho. unfold gam, vadd. destruct (vdiv t 2 ltac:(lia)) as [-> ->]. rewrite HD, Ho. reflexivity. Qed.

Lemma gam_vmul (t : int) (nd : snode) : D (to_Z t) = Some nd -> sn_op nd = SMul M_MUL ->
  gam (vmul t) = (av (sn_a nd) * av (sn_b nd)) / MW.
Proof. intros HD Ho. unfold gam, vmul. destruct (vdiv t 3 ltac:(lia)) as [-> ->]. rewrite HD, Ho. reflexivity. Qed.

Lemma gam_vsplit_add (t : int) (nd : snode) : D (to_Z t) = Some nd -> sn_op nd = SAlu ALU_ADD ->
  gam (vsplit t) = (av (sn_a nd) + av (sn_b nd)) / T32.
Proof. intros HD Ho. unfold gam, vsplit. destruct (vdiv t 4 ltac:(lia)) as [-> ->]. rewrite HD, Ho. reflexivity. Qed.

Lemma gam_vsplit_other (t : int) : (D (to_Z t) = None \/ exists nd, D (to_Z t) = Some nd /\ sn_op nd <> SAlu ALU_ADD) ->
  gam (vsplit t) = rho t / T32.
Proof.
  intros H. unfold gam, vsplit. destruct (vdiv t 4 ltac:(lia)) as [-> ->]. rewrite of_to_Z. cbn [Z.eqb].
  destruct H as [-> | (nd & -> & Hne)]; [reflexivity|]. destruct (sn_op nd) as [[]|]; try reflexivity. contradiction.
Qed.

(* [comment removed for export] *)
Definition node_inv (t : int) (ni : ninfo) : Prop :=
  rho t = peval gam (n_poly ni) /\ 0 <= rho t <= n_ub ni /\ n_ub ni <= MW - 1
  /\ match n_add ni with
     | Some (a, b, gp, su) => av a + av b = rho t + MW * peval gam gp /\ av a + av b <= su /\ gam (vsplit t) = (av a + av b) / T32
     | None => gam (vsplit t) = rho t / T32
     end.

Definition state_inv (st : ubmap * nmap) : Prop :=
  ub_ok gam (fst st) /\ forall t ni, n_get (snd st) t = Some ni -> node_inv t ni.

Lemma state_inv_set (U U' : ubmap) (N : nmap) (t : int) (ni : ninfo) :
  state_inv (U, N) -> ub_ok gam U' -> node_inv t ni -> state_inv (U', n_set N t ni).
Proof.
  intros [_ HN] HU' Hni. split; [exact HU'|]. intros t' ni' H. cbn [snd] in H. rewrite n_get_set in H.
  destruct (eqbP t t') as [E|E]; [apply to_Z_inj in E; subst t'; injection H as <-; exact Hni | exact (HN t' ni' H)].
Qed.

Lemma av_range (a : sarg) : 0 <= av a < MW.
Proof. apply bvu_range. Qed.

Lemma arg_ok (st : ubmap * nmap) (a : sarg) (pa : poly) (ua : Z) :
  state_inv st -> arg_info (snd st) a = Some (pa, ua) -> av a = peval gam pa /\ av a <= ua /\ ua <= MW - 1.
Proof.
  intros [_ HN] H. destruct a as [w|t]; cbn [arg_info] in H.
  - injection H as <- <-. unfold aval. cbn [valw]. rewrite wbv_unsigned, peval_pconst. pose proof (wZ_range w). unfold two64, MW in *. lia.
  - destruct (n_get (snd st) t) as [ni|] eqn:E; [|discriminate]. injection H as <- <-.
    destruct (HN t ni E) as (H1 & H2 & H3 & _). unfold aval. cbn [valw]. rewrite Z_to_bv_unsigned, wrap64, Z.mod_small by (unfold MW in *; lia).
    split; [exact H1|]. split; [lia | exact H3].
Qed.

Lemma av_node (st : ubmap * nmap) (t : int) (ni : ninfo) : state_inv st -> n_get (snd st) t = Some ni -> av (AN t) = rho t.
Proof.
  intros [_ HN] E. destruct (HN t ni E) as (_ & H2 & H3 & _). unfold aval. cbn [valw].
  rewrite Z_to_bv_unsigned, wrap64. apply Z.mod_small. unfold MW in *. lia.
Qed.

(* [comment removed for export] *)
Lemma split32_ok (U U' : ubmap) (N : nmap) (t : int) (q : poly) :
  state_inv (U, N) -> split32 U N t = Some (q, U') -> ub_ok gam U' /\ peval gam q = rho t / T32.
Proof.
  intros [HU HN] H. unfold split32 in H. destruct (n_get N t) as [ni|] eqn:E; [|discriminate].
  destruct (HN t ni E) as (H1 & H2 & H3 & H4). pose proof (to_Z_bounded t) as Bt.
  destruct (n_add ni) as [[[[a b] gp] su]|].
  - injection H as <- <-. destruct H4 as (E1 & E2 & E3). pose proof (av_range a). pose proof (av_range b). split.
    + apply ub_ok_set; [exact HU | unfold vsplit; lia|]. rewrite E3. split; [apply Z.div_pos; unfold T32; lia | apply Z.div_le_mono; unfold T32; lia].
    + rewrite peval_psub, peval_pvar, peval_pscale, E3, E1. replace (rho t + MW * peval gam gp) with (rho t + (T32 * peval gam gp) * T32) by (unfold MW, T32; ring).
      rewrite Z.div_add by (unfold T32; lia). ring.
  - injection H as <- <-. split.
    + apply ub_ok_set; [exact HU | unfold vsplit; lia|]. rewrite H4. split; [apply Z.div_pos; unfold T32; lia | apply Z.div_le_mono; unfold T32; lia].
    + rewrite peval_pvar. exact H4.
Qed.

Lemma lowhigh_ok (U U' : ubmap) (N : nmap) (a : sarg) (pa l q : poly) (ua k : Z) :
  state_inv (U, N) -> arg_info N a = Some (pa, ua) -> 0 <= k -> lowhigh U N a pa k = Some (l, q, U') ->
  ub_ok gam U' /\ peval gam l = av a mod 2 ^ k /\ peval gam q = av a / 2 ^ k.
Proof.
  intros Hst Ha Hk H. pose proof Hst as [HU HN]. destruct (arg_ok (U, N) a pa ua Hst Ha) as (Ev & _ & _).
  assert (P2 : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  unfold lowhigh in H. pose proof (peval_pdecomp gam (2 ^ k) pa P2) as Ed. destruct (pdecomp (2 ^ k) pa) as [L Hh]. cbn [fst snd] in Ed.
  destruct (match pub U L with Some uL => pnonneg L && (uL <=? 2 ^ k - 1) | None => false end) eqn:Edec.
  - injection H as <- <- <-. destruct (pub U L) as [uL|] eqn:EuL; [|discriminate]. apply andb_prop in Edec as [Hnn Hle]. apply Z.leb_le in Hle.
    pose proof (pub_ok gam U L uL HU EuL). pose proof (pnonneg_ok gam U L uL HU EuL Hnn).
    split; [exact HU|]. rewrite Ev, Ed. split.
    + apply (Z.mod_unique _ _ (peval gam Hh)); [left; lia | ring].
    + apply (Z.div_unique _ _ _ (peval gam L)); [left; lia | ring].
  - destruct (Z.eqb_spec k 32) as [->|]; [|discriminate]. destruct a as [w|tx]; [discriminate|].
    destruct (split32 U N tx) as [[q0 U0]|] eqn:Es; [|discriminate]. injection H as <- <- <-.
    destruct (split32_ok U U0 N tx q0 Hst Es) as [HU0 Eq]. split; [exact HU0|].
    cbn [arg_info] in Ha. destruct (n_get N tx) as [ni|] eqn:En; [|discriminate].
    rewrite (av_node (U, N) tx ni Hst En). change (2 ^ 32) with T32. split; [|exact Eq].
    rewrite peval_psub, peval_pscale, Eq, <- Ev, (av_node (U, N) tx ni Hst En). rewrite (Z.mod_eq (rho tx) T32) by (unfold T32; lia). ring.
Qed.


Lemma shl_mod (X k : Z) : 0 <= k < 64 -> (X * 2 ^ k) mod MW = (X mod 2 ^ (64 - k)) * 2 ^ k.
Proof.
  intros Hk. replace MW with (2 ^ (64 - k) * 2 ^ k) by (rewrite <- Z.pow_add_r by lia; replace (64 - k + k) with 64 by ring; reflexivity).
  apply Z.mul_mod_distr_r; apply Z.pow_nonzero; lia.
Qed.

Local Ltac zl := unfold MW, T32 in *; lia.
Local Ltac nzl := unfold MW, T32 in *; nia.

Theorem astep_sound (st st' : ubmap * nmap) (nd : snode) :
  state_inv st -> node_ok rho nd -> D (to_Z (sn_t nd)) = Some nd -> astep st nd = Some st' -> state_inv st'.
Proof.
  intros Hst Hok HD H. destruct st as [U N]. pose proof Hst as [HU HN]. cbn [fst snd] in HU, HN.
  unfold astep in H. set (t := sn_t nd) in *.
  destruct (arg_info N (sn_a nd)) as [[pa ua]|] eqn:Ea; [|discriminate].
  destruct (arg_info N (sn_b nd)) as [[pb ubb]|] eqn:Eb; [|discriminate].
  destruct (arg_ok (U, N) _ pa ua Hst Ea) as (EX & HX & HuX). destruct (arg_ok (U, N) _ pb ubb Hst Eb) as (EY & HY & HuY).
  pose proof (av_range (sn_a nd)) as RX. pose proof (av_range (sn_b nd)) as RY.
  remember (av (sn_a nd)) as X eqn:EXd. remember (av (sn_b nd)) as Y eqn:EYd.
  unfold node_ok in Hok. fold t in Hok. pose proof (to_Z_bounded t) as Bt.
  assert (Rt : forall v : bv 64, rho t = bv_unsigned v -> 0 <= rho t < MW) by (intros v ->; apply bvu_range).
  (* [comment removed for export] *)
  assert (Hsp : sn_op nd <> SAlu ALU_ADD -> gam (vsplit t) = rho t / T32).
  { intros Hne. apply gam_vsplit_other. right. exists nd. split; [exact HD | exact Hne]. }
  destruct (sn_op nd) as [op|op] eqn:Eop; [destruct op; try discriminate | destruct op; try discriminate]; cbn [sop_eval] in Hok.
  - (* [comment removed for export] *)
    pose proof (Rt _ Hok) as Rr. rewrite alu_add_u in Hok. fold (aval rho (sn_a nd)) (aval rho (sn_b nd)) in Hok. rewrite <- EXd, <- EYd in Hok.
    set (s := padd pa pb) in *. assert (Es : peval gam s = X + Y) by (unfold s; rewrite peval_padd, <- EX, <- EY; reflexivity).
    set (su := ua + ubb) in *. assert (Hsu : X + Y <= su) by (unfold su; zl).
    set (u := match pub U s with Some x => Z.min x su | None => su end) in *.
    assert (Hu : X + Y <= u).
    { unfold u. destruct (pub U s) as [x|] eqn:Ep; [|exact Hsu]. pose proof (pub_ok gam U s x HU Ep). zl. }
    clearbody u. clearbody su. clearbody s.
    assert (Esp : gam (vsplit t) = (X + Y) / T32) by (rewrite EXd, EYd; apply (gam_vsplit_add t nd HD Eop)).
    destruct (Z.leb_spec u (MW - 1)) as [Hle|Hgt]; injection H as <-.
    + apply state_inv_set with (U := U); [exact Hst | exact HU|]. rewrite Z.mod_small in Hok by zl.
      unfold node_inv. cbn [n_poly n_ub n_add]. rewrite Es, <- EXd, <- EYd. split; [exact Hok|]. split; [zl|]. split; [zl|].
      cbn [peval]. split; [zl|]. split; [exact Hsu | exact Esp].
    + pose proof (gam_vadd t nd HD Eop) as Eg. rewrite <- EXd, <- EYd in Eg.
      assert (HG : 0 <= gam (vadd t) <= 1).
      { rewrite Eg. split; [apply Z.div_pos; unfold MW in *; zl|]. assert ((X + Y) / MW < 2) by (apply Z.div_lt_upper_bound; zl). zl. }
      apply state_inv_set with (U := U); [exact Hst | apply ub_ok_set; [exact HU | unfold vadd; zl | exact HG]|].
      unfold node_inv. cbn [n_poly n_ub n_add]. rewrite peval_psub, peval_pscale, peval_pvar, Es, Eg, <- EXd, <- EYd.
      rewrite (Z.mod_eq (X + Y) MW) in Hok by (unfold MW; zl).
      split; [rewrite Hok; ring|]. split; [zl|]. split; [zl|]. split; [rewrite Hok; ring|]. split; [exact Hsu | exact Esp].
  - (* [comment removed for export] *)
    destruct (sn_b nd) as [w|] eqn:Esb; [|discriminate]. set (k := wZ w) in *.
    destruct ((0 <=? k) && (k <? 64)) eqn:Ek; [|discriminate]. apply andb_prop in Ek as [K1 K2]. apply Z.leb_le in K1. apply Z.ltb_lt in K2.
    assert (EYk : Y = k) by (rewrite EYd; unfold aval; cbn [valw]; apply wbv_unsigned).
    pose proof (Rt _ Hok) as Rr. rewrite alu_sll_u in Hok by (fold (aval rho (AC w)); rewrite <- EYd; zl).
    fold (aval rho (sn_a nd)) (aval rho (AC w)) in Hok. rewrite <- EXd, <- EYd in Hok. rewrite EYk in Hok.
    assert (P2 : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; zl).
    destruct (Z.leb_spec (ua * 2 ^ k) (MW - 1)) as [Hle|Hgt].
    + injection H as <-. apply state_inv_set with (U := U); [exact Hst | exact HU|].
      assert (X * 2 ^ k <= ua * 2 ^ k) by nzl. rewrite Z.mod_small in Hok by (unfold MW in *; nzl).
      unfold node_inv. cbn [n_poly n_ub n_add]. rewrite peval_pscale, <- EX. split; [rewrite Hok; ring|]. split; [zl|]. split; [zl|].
      apply Hsp. discriminate.
    + destruct (lowhigh U N (sn_a nd) pa (64 - k)) as [[[l q] U']|] eqn:El; [|discriminate]. injection H as <-.
      destruct (lowhigh_ok U U' N _ pa l q ua (64 - k) Hst Ea ltac:(zl) El) as (HU' & El' & _). rewrite <- EXd in El'.
      apply state_inv_set with (U := U); [exact Hst | exact HU'|]. rewrite shl_mod in Hok by zl.
      unfold node_inv. cbn [n_poly n_ub n_add]. rewrite peval_pscale, El'. split; [rewrite Hok; ring|]. split; [zl|]. split; [zl|].
      apply Hsp. discriminate.
  - (* [comment removed for export] *)
    pose proof (Rt _ Hok) as Rr. rewrite alu_sltu_u in Hok. fold (aval rho (sn_a nd)) (aval rho (sn_b nd)) in Hok. rewrite <- EXd, <- EYd in Hok.
    assert (Fin : forall K : poly, (if X <? Y then 1 else 0) = peval gam K -> state_inv (U, n_set N t (NI K 1 None))).
    { intros K EK. apply state_inv_set with (U := U); [exact Hst | exact HU|]. unfold node_inv. cbn [n_poly n_ub n_add].
      split; [rewrite Hok; exact EK|]. split; [rewrite Hok; destruct (X <? Y); zl|]. split; [unfold MW; zl|]. apply Hsp. discriminate. }
    destruct (add_carry N (sn_a nd) (sn_b nd)) as [gp|] eqn:Eac.
    + injection H as <-. apply Fin. unfold add_carry in Eac. destruct (sn_a nd) as [|tg] eqn:Esa; [discriminate|].
      destruct (n_get N tg) as [ni|] eqn:En; [|discriminate]. destruct (HN tg ni En) as (_ & _ & _ & H4).
      destruct (n_add ni) as [[[[a' b'] gp'] su']|]; [|discriminate]. destruct H4 as (E1 & _ & _).
      assert (EXt : X = rho tg) by (rewrite EXd; exact (av_node (U, N) tg ni Hst En)).
      pose proof (av_range a'). pose proof (av_range b').
      destruct (sarg_eqb (sn_b nd) a') eqn:Ea'.
      * injection Eac as <-. apply sarg_eqb_eq in Ea'. apply (sltu_carry (av b') Y X); [zl | zl | zl|]. rewrite EYd, Ea', EXt. zl.
      * destruct (sarg_eqb (sn_b nd) b') eqn:Eb'; [|discriminate]. injection Eac as <-. apply sarg_eqb_eq in Eb'.
        apply (sltu_carry (av a') Y X); [zl | zl | zl|]. rewrite EYd, Eb', EXt. zl.
    + set (x := pmodc MW (psub pa pb)) in *.
      destruct (pdivc MW (psub (padd x pb) pa)) as [K|] eqn:EK; [|discriminate]. destruct (pub U x) as [ux|] eqn:Eux; [|discriminate].
      destruct (pnonneg x && (ux <=? MW - 1)) eqn:Ec; [|discriminate]. injection H as <-. apply andb_prop in Ec as [C1 C2]. apply Z.leb_le in C2.
      apply Fin. pose proof (peval_pdivc gam MW _ K ltac:(unfold MW; zl) EK) as EKv. rewrite peval_psub, peval_padd, <- EX, <- EY in EKv.
      pose proof (pub_ok gam U x ux HU Eux). pose proof (pnonneg_ok gam U x ux HU Eux C1).
      apply (sltu_carry (peval gam x) Y X); [zl | zl | zl | exact EKv].
  - (* [comment removed for export] *)
    destruct (sn_b nd) as [w|] eqn:Esb; [|discriminate]. set (k := wZ w) in *.
    destruct ((0 <=? k) && (k <? 64)) eqn:Ek; [|discriminate]. apply andb_prop in Ek as [K1 K2]. apply Z.leb_le in K1. apply Z.ltb_lt in K2.
    assert (EYk : Y = k) by (rewrite EYd; unfold aval; cbn [valw]; apply wbv_unsigned).
    pose proof (Rt _ Hok) as Rr. rewrite alu_srl_u in Hok by (fold (aval rho (AC w)); rewrite <- EYd; zl).
    fold (aval rho (sn_a nd)) (aval rho (AC w)) in Hok. rewrite <- EXd, <- EYd in Hok. rewrite EYk in Hok.
    assert (P2 : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; zl).
    destruct (lowhigh U N (sn_a nd) pa k) as [[[l q] U']|] eqn:El; [|discriminate]. injection H as <-.
    destruct (lowhigh_ok U U' N _ pa l q ua k Hst Ea ltac:(zl) El) as (HU' & _ & Eq). rewrite <- EXd in Eq.
    apply state_inv_set with (U := U); [exact Hst | exact HU'|].
    unfold node_inv. cbn [n_poly n_ub n_add]. rewrite Eq. split; [exact Hok|].
    assert (X / 2 ^ k <= ua / 2 ^ k) by (apply Z.div_le_mono; zl). assert (ua / 2 ^ k <= ua) by (apply Z.div_le_upper_bound; nzl).
    split; [zl|]. split; [zl|]. apply Hsp. discriminate.
  - (* [comment removed for export] *)
    destruct (sn_b nd) as [w|] eqn:Esb; [|discriminate]. set (c := wZ w) in *. set (k := Z.log2 (c + 1)) in *.
    destruct ((c + 1 =? 2 ^ k) && (0 <=? k) && (k <? 64)) eqn:Ek; [|discriminate].
    apply andb_prop in Ek as [Ek K2]. apply andb_prop in Ek as [K0 K1]. apply Z.eqb_eq in K0. apply Z.leb_le in K1. apply Z.ltb_lt in K2.
    assert (EYc : Y = c) by (rewrite EYd; unfold aval; cbn [valw]; apply wbv_unsigned).
    pose proof (Rt _ Hok) as Rr. rewrite alu_and_u in Hok. fold (aval rho (sn_a nd)) (aval rho (AC w)) in Hok. rewrite <- EXd, <- EYd in Hok.
    rewrite EYc in Hok. replace c with (Z.ones k) in Hok by (rewrite Z.ones_equiv; zl). rewrite Z.land_ones in Hok by zl.
    assert (P2 : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; zl).
    destruct (lowhigh U N (sn_a nd) pa k) as [[[l q] U']|] eqn:El; [|discriminate]. injection H as <-.
    destruct (lowhigh_ok U U' N _ pa l q ua k Hst Ea ltac:(zl) El) as (HU' & El' & _). rewrite <- EXd in El'.
    apply state_inv_set with (U := U); [exact Hst | exact HU'|].
    unfold node_inv. cbn [n_poly n_ub n_add]. rewrite El'. split; [exact Hok|].
    pose proof (Z.mod_pos_bound X (2 ^ k) P2). assert (X mod 2 ^ k <= X) by (apply Z.mod_le; zl).
    split; [zl|]. split; [zl|]. apply Hsp. discriminate.
  - (* [comment removed for export] *)
    pose proof (Rt _ Hok) as Rr. rewrite mul_u in Hok. fold (aval rho (sn_a nd)) (aval rho (sn_b nd)) in Hok. rewrite <- EXd, <- EYd in Hok.
    set (s := pmul pa pb) in *. assert (Es : peval gam s = X * Y) by (unfold s; rewrite peval_pmul, <- EX, <- EY; reflexivity). clearbody s.
    assert (Hu : X * Y <= ua * ubb) by nzl.
    destruct (Z.leb_spec (ua * ubb) (MW - 1)) as [Hle|Hgt]; injection H as <-.
    + apply state_inv_set with (U := U); [exact Hst | exact HU|]. rewrite Z.mod_small in Hok by nzl.
      unfold node_inv. cbn [n_poly n_ub n_add]. rewrite Es. split; [exact Hok|]. split; [nzl|]. split; [zl|]. apply Hsp. discriminate.
    + pose proof (gam_vmul t nd HD Eop) as Eg. rewrite <- EXd, <- EYd in Eg.
      assert (HG : 0 <= gam (vmul t) <= ua * ubb / MW).
      { rewrite Eg. split; [apply Z.div_pos; unfold MW in *; nzl | apply Z.div_le_mono; unfold MW in *; zl]. }
      apply state_inv_set with (U := U); [exact Hst | apply ub_ok_set; [exact HU | unfold vmul; zl | exact HG]|].
      unfold node_inv. cbn [n_poly n_ub n_add]. rewrite peval_psub, peval_pscale, peval_pvar, Es, Eg.
      rewrite (Z.mod_eq (X * Y) MW) in Hok by (unfold MW; zl).
      split; [rewrite Hok; ring|]. split; [zl|]. split; [zl|]. apply Hsp. discriminate.
Qed.


(* [comment removed for export] *)
Lemma ainput_ok (st : ubmap * nmap) (t : int) :
  state_inv st -> 0 <= rho t < MW -> D (to_Z t) = None -> state_inv (ainput st t).
Proof.
  intros Hst Hr HD. destruct st as [U N]. pose proof Hst as [HU _]. cbn [fst] in HU. unfold ainput.
  pose proof (to_Z_bounded t) as Bt. assert (P : 0 < T32) by (unfold T32; lia).
  pose proof (Z.mod_pos_bound (rho t) T32 P) as Hm.
  assert (Hd : 0 <= rho t / T32 <= T32 - 1).
  { split; [apply Z.div_pos; lia|]. assert (rho t / T32 < T32) by (apply Z.div_lt_upper_bound; unfold MW, T32 in *; lia). lia. }
  apply state_inv_set with (U := U); [exact Hst| |].
  - apply ub_ok_set; [apply ub_ok_set; [exact HU | unfold vlo; lia | rewrite gam_vlo; lia] | unfold vhi; lia | rewrite gam_vhi; exact Hd].
  - unfold node_inv. cbn [n_poly n_ub n_add]. rewrite peval_padd, peval_pscale, !peval_pvar, gam_vlo, gam_vhi.
    split; [rewrite (Z.div_mod (rho t) T32) at 1 by lia; ring|]. split; [lia|]. split; [lia|].
    apply gam_vsplit_other. left. exact HD.
Qed.

Lemma ainputs_ok (l : list int) : forall st, state_inv st -> (forall t, In t l -> 0 <= rho t < MW /\ D (to_Z t) = None) ->
  state_inv (fold_left ainput l st).
Proof.
  induction l as [|t l IH]; intros st Hst H; cbn [fold_left]; [exact Hst|].
  apply IH; [|intros t' Ht'; apply H; right; exact Ht']. destruct (H t (or_introl eq_refl)) as [H1 H2]. exact (ainput_ok st t Hst H1 H2).
Qed.

Lemma state_inv_empty : state_inv (PositiveMap.empty Z, PositiveMap.empty ninfo).
Proof. split; [apply ub_ok_empty|]. intros t ni H. unfold n_get in H. cbn [snd] in H. rewrite PositiveMap.gempty in H. discriminate. Qed.

Lemma arun_sound (l : list snode) : forall st st', state_inv st -> Forall (node_ok rho) l ->
  (forall nd, In nd l -> D (to_Z (sn_t nd)) = Some nd) -> arun st l = Some st' -> state_inv st'.
Proof.
  induction l as [|nd l IH]; intros st st' Hst Hok HD H; cbn [arun] in H; [injection H as <-; exact Hst|].
  destruct (astep st nd) as [st1|] eqn:E; [|discriminate]. inversion Hok as [|? ? Hnd Hl]; subst.
  apply (IH st1 st'); [|exact Hl | intros nd' Hin; apply HD; right; exact Hin | exact H].
  exact (astep_sound st st1 nd Hst Hnd (HD nd (or_introl eq_refl)) E).
Qed.

(* [comment removed for export] *)
Fixpoint hsum (l : list Z) : Z := match l with [] => 0 | x :: l' => x + MW * hsum l' end.

Lemma psum_ok (st : ubmap * nmap) (tags : list int) : state_inv st -> forall p, psum (snd st) tags = Some p ->
  peval gam p = hsum (map rho tags) /\ Forall (fun t => 0 <= rho t < MW) tags.
Proof.
  intros [_ HN]. induction tags as [|t tags IH]; intros p H; cbn [psum fold_right] in H.
  - injection H as <-. cbn. split; [reflexivity | constructor].
  - fold (psum (snd st) tags) in H. destruct (n_get (snd st) t) as [ni|] eqn:En; [|discriminate].
    destruct (psum (snd st) tags) as [q|]; [|discriminate]. injection H as <-. destruct (IH q eq_refl) as [E F].
    destruct (HN t ni En) as (H1 & H2 & H3 & _). cbn [map hsum]. rewrite peval_padd, peval_pscale, E, <- H1.
    split; [reflexivity|]. constructor; [unfold MW in *; lia | exact F].
Qed.

Lemma hsum_nonneg (l : list Z) : Forall (fun x => 0 <= x) l -> 0 <= hsum l.
Proof. induction 1 as [|x l Hx _ IH]; cbn [hsum]; [lia|]. unfold MW. nia. Qed.

Lemma pdivisible (top : Z) (p : poly) : forallb (fun mc => snd mc mod top =? 0) p = true -> 0 < top -> exists e, peval gam p = top * e.
Proof.
  intros H Ht. induction p as [|[m c] p IH]; cbn [forallb snd peval] in *; [exists 0; ring|].
  apply andb_prop in H as [Hc H]. apply Z.eqb_eq in Hc. destruct (IH H) as [e E]. exists (c / top * meval gam m + e).
  rewrite E. assert (c = top * (c / top)) by (apply Z.div_exact; lia). rewrite H0 at 1. ring.
Qed.

Theorem mul_check_sound (st : ubmap * nmap) (ta tb outs : list int) (top : Z) :
  state_inv st -> mul_check st ta tb outs top = true -> 0 < top ->
  hsum (map rho ta) * hsum (map rho tb) < top ->
  hsum (map rho outs) = hsum (map rho ta) * hsum (map rho tb) /\ Forall (fun t => 0 <= rho t < MW) outs.
Proof.
  intros Hst H Htop Hlt. pose proof Hst as [HU _]. destruct st as [U N]. cbn [fst] in HU. unfold mul_check in H.
  destruct (psum N outs) as [po|] eqn:Eo; [|discriminate]. destruct (psum N ta) as [pa|] eqn:Ea; [|discriminate].
  destruct (psum N tb) as [pb|] eqn:Eb; [|discriminate].
  destruct (psum_ok (U, N) outs Hst po Eo) as [Vo Fo]. destruct (psum_ok (U, N) ta Hst pa Ea) as [Va _]. destruct (psum_ok (U, N) tb Hst pb Eb) as [Vb _].
  set (Dp := psub po (pmul pa pb)) in *. destruct (pub U Dp) as [u|] eqn:Eu; [|discriminate]. apply andb_prop in H as [Hnp Hdiv].
  pose proof (pnonpos_ok gam U Dp u HU Eu Hnp) as Hle. destruct (pdivisible top Dp Hdiv Htop) as [e Ee].
  unfold Dp in Hle, Ee. rewrite peval_psub, peval_pmul, Vo, Va, Vb in Hle, Ee.
  assert (Hpos : 0 <= hsum (map rho outs)).
  { apply hsum_nonneg. rewrite Forall_map. eapply Forall_impl; [|exact Fo]. intros t Ht. cbn in Ht. lia. }
  split; [|exact Fo]. assert (e = 0) by nia. subst e. lia.
Qed.

End Sound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition dfind (l : list snode) (z : Z) : option snode := find (fun nd => to_Z (sn_t nd) =? z) l.

(* [comment removed for export] *)
Fixpoint incr_chk (lo : Z) (l : list snode) : bool :=
  match l with
  | [] => true
  | nd :: l' => (lo <=? to_Z (sn_t nd)) && incr_chk (to_Z (sn_t nd) + 1) l'
  end.

Lemma dfind_below (l : list snode) : forall lo z, incr_chk lo l = true -> z < lo -> dfind l z = None.
Proof.
  induction l as [|nd l IH]; intros lo z H Hz; [reflexivity|]. cbn [incr_chk] in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
  unfold dfind. cbn [find]. destruct (Z.eqb_spec (to_Z (sn_t nd)) z) as [E|E]; [lia|]. apply (IH (to_Z (sn_t nd) + 1) z H2). lia.
Qed.

Lemma dfind_in (l : list snode) : forall lo nd, incr_chk lo l = true -> In nd l -> dfind l (to_Z (sn_t nd)) = Some nd.
Proof.
  induction l as [|n0 l IH]; intros lo nd H Hin; [destruct Hin|]. cbn [incr_chk] in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
  unfold dfind. cbn [find]. destruct Hin as [->|Hin]; [rewrite Z.eqb_refl; reflexivity|].
  destruct (Z.eqb_spec (to_Z (sn_t n0)) (to_Z (sn_t nd))) as [E|E]; [|exact (IH _ nd H2 Hin)].
  exfalso. pose proof (IH _ nd H2 Hin) as X. rewrite <- E in X. rewrite (dfind_below l (to_Z (sn_t n0) + 1) (to_Z (sn_t n0)) H2 ltac:(lia)) in X. discriminate.
Qed.

(* [comment removed for export] *)
Theorem mul_cert (rho : valuation) (log : list snode) (ta tb outs : list int) (lo top : Z) (st : ubmap * nmap) :
  Forall (node_ok rho) log ->
  (forall t, In t (ta ++ tb) -> 0 <= rho t < MW /\ to_Z t < lo) ->
  incr_chk lo log = true ->
  arun (fold_left ainput (ta ++ tb) (PositiveMap.empty Z, PositiveMap.empty ninfo)) log = Some st ->
  mul_check st ta tb outs top = true -> 0 < top -> hsum (map rho ta) * hsum (map rho tb) < top ->
  hsum (map rho outs) = hsum (map rho ta) * hsum (map rho tb) /\ Forall (fun t => 0 <= rho t < MW) outs.
Proof.
  intros Hok Hin Hincr Hrun Hchk Htop Hlt.
  apply (mul_check_sound rho (dfind log) st ta tb outs top); try assumption.
  eapply (arun_sound rho (dfind log) log _ st); [|exact Hok | intros nd Hnd; exact (dfind_in log lo nd Hincr Hnd) | exact Hrun].
  apply ainputs_ok; [apply state_inv_empty|]. intros t Ht. destruct (Hin t Ht) as [H1 H2]. split; [exact H1|].
  exact (dfind_below log lo (to_Z t) Hincr H2).
Qed.
