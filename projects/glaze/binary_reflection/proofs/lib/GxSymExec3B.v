(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SymExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SymExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Set Keyed Unification.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Module AX2B.
Import AX2.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
#[local] Notation "a || b" := (if a then true else b) (at level 50, left associativity, only parsing) : bool_scope.
Create HintDb bceq discriminated.
(* [comment removed for export] *)
Definition existsb_lz {A : Type} (f : A -> bool) : list A -> bool :=
  fix go (l : list A) : bool := match l with [] => false | x :: r => if f x then true else go r end.
Lemma existsb_lz_fe : forall A, @existsb_lz A = @existsb A.
Proof. reflexivity. Qed.
Definition forallb_lz {A : Type} (f : A -> bool) : list A -> bool :=
  fix go (l : list A) : bool := match l with [] => true | x :: r => if f x then go r else false end.
Lemma forallb_lz_fe : forall A, @forallb_lz A = @forallb A.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Definition zofn (n : nat) : Z :=
  match n with
  | 0%nat => 0 | 1%nat => 1 | 2%nat => 2 | 3%nat => 3 | 4%nat => 4 | 5%nat => 5 | 6%nat => 6 | 7%nat => 7 | 8%nat => 8
  | _ => Z.of_nat n
  end%Z.
Lemma zofn_fe : zofn = Z.of_nat.
Proof. apply functional_extensionality; intros n. do 9 (destruct n as [|n]; [reflexivity|]). reflexivity. Qed.
Definition elenf (n : nat) : expr := ELit (zofn n).
Lemma elenf_fe : elenf = elen.
Proof. apply functional_extensionality; intros n. unfold elenf, elen. rewrite zofn_fe. reflexivity. Qed.
#[export] Hint Rewrite zofn_fe elenf_fe : bceq.

(* [comment removed for export] *)
Definition pow2f (j : Z) : Z :=
  match j with
  | 0%Z => 1%Z | 1%Z => 2%Z | 2%Z => 4%Z | 3%Z => 8%Z | 4%Z => 16%Z | 5%Z => 32%Z | 6%Z => 64%Z | 7%Z => 128%Z | 8%Z => 256%Z | 9%Z => 512%Z | 10%Z => 1024%Z | 11%Z => 2048%Z | 12%Z => 4096%Z | 13%Z => 8192%Z | 14%Z => 16384%Z | 15%Z => 32768%Z | 16%Z => 65536%Z | 17%Z => 131072%Z | 18%Z => 262144%Z | 19%Z => 524288%Z | 20%Z => 1048576%Z | 21%Z => 2097152%Z | 22%Z => 4194304%Z | 23%Z => 8388608%Z | 24%Z => 16777216%Z | 25%Z => 33554432%Z | 26%Z => 67108864%Z | 27%Z => 134217728%Z | 28%Z => 268435456%Z | 29%Z => 536870912%Z | 30%Z => 1073741824%Z | 31%Z => 2147483648%Z | 32%Z => 4294967296%Z | 33%Z => 8589934592%Z | 34%Z => 17179869184%Z | 35%Z => 34359738368%Z | 36%Z => 68719476736%Z | 37%Z => 137438953472%Z | 38%Z => 274877906944%Z | 39%Z => 549755813888%Z | 40%Z => 1099511627776%Z | 41%Z => 2199023255552%Z | 42%Z => 4398046511104%Z | 43%Z => 8796093022208%Z | 44%Z => 17592186044416%Z | 45%Z => 35184372088832%Z | 46%Z => 70368744177664%Z | 47%Z => 140737488355328%Z | 48%Z => 281474976710656%Z | 49%Z => 562949953421312%Z | 50%Z => 1125899906842624%Z | 51%Z => 2251799813685248%Z | 52%Z => 4503599627370496%Z | 53%Z => 9007199254740992%Z | 54%Z => 18014398509481984%Z | 55%Z => 36028797018963968%Z | 56%Z => 72057594037927936%Z | 57%Z => 144115188075855872%Z | 58%Z => 288230376151711744%Z | 59%Z => 576460752303423488%Z | 60%Z => 1152921504606846976%Z | 61%Z => 2305843009213693952%Z | 62%Z => 4611686018427387904%Z | 63%Z => 9223372036854775808%Z | 64%Z => 18446744073709551616%Z
  | _ => 2 ^ j
  end%Z.
Lemma pow2f_fe : pow2f = Z.pow 2.
Proof.
  apply functional_extensionality; intros j. unfold pow2f. destruct j as [|p|p]; [reflexivity| |reflexivity].
  repeat (destruct p as [p|p|]; try reflexivity).
Qed.
Definition pmodF (a j : Z) : Z := if Z.leb 0 j then Z.land a (Z.pred (pow2f j)) else (a mod 2 ^ j)%Z.
Lemma pmodF_fe : pmodF = pmod.
Proof.
  apply functional_extensionality; intros a. apply functional_extensionality; intros j. unfold pmodF, pmod. rewrite pow2f_fe.
  destruct (Z.leb 0 j); [|reflexivity]. rewrite Z.ones_equiv. reflexivity.
Qed.
#[export] Hint Rewrite pow2f_fe pmodF_fe : bceq.

(* [comment removed for export] *)
Definition zm64 (z : Z) : Z := zmod64 z.
Lemma zm64_fe : zm64 = fun z => (z mod 2 ^ 64)%Z.
Proof. apply functional_extensionality; intros z. apply zmod64_eq. Qed.
Definition m2p (a j : Z) : Z := pmodF a j.
Lemma m2p_fe : m2p = fun a j => (a mod 2 ^ j)%Z.
Proof. apply functional_extensionality; intros a. apply functional_extensionality; intros j. unfold m2p. rewrite pmodF_fe. apply pmod_eq. Qed.
Definition d2p (a j : Z) : Z := pdiv a j.
Lemma d2p_fe : d2p = fun a j => (a / 2 ^ j)%Z.
Proof. apply functional_extensionality; intros a. apply functional_extensionality; intros j. apply pdiv_eq. Qed.
Definition d8 (a : Z) : Z := Z.shiftr a 3.
Lemma d8_fe : d8 = fun a => (a / 8)%Z.
Proof. apply functional_extensionality; intros a. unfold d8. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Definition sh6 (s : Z) : Z := Z.land s 63.
Lemma sh6_fe : sh6 = fun s => (s mod 64)%Z.
Proof. apply functional_extensionality; intros s. unfold sh6. change 63%Z with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.
Definition sh6w (s : Z) : Z := Z.land s 63.
Lemma sh6w_fe : sh6w = fun s => ((s mod two64) mod 64)%Z.
Proof.
  apply functional_extensionality; intros s. unfold sh6w. change 63%Z with (Z.ones 6). rewrite Z.land_ones by lia.
  symmetry. apply Z.mod_mod_divide. exists (2 ^ 58)%Z. reflexivity.
Qed.
Definition lit_shamtB (e : expr) : option Z := match e with ELit s => Some (sh6 s) | _ => None end.
Lemma lit_shamtB_fe : lit_shamtB = lit_shamt.
Proof. apply functional_extensionality; intros e. destruct e; try reflexivity. unfold lit_shamtB, lit_shamt. rewrite sh6_fe. reflexivity. Qed.
#[export] Hint Rewrite zm64_fe m2p_fe d2p_fe d8_fe sh6_fe sh6w_fe lit_shamtB_fe : bceq.
(* [comment removed for export] *)
Definition bsg {n : N} (b : bv n) : Z :=
  let u := bv_unsigned b in
  match n with
  | 12%N => if Z.ltb u 2048 then u else (u - 4096)%Z
  | 13%N => if Z.ltb u 4096 then u else (u - 8192)%Z
  | 20%N => if Z.ltb u 524288 then u else (u - 1048576)%Z
  | 21%N => if Z.ltb u 1048576 then u else (u - 2097152)%Z
  | _ => bv_signed b
  end.
Lemma bsg_lit : forall (n : N) (b : bv n) (h : Z), bv_half_modulus n = h -> bv_modulus n = (2 * h)%Z ->
  (if Z.ltb (bv_unsigned b) h then bv_unsigned b else (bv_unsigned b - 2 * h)%Z) = bv_signed b.
Proof.
  intros n b h Hh Hm. pose proof (bv_unsigned_in_range n b) as R. rewrite Hm in R.
  unfold bv_signed, bv_swrap, bv_wrap. rewrite Hh, Hm.
  destruct (Z.ltb_spec (bv_unsigned b) h).
  - rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_unique (bv_unsigned b + h) (2 * h) 1 (bv_unsigned b + h - 2 * h))%Z; lia.
Qed.
Lemma bsg_fe : @bsg = @bv_signed.
Proof.
  apply functional_extensionality_dep; intros n. apply functional_extensionality; intros b. unfold bsg.
  destruct n as [|p]; [reflexivity|].
  repeat (destruct p as [p|p|]; try reflexivity);
  first [ apply (bsg_lit _ b 2048) | apply (bsg_lit _ b 4096) | apply (bsg_lit _ b 524288) | apply (bsg_lit _ b 1048576) | reflexivity ]; reflexivity.
Qed.
Definition u64 (z : Z) : Z := zmod64 z.
Lemma u64_fe : u64 = fun z => bv_unsigned (Z_to_bv 64 z).
Proof. apply functional_extensionality; intros z. unfold u64. rewrite Z_to_bv_unsigned, zmod64_eq. reflexivity. Qed.
Definition w64 (z : Z) : Z := zmod64 z.
Lemma w64_fe : w64 = bv_wrap 64.
Proof. apply functional_extensionality; intros z. unfold w64. rewrite zmod64_eq. reflexivity. Qed.
#[export] Hint Rewrite bsg_fe u64_fe w64_fe : bceq.
Definition sg64 (u : Z) : Z := if Z.ltb u two63z then u else (u - two64)%Z.
Lemma sg64_ok : forall b : bv 64, bv_signed b = sg64 (bv_unsigned b).
Proof. intros b. rewrite <- (bsg_lit 64 b (2 ^ 63)%Z); reflexivity. Qed.
Definition lit_branchB (c : branch_cond) (x y : Z) : bool :=
  let ux := zmod64 x in let uy := zmod64 y in
  match c with
  | BC_EQ => Z.eqb ux uy | BC_NE => negb (Z.eqb ux uy)
  | BC_LT => Z.ltb (sg64 ux) (sg64 uy) | BC_GE => negb (Z.ltb (sg64 ux) (sg64 uy))
  | BC_LTU => Z.ltb ux uy | BC_GEU => negb (Z.ltb ux uy)
  end.
Lemma lit_branchB_fe : lit_branchB = lit_branch.
Proof.
  apply functional_extensionality; intros c. apply functional_extensionality; intros x. apply functional_extensionality; intros y.
  unfold lit_branchB, lit_branch, branch_taken, bv_eqb, bv_ltu, bv_lts. rewrite !sg64_ok.
  assert (Hx : bv_unsigned (Z_to_bv 64 x) = zmod64 x) by (rewrite Z_to_bv_unsigned, zmod64_eq; reflexivity).
  assert (Hy : bv_unsigned (Z_to_bv 64 y) = zmod64 y) by (rewrite Z_to_bv_unsigned, zmod64_eq; reflexivity).
  rewrite Hx, Hy. destruct c; reflexivity.
Qed.
#[export] Hint Rewrite lit_branchB_fe : bceq.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma p_aluop_eqb_eq : forall a b, aluop_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.
Lemma p_mulop_eqb_eq : forall a b, mulop_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.
Lemma p_expr_eqb_eq : forall x y, expr_eqb x y = true -> x = y.
Proof.
  induction x; destruct y; cbn; intros H; try discriminate;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      end;
    repeat match goal with
      | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
      | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
      | H : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in H
      | H : aluop_eqb _ _ = true |- _ => apply p_aluop_eqb_eq in H
      | H : mulop_eqb _ _ = true |- _ => apply p_mulop_eqb_eq in H
      | H : expr_eqb ?a _ = true, IH : forall y, expr_eqb ?a y = true -> _ |- _ => apply IH in H
      end; subst; reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint first_var (e : expr) : option nat :=
  match e with
  | ELit _ => None
  | EVar n => Some n
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b =>
      match first_var a with Some n => Some n | None => first_var b end
  | EExt _ _ _ a => first_var a
  | EBlob _ _ _ _ => None
  end.
Definition vkey_of (e : expr) : option nat := first_var (fst (lit_strip e)).   (* [comment removed for export] *)
Fixpoint lset {A : Type} (l : list (list A)) (n : nat) (x : A) {struct n} : list (list A) :=
  match n, l with
  | O, [] => [[x]]
  | O, b :: rest => (x :: b) :: rest
  | S m, [] => [] :: lset [] m x
  | S m, b :: rest => b :: lset rest m x
  end.
Definition lget {A : Type} (l : list (list A)) (n : nat) : list A := nth n l [].
Lemma lget_lset : forall (A : Type) (l : list (list A)) n x m,
  lget (lset l n x) m = if Nat.eqb m n then x :: lget l m else lget l m.
Proof.
  intros A l n. revert l. unfold lget. induction n as [|n IH]; intros l x m; destruct l as [|b rest]; destruct m as [|m]; cbn [lset nth Nat.eqb]; try reflexivity.
  - destruct m; reflexivity.
  - rewrite IH. destruct (Nat.eqb m n); destruct m; reflexivity.
  - apply IH.
Qed.
Record rindex := RI { ri_vars : list (list kentry); ri_other : list kentry }.
Definition ri_bucket (ri : rindex) (k : option nat) : list kentry :=
  match k with Some n => lget (ri_vars ri) n | None => ri_other ri end.
Fixpoint mk_ri (fk : list kentry) : rindex :=
  match fk with
  | [] => RI [] []
  | K :: rest =>
      let t := mk_ri rest in
      match K with
      | KRange e' _ _ =>
          match vkey_of e' with
          | Some n => RI (lset (ri_vars t) n K) (ri_other t)
          | None => RI (ri_vars t) (K :: ri_other t)
          end
      | _ => t
      end
  end.
(* [comment removed for export] *)
Fixpoint find_rangeF (kn : list kentry) (e : expr) : option (Z * Z) :=
  match kn with
  | [] => None
  | KRange e' lo hi :: rest =>
      if expr_eqb e e' then Some (lo, hi) else
      match e with
      | ELit _ => find_rangeF rest e
      | _ =>
        let '(v, c) := lit_strip e in
        let '(v', c') := lit_strip e' in
        if expr_eqb v v' then
          let d := (c - c')%Z in
          if (if (if (if (if Z.leb 0 lo then Z.leb lo hi else false) then Z.ltb hi two64 else false)
                  then Z.leb 0 (lo + d) else false) then Z.ltb (hi + d) two64 else false)
          then match find_rangeF rest e with
               | Some (lo2, hi2) => Some (Z.max (lo + d) lo2, Z.min (hi + d) hi2)%Z
               | None => Some ((lo + d)%Z, (hi + d)%Z)
               end
          else find_rangeF rest e
        else find_rangeF rest e
      end
  | _ :: rest => find_rangeF rest e
  end.
Lemma find_rangeF_fe : find_rangeF = find_range.
Proof. reflexivity. Qed.
Definition find_rangeI (ri : rindex) (e : expr) : option (Z * Z) := find_rangeF (ri_bucket ri (vkey_of e)) e.

Definition okey_eqb (a b : option nat) : bool :=
  match a, b with Some x, Some y => Nat.eqb x y | None, None => true | _, _ => false end.
Lemma okey_eqb_spec : forall a b, reflect (a = b) (okey_eqb a b).
Proof.
  intros [x|] [y|]; cbn; try (constructor; congruence).
  destruct (Nat.eqb_spec x y); constructor; congruence.
Qed.
Lemma ri_bucket_cons : forall t K e' lo hi k,
  K = KRange e' lo hi ->
  ri_bucket (match vkey_of e' with
             | Some n => RI (lset (ri_vars t) n K) (ri_other t)
             | None => RI (ri_vars t) (K :: ri_other t)
             end) k
  = if okey_eqb k (vkey_of e') then K :: ri_bucket t k else ri_bucket t k.
Proof.
  intros t K e' lo hi k ->. destruct (vkey_of e') as [n|] eqn:Ev; destruct k as [m|]; cbn [ri_bucket ri_vars ri_other okey_eqb]; try reflexivity.
  apply lget_lset.
Qed.
Lemma find_rangeI_eq : forall fk e, find_rangeI (mk_ri fk) e = find_range fk e.
Proof.
  intros fk e. unfold find_rangeI. rewrite find_rangeF_fe. induction fk as [|K rest IH].
  - cbn [mk_ri]. destruct (vkey_of e) as [n|]; cbn; [unfold lget; destruct n; reflexivity | reflexivity].
  - cbn [mk_ri]. destruct K as [a w v|a l|a l bk|lo hi|e1 m|e' lo hi|a n|a1 n1 a2 n2|a l c|a l];
      cbn [find_range]; rewrite <- ?IH; try reflexivity.
    rewrite (ri_bucket_cons (mk_ri rest) _ e' lo hi _ eq_refl).
    destruct (okey_eqb_spec (vkey_of e) (vkey_of e')) as [EQ|NE].
    + cbn [find_range]. rewrite IH. reflexivity.
    + rewrite IH. destruct (expr_eqb e e') eqn:Ee.
      * exfalso. apply NE. apply p_expr_eqb_eq in Ee. subst. reflexivity.
      * destruct (lit_strip e) as [v c] eqn:Lx. destruct (lit_strip e') as [v' c'] eqn:Le'.
        destruct (expr_eqb v v') eqn:Ev.
        -- exfalso. apply NE. unfold vkey_of. rewrite Lx, Le'. cbn [fst]. apply p_expr_eqb_eq in Ev. subst. reflexivity.
        -- destruct e; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint psn16 (n : nat) (acc : positive) : positive :=
  match n with
  | S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S m))))))))))))))) => psn16 m (Pos.add acc 16%positive)
  | S m => psn16 m (Pos.succ acc)
  | O => acc
  end.
Lemma psn16_spec : forall n acc, Zpos (psn16 n acc) = (Zpos acc + Z.of_nat n)%Z.
Proof.
  intros n. induction n as [n IH] using (well_founded_induction lt_wf). intros acc.
  do 16 (destruct n as [|n]; [cbn [psn16]; lia|]).
  cbn [psn16]. rewrite IH by lia. lia.
Qed.
Lemma psn16_one : forall n, psn16 n 1%positive = Pos.of_succ_nat n.
Proof.
  intros n. apply Pos2Z.inj. rewrite psn16_spec, Zpos_P_of_succ_nat. lia.
Qed.
Definition akey (a : expr) : Z := match a with EVar n => Zpos (psn16 n 1%positive) | _ => 0%Z end.   (* [comment removed for export] *)
Definition kterm : Type := ((Z * expr) * Z)%type.
Definition sfactK : Type := (list kterm * (Z * Z))%type.
Fixpoint kfy (ts : list (Z * expr)) : list kterm :=
  match ts with [] => [] | t :: r => (t, akey (snd t)) :: kfy r end.
Definition kfact (f : sfact) : sfactK := (kfy (fst f), snd f).
Fixpoint kfacts (fs : list sfact) : list sfactK :=
  match fs with [] => [] | f :: r => kfact f :: kfacts r end.

Record bctx : Type := BC {
  bc_fk : list kentry;      (* [comment removed for export] *)
  bc_ffk : list kentry;     (* [comment removed for export] *)
  bc_fs : list sfact;       (* [comment removed for export] *)
  bc_ri : rindex;           (* [comment removed for export] *)
  bc_fsK : list sfactK      (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition mkbc0 (fk : list kentry) (fs : list sfact) : bctx :=
  BC fk (facts_of fk) fs (mk_ri (facts_of fk)) (kfacts fs).


(* [comment removed for export] *)
Ltac beq_crush rw :=
  repeat (first [ reflexivity
                | progress rw
                | lazymatch goal with
                  | |- ?L = _ =>
                      lazymatch L with
                      | (if ?c then _ else _) => destruct c
                      | (match ?x with _ => _ end) => destruct x
                      end
                  end ]).

Fixpoint erange_fB (fuel : nat) (bc : bctx) (e : expr) {struct fuel} : option (Z * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
  let erange := erange_fB fuel' in
  match find_rangeI (bc_ri bc) e with
  | Some r => Some (clampi r)
  | None =>
  match (let l := lin_of e in
         if lin_trivial l then None
         else match lin_range (erange bc) (fst l) (snd l) with
              | Some (lo, hi) =>
                  (* [comment removed for export] *)
                  let q := zdiv64 lo in   (* [comment removed for export] *)
                  if Z.eqb q (zdiv64 hi) then Some ((lo - q * two64)%Z, (hi - q * two64)%Z) else None
              | None => None
              end) with
  | Some r => Some r
  | None =>
  match e with
  | ELit z => let v := zmod64 z in Some (v, v)   (* [comment removed for export] *)
  | EVar _ => None
  | EAlu op a b =>
      match op with
      | ALU_ADD =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.ltb (ah + bh) two64 then Some ((al + bl)%Z, (ah + bh)%Z)
              else if Z.leb two64 (al + bl) then Some ((al + bl - two64)%Z, (ah + bh - two64)%Z)
              else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.leb bh al then Some ((al - bh)%Z, (ah - bl)%Z)
              else if Z.ltb ah bl then Some ((al - bh + two64)%Z, (ah - bl + two64)%Z)
              else None
          | _, _ => None
          end
      | ALU_AND =>
          (* [comment removed for export] *)
          match (match b, erange bc a with
                 | ELit m, Some (al, ah) =>
                     let m' := (pmod64 m) in
                     let j := Z.log2 (m' + 1) in
                     if (Z.eqb (m' + 1) (2 ^ j) && Z.leb (pdiv al j) (pdiv ah j) && Z.eqb (pdiv al j) (pdiv ah j))%bool
                     then Some ((pmod al j)%Z, (pmod ah j)%Z)
                     else let jh := Z.log2 (two64 - m') in
                          if (Z.eqb (two64 - m') (2 ^ jh) && Z.ltb jh 64)%bool
                          then Some ((al - pmod al jh)%Z, (ah - pmod ah jh)%Z)
                          else None
                 | _, _ => None
                 end) with
          | Some r => Some r
          | None =>
          match erange bc a, erange bc b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, Z.min ah bh)
          | Some (_, ah), None => Some (0%Z, ah)
          | None, Some (_, bh) => Some (0%Z, bh)
          | None, None => None
          end
          end
      | ALU_OR =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) => Some (Z.max al bl, mask_cover (Z.max ah bh))
          | _, _ => None
          end
      | ALU_XOR =>
          match erange bc a, erange bc b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, mask_cover (Z.max ah bh))
          | _, _ => None
          end
      | ALU_SRL =>
          match erange bc a, lit_shamtB b with
          | Some (al, ah), Some s => Some ((pdiv al s)%Z, (pdiv ah s)%Z)
          | None, Some s => Some (0%Z, (2 ^ (64 - s) - 1)%Z)   (* [comment removed for export] *)
          | _, _ => None
          end
      | ALU_SRA =>
          match erange bc a, lit_shamtB b with
          | Some (al, ah), Some s =>
              if Z.ltb ah (2 ^ 63) then Some ((pdiv al s)%Z, (pdiv ah s)%Z)
              else (* [comment removed for export] *)
                if Z.leb (2 ^ 63) al then Some ((two64 + pdiv (al - two64) s)%Z, (two64 + pdiv (ah - two64) s)%Z)
                else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange bc a, lit_shamtB b with
          | Some (al, ah), Some s =>
              if Z.ltb (pmul ah s) two64 then Some ((pmul al s)%Z, (pmul ah s)%Z) else None
          | _, _ => None
          end
      | ALU_SLTU =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.ltb ah bl then Some (1%Z, 1%Z)
              else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z)
          | _, _ => Some (0%Z, 1%Z)
          end
      | ALU_SLT =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.ltb ah (2 ^ 63) && Z.ltb bh (2 ^ 63))%bool then
                (if Z.ltb ah bl then Some (1%Z, 1%Z)
                 else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z))
              else Some (0%Z, 1%Z)
          | _, _ => Some (0%Z, 1%Z)
          end
      end
  | EAluw op a b =>
      match op with
      | ALU_ADD =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              let bl' := if Z.eqb bl bh then zsigned64 bl else bl in
              let bh' := if Z.eqb bl bh then zsigned64 bh else bh in
              if (Z.leb 0 (al + bl') && Z.ltb (ah + bh') (2 ^ 31))%bool
              then Some ((al + bl')%Z, (ah + bh')%Z) else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb bh al && Z.ltb (ah - bl) (2 ^ 31))%bool
              then Some ((al - bh)%Z, (ah - bl)%Z) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange bc a, lit_shamtB b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb (pmul ah s') (2 ^ 31) then Some ((pmul al s')%Z, (pmul ah s')%Z) else None
          | _, _ => None
          end
      | ALU_SRL =>
          match erange bc a, lit_shamtB b with
          | Some (al0, ah0), Some s =>
              let s' := (s mod 32)%Z in
              match (if Z.ltb ah0 (2 ^ 32) then Some (al0, ah0)
                     else if Z.eqb (pdiv al0 32) (pdiv ah0 32) then Some ((pmod al0 32)%Z, (pmod ah0 32)%Z)
                     else None) with
              | Some (al, ah) =>
                  if (Z.ltb ah (2 ^ 32) && (Z.ltb 0 s' || Z.ltb ah (2 ^ 31)))%bool
                  then Some ((pdiv al s')%Z, (pdiv ah s')%Z)
                  else if Z.ltb 0 s' then Some (0%Z, (2 ^ (32 - s') - 1)%Z) else None
              | None => if Z.ltb 0 s' then Some (0%Z, (2 ^ (32 - s') - 1)%Z) else None
              end
          | None, Some s =>   (* [comment removed for export] *)
              let s' := (s mod 32)%Z in if Z.ltb 0 s' then Some (0%Z, (2 ^ (32 - s') - 1)%Z) else None
          | _, _ => None
          end
      | ALU_SRA =>
          match erange bc a, lit_shamtB b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb ah (2 ^ 31) then Some ((pdiv al s')%Z, (pdiv ah s')%Z)
              else (* [comment removed for export] *)
                if (Z.eqb (pdiv al 32) (pdiv ah 32) && Z.leb (2 ^ 31) (pmod al 32))%bool
                then Some ((two64 + pdiv (pmod al 32 - 2 ^ 32) s')%Z, (two64 + pdiv (pmod ah 32 - 2 ^ 32) s')%Z)
                else None
          | _, _ => None
          end
      | _ => None
      end
  | EMd op a b =>
      match op with
      | M_MUL =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              mul_rng al ah bl bh
          | _, _ => None
          end
      | M_MULH =>   (* [comment removed for export] *)
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl && Z.ltb ah (2 ^ 63) && Z.ltb bh (2 ^ 63))%bool
              then Some ((pdiv64 (zmulf al bl))%Z, (pdiv64 (zmulf ah bh))%Z) else None
          | _, _ => None
          end
      | M_MULHU =>   (* [comment removed for export] *)
          match rng_or_full (erange bc a), rng_or_full (erange bc b) with
          | (al, ah), (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl)%bool
              then Some ((pdiv64 (zmulf al bl))%Z, (pdiv64 (zmulf ah bh))%Z) else None
          end
      | M_DIVU =>
          match erange bc a, b with
          | Some (al, ah), ELit d =>
              let d' := (pmod64 d) in
              if Z.ltb 0 d' then Some ((al / d')%Z, (ah / d')%Z) else None
          | _, _ => None
          end
      | M_REMU =>
          match erange bc a, b with
          | Some (al, ah), ELit d =>
              let d' := (pmod64 d) in
              if Z.ltb 0 d' then Some (0%Z, Z.min ah (d' - 1)) else None
          | _, _ => None
          end
      | _ => None
      end
  | EMdw _ _ _ => None
  | EExt sx lo n a =>
      let w := ext_w n in
      if sx then
        match lo with
        | O =>
            let dec (r : option (Z * Z)) : option (Z * Z) :=
              match r with
              | Some (al, ah) =>
                  if (Z.leb 0 al && Z.ltb ah (ext_half n))%bool then Some (al, ah)
                  else if (Nat.leb 1 n && Nat.leb n 8 && Z.leb (ext_half n) al && Z.ltb ah w)%bool
                       then Some ((two64 - w + al)%Z, (two64 - w + ah)%Z) else None
              | None => None
              end in
            match dec (erange bc a) with
            | Some r => Some r
            | None => if Nat.leb n 7 then dec (erange bc (EExt false 0 n a)) else None   (* [comment removed for export] *)
            end
        | _ => None
        end
      else
        match lo, erange bc a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah w)%bool then Some (al, ah) else Some (0%Z, ext_top n)
        | _, _ => Some (0%Z, ext_top n)
        end
  | EBlob sx k i n =>
      (* [comment removed for export] *)
      if sx then Some (0%Z, two64m1) else Some (0%Z, ext_top n)%Z
  end
  end
  end
  end.

Definition erange0B (bc : bctx) (e : expr) : option (Z * Z) := erange_fB erange_fuel bc e.

Definition erangeB (bc : bctx) (e : expr) : option (Z * Z) :=
  let r := erange0B bc e in
  let '(e', s) := deand e in
  if Z.eqb s 0 then r else
  match erange0B bc (unlin (lin_of e')) with     (* [comment removed for export] *)
  | Some (lo', hi') =>
      if Z.leb s lo' then
        match r with
        | Some (lo, hi) => Some (Z.max lo (lo' - s), Z.min hi hi')
        | None => Some ((lo' - s)%Z, hi')
        end
      else r
  | None => r
  end.

Definition base_rangeB (bc : bctx) (e : expr) : option (Z * Z) :=
  match e with ELit z => let v := (z mod two64)%Z in Some (v, v) | _ => erangeB bc e end.

(* [comment removed for export] *)
Fixpoint pctz (p : positive) : Z := match p with xO q => Z.succ (pctz q) | _ => 0%Z end.
Lemma pctz_nonneg : forall p, (0 <= pctz p)%Z.
Proof. induction p; cbn [pctz]; lia. Qed.
Definition ctz64F (z : Z) : Z := match z with Z0 => 64%Z | Zpos p | Zneg p => Z.min (pctz p) 64 end.
Lemma a2_ctz_fuel_0 : forall f, ctz_fuel f 0 = Z.of_nat f.
Proof. induction f as [|f IH]; [reflexivity|]. cbn [ctz_fuel]. rewrite Zmod_0_l, Zdiv_0_l, IH. cbn [Z.eqb]. lia. Qed.
Lemma a2_ctz_fuel_pos : forall f p, ctz_fuel f (Zpos p) = Z.min (pctz p) (Z.of_nat f).
Proof.
  induction f as [|f IH]; intros p.
  - cbn [ctz_fuel]. pose proof (pctz_nonneg p). lia.
  - cbn [ctz_fuel]. destruct p as [q|q|].
    + assert (E : (Z.pos q~1 mod 2 = 1)%Z) by (rewrite Pos2Z.inj_xI, Z.add_comm, Z.mul_comm, Z.mod_add by lia; reflexivity).
      rewrite E. cbn [Z.eqb pctz]. lia.
    + assert (E : (Z.pos q~0 mod 2 = 0)%Z) by (rewrite Pos2Z.inj_xO, Z.mul_comm, Z.mod_mul by lia; reflexivity).
      assert (D : (Z.pos q~0 / 2 = Z.pos q)%Z) by (rewrite Pos2Z.inj_xO, Z.mul_comm, Z.div_mul by lia; reflexivity).
      rewrite E, D, IH. cbn [Z.eqb pctz]. lia.
    + change (Z.pos 1 mod 2)%Z with 1%Z. cbn [Z.eqb pctz]. lia.
Qed.
Lemma a2_ctz_fuel_neg : forall f p, ctz_fuel f (Zneg p) = Z.min (pctz p) (Z.of_nat f).
Proof.
  induction f as [|f IH]; intros p.
  - cbn [ctz_fuel]. pose proof (pctz_nonneg p). lia.
  - cbn [ctz_fuel]. destruct p as [q|q|].
    + assert (E : (Z.neg q~1 mod 2 = 1)%Z).
      { change (Z.neg q~1) with (- Z.pos q~1)%Z. rewrite Pos2Z.inj_xI.
        replace (- (2 * Z.pos q + 1))%Z with (1 + (- Z.pos q - 1) * 2)%Z by lia. rewrite Z.mod_add by lia. reflexivity. }
      rewrite E. cbn [Z.eqb pctz]. lia.
    + assert (E : (Z.neg q~0 mod 2 = 0)%Z).
      { change (Z.neg q~0) with (- Z.pos q~0)%Z. rewrite Pos2Z.inj_xO.
        replace (- (2 * Z.pos q))%Z with ((- Z.pos q) * 2)%Z by lia. rewrite Z.mod_mul by lia. reflexivity. }
      assert (D : (Z.neg q~0 / 2 = Z.neg q)%Z).
      { change (Z.neg q~0) with (- Z.pos q~0)%Z. rewrite Pos2Z.inj_xO.
        replace (- (2 * Z.pos q))%Z with ((- Z.pos q) * 2)%Z by lia. rewrite Z.div_mul by lia. reflexivity. }
      rewrite E, D, IH. cbn [Z.eqb pctz]. lia.
    + change (Z.neg 1 mod 2)%Z with 1%Z. cbn [Z.eqb pctz]. lia.
Qed.
Lemma ctz64F_eq : forall z, ctz64F z = ctz64 z.
Proof.
  intros [|p|p]; unfold ctz64F, ctz64.
  - rewrite a2_ctz_fuel_0. reflexivity.
  - rewrite a2_ctz_fuel_pos. reflexivity.
  - rewrite a2_ctz_fuel_neg. reflexivity.
Qed.
Lemma a2_land64 : forall z, land64 z = (z mod two64)%Z.
Proof.
  intros z. unfold land64. destruct (Z.leb 0 z && Z.ltb z two64)%bool eqn:H.
  - apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. symmetry. apply Z.mod_small. lia.
  - unfold ones64z, two64. rewrite Z.land_ones by lia. reflexivity.
Qed.
Fixpoint ealign0F (kn : list kentry) (e : expr) {struct e} : Z :=
  match find_align kn e with
  | Some m => if Z.ltb 0 m then ctz64F m else 0%Z
  | None =>
  match e with
  | ELit z => ctz64F (land64 z)
  | EAlu ALU_ADD a b => Z.min (ealign0F kn a) (ealign0F kn b)
  | EAlu ALU_SUB a b => Z.min (ealign0F kn a) (ealign0F kn b)
  | EAlu ALU_AND a b => Z.max (ealign0F kn a) (ealign0F kn b)
  | EAlu ALU_OR a b => Z.min (ealign0F kn a) (ealign0F kn b)
  | EAlu ALU_SLL a b =>
      match lit_shamt b with
      | Some s => Z.min (ealign0F kn a + s)%Z 64
      | None => 0%Z
      end
  | EMd M_MUL a b => Z.min (ealign0F kn a + ealign0F kn b)%Z 64
  | _ => 0%Z
  end
  end.
Lemma ealign0F_fe : ealign0F = ealign0.
Proof.
  apply functional_extensionality; intros kn. apply functional_extensionality; intros e.
  induction e; cbn [ealign0F ealign0]; destruct (find_align kn _) as [m|]; rewrite ?ctz64F_eq, ?a2_land64;
    try reflexivity; try (destruct op; rewrite ?IHe1, ?IHe2; reflexivity).
Qed.
Definition ealignB (bc : bctx) (e : expr) : Z := Z.max (ealign0F (bc_ffk bc) e) (pageup_align e).   (* [comment removed for export] *)

Definition lin_nowrapB (bc : bctx) (e : expr) : bool :=
  let l := lin_of e in
  match lin_range (erangeB bc) (fst l) (snd l) with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%bool
  | None => false
  end.

Fixpoint srl_expandB (bc : bctx) (ts : list (Z * expr)) : Z * list (Z * expr) :=
  match ts with
  | [] => (0%Z, [])
  | (k, a) :: rest =>
      let '(c, ts') := srl_expandB bc rest in
      let keep := (c, lins_e k a ts') in
      match a with
      | EAlu ALU_SRL e (ELit s) =>
          let k6 := sh6w s in let m := pow2f k6 in   (* [comment removed for export] *)
          if (Z.eqb (m2p k k6) 0%Z && lin_nowrapB bc e)%bool then
            let q := d2p k k6 in
            let le := lin_of e in
            if Z.leb k6 (ealignB bc e) then   (* [comment removed for export] *)
              ((c + q * fst le)%Z, fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le))
            else
            ((c + q * fst le)%Z,
             lins_e (- q)%Z (srl_rem e m) (fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le)))
          else keep
      | EAlu ALU_AND e (ELit mk) =>
          (* [comment removed for export] *)
          match highmask_s mk with
          | Some s =>
              if lin_nowrapB bc e then
                let le := lin_of e in
                ((c + k * fst le)%Z,
                 lins_e (- k)%Z (srl_rem e (2 ^ s)) (fold_right (fun t acc => lins_e (k * fst t)%Z (snd t) acc) ts' (snd le)))
              else keep
          | None => keep
          end
      | _ => keep
      end
  end.

Definition fact_nowrapB (bc : bctx) (e : expr) (hi : Z) : bool :=
  let l := lin_of e in
  match lin_range (erangeB bc) (fst l) (snd l) with
  | Some (a, b) => (Z.ltb b two64 && Z.ltb hi (a + two64))%bool
  | None => false
  end.
Definition fact_periodB (bc : bctx) (e : expr) (hi : Z) : option Z :=
  let l := lin_of e in
  match lin_range (erangeB bc) (fst l) (snd l) with
  | Some (a, b) => let q := zdiv64 b in if Z.ltb (hi + q * two64) (a + two64) then Some q else None
  | None => None
  end.

Definition sum_fact_xB (bc : bctx) (ts : list (Z * expr)) (lo hi : Z) : list sfact :=
  let '(c2, ts2) := srl_expandB bc ts in
  match ts2 with
  | _ :: _ => if Z.eqb c2 0 then [] else [(ts2, ((lo - c2)%Z, (hi - c2)%Z))]
  | [] => []
  end.

Fixpoint sum_factsB_raw (bc : bctx) (kn : list kentry) : list sfact :=
  match kn with
  | [] => []
  | KRange e lo hi :: rest =>
      match e with
      | EVar _ => sum_factsB_raw bc rest
      | _ =>
        match lin_of e with
        | (c, (_ :: _) as ts) =>
            if unit_single ts then sum_factsB_raw bc rest else
            match fact_periodB bc e hi with
            | Some q => let sh := (q * two64 - c)%Z in
                (ts, ((lo + sh)%Z, (hi + sh)%Z)) :: sum_fact_xB bc ts (lo + sh)%Z (hi + sh)%Z ++ sum_factsB_raw bc rest
            | None => sum_factsB_raw bc rest
            end
        | _ => sum_factsB_raw bc rest
        end
      end
  | _ :: rest => sum_factsB_raw bc rest
  end.
Definition sum_factsB (bc : bctx) (kn : list kentry) : list sfact := sf_sort (sum_factsB_raw bc kn).


(* [comment removed for export] *)
Lemma bc_fk_mkbc0 : forall fk fs, bc_fk (mkbc0 fk fs) = fk. Proof. reflexivity. Qed.
Lemma bc_ffk_mkbc0 : forall fk fs, bc_ffk (mkbc0 fk fs) = facts_of fk. Proof. reflexivity. Qed.
Lemma find_rangeI_mkbc0 : forall fk fs, find_rangeI (bc_ri (mkbc0 fk fs)) = find_range (facts_of fk).
Proof. intros. apply functional_extensionality. intros e. apply find_rangeI_eq. Qed.
#[export] Hint Rewrite bc_fk_mkbc0 bc_ffk_mkbc0 find_rangeI_mkbc0 : bceq.
Ltac bcfe := repeat (apply functional_extensionality; intros ?).

Lemma erange_fB_eqf0 : forall fk fs fuel, erange_fB fuel (mkbc0 fk fs) = erange_f fuel (facts_of fk).
Proof.
  intros fk fs fuel. induction fuel as [|f IH]; bcfe; [reflexivity|].
  cbn [erange_fB erange_f]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite erange_fB_eqf0 : bceq.

Lemma erange0B_eqf0 : forall fk fs, erange0B (mkbc0 fk fs) = erange0 fk.
Proof. intros. bcfe. unfold erange0B, erange0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite erange0B_eqf0 : bceq.
Lemma erangeB_eqf0 : forall fk fs, erangeB (mkbc0 fk fs) = erange fk.
Proof. intros. bcfe. unfold erangeB, erange. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite erangeB_eqf0 : bceq.
Lemma base_rangeB_eqf0 : forall fk fs, base_rangeB (mkbc0 fk fs) = base_range fk.
Proof. intros. bcfe. unfold base_rangeB, base_range. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite base_rangeB_eqf0 : bceq.
Lemma ealignB_eqf0 : forall fk fs, ealignB (mkbc0 fk fs) = ealign fk.
Proof. intros. bcfe. unfold ealignB, ealign. rewrite ealign0F_fe. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite ealignB_eqf0 : bceq.
Lemma lin_nowrapB_eqf0 : forall fk fs, lin_nowrapB (mkbc0 fk fs) = lin_nowrap fk.
Proof. intros. bcfe. unfold lin_nowrapB, lin_nowrap. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_nowrapB_eqf0 : bceq.
Lemma srl_expandB_eqf0 : forall fk fs, srl_expandB (mkbc0 fk fs) = srl_expand fk.
Proof.
  intros fk fs. apply functional_extensionality; intros ts. 
  induction ts as [|[k a] rest IH]; intros; bcfe; [reflexivity|].
  cbn [srl_expandB srl_expand]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite srl_expandB_eqf0 : bceq.
Lemma fact_nowrapB_eqf0 : forall fk fs, fact_nowrapB (mkbc0 fk fs) = fact_nowrap fk.
Proof. intros. bcfe. unfold fact_nowrapB, fact_nowrap. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite fact_nowrapB_eqf0 : bceq.
Lemma fact_periodB_eqf0 : forall fk fs, fact_periodB (mkbc0 fk fs) = fact_period fk.
Proof. intros. bcfe. unfold fact_periodB, fact_period. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite fact_periodB_eqf0 : bceq.
Lemma sum_fact_xB_eqf0 : forall fk fs, sum_fact_xB (mkbc0 fk fs) = sum_fact_x fk.
Proof. intros. bcfe. unfold sum_fact_xB, sum_fact_x. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite sum_fact_xB_eqf0 : bceq.
Lemma sum_factsB_raw_eqf0 : forall fk fs, sum_factsB_raw (mkbc0 fk fs) = sum_facts_raw fk.
Proof.
  intros fk fs. apply functional_extensionality; intros kn. 
  induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [sum_factsB_raw sum_facts_raw]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite sum_factsB_raw_eqf0 : bceq.
Lemma sum_factsB_eqf0 : forall fk fs, sum_factsB (mkbc0 fk fs) = sum_facts fk.
Proof.
  intros fk fs. apply functional_extensionality; intros kn. unfold sum_factsB, sum_facts. rewrite sum_factsB_raw_eqf0. reflexivity.
Qed.
#[export] Hint Rewrite sum_factsB_eqf0 : bceq.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mkbc (fk : list kentry) : bctx :=
  let c0 := mkbc0 fk [] in let fs := sum_factsB c0 fk in
  BC fk (bc_ffk c0) fs (bc_ri c0) (kfacts fs).
Lemma mkbc_ref : forall fk, mkbc fk = mkbc0 fk (sum_factsB (mkbc0 fk []) fk).
Proof. reflexivity. Qed.
Lemma bc_fk_mkbc : forall fk, bc_fk (mkbc fk) = fk. Proof. reflexivity. Qed.
Lemma bc_ffk_mkbc : forall fk, bc_ffk (mkbc fk) = facts_of fk. Proof. reflexivity. Qed.
Lemma bc_fs_mkbc : forall fk, bc_fs (mkbc fk) = sum_facts fk fk.
Proof. intros. rewrite mkbc_ref. cbn [bc_fs mkbc0]. rewrite sum_factsB_eqf0. reflexivity. Qed.
Lemma find_rangeI_mkbc : forall fk, find_rangeI (bc_ri (mkbc fk)) = find_range (facts_of fk).
Proof. intros. rewrite mkbc_ref. apply find_rangeI_mkbc0. Qed.
#[export] Hint Rewrite bc_fk_mkbc bc_ffk_mkbc bc_fs_mkbc find_rangeI_mkbc : bceq.
Lemma bc_fsK_mkbc : forall fk, bc_fsK (mkbc fk) = kfacts (sum_facts fk fk).
Proof. intros. rewrite mkbc_ref. cbn [bc_fsK mkbc0]. rewrite sum_factsB_eqf0. reflexivity. Qed.
Lemma erange_fB_eqf : forall fk fuel, erange_fB fuel (mkbc fk) = erange_f fuel (facts_of fk).
Proof. intros. rewrite mkbc_ref. apply erange_fB_eqf0. Qed.
#[export] Hint Rewrite erange_fB_eqf : bceq.

Lemma erange0B_eqf : forall fk, erange0B (mkbc fk) = erange0 fk.
Proof. intros. rewrite mkbc_ref. apply erange0B_eqf0. Qed.
#[export] Hint Rewrite erange0B_eqf : bceq.
Lemma erangeB_eqf : forall fk, erangeB (mkbc fk) = erange fk.
Proof. intros. rewrite mkbc_ref. apply erangeB_eqf0. Qed.
#[export] Hint Rewrite erangeB_eqf : bceq.
Lemma base_rangeB_eqf : forall fk, base_rangeB (mkbc fk) = base_range fk.
Proof. intros. rewrite mkbc_ref. apply base_rangeB_eqf0. Qed.
#[export] Hint Rewrite base_rangeB_eqf : bceq.
Lemma ealignB_eqf : forall fk, ealignB (mkbc fk) = ealign fk.
Proof. intros. rewrite mkbc_ref. apply ealignB_eqf0. Qed.
#[export] Hint Rewrite ealignB_eqf : bceq.
Lemma lin_nowrapB_eqf : forall fk, lin_nowrapB (mkbc fk) = lin_nowrap fk.
Proof. intros. rewrite mkbc_ref. apply lin_nowrapB_eqf0. Qed.
#[export] Hint Rewrite lin_nowrapB_eqf : bceq.
Lemma srl_expandB_eqf : forall fk, srl_expandB (mkbc fk) = srl_expand fk.
Proof. intros. rewrite mkbc_ref. apply srl_expandB_eqf0. Qed.
#[export] Hint Rewrite srl_expandB_eqf : bceq.
Lemma fact_nowrapB_eqf : forall fk, fact_nowrapB (mkbc fk) = fact_nowrap fk.
Proof. intros. rewrite mkbc_ref. apply fact_nowrapB_eqf0. Qed.
#[export] Hint Rewrite fact_nowrapB_eqf : bceq.
Lemma fact_periodB_eqf : forall fk, fact_periodB (mkbc fk) = fact_period fk.
Proof. intros. rewrite mkbc_ref. apply fact_periodB_eqf0. Qed.
#[export] Hint Rewrite fact_periodB_eqf : bceq.
Lemma sum_fact_xB_eqf : forall fk, sum_fact_xB (mkbc fk) = sum_fact_x fk.
Proof. intros. rewrite mkbc_ref. apply sum_fact_xB_eqf0. Qed.
#[export] Hint Rewrite sum_fact_xB_eqf : bceq.
Lemma sum_factsB_eqf : forall fk, sum_factsB (mkbc fk) = sum_facts fk.
Proof. intros. rewrite mkbc_ref. apply sum_factsB_eqf0. Qed.
#[export] Hint Rewrite sum_factsB_eqf : bceq.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zqr (K k : Z) : Z * Z := if Z.eqb K k then (1, 0)%Z else Z.div_eucl K k.
Lemma zqr_spec : forall K k, k <> 0%Z -> zqr K k = (K / k, K mod k)%Z.
Proof.
  intros K k Hk. unfold zqr. destruct (Z.eqb_spec K k) as [->|_].
  - rewrite Z.div_same, Z.mod_same by exact Hk. reflexivity.
  - unfold Z.div, Z.modulo. destruct (Z.div_eucl K k); reflexivity.
Qed.
Fixpoint fact_quotF (fts ts : list (Z * expr)) (acc : option Z) : option Z :=
  match fts with
  | [] => acc
  | (k, a) :: r =>
      if Z.eqb k 0 then None else
      let K := coef_of a ts in
      if Z.eqb K 0 then None else
      let qr := zqr K k in
      if negb (Z.eqb (snd qr) 0) then None else
      match acc with
      | None => fact_quotF r ts (Some (fst qr))
      | Some q0 => if Z.eqb q0 (fst qr) then fact_quotF r ts acc else None
      end
  end.
Lemma fact_quotF_eq : forall fts ts acc, fact_quotF fts ts acc = fact_quot fts ts acc.
Proof.
  induction fts as [|[k a] r IH]; intros ts acc; [reflexivity|]. cbn [fact_quotF fact_quot]. cbv zeta.
  destruct (Z.eqb_spec k 0) as [_|Hk]; [reflexivity|].
  destruct (Z.eqb (coef_of a ts) 0); [reflexivity|]. rewrite (zqr_spec _ _ Hk). cbn [fst snd].
  destruct (negb _); [reflexivity|]. destruct acc as [q0|]; [destruct (Z.eqb q0 _)|]; rewrite ?IH; reflexivity.
Qed.

Fixpoint sum_substF (fs : list sfact) (ts : list (Z * expr)) (lo hi : Z) (hit : bool) : list (Z * expr) * (Z * Z) * bool :=
  match fs with
  | [] => (ts, (lo, hi), hit)
  | (fts, (flo, fhi)) :: r =>
      match fact_quotF fts ts None with
      | Some q =>
          let ts' := sub_fact q fts ts in
          if Z.leb 0 q then sum_substF r ts' (lo + q * flo)%Z (hi + q * fhi)%Z true
          else sum_substF r ts' (lo + q * fhi)%Z (hi + q * flo)%Z true
      | None => sum_substF r ts lo hi hit
      end
  end.
Lemma sum_substF_fe : sum_substF = sum_subst.
Proof.
  do 5 (apply functional_extensionality; intro). rename x into fs. revert x0 x1 x2 x3.
  induction fs as [|[fts [flo fhi]] r IH]; intros ts lo hi hit; [reflexivity|]. cbn [sum_substF sum_subst].
  rewrite fact_quotF_eq. destruct (fact_quot fts ts None) as [q|]; [destruct (Z.leb 0 q)|]; apply IH.
Qed.
Fixpoint sf_ordersF (fs all : list sfact) (ts : list (Z * expr)) : list (list sfact) :=
  match fs with
  | [] => []
  | f :: r => match fact_quotF (fst f) ts None with
              | Some _ => (f :: all) :: sf_ordersF r all ts
              | None => sf_ordersF r all ts
              end
  end.
Lemma sf_ordersF_fe : sf_ordersF = sf_orders.
Proof.
  do 3 (apply functional_extensionality; intro). rename x into fs. revert x0 x1.
  induction fs as [|f r IH]; intros all ts; [reflexivity|]. cbn [sf_ordersF sf_orders]. rewrite fact_quotF_eq, IH. reflexivity.
Qed.
Definition lin_rel_coreF (rng : expr -> option (Z * Z)) (fs : list sfact) (c : Z) (ts : list (Z * expr)) : option (Z * Z) :=
  match sum_substF fs ts 0 0 false with
  | (ts', (lo0, hi0), true) =>
      match lin_range rng c ts' with
      | Some (lo, hi) => Some ((lo + lo0)%Z, (hi + hi0)%Z)
      | None => None
      end
  | _ => None
  end.
Lemma lin_rel_coreF_fe : lin_rel_coreF = lin_rel_core.
Proof. unfold lin_rel_coreF, lin_rel_core. rewrite sum_substF_fe. reflexivity. Qed.
Fixpoint lin_rel_foldF (rng : expr -> option (Z * Z)) (ords : list (list sfact)) (c : Z) (ts : list (Z * expr))
         (acc : option (Z * Z)) : option (Z * Z) :=
  match ords with
  | [] => acc
  | o :: r =>
      let acc' := match lin_rel_coreF rng o c ts, acc with
                  | Some (l, h), Some (l0, h0) => Some (Z.max l l0, Z.min h h0)
                  | Some p, None => Some p
                  | None, _ => acc
                  end in
      lin_rel_foldF rng r c ts acc'
  end.
Lemma lin_rel_foldF_fe : lin_rel_foldF = lin_rel_fold.
Proof. unfold lin_rel_foldF. rewrite lin_rel_coreF_fe. reflexivity. Qed.
Definition zcdivF (a b : Z) : Z := if Z.eqb b 1 then a else zcdiv a b.
Lemma zcdivF_fe : zcdivF = zcdiv.
Proof.
  do 2 (apply functional_extensionality; intro). unfold zcdivF, zcdiv. destruct (Z.eqb_spec x0 1) as [->|]; [|reflexivity].
  rewrite Z.div_1_r. lia.
Qed.
Definition zdivF (a b : Z) : Z := if Z.eqb b 1 then a else (a / b)%Z.
Lemma zdivF_fe : zdivF = Z.div.
Proof. do 2 (apply functional_extensionality; intro). unfold zdivF. destruct (Z.eqb_spec x0 1) as [->|]; [|reflexivity]. rewrite Z.div_1_r. reflexivity. Qed.
Lemma a1_pq_diag : forall k K, k <> 0%Z -> K = k ->
  (Z.leb 1 (Z.abs k / Z.gcd K k) && Z.eqb ((Z.abs k / Z.gcd K k * K) mod k) 0)%bool = true /\
  (Z.abs k / Z.gcd K k * K / k = 1)%Z /\ (Z.abs k / Z.gcd K k = 1)%Z.
Proof.
  intros k K Hk ->. rewrite Z.gcd_diag. assert (Ha : Z.abs k <> 0%Z) by lia. rewrite Z.div_same by exact Ha.
  rewrite Z.mul_1_l, Z.mod_same, Z.div_same by exact Hk. split; [reflexivity | split; reflexivity].
Qed.
Fixpoint part_quotF (fts ts : list (Z * expr)) : option (Z * Z) :=
  match fts with
  | [] => None
  | (k, a) :: r =>
      if Z.eqb k 0 then part_quotF r ts else
      let K := coef_of a ts in
      if Z.eqb K 0 then part_quotF r ts else
      if Z.eqb K k then Some (1, 1)%Z else
      let m := (Z.abs k / Z.gcd K k)%Z in
      if Z.leb 1 m then
        let qr := Z.div_eucl (m * K) k in
        if Z.eqb (snd qr) 0 then Some (m, fst qr) else part_quotF r ts
      else part_quotF r ts
  end.
Lemma part_quotF_fe : part_quotF = part_quot.
Proof.
  do 2 (apply functional_extensionality; intro). rename x into fts. revert x0.
  induction fts as [|[k a] r IH]; intros ts; [reflexivity|]. cbn [part_quotF part_quot]. cbv zeta.
  destruct (Z.eqb_spec k 0) as [_|Hk]; [apply IH|].
  destruct (Z.eqb (coef_of a ts) 0); [apply IH|].
  destruct (Z.eqb_spec (coef_of a ts) k) as [E|_].
  - destruct (a1_pq_diag k (coef_of a ts) Hk E) as (H1 & H2 & H3). rewrite H1, H2, H3. reflexivity.
  - destruct (Z.leb 1 (Z.abs k / Z.gcd (coef_of a ts) k)); cbn [andb]; [|apply IH].
    unfold Z.modulo, Z.div. destruct (Z.div_eucl _ k) as [q rm]. cbn [fst snd]. destruct (Z.eqb rm 0); [reflexivity | apply IH].
Qed.
Definition fq_pre (ts : list (Z * expr)) (f : sfact) : bool :=
  match fst f with
  | (k, a) :: _ => negb (Z.eqb (coef_of a ts) 0%Z)
  | [] => true
  end.
Definition lin_rel_multiF (rng : expr -> option (Z * Z)) (fs : list sfact) (c : Z) (ts : list (Z * expr)) : option (Z * Z) :=
  let fsf := List.filter (fq_pre ts) fs in
  lin_rel_foldF rng (fsf :: sf_ordersF fsf fsf ts) c ts None.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition lin_evalF (rng : expr -> option (Z * Z)) (fs : list sfact) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  if match lin_range rng c ts with
     | Some (lo, hi) => test lo hi
     | None => false
     end then true
  else match lin_rel_multiF rng fs c ts with
       | Some (lo, hi) => test lo hi
       | None => false
       end.
Fixpoint lin_chainF (fuel : nat) (rng : expr -> option (Z * Z)) (fs : list sfact) (c : Z) (ts : list (Z * expr))
         (test : Z -> Z -> bool) {struct fuel} : bool :=
  lin_evalF rng fs c ts test
  || match fuel with
     | O => false
     | S f =>
         existsb_lz (fun sf : sfact =>   (* [comment removed for export] *)
                    match part_quotF (fst sf) ts with
                    | Some (m, q) =>
                        let d := if Z.leb 0 q then ((q * fst (snd sf))%Z, (q * snd (snd sf))%Z)
                                 else ((q * snd (snd sf))%Z, (q * fst (snd sf))%Z) in
                        lin_chainF f rng fs (m * c)%Z (sub_fact q (fst sf) (scale_ts m ts))
                                  (fun lo hi => test (zcdivF (lo + fst d) m) (zdivF (hi + snd d) m))%Z
                    | None => false
                    end) fs
     end.
Lemma coef_of_lins_e_ne : forall a b k ts, expr_eqb a b = false -> coef_of a (lins_e k b ts) = coef_of a ts.
Proof.
  intros a b k ts Hab. induction ts as [|[k' a'] rest IH]; cbn [lins_e coef_of].
  - destruct (Z.eqb k 0); cbn [coef_of]; [reflexivity | rewrite Hab; reflexivity].
  - destruct (expr_eqb b a') eqn:Hba.
    + apply p_expr_eqb_eq in Hba. subst a'. rewrite Hab.
      destruct (Z.eqb (k + k') 0); cbn [coef_of]; [reflexivity | rewrite Hab; reflexivity].
    + cbn [coef_of]. destruct (expr_eqb a a'); [reflexivity | exact IH].
Qed.
Lemma coef_of_sub_fact_ne : forall a q g ts,
  (forall t, In t g -> expr_eqb a (snd t) = false) -> coef_of a (sub_fact q g ts) = coef_of a ts.
Proof.
  intros a q g ts. unfold sub_fact. induction g as [|t r IH]; intros H; [reflexivity|].
  cbn [fold_right]. rewrite coef_of_lins_e_ne by (apply H; left; reflexivity). apply IH. intros t' Ht'. apply H. right. exact Ht'.
Qed.
Lemma fact_quot_atoms : forall g ts acc q, fact_quot g ts acc = Some q -> forall t, In t g -> coef_of (snd t) ts <> 0%Z.
Proof.
  induction g as [|[k a] r IH]; intros ts acc q H t Ht; [destruct Ht|].
  cbn [fact_quot] in H. destruct (Z.eqb k 0); [discriminate|].
  destruct (Z.eqb (coef_of a ts) 0) eqn:HK; [discriminate|].
  destruct (negb (Z.eqb (coef_of a ts mod k) 0)); [discriminate|].
  destruct Ht as [<-|Ht].
  - cbn [snd]. apply Z.eqb_neq. exact HK.
  - destruct acc as [q0|]; [destruct (Z.eqb q0 (coef_of a ts / k)); [|discriminate]|]; eapply IH; eassumption.
Qed.
Definition INVc (ts0 ts' : list (Z * expr)) : Prop := forall a, coef_of a ts0 = 0%Z -> coef_of a ts' = 0%Z.
Lemma INVc_sub_fact : forall ts0 ts' g q, INVc ts0 ts' -> fact_quot g ts' None = Some q -> INVc ts0 (sub_fact q g ts').
Proof.
  intros ts0 ts' g q HI HQ a Ha. rewrite coef_of_sub_fact_ne; [exact (HI a Ha)|].
  intros t Ht. destruct (expr_eqb a (snd t)) eqn:E; [|reflexivity].
  apply p_expr_eqb_eq in E. subst a. exfalso. exact (fact_quot_atoms g ts' None q HQ t Ht (HI _ Ha)).
Qed.
Lemma fq_pre_false : forall ts0 ts' f, fq_pre ts0 f = false -> INVc ts0 ts' -> fact_quot (fst f) ts' None = None.
Proof.
  intros ts0 ts' [g iv] H HI. unfold fq_pre in H. cbn [fst] in *. destruct g as [|[k a] r]; [discriminate|].
  apply Bool.negb_false_iff in H. apply Z.eqb_eq in H. cbn [fact_quot]. destruct (Z.eqb k 0); [reflexivity|].
  rewrite (HI a H). reflexivity.
Qed.
Lemma sum_subst_filter : forall ts0 fs ts' lo hi hit, INVc ts0 ts' ->
  sum_subst (List.filter (fq_pre ts0) fs) ts' lo hi hit = sum_subst fs ts' lo hi hit.
Proof.
  intros ts0 fs. induction fs as [|[g [flo fhi]] r IH]; intros ts' lo hi hit HI; [reflexivity|].
  cbn [List.filter]. destruct (fq_pre ts0 (g, (flo, fhi))) eqn:HP.
  - cbn [sum_subst]. destruct (fact_quot g ts' None) as [q|] eqn:HQ.
    + pose proof (INVc_sub_fact ts0 ts' g q HI HQ) as HI'. destruct (Z.leb 0 q); apply IH; exact HI'.
    + apply IH; exact HI.
  - cbn [sum_subst]. pose proof (fq_pre_false ts0 ts' (g, (flo, fhi)) HP HI) as X. cbn [fst] in X. rewrite X. apply IH; exact HI.
Qed.
Lemma INVc_refl : forall ts, INVc ts ts. Proof. intros ts a H. exact H. Qed.
Lemma lin_rel_core_filter : forall rng fs c ts,
  lin_rel_core rng (List.filter (fq_pre ts) fs) c ts = lin_rel_core rng fs c ts.
Proof. intros. unfold lin_rel_core. rewrite (sum_subst_filter ts fs ts 0%Z 0%Z false (INVc_refl ts)). reflexivity. Qed.
Lemma lin_rel_fold_orders : forall rng fs c ts fs1 acc,
  lin_rel_fold rng (sf_orders (List.filter (fq_pre ts) fs1) (List.filter (fq_pre ts) fs) ts) c ts acc
  = lin_rel_fold rng (sf_orders fs1 fs ts) c ts acc.
Proof.
  intros rng fs c ts fs1. induction fs1 as [|f r IH]; intros acc; [reflexivity|].
  cbn [List.filter]. destruct (fq_pre ts f) eqn:HP.
  - cbn [sf_orders]. destruct (fact_quot (fst f) ts None) as [q|]; [|apply IH].
    cbn [lin_rel_fold].
    replace (lin_rel_core rng (f :: List.filter (fq_pre ts) fs) c ts) with (lin_rel_core rng (f :: fs) c ts).
    + apply IH.
    + rewrite <- (lin_rel_core_filter rng (f :: fs) c ts). cbn [List.filter]. rewrite HP. reflexivity.
  - cbn [sf_orders]. rewrite (fq_pre_false ts ts f HP (INVc_refl ts)). apply IH.
Qed.
Lemma lin_rel_multiF_eq : forall rng fs c ts, lin_rel_multiF rng fs c ts = lin_rel_multi rng fs c ts.
Proof.
  intros. unfold lin_rel_multiF, lin_rel_multi. cbv zeta. rewrite lin_rel_foldF_fe, sf_ordersF_fe. cbn [lin_rel_fold].
  rewrite lin_rel_core_filter. apply lin_rel_fold_orders.
Qed.
Lemma lin_evalF_eq : forall rng fs c ts test, lin_evalF rng fs c ts test = lin_eval rng fs c ts test.
Proof.
  intros. unfold lin_evalF, lin_eval. rewrite lin_rel_multiF_eq.
  destruct (lin_range rng c ts) as [[lo hi]|]; destruct (lin_rel_multi rng fs c ts) as [[lo' hi']|];
    try destruct (test lo hi); try destruct (test lo' hi'); reflexivity.
Qed.
Lemma rf_existsb_ext : forall (A : Type) (f g : A -> bool) l, (forall x, f x = g x) -> existsb f l = existsb g l.
Proof. intros A f g l H. induction l as [|x r IH]; [reflexivity|]. cbn. rewrite H, IH. reflexivity. Qed.
Lemma lin_chainF_eq : forall fuel rng fs c ts test, lin_chainF fuel rng fs c ts test = lin_chain fuel rng fs c ts test.
Proof.
  induction fuel as [|f IH]; intros rng fs c ts test; cbn [lin_chainF lin_chain]; rewrite lin_evalF_eq;
    destruct (lin_eval rng fs c ts test); try reflexivity.
  cbn [orb]. rewrite existsb_lz_fe, part_quotF_fe, zcdivF_fe, zdivF_fe. apply rf_existsb_ext. intros sf. destruct (part_quot (fst sf) ts) as [[m q]|]; [|reflexivity]. apply IH.
Qed.
Lemma lin_chainF_fe : lin_chainF = lin_chain.
Proof. do 6 (apply functional_extensionality; intro). apply lin_chainF_eq. Qed.

(* [comment removed for export] *)
Definition keq (a : expr) (ka : Z) (a' : expr) (ka' : Z) : bool :=
  match ka with
  | Z0 => match ka' with Z0 => expr_eqb a a' | _ => false end
  | _ => Z.eqb ka ka'
  end.
Lemma keq_akey : forall a a', keq a (akey a) a' (akey a') = expr_eqb a a'.
Proof.
  intros a a'. destruct a; destruct a'; unfold keq, akey; rewrite ?psn16_one; try reflexivity.
  cbn [expr_eqb Z.eqb]. destruct (Nat.eqb_spec n n0) as [->|NE]; [apply Pos.eqb_refl|].
  apply Pos.eqb_neq. intros H. apply NE. exact (SuccNat2Pos.inj _ _ H).
Qed.
Definition ers (ts : list kterm) : list (Z * expr) := map fst ts.
Lemma ers_kfy : forall ts, ers (kfy ts) = ts.
Proof. induction ts as [|t r IH]; [reflexivity|]. cbn [kfy ers map fst]. unfold ers in IH. rewrite IH. reflexivity. Qed.
Fixpoint coef_ofK (a : expr) (ka : Z) (ts : list kterm) : Z :=
  match ts with
  | [] => 0
  | ((k, a'), ka') :: r => if keq a ka a' ka' then k else coef_ofK a ka r
  end.
Lemma coef_ofK_eq : forall a ts, coef_ofK a (akey a) (kfy ts) = coef_of a ts.
Proof.
  intros a ts. induction ts as [|[k a'] r IH]; [reflexivity|]. cbn [kfy coef_ofK coef_of snd].
  rewrite keq_akey. destruct (expr_eqb a a'); [reflexivity|exact IH].
Qed.
Fixpoint fact_quotK (fts ts : list kterm) (acc : option Z) : option Z :=
  match fts with
  | [] => acc
  | ((k, a), ka) :: r =>
      if Z.eqb k 0 then None else
      let K := coef_ofK a ka ts in
      if Z.eqb K 0 then None else
      let qr := zqr K k in
      if negb (Z.eqb (snd qr) 0) then None else
      match acc with
      | None => fact_quotK r ts (Some (fst qr))
      | Some q0 => if Z.eqb q0 (fst qr) then fact_quotK r ts acc else None
      end
  end.
Lemma fact_quotK_eq : forall fts ts acc, fact_quotK (kfy fts) (kfy ts) acc = fact_quotF fts ts acc.
Proof.
  induction fts as [|[k a] r IH]; intros ts acc; [reflexivity|]. cbn [kfy fact_quotK fact_quotF snd]. rewrite coef_ofK_eq.
  destruct (Z.eqb k 0); [reflexivity|]. destruct (Z.eqb (coef_of a ts) 0); [reflexivity|].
  destruct (negb _); [reflexivity|]. destruct acc as [q0|]; [destruct (Z.eqb q0 _)|]; rewrite ?IH; reflexivity.
Qed.
Fixpoint lins_eK (k : Z) (a : expr) (ka : Z) (ts : list kterm) : list kterm :=
  match ts with
  | [] => if Z.eqb k 0 then [] else [((k, a), ka)]
  | ((k', a'), ka') :: rest =>
      if keq a ka a' ka' then (let s := (k + k')%Z in if Z.eqb s 0 then rest else ((s, a'), ka') :: rest)
      else ((k', a'), ka') :: lins_eK k a ka rest
  end.
Lemma lins_eK_eq : forall k a ts, lins_eK k a (akey a) (kfy ts) = kfy (lins_e k a ts).
Proof.
  intros k a ts. induction ts as [|[k' a'] rest IH]; cbn [kfy lins_eK lins_e snd].
  - destruct (Z.eqb k 0); reflexivity.
  - rewrite keq_akey. destruct (expr_eqb a a') eqn:E.
    + apply p_expr_eqb_eq in E. subst a'. destruct (Z.eqb (k + k') 0); reflexivity.
    + rewrite IH. reflexivity.
Qed.
Definition sub_factK (q : Z) (fts ts : list kterm) : list kterm :=
  fold_right (fun t acc => lins_eK (- (q * fst (fst t)))%Z (snd (fst t)) (snd t) acc) ts fts.
Lemma sub_factK_eq : forall q fts ts, sub_factK q (kfy fts) (kfy ts) = kfy (sub_fact q fts ts).
Proof.
  intros q fts ts. unfold sub_factK, sub_fact. induction fts as [|[k a] r IH]; [reflexivity|].
  cbn [kfy fold_right fst snd]. rewrite IH. apply lins_eK_eq.
Qed.
Definition scale_tsK (m : Z) (ts : list kterm) : list kterm := map (fun t => (((m * fst (fst t))%Z, snd (fst t)), snd t)) ts.
Lemma scale_tsK_eq : forall m ts, scale_tsK m (kfy ts) = kfy (scale_ts m ts).
Proof. intros m ts. unfold scale_tsK, scale_ts. induction ts as [|[k a] r IH]; [reflexivity|]. cbn [kfy map fst snd]. rewrite IH. reflexivity. Qed.
Fixpoint sum_substK (fs : list sfactK) (ts : list kterm) (lo hi : Z) (hit : bool) : list kterm * (Z * Z) * bool :=
  match fs with
  | [] => (ts, (lo, hi), hit)
  | (fts, (flo, fhi)) :: r =>
      match fact_quotK fts ts None with
      | Some q =>
          let ts' := sub_factK q fts ts in
          if Z.leb 0 q then sum_substK r ts' (lo + q * flo)%Z (hi + q * fhi)%Z true
          else sum_substK r ts' (lo + q * fhi)%Z (hi + q * flo)%Z true
      | None => sum_substK r ts lo hi hit
      end
  end.
Definition kres (x : list (Z * expr) * (Z * Z) * bool) : list kterm * (Z * Z) * bool := (kfy (fst (fst x)), snd (fst x), snd x).
Lemma sum_substK_eq : forall fs ts lo hi hit, sum_substK (kfacts fs) (kfy ts) lo hi hit = kres (sum_substF fs ts lo hi hit).
Proof.
  induction fs as [|[fts [flo fhi]] r IH]; intros ts lo hi hit; [reflexivity|]. cbn [kfacts kfact fst snd sum_substK sum_substF].
  rewrite fact_quotK_eq. destruct (fact_quotF fts ts None) as [q|]; [|apply IH].
  rewrite sub_factK_eq. destruct (Z.leb 0 q); apply IH.
Qed.
Definition lin_rel_coreK (rng : expr -> option (Z * Z)) (fs : list sfactK) (c : Z) (ts : list kterm) : option (Z * Z) :=
  match sum_substK fs ts 0 0 false with
  | (ts', (lo0, hi0), true) =>
      match lin_range rng c (ers ts') with
      | Some (lo, hi) => Some ((lo + lo0)%Z, (hi + hi0)%Z)
      | None => None
      end
  | _ => None
  end.
Lemma lin_rel_coreK_eq : forall rng fs c ts, lin_rel_coreK rng (kfacts fs) c (kfy ts) = lin_rel_coreF rng fs c ts.
Proof.
  intros. unfold lin_rel_coreK, lin_rel_coreF. rewrite sum_substK_eq.
  destruct (sum_substF fs ts 0 0 false) as [[ts' [lo0 hi0]] h]. cbn [kres fst snd]. rewrite ers_kfy. reflexivity.
Qed.
Fixpoint sf_ordersK (fs all : list sfactK) (ts : list kterm) : list (list sfactK) :=
  match fs with
  | [] => []
  | f :: r => match fact_quotK (fst f) ts None with
              | Some _ => (f :: all) :: sf_ordersK r all ts
              | None => sf_ordersK r all ts
              end
  end.
Lemma sf_ordersK_eq : forall fs all ts, sf_ordersK (kfacts fs) (kfacts all) (kfy ts) = map kfacts (sf_ordersF fs all ts).
Proof.
  induction fs as [|f r IH]; intros all ts; [reflexivity|]. cbn [kfacts sf_ordersK sf_ordersF].
  change (fst (kfact f)) with (kfy (fst f)). rewrite fact_quotK_eq. destruct (fact_quotF (fst f) ts None); cbn [map]; rewrite IH; reflexivity.
Qed.
Fixpoint lin_rel_foldK (rng : expr -> option (Z * Z)) (ords : list (list sfactK)) (c : Z) (ts : list kterm)
         (acc : option (Z * Z)) : option (Z * Z) :=
  match ords with
  | [] => acc
  | o :: r =>
      let acc' := match lin_rel_coreK rng o c ts, acc with
                  | Some (l, h), Some (l0, h0) => Some (Z.max l l0, Z.min h h0)
                  | Some p, None => Some p
                  | None, _ => acc
                  end in
      lin_rel_foldK rng r c ts acc'
  end.
Lemma lin_rel_foldK_eq : forall rng ords c ts acc, lin_rel_foldK rng (map kfacts ords) c (kfy ts) acc = lin_rel_foldF rng ords c ts acc.
Proof.
  intros rng ords c ts. induction ords as [|o r IH]; intros acc; [reflexivity|]. cbn [map lin_rel_foldK lin_rel_foldF].
  rewrite lin_rel_coreK_eq. apply IH.
Qed.
Definition fq_preK (ts : list kterm) (f : sfactK) : bool :=
  match fst f with
  | ((k, a), ka) :: _ => negb (Z.eqb (coef_ofK a ka ts) 0%Z)
  | [] => true
  end.
Lemma filter_fq_preK : forall ts fs, List.filter (fq_preK (kfy ts)) (kfacts fs) = kfacts (List.filter (fq_pre ts) fs).
Proof.
  intros ts fs. induction fs as [|[g iv] r IH]; [reflexivity|]. cbn [kfacts List.filter].
  assert (E : fq_preK (kfy ts) (kfact (g, iv)) = fq_pre ts (g, iv)).
  { unfold fq_preK, fq_pre, kfact. cbn [fst]. destruct g as [|[k a] g']; [reflexivity|]. cbn [kfy snd]. rewrite coef_ofK_eq. reflexivity. }
  rewrite E. destruct (fq_pre ts (g, iv)); cbn [kfacts]; rewrite IH; reflexivity.
Qed.
Definition lin_rel_multiK (rng : expr -> option (Z * Z)) (fs : list sfactK) (c : Z) (ts : list kterm) : option (Z * Z) :=
  let fsf := List.filter (fq_preK ts) fs in
  lin_rel_foldK rng (fsf :: sf_ordersK fsf fsf ts) c ts None.
Lemma lin_rel_multiK_eq : forall rng fs c ts, lin_rel_multiK rng (kfacts fs) c (kfy ts) = lin_rel_multiF rng fs c ts.
Proof.
  intros. unfold lin_rel_multiK, lin_rel_multiF. cbv zeta. rewrite filter_fq_preK, sf_ordersK_eq.
  change (kfacts (List.filter (fq_pre ts) fs) :: map kfacts (sf_ordersF (List.filter (fq_pre ts) fs) (List.filter (fq_pre ts) fs) ts))
    with (map kfacts (List.filter (fq_pre ts) fs :: sf_ordersF (List.filter (fq_pre ts) fs) (List.filter (fq_pre ts) fs) ts)).
  apply lin_rel_foldK_eq.
Qed.
Definition lin_evalK (rng : expr -> option (Z * Z)) (fs : list sfactK) (c : Z) (ts : list kterm) (test : Z -> Z -> bool) : bool :=
  if match lin_range rng c (ers ts) with
     | Some (lo, hi) => test lo hi
     | None => false
     end then true
  else match lin_rel_multiK rng fs c ts with
       | Some (lo, hi) => test lo hi
       | None => false
       end.
Lemma lin_evalK_eq : forall rng fs c ts test, lin_evalK rng (kfacts fs) c (kfy ts) test = lin_evalF rng fs c ts test.
Proof. intros. unfold lin_evalK, lin_evalF. rewrite ers_kfy, lin_rel_multiK_eq. reflexivity. Qed.
Fixpoint part_quotK (fts ts : list kterm) : option (Z * Z) :=
  match fts with
  | [] => None
  | ((k, a), ka) :: r =>
      if Z.eqb k 0 then part_quotK r ts else
      let K := coef_ofK a ka ts in
      if Z.eqb K 0 then part_quotK r ts else
      if Z.eqb K k then Some (1, 1)%Z else
      let m := (Z.abs k / Z.gcd K k)%Z in
      if Z.leb 1 m then
        let qr := Z.div_eucl (m * K) k in
        if Z.eqb (snd qr) 0 then Some (m, fst qr) else part_quotK r ts
      else part_quotK r ts
  end.
Lemma part_quotK_eq : forall fts ts, part_quotK (kfy fts) (kfy ts) = part_quotF fts ts.
Proof.
  induction fts as [|[k a] r IH]; intros ts; [reflexivity|]. cbn [kfy part_quotK part_quotF snd]. rewrite coef_ofK_eq, !IH. reflexivity.
Qed.
Lemma k1_existsb_kfacts : forall (f : sfactK -> bool) (g : sfact -> bool) fs,
  (forall sf, f (kfact sf) = g sf) -> existsb_lz f (kfacts fs) = existsb_lz g fs.
Proof. intros f g fs H. induction fs as [|sf r IH]; [reflexivity|]. cbn [kfacts]. rewrite !existsb_lz_fe in *. cbn [existsb]. rewrite H, IH. reflexivity. Qed.
Fixpoint lin_chainK (fuel : nat) (rng : expr -> option (Z * Z)) (fs : list sfactK) (c : Z) (ts : list kterm)
         (test : Z -> Z -> bool) {struct fuel} : bool :=
  if lin_evalK rng fs c ts test then true
  else match fuel with
     | O => false
     | S f =>
         existsb_lz (fun sf : sfactK =>
                    match part_quotK (fst sf) ts with
                    | Some (m, q) =>
                        let d := if Z.leb 0 q then ((q * fst (snd sf))%Z, (q * snd (snd sf))%Z)
                                 else ((q * snd (snd sf))%Z, (q * fst (snd sf))%Z) in
                        lin_chainK f rng fs (m * c)%Z (sub_factK q (fst sf) (scale_tsK m ts))
                                  (fun lo hi => test (zcdivF (lo + fst d) m) (zdivF (hi + snd d) m))%Z
                    | None => false
                    end) fs
     end.
Lemma lin_chainK_eq : forall fuel rng fs c ts test, lin_chainK fuel rng (kfacts fs) c (kfy ts) test = lin_chainF fuel rng fs c ts test.
Proof.
  induction fuel as [|f IH]; intros rng fs c ts test; cbn [lin_chainK lin_chainF]; rewrite lin_evalK_eq;
    destruct (lin_evalF rng fs c ts test); cbn [orb]; try reflexivity.
  apply k1_existsb_kfacts. intros [g [flo fhi]]. unfold kfact. cbn [fst snd]. rewrite part_quotK_eq.
  destruct (part_quotF g ts) as [[m q]|]; [|reflexivity]. rewrite scale_tsK_eq, sub_factK_eq. apply IH.
Qed.

Definition lin_test_relB (bc : bctx) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match bc_fs bc with
  | [] => false
  | _ => lin_chainK LCHAIN (erangeB bc) (bc_fsK bc) c (kfy ts) test   (* [comment removed for export] *)
  end.

Definition lin_testB (bc : bctx) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match lin_range (erangeB bc) c ts with
  | Some (lo, hi) => if test lo hi then true else lin_test_relB bc c ts test
  | None => lin_test_relB bc c ts test
  end.

Definition lin_srangeB (bc : bctx) (e : expr) : option (Z * Z) :=
  let l := lin_of e in
  let j := srl_scale_need (snd l) in
  if (if Z.leb 0 j then Z.leb j 24 else false) then   (* [comment removed for export] *)
    let sc := (2 ^ j)%Z in
    let ts := List.map (fun t => ((sc * fst t)%Z, snd t)) (snd l) in
    let '(c2, t2) := srl_expandB bc ts in
    let '(c3, t3) := (if has_srl t2 then srl_expandB bc t2 else (0%Z, t2)) in
    match lin_range (erangeB bc) (sc * fst l + c2 + c3)%Z t3 with
    | Some (lo', hi') =>
        let lo := zcdiv lo' sc in let hi := (hi' / sc)%Z in
        if (if Z.leb 0 lo then (if Z.leb lo hi then Z.ltb hi two64 else false) else false) then Some (lo, hi) else None
    | None => None
    end
  else None.

Definition lin_nowrapRB (bc : bctx) (e : expr) : bool :=
  let l := lin_of e in
  if lin_testB bc (fst l) (snd l) (fun lo hi => (Z.leb 0 lo && Z.ltb hi two64)%bool) then true else
  let '(c2, t2) := srl_expandB bc (snd l) in            (* [comment removed for export] *)
  if lin_testB bc (fst l + c2)%Z t2 (fun lo hi => (Z.leb 0 lo && Z.ltb hi two64)%bool) then true
  else (* [comment removed for export] *)
    match lin_srangeB bc e with Some _ => true | None => false end.

Definition lin_apart0B (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  (lin_nowrapRB bc b1 && lin_nowrapRB bc b2 &&
   let l1 := lin_of b1 in let l2 := lin_of b2 in
   lin_testB bc (fst l2 + k2 - fst l1 - k1)%Z (lsub_e (snd l2) (snd l1))
            (fun lo hi => (Z.leb n1 lo || Z.leb hi (- n2))%bool))%bool.

Definition lin_apartB (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if shares_var b1 b2 then lin_apart0B bc b1 k1 n1 b2 k2 n2 else false.

Definition lin_brangeB (bc : bctx) (e : expr) : option (Z * Z) :=
  let l := lin_of e in
  match bc_fs bc with
  | [] => None
  | _ =>
      match lin_rel_multiK (erangeB bc) (bc_fsK bc) (fst l) (kfy (snd l)) with   (* [comment removed for export] *)
      | Some (lo', hi') =>
          if (Z.leb 0 lo' && Z.ltb hi' two64)%bool then Some (lo', hi')
          else (* [comment removed for export] *)
            let q := zdiv64 lo' in
            if Z.eqb q (zdiv64 hi') then Some ((lo' - q * two64)%Z, (hi' - q * two64)%Z) else None
      | None => None
      end
  end.

Definition xloB (bc : bctx) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erangeB bc e with
         | Some (lo, _) => Some lo
         | None => match lin_brangeB bc e with
                   | Some (lo, _) => Some lo
                   | None => match lin_srangeB bc e with Some (lo, _) => Some lo | None => None end   (* [comment removed for export] *)
                   end
         end
  end.

Definition xhiB (bc : bctx) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erangeB bc e with
         | Some (_, hi) => Some hi
         | None => match lin_brangeB bc e with
                   | Some (_, hi) => Some hi
                   | None => match lin_srangeB bc e with Some (_, hi) => Some hi | None => None end   (* [comment removed for export] *)
                   end
         end
  end.

Fixpoint xt_nowrapB (bc : bctx) (ts : xterms) : bool :=
  match ts with [] => true | (e, _) :: r => lin_nowrapRB bc e && xt_nowrapB bc r end.

Definition lin_ge0_scaledB (bc : bctx) (c : Z) (ts : list (Z * expr)) : bool :=
  let j := srl_scale_need ts in
  if (if Z.ltb 0 j then Z.leb j 24 else false) then
    let sc := (2 ^ j)%Z in
    let ts' := List.map (fun t => ((sc * fst t)%Z, snd t)) ts in
    let '(c2, t2) := srl_expandB bc ts' in
    let '(c3, t3) := (if has_srl t2 then srl_expandB bc t2 else (0%Z, t2)) in
    lin_testB bc (sc * c + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
  else false.

(* [comment removed for export] *)
Definition e15_lnf (ts : list (Z * expr)) : list (Z * expr) := fold_right (fun t acc => lins_e (fst t) (snd t) acc) [] ts.
Definition srl_noexp1B (bc : bctx) (t : Z * expr) : bool :=
  match snd t with
  | EAlu ALU_SRL e (ELit s) => if Z.eqb (m2p (fst t) (sh6w s)) 0%Z then negb (lin_nowrapB bc e) else true
  | EAlu ALU_AND e (ELit mk) => match highmask_s mk with Some _ => negb (lin_nowrapB bc e) | None => true end
  | _ => true
  end.
Fixpoint srl_noexpB (bc : bctx) (ts : list (Z * expr)) : bool :=
  match ts with [] => true | t :: r => if srl_noexp1B bc t then srl_noexpB bc r else false end.
Definition lin_ge0B_fb0 (bc : bctx) (c : Z) (ts : list (Z * expr)) : bool :=
  let '(c2, t2) := srl_expandB bc ts in
  if lin_testB bc (c + c2)%Z t2 (fun lo _ => Z.leb 0 lo) then true
  else
  if (if has_srl t2 then
        let '(c3, t3) := srl_expandB bc t2 in
        lin_testB bc (c + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
      else false) then true
  else lin_ge0_scaledB bc c ts.
Definition lin_ge0B_fb (bc : bctx) (c : Z) (ts : list (Z * expr)) : bool :=
  if srl_noexpB bc ts then lin_ge0_scaledB bc c ts else lin_ge0B_fb0 bc c ts.

Definition lin_ge0B_old (bc : bctx) (pos neg : xterms) : bool :=
  (xt_nowrapB bc pos && xt_nowrapB bc neg &&
   (* [comment removed for export] *)
   (if lin_testB bc (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) (fun lo _ => Z.leb 0 lo) then true
    else let '(c2, t2) := srl_expandB bc (lsub_e (xt_lin pos) (xt_lin neg)) in
         if lin_testB bc (xt_const pos - xt_const neg + c2)%Z t2 (fun lo _ => Z.leb 0 lo) then true
         else (* [comment removed for export] *)
         if (if has_srl t2 then
               let '(c3, t3) := srl_expandB bc t2 in
               lin_testB bc (xt_const pos - xt_const neg + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
             else false) then true
         else (* [comment removed for export] *)
           lin_ge0_scaledB bc (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg))))%bool.
Definition lin_ge0B (bc : bctx) (pos neg : xterms) : bool :=
  (xt_nowrapB bc pos && xt_nowrapB bc neg &&
   (let c := (xt_const pos - xt_const neg)%Z in
    let ts := lsub_e (xt_lin pos) (xt_lin neg) in
    (* [comment removed for export] *)
    if lin_testB bc c ts (fun lo _ => Z.leb 0 lo) then true else lin_ge0B_fb bc c ts))%bool.

Definition xinside0B (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if lin_ge0B bc [(b1, k1)] [(b2, k2)] then lin_ge0B bc [(b2, k2); (n2, 0%Z)] [(b1, k1); (n1, 0%Z)] else false.

Definition xinside_numB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match xloB bc b2, xhiB bc b2 with
  | Some lo2, Some hi2 =>
      if Z.eqb lo2 hi2 then
        match base_rangeB bc b1, xhiB bc n1, xloB bc n2 with
        | Some (lo1, hi1), Some h1, Some l2 => Z.leb (lo2 + k2) (lo1 + k1) && Z.leb (hi1 + k1 + h1) (lo2 + k2 + l2)
        | _, _, _ => false
        end
      else false
  | _, _ => false
  end.

Definition xinsideB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if shares_var b1 b2 then xinside0B bc b1 k1 n1 b2 k2 n2
  else if novars b2 then xinside_numB bc b1 k1 n1 b2 k2 n2 else false.

Definition sub_itvB (bc : bctx) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
  if (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
        match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
      else false)
  then true
  else (* [comment removed for export] *)
    if (Z.leb 0 n && Z.ltb n two64)%bool then xinsideB bc b k (ELit n) (a_base c) (a_off c) m else false.

(* [comment removed for export] *)
Definition sub_pre (b : expr) (c : saddr) : bool :=
  if expr_eqb b (a_base c) then true else if shares_var b (a_base c) then true else novars (a_base c).
Lemma sub_pre_false : forall bc b k n c m, sub_pre b c = false -> sub_itvB bc b k n c m = false.
Proof.
  intros bc b k n c m H. unfold sub_pre in H. unfold sub_itvB, xinsideB.
  destruct (expr_eqb b (a_base c)); [discriminate|]. destruct (shares_var b (a_base c)); [discriminate|]. rewrite H.
  cbn [andb]. destruct (Z.leb 0 n && Z.ltb n two64)%bool; reflexivity.
Qed.
Lemma kd_pre_eq : forall bc b1 k1 n1 c1 m1 b2 k2 n2 c2 m2,
  (if sub_pre b1 c1 then (if sub_pre b2 c2 then (if sub_itvB bc b1 k1 n1 c1 m1 then sub_itvB bc b2 k2 n2 c2 m2 else false) else false) else false)
  = (if sub_itvB bc b1 k1 n1 c1 m1 then sub_itvB bc b2 k2 n2 c2 m2 else false).
Proof.
  intros. destruct (sub_pre b1 c1) eqn:P1.
  - destruct (sub_pre b2 c2) eqn:P2; [reflexivity|]. rewrite (sub_pre_false bc b2 k2 n2 c2 m2 P2). destruct (sub_itvB bc b1 k1 n1 c1 m1); reflexivity.
  - rewrite (sub_pre_false bc b1 k1 n1 c1 m1 P1). reflexivity.
Qed.
Fixpoint kdisj_apartB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_pre b1 c1 then (if sub_pre b2 c2 then (if sub_itvB bc b1 k1 n1 c1 m1 then sub_itvB bc b2 k2 n2 c2 m2 else false) else false) else false) then true
      else if (if sub_pre b1 c2 then (if sub_pre b2 c1 then (if sub_itvB bc b1 k1 n1 c2 m2 then sub_itvB bc b2 k2 n2 c1 m1 else false) else false) else false) then true
      else kdisj_apartB bc rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apartB bc rest b1 k1 n1 b2 k2 n2
  end.

Definition ranges_apartB (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match base_rangeB bc b1, base_rangeB bc b2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
      | _, _ => false
      end) then true
  else if kdisj_apartB bc (bc_fk bc) b1 k1 n1 b2 k2 n2 then true
  else lin_apartB bc b1 k1 n1 b2 k2 n2.

Definition sub_itv_xB (bc : bctx) (b : expr) (k : Z) (n : expr) (c : saddr) (m : expr) : bool :=
  xinsideB bc b k n (a_base c) (a_off c) m.

Definition sub_prex (b : expr) (c : saddr) : bool := if shares_var b (a_base c) then true else novars (a_base c).
Lemma sub_prex_false : forall bc b k n c m, sub_prex b c = false -> sub_itv_xB bc b k n c m = false.
Proof.
  intros bc b k n c m H. unfold sub_prex in H. unfold sub_itv_xB, xinsideB.
  destruct (shares_var b (a_base c)); [discriminate|]. rewrite H. reflexivity.
Qed.
Lemma kd_prex_eq : forall bc b1 k1 n1 c1 m1 b2 k2 n2 c2 m2,
  (if sub_prex b1 c1 then (if sub_prex b2 c2 then (if sub_itv_xB bc b1 k1 n1 c1 m1 then sub_itv_xB bc b2 k2 n2 c2 m2 else false) else false) else false)
  = (if sub_itv_xB bc b1 k1 n1 c1 m1 then sub_itv_xB bc b2 k2 n2 c2 m2 else false).
Proof.
  intros. destruct (sub_prex b1 c1) eqn:P1.
  - destruct (sub_prex b2 c2) eqn:P2; [reflexivity|]. rewrite (sub_prex_false bc b2 k2 n2 c2 m2 P2). destruct (sub_itv_xB bc b1 k1 n1 c1 m1); reflexivity.
  - rewrite (sub_prex_false bc b1 k1 n1 c1 m1 P1). reflexivity.
Qed.
Fixpoint kdisj_apart_xB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_prex b1 c1 then (if sub_prex b2 c2 then (if sub_itv_xB bc b1 k1 n1 c1 m1 then sub_itv_xB bc b2 k2 n2 c2 m2 else false) else false) else false) then true
      else if (if sub_prex b1 c2 then (if sub_prex b2 c1 then (if sub_itv_xB bc b1 k1 n1 c2 m2 then sub_itv_xB bc b2 k2 n2 c1 m1 else false) else false) else false) then true
      else kdisj_apart_xB bc rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apart_xB bc rest b1 k1 n1 b2 k2 n2
  end.

Definition end_hiB (bc : bctx) (b : expr) (k : Z) (n : expr) (lo1 hi1 h1 : Z) : option Z :=
  match n with
  | ELit _ => None
  | _ => if (if Z.leb 0 (lo1 + k) then Z.ltb (hi1 + k + h1) two64 else false)
         then match find_rangeI (bc_ri bc) (mkAlu ALU_ADD (mkAlu ALU_ADD b (ELit k)) n) with
              | Some (_, ehi) => Some ehi
              | None => None
              end
         else None
  end.

Definition ranges_apart_xB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 => ranges_apartB bc b1 k1 (zlit64 z1) b2 k2 (zlit64 z2)
  | _, _ =>
    if (match base_rangeB bc b1, base_rangeB bc b2, xhiB bc n1, xhiB bc n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else (* [comment removed for export] *)
            if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if kdisj_apart_xB bc (bc_fk bc) b1 k1 n1 b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

Fixpoint disj_sidesB_ref (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sidesB_ref bc rest b1 k1 n1 in
      let r1 := if sub_itvB bc b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itvB bc b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sidesB_ref bc rest b1 k1 n1
  end.
(* [comment removed for export] *)
Definition side_eqb (s s' : saddr * expr) : bool :=
  if Z.eqb (a_off (fst s)) (a_off (fst s')) then
    (if expr_eqb (snd s) (snd s') then expr_eqb (a_base (fst s)) (a_base (fst s')) else false)
  else false.
Fixpoint side_find {A : Type} (s : saddr * expr) (memo : list ((saddr * expr) * A)) : option A :=
  match memo with
  | [] => None
  | (s', t) :: r => if side_eqb s s' then Some t else side_find s r
  end.
Definition side_test (bc : bctx) (b1 : expr) (k1 n1 : Z) (s : saddr * expr) (memo : list ((saddr * expr) * bool))
  : bool * list ((saddr * expr) * bool) :=
  match side_find s memo with
  | Some t => (t, memo)
  | None => let t := sub_itvB bc b1 k1 n1 (fst s) (snd s) in (t, (s, t) :: memo)
  end.
Fixpoint disj_sidesM (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) (memo : list ((saddr * expr) * bool))
  : list (saddr * expr) * list ((saddr * expr) * bool) :=
  match kn with
  | [] => ([], memo)
  | KDisj c1 m1 c2 m2 :: rest =>
      let rm := disj_sidesM bc rest b1 k1 n1 memo in
      let x2 := side_test bc b1 k1 n1 (c2, m2) (snd rm) in
      let x1 := side_test bc b1 k1 n1 (c1, m1) (snd x2) in
      let r1 := if fst x2 then (c1, m1) :: fst rm else fst rm in
      ((if fst x1 then (c2, m2) :: r1 else r1), snd x1)
  | _ :: rest => disj_sidesM bc rest b1 k1 n1 memo
  end.
Definition disj_sidesB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) :=
  fst (disj_sidesM bc kn b1 k1 n1 []).
Lemma side_eqb_eq : forall s s', side_eqb s s' = true -> s = s'.
Proof.
  intros [[b o] m] [[b' o'] m']. unfold side_eqb. cbn [fst snd a_off a_base].
  destruct (Z.eqb o o') eqn:E1; [|intros H; discriminate H]. destruct (expr_eqb m m') eqn:E2; [|intros H; discriminate H].
  intros H. apply Z.eqb_eq in E1. apply p_expr_eqb_eq in E2. apply p_expr_eqb_eq in H. subst. reflexivity.
Qed.
Lemma side_find_in : forall {A : Type} (memo : list ((saddr * expr) * A)) s t, side_find s memo = Some t -> In (s, t) memo.
Proof.
  intros A memo. induction memo as [|[s' t'] r IH]; intros s t H; [discriminate|]. cbn [side_find] in H.
  destruct (side_eqb s s') eqn:E.
  - injection H as <-. apply side_eqb_eq in E. subst s'. left. reflexivity.
  - right. apply IH. exact H.
Qed.
Definition side_memo_ok (bc : bctx) (b1 : expr) (k1 n1 : Z) (memo : list ((saddr * expr) * bool)) : Prop :=
  forall s t, In (s, t) memo -> t = sub_itvB bc b1 k1 n1 (fst s) (snd s).
Lemma side_test_ok : forall bc b1 k1 n1 s memo, side_memo_ok bc b1 k1 n1 memo ->
  fst (side_test bc b1 k1 n1 s memo) = sub_itvB bc b1 k1 n1 (fst s) (snd s)
  /\ side_memo_ok bc b1 k1 n1 (snd (side_test bc b1 k1 n1 s memo)).
Proof.
  intros bc b1 k1 n1 s memo OK. unfold side_test. destruct (side_find s memo) as [t|] eqn:F.
  - cbn [fst snd]. split; [|exact OK]. apply OK. apply side_find_in. exact F.
  - cbn [fst snd]. split; [reflexivity|]. intros s' t' [E|I]; [injection E as <- <-; reflexivity|]. apply OK. exact I.
Qed.
Lemma disj_sidesM_ok : forall bc b1 k1 n1 kn memo, side_memo_ok bc b1 k1 n1 memo ->
  fst (disj_sidesM bc kn b1 k1 n1 memo) = disj_sidesB_ref bc kn b1 k1 n1
  /\ side_memo_ok bc b1 k1 n1 (snd (disj_sidesM bc kn b1 k1 n1 memo)).
Proof.
  intros bc b1 k1 n1 kn. induction kn as [|K rest IH]; intros memo OK; [split; [reflexivity|exact OK]|].
  destruct K as [| | | | | | |c1 m1 c2 m2| |]; cbn [disj_sidesM disj_sidesB_ref]; try (apply IH; exact OK).
  cbv zeta. destruct (IH memo OK) as [E0 OK0].
  destruct (side_test_ok bc b1 k1 n1 (c2, m2) _ OK0) as [E2 OK2].
  destruct (side_test_ok bc b1 k1 n1 (c1, m1) _ OK2) as [E1 OK1].
  cbn [fst snd] in E1, E2. cbn [fst snd]. rewrite E1, E2, E0. split; [reflexivity|exact OK1].
Qed.
Lemma disj_sidesB_ref_eq : forall bc kn b1 k1 n1, disj_sidesB bc kn b1 k1 n1 = disj_sidesB_ref bc kn b1 k1 n1.
Proof. intros. unfold disj_sidesB. exact (proj1 (disj_sidesM_ok bc b1 k1 n1 kn [] (fun s t (H : In (s, t) []) => match H with end))). Qed.

Fixpoint disj_sides_xB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sides_xB bc rest b1 k1 n1 in
      let r1 := if sub_itv_xB bc b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itv_xB bc b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sides_xB bc rest b1 k1 n1
  end.

Fixpoint in_sidesB (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itvB bc b2 k2 n2 c m then true else in_sidesB bc r b2 k2 n2
  end.

Fixpoint in_sides_xB (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv_xB bc b2 k2 n2 c m then true else in_sides_xB bc r b2 k2 n2
  end.

Definition mk_sprepB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) : sprep :=
  SPrep (base_rangeB bc b1) (xhiB bc n1)
        (match n1 with ELit z1 => disj_sidesB bc (bc_fk bc) b1 k1 (zlit64 z1) | _ => [] end)
        (disj_sides_xB bc (bc_fk bc) b1 k1 n1).

Definition ranges_apart_pB (bc : bctx) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
           (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, base_rangeB bc b2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then true
      else if in_sidesB bc (sp_D sp) b2 k2 m2 then true
      else lin_apartB bc b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match sp_rng sp, base_rangeB bc b2, sp_h1 sp, xhiB bc n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else (* [comment removed for export] *)
            if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_xB bc (sp_Dx sp) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

Lemma lin_test_relB_eqf : forall fk, lin_test_relB (mkbc fk) = lin_test_rel fk.
Proof.
  intros. bcfe. unfold lin_test_relB, lin_test_rel, lin_test_reld. rewrite bc_fsK_mkbc, bc_fs_mkbc, erangeB_eqf.
  destruct (sum_facts fk fk) as [|f r]; [reflexivity|]. rewrite lin_chainK_eq, lin_chainF_fe. reflexivity.
Qed.
#[export] Hint Rewrite lin_test_relB_eqf : bceq.
Lemma lin_testB_eqf : forall fk, lin_testB (mkbc fk) = lin_test fk.
Proof. intros. bcfe. unfold lin_testB, lin_test. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_testB_eqf : bceq.
Lemma lin_srangeB_eqf : forall fk, lin_srangeB (mkbc fk) = lin_srange fk.
Proof. intros. bcfe. unfold lin_srangeB, lin_srange. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_srangeB_eqf : bceq.
Lemma lin_nowrapRB_eqf : forall fk, lin_nowrapRB (mkbc fk) = lin_nowrapR fk.
Proof. intros. bcfe. unfold lin_nowrapRB, lin_nowrapR. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_nowrapRB_eqf : bceq.
Lemma lin_apart0B_eqf : forall fk, lin_apart0B (mkbc fk) = lin_apart0 fk.
Proof. intros. bcfe. unfold lin_apart0B, lin_apart0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_apart0B_eqf : bceq.
Lemma lin_apartB_eqf : forall fk, lin_apartB (mkbc fk) = lin_apart fk.
Proof. intros. bcfe. unfold lin_apartB, lin_apart. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_apartB_eqf : bceq.
Lemma lin_rel_multiF_fe : lin_rel_multiF = lin_rel_multi.
Proof. do 4 (apply functional_extensionality; intro). apply lin_rel_multiF_eq. Qed.
#[export] Hint Rewrite lin_rel_multiF_fe : bceq.
Lemma lin_brangeB_eqf : forall fk, lin_brangeB (mkbc fk) = lin_brange fk.
Proof.
  intros. bcfe. unfold lin_brangeB, lin_brange. rewrite bc_fsK_mkbc, bc_fs_mkbc, erangeB_eqf.
  destruct (sum_facts fk fk) as [|f r]; [reflexivity|]. rewrite lin_rel_multiK_eq, lin_rel_multiF_fe. reflexivity.
Qed.
#[export] Hint Rewrite lin_brangeB_eqf : bceq.
Lemma xloB_eqf : forall fk, xloB (mkbc fk) = xlo fk.
Proof. intros. bcfe. unfold xloB, xlo. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite xloB_eqf : bceq.
Lemma xhiB_eqf : forall fk, xhiB (mkbc fk) = xhi fk.
Proof. intros. bcfe. unfold xhiB, xhi. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite xhiB_eqf : bceq.
Lemma xt_nowrapB_eqf : forall fk, xt_nowrapB (mkbc fk) = xt_nowrap fk.
Proof.
  intros fk. apply functional_extensionality; intros ts. 
  induction ts as [|[e k] rest IH]; intros; bcfe; [reflexivity|].
  cbn [xt_nowrapB xt_nowrap]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite xt_nowrapB_eqf : bceq.
Lemma lin_ge0_scaledB_eqf : forall fk, lin_ge0_scaledB (mkbc fk) = lin_ge0_scaled fk.
Proof. intros. bcfe. unfold lin_ge0_scaledB, lin_ge0_scaled. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_ge0_scaledB_eqf : bceq.
(* [comment removed for export] *)
Section E15Perm.
Lemma e15_aluop_eqb_eq : forall a b, aluop_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.
Lemma e15_mulop_eqb_eq : forall a b, mulop_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.
Lemma e15_expr_eqb_eq : forall x y, expr_eqb x y = true -> x = y.
Proof.
  induction x; destruct y; cbn; intros H; try discriminate;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      end;
    repeat match goal with
      | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
      | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
      | H : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in H
      | H : aluop_eqb _ _ = true |- _ => apply e15_aluop_eqb_eq in H
      | H : mulop_eqb _ _ = true |- _ => apply e15_mulop_eqb_eq in H
      | H : expr_eqb ?a _ = true, IH : forall y, expr_eqb ?a y = true -> _ |- _ => apply IH in H
      end; subst; reflexivity.
Qed.
Lemma e15_aluop_eqb_refl : forall a, aluop_eqb a a = true. Proof. intros []; reflexivity. Qed.
Lemma e15_mulop_eqb_refl : forall a, mulop_eqb a a = true. Proof. intros []; reflexivity. Qed.
Lemma e15_expr_eqb_refl : forall x, expr_eqb x x = true.
Proof.
  induction x; cbn -[Z.eqb Nat.eqb]; rewrite ?e15_aluop_eqb_refl, ?e15_mulop_eqb_refl, ?IHx, ?IHx1, ?IHx2, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
Qed.
Lemma e15_expr_dec : forall x y : expr, {x = y} + {x <> y}.
Proof.
  intros x y. destruct (expr_eqb x y) eqn:E; [left; apply e15_expr_eqb_eq; exact E|right].
  intros ->. rewrite e15_expr_eqb_refl in E. discriminate.
Qed.
Lemma e15_expr_eqb_false : forall x y, x <> y -> expr_eqb x y = false.
Proof. intros x y N. destruct (expr_eqb x y) eqn:E; [|reflexivity]. apply e15_expr_eqb_eq in E. contradiction. Qed.

(* [comment removed for export] *)
Lemma e15_coef_in : forall a k ts, List.NoDup (map snd ts) -> In (k, a) ts -> coef_of a ts = k.
Proof.
  intros a k ts. induction ts as [|[k' a'] r IH]; intros ND H; [contradiction|].
  cbn [map snd] in ND. inversion ND as [|x l NI ND' E]; subst. cbn [coef_of].
  destruct H as [H|H].
  - injection H as -> ->. rewrite e15_expr_eqb_refl. reflexivity.
  - destruct (expr_eqb a a') eqn:E.
    + apply e15_expr_eqb_eq in E. subst a'. exfalso. apply NI. apply in_map_iff. exists (k, a). auto.
    + apply IH; assumption.
Qed.
Lemma e15_coef_notin : forall a ts, ~ In a (map snd ts) -> coef_of a ts = 0%Z.
Proof.
  intros a ts. induction ts as [|[k' a'] r IH]; intros H; [reflexivity|]. cbn [coef_of].
  cbn [map snd In] in H. rewrite e15_expr_eqb_false by (intros ->; apply H; left; reflexivity). apply IH. intros I; apply H; right; exact I.
Qed.
Lemma e15_nodup_perm : forall (ts ts' : list (Z * expr)), List.NoDup (map snd ts) -> Permutation.Permutation ts ts' -> List.NoDup (map snd ts').
Proof. intros ts ts' ND P. eapply Permutation.Permutation_NoDup; [apply Permutation.Permutation_map; exact P|exact ND]. Qed.
Lemma e15_coef_perm : forall a ts ts', List.NoDup (map snd ts) -> Permutation.Permutation ts ts' -> coef_of a ts = coef_of a ts'.
Proof.
  intros a ts ts' ND P. pose proof (e15_nodup_perm ts ts' ND P) as ND'.
  destruct (in_dec e15_expr_dec a (map snd ts)) as [I|NI].
  - apply in_map_iff in I as [[k a0] [E I]]. cbn [snd] in E. subst a0.
    rewrite (e15_coef_in a k ts ND I). symmetry. apply e15_coef_in; [exact ND'|]. eapply Permutation.Permutation_in; eauto.
  - rewrite (e15_coef_notin a ts NI). symmetry. apply e15_coef_notin. intros I. apply NI.
    eapply Permutation.Permutation_in; [apply Permutation.Permutation_map; apply Permutation.Permutation_sym; exact P|exact I].
Qed.
Lemma e15_fact_quot_perm : forall fts ts ts' acc, List.NoDup (map snd ts) -> Permutation.Permutation ts ts' -> fact_quot fts ts acc = fact_quot fts ts' acc.
Proof.
  intros fts ts ts' acc ND P. revert acc. induction fts as [|[k a] r IH]; intros acc; [reflexivity|].
  cbn [fact_quot]. rewrite (e15_coef_perm a ts ts' ND P). destruct acc; rewrite ?IH; reflexivity.
Qed.
Lemma e15_part_quot_perm : forall fts ts ts', List.NoDup (map snd ts) -> Permutation.Permutation ts ts' -> part_quot fts ts = part_quot fts ts'.
Proof.
  intros fts ts ts' ND P. induction fts as [|[k a] r IH]; [reflexivity|].
  cbn [part_quot]. rewrite (e15_coef_perm a ts ts' ND P), IH. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma e15_lins_notin : forall k a ts, ~ In a (map snd ts) -> lins_e k a ts = ts ++ (if Z.eqb k 0%Z then [] else [(k, a)]).
Proof.
  intros k a ts. induction ts as [|[k' a'] r IH]; intros H; cbn [lins_e app].
  - reflexivity.
  - cbn [map snd In] in H. rewrite e15_expr_eqb_false by (intros ->; apply H; left; reflexivity).
    rewrite IH by (intros I; apply H; right; exact I). reflexivity.
Qed.
Lemma e15_lins_in : forall k a k' l1 l2, ~ In a (map snd l1) ->
  lins_e k a (l1 ++ (k', a) :: l2) = l1 ++ (if Z.eqb (k + k')%Z 0%Z then l2 else ((k + k')%Z, a) :: l2).
Proof.
  intros k a k' l1 l2. induction l1 as [|[k1 a1] r IH]; intros H; cbn [lins_e app].
  - rewrite e15_expr_eqb_refl. reflexivity.
  - cbn [map snd In] in H. rewrite e15_expr_eqb_false by (intros ->; apply H; left; reflexivity).
    rewrite IH by (intros I; apply H; right; exact I). reflexivity.
Qed.
Lemma e15_lins_perm : forall k a ts ts', List.NoDup (map snd ts) -> Permutation.Permutation ts ts' ->
  Permutation.Permutation (lins_e k a ts) (lins_e k a ts') /\ List.NoDup (map snd (lins_e k a ts)).
Proof.
  intros k a ts ts' ND P. pose proof (e15_nodup_perm ts ts' ND P) as ND'.
  destruct (in_dec e15_expr_dec a (map snd ts)) as [I|NI].
  - apply in_map_iff in I as [[k' a0] [E I]]. cbn [snd] in E. subst a0.
    assert (I' : In (k', a) ts') by (eapply Permutation.Permutation_in; eauto).
    apply in_split in I as [l1 [l2 E1]]. apply in_split in I' as [l1' [l2' E2]]. subst ts ts'.
    rewrite map_app in ND, ND'. cbn [map snd] in ND, ND'.
    pose proof (List.NoDup_remove_2 _ _ _ ND) as N1. pose proof (List.NoDup_remove_2 _ _ _ ND') as N2.
    rewrite in_app_iff in N1, N2.
    rewrite !e15_lins_in by (intros X; first [apply N1; left; exact X | apply N2; left; exact X]).
    pose proof (Permutation.Permutation_app_inv _ _ _ _ _ P) as P'.
    split.
    + destruct (Z.eqb (k + k')%Z 0%Z); [exact P'|]. apply Permutation.Permutation_elt. exact P'.
    + destruct (Z.eqb (k + k')%Z 0%Z).
      * rewrite map_app. exact (List.NoDup_remove_1 _ _ _ ND).
      * rewrite map_app. cbn [map snd]. exact ND.
  - assert (NI' : ~ In a (map snd ts')).
    { intros X. apply NI. eapply Permutation.Permutation_in; [apply Permutation.Permutation_map; apply Permutation.Permutation_sym; exact P|exact X]. }
    rewrite !e15_lins_notin by assumption. split.
    + apply Permutation.Permutation_app_tail. exact P.
    + rewrite map_app. destruct (Z.eqb k 0); cbn [map snd]; [rewrite app_nil_r; exact ND|].
      apply List.NoDup_app; [exact ND|constructor; [intros []|constructor]|].
      intros x X1 X2. destruct X2 as [<-|[]]. exact (NI X1).
Qed.
Lemma e15_sub_fact_perm : forall q fts ts ts', List.NoDup (map snd ts) -> Permutation.Permutation ts ts' ->
  Permutation.Permutation (sub_fact q fts ts) (sub_fact q fts ts') /\ List.NoDup (map snd (sub_fact q fts ts)).
Proof.
  intros q fts ts ts' ND P. unfold sub_fact. induction fts as [|t r IH]; [split; assumption|].
  cbn [fold_right]. destruct IH as [P1 N1]. apply e15_lins_perm; assumption.
Qed.
Lemma e15_scale_ts_perm : forall m ts ts', List.NoDup (map snd ts) -> Permutation.Permutation ts ts' ->
  Permutation.Permutation (scale_ts m ts) (scale_ts m ts') /\ List.NoDup (map snd (scale_ts m ts)).
Proof.
  intros m ts ts' ND P. unfold scale_ts. split; [apply Permutation.Permutation_map; exact P|].
  rewrite map_map. cbn [snd]. exact ND.
Qed.

(* [comment removed for export] *)
Lemma e15_lin_range_perm : forall rng c ts ts', Permutation.Permutation ts ts' -> lin_range rng c ts = lin_range rng c ts'.
Proof.
  intros rng c ts ts' P. induction P as [|[k a] l l' P IH|[k1 a1] [k2 a2] l|l l' l'' P1 IH1 P2 IH2].
  - reflexivity.
  - cbn [lin_range]. rewrite IH. reflexivity.
  - cbn [lin_range].
    destruct (rng a1) as [[al1 ah1]|]; destruct (rng a2) as [[al2 ah2]|]; destruct (lin_range rng c l) as [[lo hi]|]; try reflexivity;
      destruct (Z.leb 0 k1); destruct (Z.leb 0 k2); f_equal; f_equal; lia.
  - congruence.
Qed.

(* [comment removed for export] *)
Lemma e15_sum_subst_perm : forall fs ts ts' lo hi hit, List.NoDup (map snd ts) -> Permutation.Permutation ts ts' ->
  Permutation.Permutation (fst (fst (sum_subst fs ts lo hi hit))) (fst (fst (sum_subst fs ts' lo hi hit)))
  /\ List.NoDup (map snd (fst (fst (sum_subst fs ts lo hi hit))))
  /\ snd (fst (sum_subst fs ts lo hi hit)) = snd (fst (sum_subst fs ts' lo hi hit))
  /\ snd (sum_subst fs ts lo hi hit) = snd (sum_subst fs ts' lo hi hit).
Proof.
  induction fs as [|[fts [flo fhi]] r IH]; intros ts ts' lo hi hit ND P.
  - cbn. auto.
  - cbn [sum_subst]. rewrite (e15_fact_quot_perm fts ts ts' None ND P).
    destruct (fact_quot fts ts' None) as [q|]; [|apply IH; assumption].
    destruct (e15_sub_fact_perm q fts ts ts' ND P) as [P1 N1].
    destruct (Z.leb 0 q); apply IH; assumption.
Qed.
Lemma e15_lin_rel_core_perm : forall rng o c ts ts', List.NoDup (map snd ts) -> Permutation.Permutation ts ts' ->
  lin_rel_core rng o c ts = lin_rel_core rng o c ts'.
Proof.
  intros rng o c ts ts' ND P. unfold lin_rel_core.
  destruct (e15_sum_subst_perm o ts ts' 0 0 false ND P) as (P1 & _ & E1 & E2).
  destruct (sum_subst o ts 0 0 false) as [[t1 [l1 h1]] b1]; destruct (sum_subst o ts' 0 0 false) as [[t2 [l2 h2]] b2].
  cbn [fst snd] in *. injection E1 as <- <-. subst b2.
  destruct b1; [|reflexivity]. rewrite (e15_lin_range_perm rng c t1 t2 P1). reflexivity.
Qed.
Lemma e15_sf_orders_perm : forall fs all ts ts', List.NoDup (map snd ts) -> Permutation.Permutation ts ts' ->
  sf_orders fs all ts = sf_orders fs all ts'.
Proof.
  intros fs all ts ts' ND P. induction fs as [|f r IH]; [reflexivity|]. cbn [sf_orders].
  rewrite (e15_fact_quot_perm (fst f) ts ts' None ND P), IH. reflexivity.
Qed.
Lemma e15_lin_rel_fold_perm : forall rng ords c ts ts' acc, List.NoDup (map snd ts) -> Permutation.Permutation ts ts' ->
  lin_rel_fold rng ords c ts acc = lin_rel_fold rng ords c ts' acc.
Proof.
  intros rng ords c ts ts' acc ND P. revert acc. induction ords as [|o r IH]; intros acc; [reflexivity|].
  cbn [lin_rel_fold]. rewrite (e15_lin_rel_core_perm rng o c ts ts' ND P). apply IH.
Qed.
Lemma e15_lin_rel_multi_perm : forall rng fs c ts ts', List.NoDup (map snd ts) -> Permutation.Permutation ts ts' ->
  lin_rel_multi rng fs c ts = lin_rel_multi rng fs c ts'.
Proof.
  intros rng fs c ts ts' ND P. unfold lin_rel_multi. rewrite (e15_sf_orders_perm fs fs ts ts' ND P).
  apply e15_lin_rel_fold_perm; assumption.
Qed.
Lemma e15_lin_eval_perm : forall rng fs c ts ts' test, List.NoDup (map snd ts) -> Permutation.Permutation ts ts' ->
  lin_eval rng fs c ts test = lin_eval rng fs c ts' test.
Proof.
  intros rng fs c ts ts' test ND P. unfold lin_eval.
  rewrite (e15_lin_rel_multi_perm rng fs c ts ts' ND P), (e15_lin_range_perm rng c ts ts' P). reflexivity.
Qed.
Lemma e15_existsb_ext : forall {A : Type} (f g : A -> bool) l, (forall x, f x = g x) -> existsb f l = existsb g l.
Proof. intros A f g l H. induction l as [|x r IH]; [reflexivity|]. cbn [existsb]. rewrite H, IH. reflexivity. Qed.
Lemma e15_lin_chain_perm : forall fuel rng fs c ts ts' test, List.NoDup (map snd ts) -> Permutation.Permutation ts ts' ->
  lin_chain fuel rng fs c ts test = lin_chain fuel rng fs c ts' test.
Proof.
  induction fuel as [|f IH]; intros rng fs c ts ts' test ND P; cbn [lin_chain];
    rewrite (e15_lin_eval_perm rng fs c ts ts' test ND P); [reflexivity|].
  destruct (lin_eval rng fs c ts' test); [reflexivity|]. cbn [orb]. apply e15_existsb_ext. intros sf. rewrite (e15_part_quot_perm (fst sf) ts ts' ND P).
  destruct (part_quot (fst sf) ts') as [[m q]|]; [|reflexivity].
  destruct (e15_scale_ts_perm m ts ts' ND P) as [P1 N1].
  destruct (e15_sub_fact_perm q (fst sf) _ _ N1 P1) as [P2 N2].
  apply IH; assumption.
Qed.
Lemma e15_lin_test_rel_perm : forall kn c ts ts' test, List.NoDup (map snd ts) -> Permutation.Permutation ts ts' ->
  lin_test_rel kn c ts test = lin_test_rel kn c ts' test.
Proof.
  intros kn c ts ts' test ND P. unfold lin_test_rel, lin_test_reld.
  destruct (sum_facts kn kn); [reflexivity|]. apply e15_lin_chain_perm; assumption.
Qed.
Lemma e15_lin_test_perm : forall kn c ts ts' test, List.NoDup (map snd ts) -> Permutation.Permutation ts ts' ->
  lin_test kn c ts test = lin_test kn c ts' test.
Proof.
  intros kn c ts ts' test ND P. unfold lin_test.
  rewrite (e15_lin_range_perm (erange kn) c ts ts' P), (e15_lin_test_rel_perm kn c ts ts' test ND P). reflexivity.
Qed.
End E15Perm.
Definition e15_normal (ts : list (Z * expr)) : Prop := List.NoDup (map snd ts) /\ Forall (fun t => fst t <> 0%Z) ts.
Lemma e15_lins_atoms : forall x k a ts, In x (map snd (lins_e k a ts)) -> x = a \/ In x (map snd ts).
Proof.
  intros x k a ts. induction ts as [|[k' a'] r IH]; cbn [lins_e].
  - destruct (Z.eqb k 0%Z); cbn; [intros []|]. intros [<-|[]]; left; reflexivity.
  - destruct (expr_eqb a a') eqn:E.
    + apply e15_expr_eqb_eq in E. subst a'. destruct (Z.eqb (k + k')%Z 0%Z); cbn [map snd In]; intros H; [right; right; exact H|].
      destruct H as [<-|H]; [left; reflexivity|right; right; exact H].
    + cbn [map snd In]. intros [<-|H]; [right; left; reflexivity|]. destruct (IH H) as [X|X]; [left; exact X|right; right; exact X].
Qed.
Lemma e15_lins_normal : forall k a ts, e15_normal ts -> e15_normal (lins_e k a ts).
Proof.
  intros k a ts. induction ts as [|[k' a'] r IH]; intros [ND NZ]; cbn [lins_e].
  - destruct (Z.eqb k 0%Z) eqn:E.
    + split; constructor.
    + split; cbn [map snd].
      * constructor; [intros []|constructor].
      * constructor; [|constructor]. cbn [fst]. apply Z.eqb_neq. exact E.
  - cbn [map snd] in ND. inversion ND as [|x l NI ND1 EE]; subst. inversion NZ as [|x l NZ0 NZ1 EE]; subst.
    destruct (expr_eqb a a') eqn:E.
    + destruct (Z.eqb (k + k')%Z 0%Z) eqn:E2; split; cbn [map snd fst]; auto; constructor; auto.
      intros X. apply Z.eqb_neq in E2. contradiction.
    + destruct (IH (conj ND1 NZ1)) as [ND' NZ']. split; cbn [map snd]; constructor; auto.
      intros X. destruct (e15_lins_atoms a' k a r X) as [Y|Y]; [|contradiction].
      subst a'. rewrite e15_expr_eqb_refl in E. discriminate.
Qed.
Lemma e15_fold_lins_normal : forall (f : Z * expr -> Z) l acc, e15_normal acc ->
  e15_normal (fold_right (fun t acc => lins_e (f t) (snd t) acc) acc l).
Proof. intros f l acc H. induction l as [|t r IH]; [exact H|]. cbn [fold_right]. apply e15_lins_normal. exact IH. Qed.
Lemma e15_xt_lin_normal : forall xs, e15_normal (xt_lin xs).
Proof.
  induction xs as [|[e k] r IH]; cbn [xt_lin].
  - split; constructor.
  - apply (e15_fold_lins_normal fst). exact IH.
Qed.
Lemma e15_lsub_normal : forall pos neg, e15_normal (lsub_e (xt_lin pos) (xt_lin neg)).
Proof. intros. unfold lsub_e. apply (e15_fold_lins_normal (fun t => (- fst t)%Z)). apply e15_xt_lin_normal. Qed.
Lemma e15_lnf_perm : forall ts, e15_normal ts -> Permutation.Permutation (e15_lnf ts) ts /\ e15_normal (e15_lnf ts).
Proof.
  intros ts NT. split; [|apply (e15_fold_lins_normal fst); split; constructor].
  destruct NT as [ND NZ]. induction ts as [|[k a] r IH]; [constructor|].
  cbn [map snd] in ND. inversion ND as [|x l NI ND1 EE]; subst. inversion NZ as [|x l NZ0 NZ1 EE]; subst.
  unfold e15_lnf. cbn [fold_right fst snd]. fold (e15_lnf r).
  specialize (IH ND1 NZ1).
  rewrite e15_lins_notin.
  - cbn [fst] in NZ0. apply Z.eqb_neq in NZ0. rewrite NZ0. eapply Permutation.perm_trans; [apply Permutation.Permutation_sym; apply Permutation.Permutation_cons_append|]. constructor. exact IH.
  - intros X. apply NI. eapply Permutation.Permutation_in; [apply Permutation.Permutation_map; exact IH|exact X].
Qed.
Lemma e15_noexp_forall : forall bc ts, srl_noexpB bc ts = true <-> (forall t, In t ts -> srl_noexp1B bc t = true).
Proof.
  intros bc ts. induction ts as [|t r IH]; cbn [srl_noexpB In]; [split; [intros _ t []|reflexivity]|].
  destruct (srl_noexp1B bc t) eqn:E; split.
  - intros H x [<-|X]; [exact E|]. apply IH; assumption.
  - intros H. apply IH. intros x X. apply H. right; exact X.
  - discriminate.
  - intros H. rewrite <- E. apply H. left; reflexivity.
Qed.
Lemma e15_noexp_perm : forall bc ts ts', Permutation.Permutation ts ts' -> srl_noexpB bc ts = srl_noexpB bc ts'.
Proof.
  intros bc ts ts' P. destruct (srl_noexpB bc ts) eqn:E; destruct (srl_noexpB bc ts') eqn:E'; try reflexivity.
  - rewrite e15_noexp_forall in E. rewrite <- E'. symmetry. apply e15_noexp_forall. intros t T. apply E.
    eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact P|exact T].
  - rewrite e15_noexp_forall in E'. rewrite <- E. apply e15_noexp_forall. intros t T. apply E'.
    eapply Permutation.Permutation_in; [exact P|exact T].
Qed.
Lemma e15_noexp_expand : forall bc ts, srl_noexpB bc ts = true -> srl_expandB bc ts = (0%Z, e15_lnf ts).
Proof.
  intros bc ts. induction ts as [|[k a] r IH]; intros H; [reflexivity|].
  cbn [srl_noexpB] in H. destruct (srl_noexp1B bc (k, a)) eqn:H1; [|discriminate].
  cbn [srl_expandB]. rewrite (IH H). unfold e15_lnf. cbn [fold_right fst snd]. fold (e15_lnf r).
  unfold srl_noexp1B in H1. cbn [snd fst] in H1.
  destruct a as [z0|n0|op e b|op e b|op e b|op e b|x1 x2 x3 x4|x1 x2 x3 x4]; try reflexivity.
  destruct op; try reflexivity; destruct b as [s|n1|o1 b1 b2|o1 b1 b2|o1 b1 b2|o1 b1 b2|y1 y2 y3 y4|y1 y2 y3 y4]; try reflexivity.
  - cbv zeta. revert H1. destruct (Z.eqb (m2p k (sh6w s)) 0%Z); intros H1; [|reflexivity].
    apply negb_true_iff in H1. rewrite H1. reflexivity.
  - revert H1. destruct (highmask_s s); intros H1; [|reflexivity]. apply negb_true_iff in H1. rewrite H1. reflexivity.
Qed.
Lemma e15_fb_eq : forall fk c ts, e15_normal ts -> lin_testB (mkbc fk) c ts (fun lo _ => Z.leb 0 lo) = false ->
  lin_ge0B_fb (mkbc fk) c ts = lin_ge0B_fb0 (mkbc fk) c ts.
Proof.
  intros fk c ts NT E. unfold lin_ge0B_fb. destruct (srl_noexpB (mkbc fk) ts) eqn:N; [|reflexivity].
  rewrite lin_testB_eqf in E.
  destruct (e15_lnf_perm ts NT) as [P1 NT1].
  unfold lin_ge0B_fb0. rewrite (e15_noexp_expand _ _ N). cbv beta iota. rewrite Z.add_0_r.
  rewrite lin_testB_eqf, (e15_lin_test_perm fk c (e15_lnf ts) ts _ (proj1 NT1) P1), E.
  destruct (has_srl (e15_lnf ts)); [|reflexivity].
  assert (N1 : srl_noexpB (mkbc fk) (e15_lnf ts) = true) by (rewrite (e15_noexp_perm _ _ _ P1); exact N).
  rewrite (e15_noexp_expand _ _ N1). cbv beta iota. rewrite Z.add_0_r.
  destruct (e15_lnf_perm (e15_lnf ts) NT1) as [P2 NT2].
  rewrite (e15_lin_test_perm fk c (e15_lnf (e15_lnf ts)) ts _ (proj1 NT2) (Permutation.perm_trans P2 P1)), E. reflexivity.
Qed.
Lemma lin_ge0B_old_eqf : forall fk, lin_ge0B_old (mkbc fk) = lin_ge0 fk.
Proof. intros. bcfe. unfold lin_ge0B_old, lin_ge0. autorewrite with bceq. reflexivity. Qed.
Lemma lin_ge0B_eqf : forall fk, lin_ge0B (mkbc fk) = lin_ge0 fk.
Proof.
  intros fk. rewrite <- lin_ge0B_old_eqf. bcfe. rename x into pos, x0 into neg.
  unfold lin_ge0B, lin_ge0B_old. cbv zeta.
  destruct (lin_testB (mkbc fk) (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) (fun lo _ => Z.leb 0 lo)) eqn:E;
    [reflexivity|].
  rewrite (e15_fb_eq fk _ _ (e15_lsub_normal pos neg) E). reflexivity.
Qed.
#[export] Hint Rewrite lin_ge0B_eqf : bceq.
Lemma xinside0B_eqf : forall fk, xinside0B (mkbc fk) = xinside0 fk.
Proof. intros. bcfe. unfold xinside0B, xinside0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite xinside0B_eqf : bceq.
Lemma xinside_numB_eqf : forall fk, xinside_numB (mkbc fk) = xinside_num fk.
Proof. intros. bcfe. unfold xinside_numB, xinside_num. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite xinside_numB_eqf : bceq.
Lemma xinsideB_eqf : forall fk, xinsideB (mkbc fk) = xinside fk.
Proof. intros. bcfe. unfold xinsideB, xinside. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite xinsideB_eqf : bceq.
Lemma sub_itvB_eqf : forall fk, sub_itvB (mkbc fk) = sub_itv fk.
Proof. intros. bcfe. unfold sub_itvB, sub_itv. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite sub_itvB_eqf : bceq.
Lemma kdisj_apartB_eqf : forall fk, kdisj_apartB (mkbc fk) = kdisj_apart fk.
Proof.
  intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2. 
  revert b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kdisj_apartB kdisj_apart]. destruct K; try apply IH. rewrite IH, !kd_pre_eq. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite kdisj_apartB_eqf : bceq.
Lemma ranges_apartB_eqf : forall fk, ranges_apartB (mkbc fk) = ranges_apart fk.
Proof. intros. bcfe. unfold ranges_apartB, ranges_apart. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite ranges_apartB_eqf : bceq.
Lemma sub_itv_xB_eqf : forall fk, sub_itv_xB (mkbc fk) = sub_itv_x fk.
Proof. intros. bcfe. unfold sub_itv_xB, sub_itv_x. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite sub_itv_xB_eqf : bceq.
Lemma kdisj_apart_xB_eqf : forall fk, kdisj_apart_xB (mkbc fk) = kdisj_apart_x fk.
Proof.
  intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2. 
  revert b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kdisj_apart_xB kdisj_apart_x]. destruct K; try apply IH. rewrite IH, !kd_prex_eq. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite kdisj_apart_xB_eqf : bceq.
Lemma end_hiB_eqf : forall fk, end_hiB (mkbc fk) = end_hi fk.
Proof. intros. bcfe. unfold end_hiB, end_hi. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite end_hiB_eqf : bceq.
Lemma ranges_apart_xB_eqf : forall fk, ranges_apart_xB (mkbc fk) = ranges_apart_x fk.
Proof. intros. bcfe. unfold ranges_apart_xB, ranges_apart_x. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite ranges_apart_xB_eqf : bceq.
Lemma disj_sidesB_eqf : forall fk, disj_sidesB (mkbc fk) = disj_sides fk.
Proof.
  intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1. 
  rewrite disj_sidesB_ref_eq.
  revert b1 k1 n1. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [disj_sidesB_ref disj_sides]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite disj_sidesB_eqf : bceq.
Lemma disj_sides_xB_eqf : forall fk, disj_sides_xB (mkbc fk) = disj_sides_x fk.
Proof.
  intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1. 
  revert b1 k1 n1. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [disj_sides_xB disj_sides_x]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite disj_sides_xB_eqf : bceq.
Lemma in_sidesB_eqf : forall fk, in_sidesB (mkbc fk) = in_sides fk.
Proof.
  intros fk. apply functional_extensionality; intros D. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2. 
  revert b2 k2 n2. induction D as [|[c m] rest IH]; intros; bcfe; [reflexivity|].
  cbn [in_sidesB in_sides]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite in_sidesB_eqf : bceq.
Lemma in_sides_xB_eqf : forall fk, in_sides_xB (mkbc fk) = in_sides_x fk.
Proof.
  intros fk. apply functional_extensionality; intros D. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2. 
  revert b2 k2 n2. induction D as [|[c m] rest IH]; intros; bcfe; [reflexivity|].
  cbn [in_sides_xB in_sides_x]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite in_sides_xB_eqf : bceq.
Lemma mk_sprepB_eqf : forall fk, mk_sprepB (mkbc fk) = mk_sprep fk.
Proof. intros. bcfe. unfold mk_sprepB, mk_sprep. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mk_sprepB_eqf : bceq.
Lemma ranges_apart_pB_eqf : forall fk, ranges_apart_pB (mkbc fk) = ranges_apart_p fk.
Proof. intros. bcfe. unfold ranges_apart_pB, ranges_apart_p. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite ranges_apart_pB_eqf : bceq.

(* [comment removed for export] *)
Fixpoint coeffs_divkB (bc : bctx) (m : Z) (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => true
  | (k, a) :: rest => ((Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealignB bc a) mod m) 0) && coeffs_divkB bc m rest)%bool
  end.

Definition lin_lowbits_knB (bc : bctx) (e : expr) (k : Z) : option Z :=
  let l := lin_of e in
  if coeffs_divkB bc (2 ^ k) (snd l) then Some ((fst l) mod 2 ^ k)%Z
  else pageup_low e (2 ^ k).

Definition lin_nowrap_lB (bc : bctx) (c : Z) (ts : list (Z * expr)) : bool :=
  match lin_range (erangeB bc) c ts with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%bool
  | None => false
  end.

Definition lin_periodB (bc : bctx) (a : expr) : option Z :=
  let l := lin_of a in
  match lin_range (erangeB bc) (fst l) (snd l) with
  | Some (lo, hi) => let q := zdiv64 lo in if Z.eqb q (zdiv64 hi) then Some q else None
  | None => None
  end.

Definition mkSrlB (bc : bctx) (a : expr) (s : Z) : expr :=
  let l := lin_of a in
  let m := (2 ^ s)%Z in
  match (if (negb (lin_trivial l) && coeffs_div m (snd l))%bool then lin_periodB bc a else None) with
  | Some q => unlin (((fst l - q * two64) / m)%Z, ldiv_terms m (snd l))
  | None =>
  if (negb (lin_trivial l) && coeffs_div m (snd l) && lin_nowrapB bc a)%bool
  then unlin ((fst l / m)%Z, ldiv_terms m (snd l))     (* [comment removed for export] *)
  else
    (* [comment removed for export] *)
    match (if (negb (lin_trivial l) && lin_nowrapB bc a)%bool then lsplit_divc m (snd l) else ([], [])) with
    | ((_ :: _) as dts, (_ :: _) as rts) =>
        match (if lin_nowrap_lB bc (fst l) rts then erangeB bc (unlin (fst l, rts)) else None) with
        | Some (lo, hi) =>
            if Z.eqb (lo / m) (hi / m) then unlin ((lo / m)%Z, ldiv_terms m dts)
            else mkAlu ALU_SRL a (ELit s)
        | None => mkAlu ALU_SRL a (ELit s)
        end
    | _ => mkAlu ALU_SRL a (ELit s)
    end
  end.

Fixpoint lowbitsB (bc : bctx) (e : expr) (j : Z) {struct e} : option Z :=
  let m := pow2f j in   (* [comment removed for export] *)
  let dfl := fun (_ : unit) => if Z.leb j (ealignB bc e) then Some 0%Z else lin_lowbits_knB bc e j in
  match e with
  | ELit z => Some (m2p (zm64 z) j)%Z
  | EAlu ALU_AND a (ELit c) =>
      if Z.eqb (m2p (zm64 c) j) 0 then Some 0%Z else
      match lowbitsB bc a j with Some v => Some (Z.land v (m2p (zm64 c) j)) | None => dfl tt end
  | EAlu ALU_OR a (ELit c) =>
      match lowbitsB bc a j with Some v => Some (Z.lor v (m2p (zm64 c) j)) | None => dfl tt end
  | EAlu ALU_XOR a (ELit c) =>
      match lowbitsB bc a j with Some v => Some (Z.lxor v (m2p (zm64 c) j)) | None => dfl tt end
  | EAlu ALU_ADD a b =>
      match lowbitsB bc a j, lowbitsB bc b j with Some x, Some y => Some (m2p (x + y) j) | _, _ => dfl tt end
  | EAlu ALU_SUB a b =>
      match lowbitsB bc a j, lowbitsB bc b j with Some x, Some y => Some (m2p (x - y) j) | _, _ => dfl tt end
  | EMd M_MUL (ELit c) a =>
      if Z.eqb (m2p (zm64 c) j) 0 then Some 0%Z else
      match lowbitsB bc a j with Some v => Some (m2p (c * v) j) | None => dfl tt end
  | EExt false O n a =>
      if Z.leb j (8 * Z.of_nat n) then match lowbitsB bc a j with Some v => Some v | None => dfl tt end else dfl tt
  | _ => dfl tt
  end.

Fixpoint lsplit_divB (bc : bctx) (m : Z) (ts : list (Z * expr)) : list (Z * expr) * list (Z * expr) :=
  match ts with
  | [] => ([], [])
  | (k, a) :: rest =>
      let (d, r) := lsplit_divB bc m rest in
      if (Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealignB bc a) mod m) 0)%bool then ((k, a) :: d, r) else (d, (k, a) :: r)
  end.

Definition and_high_splitB (bc : bctx) (bk : expr) (j c : Z) (dts rts : list (Z * expr)) : expr :=
  let m := (2 ^ j)%Z in
  let cA := (c - c mod m)%Z in
  let r := unlin ((c mod m)%Z, rts) in
  match erangeB bc r with
  | Some (lo, hi) =>
      if Z.eqb (lo / m) (hi / m) then unlin ((cA + (lo / m) * m)%Z, dts)
      else mkAlu ALU_ADD (unlin (cA, dts)) (mkAlu ALU_AND r bk)
  | None => mkAlu ALU_ADD (unlin (cA, dts)) (mkAlu ALU_AND r bk)
  end.

Definition and_low_splitB (bc : bctx) (bk : expr) (j c : Z) (rts : list (Z * expr)) : expr :=
  let m := (2 ^ j)%Z in
  let r := unlin ((c mod m)%Z, rts) in
  match erangeB bc r with
  | Some (lo, hi) =>
      if Z.eqb (lo / m) (hi / m) then unlin ((c mod m - (lo / m) * m)%Z, rts)
      else mkAlu ALU_AND r bk
  | None => mkAlu ALU_AND r bk
  end.

Definition narrow_maskB (bc : bctx) (a : expr) (k' : Z) : option Z :=
  let i := ctz64 k' in
  let m := (k' + 2 ^ i)%Z in
  let j := Z.log2 m in
  if (Z.ltb 0 k' && Z.eqb m (2 ^ j) && Z.ltb j 64)%bool then
    match xhiB bc a with
    | Some h => if Z.ltb h (2 ^ j) then Some (two64 - 2 ^ i)%Z else None
    | None => None
    end
  else None.

Definition mkAnd0B (bc : bctx) (a b : expr) : expr :=
  match b with
  | ELit k =>
      let k' := (k mod two64)%Z in
      let j := Z.log2 (two64 - k') in
      if (Z.eqb (two64 - k') (2 ^ j) && Z.ltb j 64)%bool then
        (* [comment removed for export] *)
        (if Z.leb j (ealignB bc a) then a
         else let l := lin_of a in
              if (negb (lin_trivial l) && coeffs_divkB bc (2 ^ j) (snd l))%bool
              then unlin ((fst l - (fst l) mod 2 ^ j)%Z, snd l)
              else (* [comment removed for export] *)
                match (if lin_trivial l then ([], snd l) else lsplit_divB bc (2 ^ j) (snd l)) with
                | ((_ :: _) as dts, (_ :: _) as rts) => and_high_splitB bc b j (fst l) dts rts
                | _ => (* [comment removed for export] *)
                       mkMd M_MUL (ELit (2 ^ j)%Z) (mkSrlB bc a j)
                end)
      else
        let j2 := Z.log2 (k' + 1) in
        if (Z.eqb (k' + 1) (2 ^ j2) && Z.ltb j2 64)%bool then
          (* [comment removed for export] *)
          (if Z.leb j2 (ealignB bc a) then ELit 0
           else match lowbitsB bc a j2 with        (* [comment removed for export] *)
           | Some v => ELit v
           | None =>
           if lin_trivial (lin_of a) then mkAlu ALU_AND a b
           else match lin_lowbits_knB bc a j2 with
                | Some v => ELit v
                | None => (* [comment removed for export] *)
                    match lsplit_divB bc (2 ^ j2) (snd (lin_of a)) with
                    | (_ :: _, (_ :: _) as rts) => and_low_splitB bc b j2 (fst (lin_of a)) rts
                    | _ => mkAlu ALU_AND a b
                    end
                end
           end)
        else (* [comment removed for export] *)
          let j3 := (Z.log2 k' + 1)%Z in
          if (Z.ltb 0 k' && Z.leb j3 64 && negb (lin_trivial (lin_of a)))%bool then
            match lin_lowbits_knB bc a j3 with
            | Some v => ELit (Z.land v k')
            | None => mkAlu ALU_AND a b
            end
          else mkAlu ALU_AND a b
  | _ => mkAlu ALU_AND a b
  end.

Definition mkAndB (bc : bctx) (a b : expr) : expr :=
  match b with
  | ELit k =>
      match narrow_maskB bc a (k mod two64)%Z with
      | Some m => mkAnd0B bc a (ELit m)
      | None => mkAnd0B bc a b
      end
  | _ => mkAnd0B bc a b
  end.

Definition mkAndKB (bc : bctx) (a b : expr) : expr :=
  match a, b with
  | EAlu ALU_AND x (ELit m1), ELit k => mkAndB bc x (ELit (Z.land (m1 mod two64) (k mod two64))%Z)
  | EMd M_MUL (ELit m) (EAlu ALU_SRL x (ELit i)), ELit k =>
      (* [comment removed for export] *)
      let i' := ((i mod two64) mod 64)%Z in
      if Z.eqb (m mod two64) (2 ^ i') then mkAndB bc x (ELit (Z.land (two64 - 2 ^ i') (k mod two64))%Z)
      else mkAndB bc a b
  | _, _ => mkAndB bc a b
  end.

Definition or_disjointB (bc : bctx) (a b : expr) : bool :=
  match erangeB bc b with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi (2 ^ (ealignB bc a)))%bool
  | None => false
  end.

Definition mkOrB (bc : bctx) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (zalu ALU_OR x y)
  | _, _ =>
      if or_disjointB bc a b then mkAlu ALU_ADD a b
      else if or_disjointB bc b a then mkAlu ALU_ADD a b
      else (* [comment removed for export] *)
           match b with
           | ELit c => mkAlu ALU_ADD (mkAndKB bc a (ELit (Z.lnot (c mod two64)))) (ELit c)
           | _ => match a with
                  | ELit c => mkAlu ALU_ADD (mkAndKB bc b (ELit (Z.lnot (c mod two64)))) (ELit c)
                  | _ => EAlu ALU_OR a b
                  end
           end
  end.

(* [comment removed for export] *)
Definition zcanon (x : Z) : bool := if Z.leb 0 x then Z.ltb x two64 else false.
Definition zsgn32 (r : Z) : Z := if Z.ltb r 2147483648 then r else (r - 4294967296)%Z.
Definition zfastF (op : aluop) (x y : Z) : Z :=
  match op with
  | ALU_SLT => if zcanon x then if zcanon y then (if Z.ltb (zsigned64 x) (zsigned64 y) then 1 else 0)%Z else zfast op x y
               else zfast op x y
  | ALU_SRA => if zcanon x then if zcanon y then land64 (Z.shiftr (zsigned64 x) (Z.land y 63)) else zfast op x y
               else zfast op x y
  | _ => zfast op x y
  end.
Definition zfastwF (op : aluop) (x y : Z) : Z :=
  match op with
  | ALU_SRA => if zcanon x then if zcanon y then sx32 (land32 (Z.shiftr (zsgn32 (land32 x)) (Z.land y 31))) else zfastw op x y
               else zfastw op x y
  | _ => zfastw op x y
  end.
Definition zfastmF (op : mulop) (x y : Z) : Z :=
  match op with
  | M_MULHU => if zcanon x then if zcanon y then Z.shiftr (x * y) 64 else zfastm op x y else zfastm op x y
  | _ => zfastm op x y
  end.
Lemma g2_u_small : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned, bv_wrap64_mod. apply Z.mod_small. exact Hz. Qed.
Lemma g2_signed : forall z, (0 <= z < 2 ^ 64)%Z -> bv_signed (Z_to_bv 64 z) = zsigned64 z.
Proof.
  intros z Hz. unfold zsigned64, two63z, two64. destruct (Z.leb_spec (2 ^ 63) z).
  - rewrite bv_signed_hi; rewrite g2_u_small; lia.
  - rewrite bv_signed_small; rewrite g2_u_small; lia.
Qed.
Lemma g2_canon : forall x, zcanon x = true -> (0 <= x < 2 ^ 64)%Z.
Proof.
  intros x H. unfold zcanon, two64 in H. destruct (Z.leb_spec 0 x); [|discriminate]. apply Z.ltb_lt in H. lia.
Qed.
Lemma g2_land64 : forall z, land64 z = (z mod 2 ^ 64)%Z.
Proof.
  intros z. unfold land64. destruct (Z.leb 0 z && Z.ltb z two64)%bool eqn:H.
  - apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64 in H2. symmetry. apply Z.mod_small. lia.
  - unfold ones64z. rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma g2_land32 : forall z, land32 z = (z mod 4294967296)%Z.
Proof.
  intros z. unfold land32. destruct (Z.leb 0 z && Z.ltb z two32z)%bool eqn:H.
  - apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two32z in H2. symmetry. apply Z.mod_small. lia.
  - unfold ones32z. rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma g2_land63 : forall y, Z.land y 63 = (y mod 64)%Z.
Proof. intros y. change 63%Z with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma g2_land31 : forall y, Z.land y 31 = (y mod 32)%Z.
Proof. intros y. change 31%Z with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma g2_swrap32 : forall t, bv_unsigned (Z_to_bv 64 (bv_swrap 32 t)) = sx32 (t mod 4294967296)%Z.
Proof.
  intros t. rewrite Z_to_bv_unsigned, bv_wrap64_mod. unfold bv_swrap, bv_wrap, sx32.
  change (bv_modulus 32) with 4294967296%Z. change (bv_half_modulus 32) with 2147483648%Z.
  pose proof (Z.mod_pos_bound t 4294967296 ltac:(lia)) as Hr.
  set (r := (t mod 4294967296)%Z) in *.
  assert (E : ((t + 2147483648) mod 4294967296 = (r + 2147483648) mod 4294967296)%Z).
  { subst r. rewrite <- Zplus_mod_idemp_l. reflexivity. }
  rewrite E. destruct (Z.ltb_spec r 2147483648).
  - rewrite (Z.mod_small (r + 2147483648)) by lia. rewrite Z.add_simpl_r. apply Z.mod_small. lia.
  - replace (r + 2147483648)%Z with (r - 2147483648 + 1 * 4294967296)%Z by lia.
    rewrite Z.mod_add by lia. rewrite (Z.mod_small (r - 2147483648)) by lia.
    replace (r - 2147483648 - 2147483648)%Z with (r + 18446744069414584320 + (-1) * 18446744073709551616)%Z by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma g2_swrap32_sgn : forall x, bv_swrap 32 x = zsgn32 (x mod 4294967296)%Z.
Proof.
  intros x. unfold bv_swrap, bv_wrap, zsgn32.
  change (bv_modulus 32) with 4294967296%Z. change (bv_half_modulus 32) with 2147483648%Z.
  pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)) as Hr.
  set (r := (x mod 4294967296)%Z) in *.
  assert (E : ((x + 2147483648) mod 4294967296 = (r + 2147483648) mod 4294967296)%Z).
  { subst r. rewrite <- Zplus_mod_idemp_l. reflexivity. }
  rewrite E. destruct (Z.ltb_spec r 2147483648).
  - rewrite (Z.mod_small (r + 2147483648)) by lia. lia.
  - replace (r + 2147483648)%Z with (r - 2147483648 + 1 * 4294967296)%Z by lia.
    rewrite Z.mod_add by lia. rewrite (Z.mod_small (r - 2147483648)) by lia. lia.
Qed.
Lemma zfastF_fe : zfastF = zfast.
Proof.
  apply functional_extensionality; intros op. apply functional_extensionality; intros x. apply functional_extensionality; intros y.
  destruct op; cbn [zfastF]; try reflexivity;
    (destruct (zcanon x) eqn:Cx; [|reflexivity]); (destruct (zcanon y) eqn:Cy; [|reflexivity]);
    apply g2_canon in Cx; apply g2_canon in Cy; cbn [zfast]; unfold zalu.
  - rewrite alu_slt. unfold v_slt, c_lts, bv_lts. rewrite !g2_signed by assumption.
    destruct (Z.ltb (zsigned64 x) (zsigned64 y)); symmetry; apply g2_u_small; lia.
  - rewrite alu_sra. unfold v_sra. rewrite Z_to_bv_unsigned, bv_wrap64_mod, g2_signed, (g2_u_small y) by assumption.
    rewrite g2_land64, g2_land63. reflexivity.
Qed.
Lemma zfastwF_fe : zfastwF = zfastw.
Proof.
  apply functional_extensionality; intros op. apply functional_extensionality; intros x. apply functional_extensionality; intros y.
  destruct op; cbn [zfastwF]; try reflexivity.
  destruct (zcanon x) eqn:Cx; [|reflexivity]. destruct (zcanon y) eqn:Cy; [|reflexivity].
  apply g2_canon in Cx; apply g2_canon in Cy. cbn [zfastw]. unfold zaluw.
  rewrite w_sraw. unfold v_sraw. rewrite g2_swrap32, (g2_u_small x Cx), (g2_u_small y Cy).
  rewrite g2_land32, g2_swrap32_sgn, g2_land32, g2_land31. reflexivity.
Qed.
Lemma zfastmF_fe : zfastmF = zfastm.
Proof.
  apply functional_extensionality; intros op. apply functional_extensionality; intros x. apply functional_extensionality; intros y.
  destruct op; cbn [zfastmF]; try reflexivity.
  destruct (zcanon x) eqn:Cx; [|reflexivity]. destruct (zcanon y) eqn:Cy; [|reflexivity].
  apply g2_canon in Cx; apply g2_canon in Cy. cbn [zfastm]. unfold zmd.
  rewrite m_mulhu. unfold v_mulhu. rewrite (g2_u_small x Cx), (g2_u_small y Cy).
  assert (0 <= x * y < 2 ^ 64 * 2 ^ 64)%Z as Hp by nia.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.shiftr_div_pow2 by lia. symmetry. apply Z.mod_small.
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.
(* [comment removed for export] *)
Definition mlitnegF (op : mulop) (a s : expr) : option Z :=
  match op, a with
  | M_MUL, ELit k => if Z.ltb k 0 then (if expr_eqb a s then None else Some k) else None
  | _, _ => None
  end.
Fixpoint evalSF (s : expr) (z : Z) (e : expr) : option Z :=
  if expr_eqb e s then Some z else
  match e with
  | ELit w => Some (land64 w)   (* [comment removed for export] *)
  | EVar _ => None
  | EAlu op a b => match evalSF s z a with
                   | Some x => match evalSF s z b with Some y => Some (zfastF op x y) | None => None end
                   | None => None
                   end
  | EAluw op a b => match evalSF s z a with
                    | Some x => match evalSF s z b with Some y => Some (zfastwF op x y) | None => None end
                    | None => None
                    end
  | EMd op a b => match mlitnegF op a s with
                  | Some k => match evalSF s z b with Some y => Some (land64 (k * y)) | None => None end
                  | None =>
                  match evalSF s z a with
                  | Some x => match evalSF s z b with Some y => Some (zfastmF op x y) | None => None end
                  | None => None
                  end end
  | EMdw op a b => match evalSF s z a with
                   | Some x => match evalSF s z b with Some y => Some (zmdw op x y) | None => None end
                   | None => None
                   end
  | EExt sx lo n a => match evalSF s z a with
                      | Some x => Some (zext_fast sx lo n x) | None => None end
  | EBlob _ _ _ _ => None
  end.
Lemma g2_land64_wrap : forall z, land64 z = wrap64 z.
Proof.
  intros z. rewrite g2_land64. unfold wrap64. destruct (Z.leb 0 z && Z.ltb z two64)%bool eqn:H; [|unfold two64; reflexivity].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64 in H2. apply Z.mod_small. lia.
Qed.
Lemma s1_mul_mod : forall k y, land64 (k * y) = zfastm M_MUL (wrap64 k) y.
Proof.
  intros k y. cbn [zfastm]. rewrite !g2_land64, <- g2_land64_wrap, g2_land64. rewrite Z.mul_mod_idemp_l by (vm_compute; discriminate). reflexivity.
Qed.
Lemma mlitnegF_some : forall op a s k, mlitnegF op a s = Some k -> op = M_MUL /\ a = ELit k /\ expr_eqb a s = false.
Proof.
  intros op a s k H. unfold mlitnegF in H. destruct op; try discriminate H. destruct a; try discriminate H.
  destruct (Z.ltb _ 0); [|discriminate H]. destruct (expr_eqb _ s); [discriminate H|]. injection H as <-. repeat split; reflexivity.
Qed.
Lemma evalSF_fe : evalSF = evalS.
Proof.
  apply functional_extensionality; intros s. apply functional_extensionality; intros z. apply functional_extensionality; intros e.
  induction e; cbn [evalSF evalS]; destruct (expr_eqb _ s) eqn:Es; try reflexivity;
    rewrite ?IHe1, ?IHe2, ?IHe, ?zfastF_fe, ?zfastwF_fe, ?zfastmF_fe, ?g2_land64_wrap; try reflexivity.
  (* [comment removed for export] *) destruct (mlitnegF _ _ s) as [k|] eqn:M; [|reflexivity].
  apply mlitnegF_some in M as [-> [-> Ea]]. cbn [evalS]. rewrite Ea.
  destruct (evalS s z e2); [|reflexivity]. rewrite s1_mul_mod. reflexivity.
Qed.
Fixpoint all_eval_toSF (s e : expr) (v lo : Z) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c => match evalSF s (wrap64 lo) e with
           | Some w => if Z.eqb w v then all_eval_toSF s e v (lo + 1) c else false
           | None => false
           end
  end.
Lemma all_eval_toSF_fe : all_eval_toSF = all_eval_toS.
Proof.
  apply functional_extensionality; intros s. apply functional_extensionality; intros e. apply functional_extensionality; intros v.
  apply functional_extensionality; intros lo. apply functional_extensionality; intros cnt. revert lo.
  induction cnt as [|c IH]; intros lo; cbn [all_eval_toSF all_eval_toS]; [reflexivity|]. rewrite evalSF_fe, IH. reflexivity.
Qed.
Definition probeSF (s e : expr) (v z : Z) : bool :=
  match evalSF s (wrap64 z) e with Some w => Z.eqb w v | None => false end.
Lemma probeSF_fe : probeSF = probeS.
Proof. unfold probeSF, probeS. rewrite evalSF_fe. reflexivity. Qed.
#[export] Hint Rewrite evalSF_fe all_eval_toSF_fe probeSF_fe : bceq.
(* [comment removed for export] *)
Fixpoint compSF (s e : expr) {struct e} : option (Z -> Z) :=
  if expr_eqb e s then Some (fun z => z) else
  match e with
  | ELit w => let c := land64 w in Some (fun _ => c)
  | EVar _ => None
  | EAlu op a b => match compSF s a with
                   | Some f => match compSF s b with Some g => Some (fun z => zfastF op (f z) (g z)) | None => None end
                   | None => None
                   end
  | EAluw op a b => match compSF s a with
                    | Some f => match compSF s b with Some g => Some (fun z => zfastwF op (f z) (g z)) | None => None end
                    | None => None
                    end
  | EMd op a b => match mlitnegF op a s with
                  | Some k => match compSF s b with Some g => Some (fun z => land64 (k * g z)) | None => None end
                  | None =>
                  match compSF s a with
                  | Some f => match compSF s b with Some g => Some (fun z => zfastmF op (f z) (g z)) | None => None end
                  | None => None
                  end end
  | EMdw op a b => match compSF s a with
                   | Some f => match compSF s b with Some g => Some (fun z => zmdw op (f z) (g z)) | None => None end
                   | None => None
                   end
  | EExt sx lo n a => match compSF s a with
                      | Some f => Some (fun z => zext_fast sx lo n (f z)) | None => None end
  | EBlob _ _ _ _ => None
  end.
Lemma compSF_ok : forall s e,
  match compSF s e with Some f => forall z, evalSF s z e = Some (f z) | None => forall z, evalSF s z e = None end.
Proof.
  intros s e. induction e; cbn [compSF evalSF]; (destruct (expr_eqb _ s); [intros z0; reflexivity|]);
    try (intros z0; reflexivity).
  - destruct (compSF s e1) as [f|]; [|intros z0; rewrite IHe1; reflexivity].
    destruct (compSF s e2) as [g|]; intros z0; rewrite IHe1, IHe2; reflexivity.
  - destruct (compSF s e1) as [f|]; [|intros z0; rewrite IHe1; reflexivity].
    destruct (compSF s e2) as [g|]; intros z0; rewrite IHe1, IHe2; reflexivity.
  - destruct (mlitnegF _ _ s) as [k|].
    + destruct (compSF s e2) as [g|]; intros z0; rewrite IHe2; reflexivity.
    + destruct (compSF s e1) as [f|]; [|intros z0; rewrite IHe1; reflexivity].
      destruct (compSF s e2) as [g|]; intros z0; rewrite IHe1, IHe2; reflexivity.
  - destruct (compSF s e1) as [f|]; [|intros z0; rewrite IHe1; reflexivity].
    destruct (compSF s e2) as [g|]; intros z0; rewrite IHe1, IHe2; reflexivity.
  - destruct (compSF s e) as [f|]; intros z0; rewrite IHe; reflexivity.
Qed.
Fixpoint sweepF (f : Z -> Z) (v lo : Z) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c => if Z.eqb (f (wrap64 lo)) v then sweepF f v (lo + 1) c else false
  end.
Definition all_eval_toSF2 (s e : expr) (v lo : Z) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S _ => match compSF s e with Some f => sweepF f v lo cnt | None => false end
  end.
Lemma all_eval_toSF2_fe : all_eval_toSF2 = all_eval_toSF.
Proof.
  apply functional_extensionality; intros s. apply functional_extensionality; intros e. apply functional_extensionality; intros v.
  apply functional_extensionality; intros lo. apply functional_extensionality; intros cnt.
  pose proof (compSF_ok s e) as C. unfold all_eval_toSF2.
  destruct cnt as [|c]; [reflexivity|]. destruct (compSF s e) as [f|].
  - revert lo. generalize (S c) as n. induction n as [|n IH]; intros lo; [reflexivity|].
    cbn [sweepF all_eval_toSF]. rewrite C, IH. reflexivity.
  - cbn [all_eval_toSF]. rewrite C. reflexivity.
Qed.
#[export] Hint Rewrite all_eval_toSF2_fe : bceq.
Fixpoint conc_tryB (bc : bctx) (e : expr) (cands : list expr) : option Z :=
  match cands with
  | [] => None
  | s :: rest =>
      if closedb s then conc_tryB bc e rest else
      if negb (evalS_def s e) then conc_tryB bc e rest else
      match erangeB bc s with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            match evalSF s (wrap64 lo) e with
            | Some v =>
                if (if Z.ltb hi lo then true
                     else if probeSF s e v hi then probeSF s e v (lo + (hi - lo) / 2)%Z else false) then
                  if all_eval_toSF2 s e v lo (Z.to_nat (hi - lo + 1)) then Some v
                  else conc_tryB bc e rest
                else conc_tryB bc e rest
            | None => conc_tryB bc e rest
            end
          else conc_tryB bc e rest
      | None => conc_tryB bc e rest
      end
  end.

Definition concretizeB (bc : bctx) (e : expr) : option Z :=
  if closedb e then eval_closed e else
  match (match erangeB bc e with Some (lo, hi) => if Z.eqb lo hi then Some lo else None | None => None end) with
  | Some v => Some v
  | None => if conc_small e then conc_tryB bc e (nubE (subexprs e)) else None
  end.

Definition concretize_nrB (bc : bctx) (e : expr) : option Z :=
  if closedb e then eval_closed e else if conc_small e then conc_tryB bc e (nubE (subexprs e)) else None.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition erange_bodyB (erange : bctx -> expr -> option (Z * Z)) (bc : bctx) (e : expr) : option (Z * Z) :=
  match find_rangeI (bc_ri bc) e with
  | Some r => Some (clampi r)
  | None =>
  match (let l := lin_of e in
         if lin_trivial l then None
         else match lin_range (erange bc) (fst l) (snd l) with
              | Some (lo, hi) =>
                  (* [comment removed for export] *)
                  let q := zdiv64 lo in   (* [comment removed for export] *)
                  if Z.eqb q (zdiv64 hi) then Some ((lo - q * two64)%Z, (hi - q * two64)%Z) else None
              | None => None
              end) with
  | Some r => Some r
  | None =>
  match e with
  | ELit z => let v := zmod64 z in Some (v, v)   (* [comment removed for export] *)
  | EVar _ => None
  | EAlu op a b =>
      match op with
      | ALU_ADD =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.ltb (ah + bh) two64 then Some ((al + bl)%Z, (ah + bh)%Z)
              else if Z.leb two64 (al + bl) then Some ((al + bl - two64)%Z, (ah + bh - two64)%Z)
              else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.leb bh al then Some ((al - bh)%Z, (ah - bl)%Z)
              else if Z.ltb ah bl then Some ((al - bh + two64)%Z, (ah - bl + two64)%Z)
              else None
          | _, _ => None
          end
      | ALU_AND =>
          (* [comment removed for export] *)
          match (match b, erange bc a with
                 | ELit m, Some (al, ah) =>
                     let m' := (pmod64 m) in
                     let j := Z.log2 (m' + 1) in
                     if (Z.eqb (m' + 1) (2 ^ j) && Z.leb (pdiv al j) (pdiv ah j) && Z.eqb (pdiv al j) (pdiv ah j))%bool
                     then Some ((pmod al j)%Z, (pmod ah j)%Z)
                     else let jh := Z.log2 (two64 - m') in
                          if (Z.eqb (two64 - m') (2 ^ jh) && Z.ltb jh 64)%bool
                          then Some ((al - pmod al jh)%Z, (ah - pmod ah jh)%Z)
                          else None
                 | _, _ => None
                 end) with
          | Some r => Some r
          | None =>
          match erange bc a, erange bc b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, Z.min ah bh)
          | Some (_, ah), None => Some (0%Z, ah)
          | None, Some (_, bh) => Some (0%Z, bh)
          | None, None => None
          end
          end
      | ALU_OR =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) => Some (Z.max al bl, mask_cover (Z.max ah bh))
          | _, _ => None
          end
      | ALU_XOR =>
          match erange bc a, erange bc b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, mask_cover (Z.max ah bh))
          | _, _ => None
          end
      | ALU_SRL =>
          match erange bc a, lit_shamtB b with
          | Some (al, ah), Some s => Some ((pdiv al s)%Z, (pdiv ah s)%Z)
          | None, Some s => Some (0%Z, (2 ^ (64 - s) - 1)%Z)   (* [comment removed for export] *)
          | _, _ => None
          end
      | ALU_SRA =>
          match erange bc a, lit_shamtB b with
          | Some (al, ah), Some s =>
              if Z.ltb ah (2 ^ 63) then Some ((pdiv al s)%Z, (pdiv ah s)%Z)
              else (* [comment removed for export] *)
                if Z.leb (2 ^ 63) al then Some ((two64 + pdiv (al - two64) s)%Z, (two64 + pdiv (ah - two64) s)%Z)
                else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange bc a, lit_shamtB b with
          | Some (al, ah), Some s =>
              if Z.ltb (pmul ah s) two64 then Some ((pmul al s)%Z, (pmul ah s)%Z) else None
          | _, _ => None
          end
      | ALU_SLTU =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.ltb ah bl then Some (1%Z, 1%Z)
              else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z)
          | _, _ => Some (0%Z, 1%Z)
          end
      | ALU_SLT =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.ltb ah (2 ^ 63) && Z.ltb bh (2 ^ 63))%bool then
                (if Z.ltb ah bl then Some (1%Z, 1%Z)
                 else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z))
              else Some (0%Z, 1%Z)
          | _, _ => Some (0%Z, 1%Z)
          end
      end
  | EAluw op a b =>
      match op with
      | ALU_ADD =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              let bl' := if Z.eqb bl bh then zsigned64 bl else bl in
              let bh' := if Z.eqb bl bh then zsigned64 bh else bh in
              if (Z.leb 0 (al + bl') && Z.ltb (ah + bh') (2 ^ 31))%bool
              then Some ((al + bl')%Z, (ah + bh')%Z) else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb bh al && Z.ltb (ah - bl) (2 ^ 31))%bool
              then Some ((al - bh)%Z, (ah - bl)%Z) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange bc a, lit_shamtB b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb (pmul ah s') (2 ^ 31) then Some ((pmul al s')%Z, (pmul ah s')%Z) else None
          | _, _ => None
          end
      | ALU_SRL =>
          match erange bc a, lit_shamtB b with
          | Some (al0, ah0), Some s =>
              let s' := (s mod 32)%Z in
              match (if Z.ltb ah0 (2 ^ 32) then Some (al0, ah0)
                     else if Z.eqb (pdiv al0 32) (pdiv ah0 32) then Some ((pmod al0 32)%Z, (pmod ah0 32)%Z)
                     else None) with
              | Some (al, ah) =>
                  if (Z.ltb ah (2 ^ 32) && (Z.ltb 0 s' || Z.ltb ah (2 ^ 31)))%bool
                  then Some ((pdiv al s')%Z, (pdiv ah s')%Z)
                  else if Z.ltb 0 s' then Some (0%Z, (2 ^ (32 - s') - 1)%Z) else None
              | None => if Z.ltb 0 s' then Some (0%Z, (2 ^ (32 - s') - 1)%Z) else None
              end
          | None, Some s =>   (* [comment removed for export] *)
              let s' := (s mod 32)%Z in if Z.ltb 0 s' then Some (0%Z, (2 ^ (32 - s') - 1)%Z) else None
          | _, _ => None
          end
      | ALU_SRA =>
          match erange bc a, lit_shamtB b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb ah (2 ^ 31) then Some ((pdiv al s')%Z, (pdiv ah s')%Z)
              else (* [comment removed for export] *)
                if (Z.eqb (pdiv al 32) (pdiv ah 32) && Z.leb (2 ^ 31) (pmod al 32))%bool
                then Some ((two64 + pdiv (pmod al 32 - 2 ^ 32) s')%Z, (two64 + pdiv (pmod ah 32 - 2 ^ 32) s')%Z)
                else None
          | _, _ => None
          end
      | _ => None
      end
  | EMd op a b =>
      match op with
      | M_MUL =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              mul_rng al ah bl bh
          | _, _ => None
          end
      | M_MULH =>   (* [comment removed for export] *)
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl && Z.ltb ah (2 ^ 63) && Z.ltb bh (2 ^ 63))%bool
              then Some ((pdiv64 (zmulf al bl))%Z, (pdiv64 (zmulf ah bh))%Z) else None
          | _, _ => None
          end
      | M_MULHU =>   (* [comment removed for export] *)
          match rng_or_full (erange bc a), rng_or_full (erange bc b) with
          | (al, ah), (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl)%bool
              then Some ((pdiv64 (zmulf al bl))%Z, (pdiv64 (zmulf ah bh))%Z) else None
          end
      | M_DIVU =>
          match erange bc a, b with
          | Some (al, ah), ELit d =>
              let d' := (pmod64 d) in
              if Z.ltb 0 d' then Some ((al / d')%Z, (ah / d')%Z) else None
          | _, _ => None
          end
      | M_REMU =>
          match erange bc a, b with
          | Some (al, ah), ELit d =>
              let d' := (pmod64 d) in
              if Z.ltb 0 d' then Some (0%Z, Z.min ah (d' - 1)) else None
          | _, _ => None
          end
      | _ => None
      end
  | EMdw _ _ _ => None
  | EExt sx lo n a =>
      let w := ext_w n in
      if sx then
        match lo with
        | O =>
            let dec (r : option (Z * Z)) : option (Z * Z) :=
              match r with
              | Some (al, ah) =>
                  if (Z.leb 0 al && Z.ltb ah (ext_half n))%bool then Some (al, ah)
                  else if (Nat.leb 1 n && Nat.leb n 8 && Z.leb (ext_half n) al && Z.ltb ah w)%bool
                       then Some ((two64 - w + al)%Z, (two64 - w + ah)%Z) else None
              | None => None
              end in
            match dec (erange bc a) with
            | Some r => Some r
            | None => if Nat.leb n 7 then dec (erange bc (EExt false 0 n a)) else None   (* [comment removed for export] *)
            end
        | _ => None
        end
      else
        match lo, erange bc a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah w)%bool then Some (al, ah) else Some (0%Z, ext_top n)
        | _, _ => Some (0%Z, ext_top n)
        end
  | EBlob sx k i n =>
      (* [comment removed for export] *)
      if sx then Some (0%Z, two64m1) else Some (0%Z, ext_top n)%Z
  end
  end
  end.
Lemma erange_fB_S : forall f bc e, erange_fB (S f) bc e = erange_bodyB (erange_fB f) bc e.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint eheight (e : expr) : nat :=
  match e with
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => S (Nat.max (eheight a) (eheight b))
  | EExt sx _ _ a => if sx then S (S (eheight a)) else S (eheight a)
  | _ => O
  end.
Definition atoms_le (n : nat) (ts : list (Z * expr)) : Prop := Forall (fun t => (eheight (snd t) <= n)%nat) ts.
Lemma lins_atoms : forall n k a ts, (eheight a <= n)%nat -> atoms_le n ts -> atoms_le n (lins k a ts).
Proof.
  intros n k a ts Ha. induction ts as [|[k' a'] rest IH]; intros Hts; cbn [lins].
  - destruct (Z.eqb (snorm k) 0); constructor; [exact Ha|constructor].
  - inversion Hts as [|? ? Hh Hr]; subst. destruct (expr_eqb a a').
    + destruct (Z.eqb (snorm (k + k')) 0); [exact Hr|]. constructor; [exact Hh|exact Hr].
    + destruct (expr_cmp a a').
      * constructor; [exact Hh|apply IH; exact Hr].
      * destruct (Z.eqb (snorm k) 0); [exact Hts|]. constructor; [exact Ha|exact Hts].
      * constructor; [exact Hh|apply IH; exact Hr].
Qed.
Lemma ladd_atoms : forall n x y, atoms_le n (snd x) -> atoms_le n (snd y) -> atoms_le n (snd (ladd x y)).
Proof.
  intros n x y Hx Hy. unfold ladd. cbn [snd]. induction (snd x) as [|t rest IH]; cbn [fold_right]; [exact Hy|].
  inversion Hx; subst. apply lins_atoms; [assumption|apply IH; assumption].
Qed.
Lemma lscale_terms_atoms : forall n m ts, atoms_le n ts -> atoms_le n (lscale_terms m ts).
Proof.
  intros n m ts. induction ts as [|[k a] rest IH]; intros H; cbn [lscale_terms]; [constructor|].
  inversion H; subst. destruct (Z.eqb (snorm (m * k)) 0); [apply IH; assumption|]. constructor; [assumption|apply IH; assumption].
Qed.
Lemma lscale_atoms : forall n m x, atoms_le n (snd x) -> atoms_le n (snd (lscale m x)).
Proof. intros. unfold lscale. cbn [snd]. apply lscale_terms_atoms. assumption. Qed.
Lemma atoms_le_mono : forall n n' ts, (n <= n')%nat -> atoms_le n ts -> atoms_le n' ts.
Proof. intros n n' ts Hn H. unfold atoms_le in *. rewrite Forall_forall in *. intros t Ht. specialize (H t Ht). lia. Qed.
Lemma lin_of_atoms : forall e, atoms_le (eheight e) (snd (lin_of e)).
Proof.
  assert (TRIV : forall e, atoms_le (eheight e) [(1%Z, e)]) by (intros; constructor; [cbn; lia|constructor]).
  induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n]; try apply TRIV.
  - constructor.
  - assert (Ha : atoms_le (eheight (EAlu op a b)) (snd (lin_of a))) by (eapply atoms_le_mono; [|exact IHa]; cbn; lia).
    assert (Hb : atoms_le (eheight (EAlu op a b)) (snd (lin_of b))) by (eapply atoms_le_mono; [|exact IHb]; cbn; lia).
    destruct op; try apply TRIV.
    + cbn [lin_of]. apply ladd_atoms; assumption.
    + cbn [lin_of]. apply ladd_atoms; [assumption|apply lscale_atoms; assumption].
    + destruct b; try apply TRIV. cbn [lin_of]. apply lscale_atoms; assumption.
  - assert (Ha : atoms_le (eheight (EMd op a b)) (snd (lin_of a))) by (eapply atoms_le_mono; [|exact IHa]; cbn; lia).
    assert (Hb : atoms_le (eheight (EMd op a b)) (snd (lin_of b))) by (eapply atoms_le_mono; [|exact IHb]; cbn; lia).
    destruct op; try apply TRIV.
    destruct a; try (cbn [lin_of]; apply lscale_atoms; assumption);
    destruct b; try (cbn [lin_of]; apply lscale_atoms; assumption); apply TRIV.
Qed.
Lemma lin_of_atoms_lt : forall e, lin_trivial (lin_of e) = false ->
  Forall (fun t => (eheight (snd t) < eheight e)%nat) (snd (lin_of e)).
Proof.
  assert (LT : forall n ts, atoms_le n ts -> Forall (fun t => (eheight (snd t) < S n)%nat) ts).
  { intros n ts H. unfold atoms_le in H. rewrite Forall_forall in *. intros t Ht. specialize (H t Ht). lia. }
  intros e. destruct e as [z|n|op a b|op a b|op a b|op a b|sx lo n a|sx k i n]; try (cbn; discriminate).
  - intros _. constructor.
  - intros Hnt. cbn [eheight]. apply LT.
    assert (Ha : atoms_le (Nat.max (eheight a) (eheight b)) (snd (lin_of a))) by (eapply atoms_le_mono; [|apply lin_of_atoms]; lia).
    assert (Hb : atoms_le (Nat.max (eheight a) (eheight b)) (snd (lin_of b))) by (eapply atoms_le_mono; [|apply lin_of_atoms]; lia).
    destruct op; try (cbn in Hnt; discriminate).
    + cbn [lin_of]. apply ladd_atoms; assumption.
    + cbn [lin_of]. apply ladd_atoms; [assumption|apply lscale_atoms; assumption].
    + destruct b; try (cbn in Hnt; discriminate). cbn [lin_of]. apply lscale_atoms; assumption.
  - intros Hnt. cbn [eheight]. apply LT.
    assert (Ha : atoms_le (Nat.max (eheight a) (eheight b)) (snd (lin_of a))) by (eapply atoms_le_mono; [|apply lin_of_atoms]; lia).
    assert (Hb : atoms_le (Nat.max (eheight a) (eheight b)) (snd (lin_of b))) by (eapply atoms_le_mono; [|apply lin_of_atoms]; lia).
    destruct op; try (cbn in Hnt; discriminate).
    destruct a; try (cbn [lin_of]; apply lscale_atoms; assumption);
    destruct b; try (cbn [lin_of]; apply lscale_atoms; assumption); cbn in Hnt; discriminate.
Qed.
Lemma lin_range_ext_in : forall r1 r2 c ts, Forall (fun t => r1 (snd t) = r2 (snd t)) ts -> lin_range r1 c ts = lin_range r2 c ts.
Proof.
  intros r1 r2 c ts H. induction ts as [|[k a] rest IH]; [reflexivity|]. inversion H; subst. cbn [lin_range]. cbn [snd] in *.
  match goal with E : r1 a = r2 a |- _ => rewrite E end. rewrite IH by assumption. reflexivity.
Qed.

Lemma erange_bodyB_ext : forall r1 r2 bc e,
  (forall x, (eheight x < eheight e)%nat -> r1 bc x = r2 bc x) ->
  erange_bodyB r1 bc e = erange_bodyB r2 bc e.
Proof.
  intros r1 r2 bc e H. unfold erange_bodyB.
  destruct (find_rangeI (bc_ri bc) e); [reflexivity|]. cbv zeta.
  destruct (lin_trivial (lin_of e)) eqn:LT.
  2:{ rewrite (lin_range_ext_in (r1 bc) (r2 bc)).
      2:{ pose proof (lin_of_atoms_lt e LT) as HA. rewrite Forall_forall in *. intros t Ht. apply H. apply HA. exact Ht. }
      match goal with |- match ?X with _ => _ end = _ => destruct X; [reflexivity|] end.
      clear LT.
      destruct e as [z|n|op a b|op a b|op a b|op a b|sx lo n a|sx k i n]; try reflexivity.
      - rewrite ?(H a), ?(H b) by (cbn [eheight]; lia). reflexivity.
      - rewrite ?(H a), ?(H b) by (cbn [eheight]; lia). reflexivity.
      - rewrite ?(H a), ?(H b) by (cbn [eheight]; lia). reflexivity.
      - destruct sx; rewrite ?(H a), ?(H (EExt false 0 n a)) by (cbn [eheight]; lia); reflexivity. }
  clear LT.
  destruct e as [z|n|op a b|op a b|op a b|op a b|sx lo n a|sx k i n]; try reflexivity.
  - rewrite ?(H a), ?(H b) by (cbn [eheight]; lia). reflexivity.
  - rewrite ?(H a), ?(H b) by (cbn [eheight]; lia). reflexivity.
  - rewrite ?(H a), ?(H b) by (cbn [eheight]; lia). reflexivity.
  - destruct sx; rewrite ?(H a), ?(H (EExt false 0 n a)) by (cbn [eheight]; lia); reflexivity.
Qed.

Lemma erange_fB_fuel : forall f1 f2 bc e, (eheight e < f1)%nat -> (eheight e < f2)%nat -> erange_fB f1 bc e = erange_fB f2 bc e.
Proof.
  induction f1 as [|f1 IH]; intros f2 bc e H1 H2; [lia|]. destruct f2 as [|f2]; [lia|].
  rewrite !erange_fB_S. apply erange_bodyB_ext. intros x Hx. apply IH; lia.
Qed.

(* [comment removed for export] *)
Definition rmemo := list (expr * option (Z * Z)).
Fixpoint memo_get (m : rmemo) (e : expr) : option (option (Z * Z)) :=
  match m with [] => None | (x, r) :: rest => if expr_eqb e x then Some r else memo_get rest e end.
Fixpoint erange_fM (m : rmemo) (fuel : nat) (bc : bctx) (e : expr) {struct fuel} : option (Z * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
      match e with
      | ELit _ => erange_bodyB (erange_fM m fuel') bc e
      | _ => match memo_get m e with Some r => r | None => erange_bodyB (erange_fM m fuel') bc e end
      end
  end.
Definition memo_ok (bc : bctx) (m : rmemo) : Prop :=
  Forall (fun xr => forall f, (eheight (fst xr) < f)%nat -> erange_fB f bc (fst xr) = snd xr) m.
Lemma memo_get_ok : forall bc m e r, memo_ok bc m -> memo_get m e = Some r ->
  forall f, (eheight e < f)%nat -> erange_fB f bc e = r.
Proof.
  intros bc m e r Hm. induction m as [|[x rx] rest IH]; cbn [memo_get]; [discriminate|].
  inversion Hm as [|? ? Hx Hr]; subst. destruct (expr_eqb e x) eqn:E.
  - intros G f Hf. injection G as <-. apply p_expr_eqb_eq in E. subst x. apply (Hx f Hf).
  - intros G. apply IH; assumption.
Qed.
Lemma erange_fM_eq : forall bc m, memo_ok bc m -> forall f e, (eheight e < f)%nat -> erange_fM m f bc e = erange_fB f bc e.
Proof.
  intros bc m Hm. induction f as [|f IH]; intros e He; [lia|].
  rewrite erange_fB_S. cbn [erange_fM].
  assert (B : erange_bodyB (erange_fM m f) bc e = erange_bodyB (erange_fB f) bc e).
  { apply erange_bodyB_ext. intros x Hx. apply IH. lia. }
  destruct (memo_get m e) as [r|] eqn:G.
  - rewrite <- erange_fB_S. rewrite (memo_get_ok bc m e r Hm G (S f) He). destruct e; try reflexivity.
    (* [comment removed for export] *) rewrite <- (memo_get_ok bc m _ r Hm G (S f) He). rewrite erange_fB_S. exact B.
  - destruct e; exact B.
Qed.

Definition erangeB_with (r : option (Z * Z)) (bc : bctx) (e : expr) : option (Z * Z) :=
  let '(e', s) := deand e in
  if Z.eqb s 0 then r else
  match erange0B bc (unlin (lin_of e')) with
  | Some (lo', hi') =>
      if Z.leb s lo' then
        match r with
        | Some (lo, hi) => Some (Z.max lo (lo' - s), Z.min hi hi')
        | None => Some ((lo' - s)%Z, hi')
        end
      else r
  | None => r
  end.
Lemma erangeB_with_eq : forall bc e, erangeB_with (erange0B bc e) bc e = erangeB bc e.
Proof. reflexivity. Qed.

Fixpoint conc_tryM (m : rmemo) (bc : bctx) (e : expr) (cands : list expr) : option Z :=
  match cands with
  | [] => None
  | s :: rest =>
      if closedb s then conc_tryM m bc e rest else
      if negb (evalS_def s e) then conc_tryM m bc e rest else
      let '(r, m') := if Nat.ltb (eheight s) erange_fuel
                      then let r0 := erange_fM m erange_fuel bc s in (erangeB_with r0 bc s, (s, r0) :: m)
                      else (erangeB bc s, m) in
      match r with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            match evalSF s (wrap64 lo) e with
            | Some v =>
                if (if Z.ltb hi lo then true
                     else if probeSF s e v hi then probeSF s e v (lo + (hi - lo) / 2)%Z else false) then
                  if all_eval_toSF2 s e v lo (Z.to_nat (hi - lo + 1)) then Some v
                  else conc_tryM m' bc e rest
                else conc_tryM m' bc e rest
            | None => conc_tryM m' bc e rest
            end
          else conc_tryM m' bc e rest
      | None => conc_tryM m' bc e rest
      end
  end.
Lemma conc_tryM_eq : forall bc e cands m, memo_ok bc m -> conc_tryM m bc e cands = conc_tryB bc e cands.
Proof.
  intros bc e cands. induction cands as [|s rest IH]; intros m Hm; [reflexivity|].
  cbn [conc_tryM conc_tryB]. destruct (closedb s); [apply IH; exact Hm|].
  destruct (negb (evalS_def s e)); [apply IH; exact Hm|].
  destruct (Nat.ltb_spec (eheight s) erange_fuel) as [Hlt|Hge].
  - rewrite (erange_fM_eq bc m Hm erange_fuel s Hlt). fold (erange0B bc s). rewrite erangeB_with_eq.
    assert (Hm' : memo_ok bc ((s, erange0B bc s) :: m)).
    { constructor; [|exact Hm]. cbn [fst snd]. intros f Hf. unfold erange0B. apply erange_fB_fuel; assumption. }
    rewrite !(IH _ Hm'). reflexivity.
  - rewrite !(IH _ Hm). reflexivity.
Qed.
Definition concretize_nrM (bc : bctx) (e : expr) : option Z :=
  if closedb e then eval_closed e else if conc_small e then conc_tryM [] bc e (nubE (subexprs e)) else None.
Lemma concretize_nrM_eq : forall bc e, concretize_nrM bc e = concretize_nrB bc e.
Proof. intros. unfold concretize_nrM, concretize_nrB. rewrite conc_tryM_eq by constructor. reflexivity. Qed.

(* [comment removed for export] *)
Definition memo_add (bc : bctx) (e : expr) (m : rmemo) : rmemo :=
  if Nat.ltb (eheight e) erange_fuel then (e, erange_fM m erange_fuel bc e) :: m else m.
Fixpoint memo_build (bc : bctx) (e : expr) (m : rmemo) {struct e} : rmemo :=
  match e with
  | ELit _ => m
  | EVar _ | EBlob _ _ _ _ => match memo_get m e with Some _ => m | None => memo_add bc e m end
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b =>
      match memo_get m e with
      | Some _ => m
      | None => memo_add bc e (memo_build bc b (memo_build bc a m))
      end
  | EExt _ _ _ a =>
      match memo_get m e with
      | Some _ => m
      | None => memo_add bc e (memo_build bc a m)
      end
  end.
Lemma memo_add_ok : forall bc e m, memo_ok bc m -> memo_ok bc (memo_add bc e m).
Proof.
  intros bc e m Hm. unfold memo_add. destruct (Nat.ltb_spec (eheight e) erange_fuel) as [Hlt|]; [|exact Hm].
  constructor; [|exact Hm]. cbn [fst snd]. intros f Hf.
  rewrite (erange_fM_eq bc m Hm erange_fuel e Hlt). apply erange_fB_fuel; assumption.
Qed.
Lemma memo_build_ok : forall bc e m, memo_ok bc m -> memo_ok bc (memo_build bc e m).
Proof.
  intros bc e. induction e; intros m Hm; cbn [memo_build]; try exact Hm;
    try (destruct (memo_get m _); [exact Hm|]; apply memo_add_ok; auto).
Qed.

(* [comment removed for export] *)
Fixpoint esize_ge (e : expr) (n : nat) {struct e} : nat :=   (* [comment removed for export] *)
  match n with
  | O => O
  | S n' =>
      match e with
      | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => esize_ge b (esize_ge a n')
      | EExt _ _ _ a => esize_ge a n'
      | _ => n'
      end
  end.
Definition MEMO_MIN : nat := 24.
Definition fold_worth (bc : bctx) (e : expr) : bool :=
  match esize_ge e MEMO_MIN with
  | O => match find_rangeI (bc_ri bc) e with None => Nat.ltb (eheight e) erange_fuel | Some _ => false end
  | S _ => false
  end.

Definition concretize_nrM2 (m : rmemo) (bc : bctx) (e : expr) : option Z :=
  if closedb e then eval_closed e else if conc_small e then conc_tryM m bc e (nubE (subexprs e)) else None.
Lemma concretize_nrM2_eq : forall bc m e, memo_ok bc m -> concretize_nrM2 m bc e = concretize_nrB bc e.
Proof. intros. unfold concretize_nrM2, concretize_nrB. rewrite conc_tryM_eq by assumption. reflexivity. Qed.


Definition foldKB_ref (bc : bctx) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match erangeB bc e with
         | Some (lo, hi) => if Z.eqb lo hi then ELit lo
                            else match concretize_nrB bc e with Some v => ELit v | None => e end
         | None => match concretize_nrB bc e with Some v => ELit v | None => e end
         end
  end.
(* [comment removed for export] *)
Definition foldKB (bc : bctx) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ =>
    if fold_worth bc e then
      let m := memo_build bc e [] in
      match erangeB_with (erange_fM m erange_fuel bc e) bc e with
      | Some (lo, hi) => if Z.eqb lo hi then ELit lo
                         else match concretize_nrM2 m bc e with Some v => ELit v | None => e end
      | None => match concretize_nrM2 m bc e with Some v => ELit v | None => e end
      end
    else
      match erangeB bc e with
      | Some (lo, hi) => if Z.eqb lo hi then ELit lo
                         else match concretize_nrM bc e with Some v => ELit v | None => e end
      | None => match concretize_nrM bc e with Some v => ELit v | None => e end
      end
  end.
Lemma foldKB_eq : forall bc e, foldKB bc e = foldKB_ref bc e.
Proof.
  intros bc e. unfold foldKB, foldKB_ref. destruct e; try reflexivity;
  (destruct (fold_worth bc _) eqn:W;
   [ unfold fold_worth in W; destruct (esize_ge _ MEMO_MIN); [|discriminate];
     destruct (find_rangeI _ _); [discriminate|]; apply Nat.ltb_lt in W;
     cbv zeta;
     rewrite (erange_fM_eq bc _ (memo_build_ok bc _ [] (Forall_nil _)) erange_fuel _ W);
     match goal with |- context [erangeB_with (erange_fB erange_fuel bc ?x) bc ?x] =>
       change (erange_fB erange_fuel bc x) with (erange0B bc x); rewrite (erangeB_with_eq bc x) end;
     rewrite (concretize_nrM2_eq bc _ _ (memo_build_ok bc _ [] (Forall_nil _))); reflexivity
   | rewrite concretize_nrM_eq; reflexivity ]).
Qed.

(* [comment removed for export] *)
Definition lin_negwrapRB (bc : bctx) (e : expr) : bool :=
  let l := lin_of e in
  lin_testB bc (fst l) (snd l) (fun lo hi => (Z.leb (- two64) lo && Z.ltb hi 0)%bool).
Definition ltu_negwrapB (bc : bctx) (a b : expr) : option bool :=
  if (lin_negwrapRB bc a && lin_negwrapRB bc b)%bool then
    let la := lin_of a in let lb := lin_of b in
    if lin_testB bc (fst lb - 1 - fst la)%Z (lsub_e (snd lb) (snd la)) (fun lo _ => Z.leb 0 lo) then Some true
    else if lin_testB bc (fst la - fst lb)%Z (lsub_e (snd la) (snd lb)) (fun lo _ => Z.leb 0 lo) then Some false
    else None
  else None.

Definition lin_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
  let ltu := if lin_ge0B bc [(b, (-1)%Z)] [(a, 0%Z)] then Some true
             else if lin_ge0B bc [(a, 0%Z)] [(b, 0%Z)] then Some false
             else ltu_negwrapB bc a b in        (* [comment removed for export] *)
  match c with
  | BC_LTU => ltu
  | BC_GEU => option_map negb ltu
  | BC_LT | BC_GE =>
      match erangeB bc a, erangeB bc b with
      | Some (_, ah), Some (_, bh) =>
          if (Z.ltb ah (2 ^ 63) && Z.ltb bh (2 ^ 63))%bool
          then match c with BC_LT => ltu | _ => option_map negb ltu end
          else None
      | _, _ => None
      end
  | BC_EQ | BC_NE =>
      (* [comment removed for export] *)
      if (lin_ge0B bc [(b, (-1)%Z)] [(a, 0%Z)] || lin_ge0B bc [(a, (-1)%Z)] [(b, 0%Z)])%bool
      then Some (match c with BC_EQ => false | _ => true end)
      else
      (* [comment removed for export] *)
      if (if lin_ge0B bc [(a, 0%Z)] [(b, 0%Z)] then lin_ge0B bc [(b, 0%Z)] [(a, 0%Z)] else false)
      then Some (match c with BC_EQ => true | _ => false end)
      else None
  end.

Definition decide_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
  match a, b with
  | ELit x, ELit y => Some (lit_branchB c x y)
  | _, _ =>
      if expr_eqb a b then Some (cond_on_eq c)
      else match diff_branch c a b with
           | Some t => Some t
           | None =>
             match (match erangeB bc a, erangeB bc b with
                    | Some (al, ah), Some (bl, bh) => range_branch c al ah bl bh
                    | _, _ => None
                    end) with
             | Some t => Some t
             | None => lin_branchB bc c a b      (* [comment removed for export] *)
             end
           end
  end.

Definition mkSltB (bc : bctx) (c : branch_cond) (op : aluop) (a b : expr) : expr :=
  match a, b with
  | ELit _, ELit _ => mkAlu op a b
  | _, _ => match decide_branchB bc c a b with
            | Some true => ELit 1
            | Some false => ELit 0
            | None => mkAlu op a b
            end
  end.

Definition mkAluK0B (bc : bctx) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_SLTU => mkSltB bc BC_LTU ALU_SLTU a b
  | ALU_SLT => mkSltB bc BC_LT ALU_SLT a b
  | ALU_AND => match a, b with
               | ELit _, ELit _ => mkAndB bc a b
               | ELit _, _ => mkAndKB bc b a      (* [comment removed for export] *)
               | _, _ => mkAndKB bc a b
               end
  | ALU_OR => if expr_eqb a b then a else mkOrB bc a b
  | ALU_XOR => if expr_eqb a b then ELit 0 else match is_lit a, b with
               | None, ELit k => if Z.eqb (k mod two64) (two64 - 1) then mkAlu ALU_SUB (ELit (two64 - 1)) a
                                else if Z.eqb (k mod two64) 0 then a    (* [comment removed for export] *)
                                else mkAlu op a b
               | _, _ => mkAlu op a b
               end
  | ALU_SRL => match is_lit a, shamt_of b 6 with
               | None, Some s => mkSrlB bc a s
               | _, _ => mkAlu op a b
               end
  | _ => mkAlu op a b
  end.

Definition mkAluKB (bc : bctx) (op : aluop) (a b : expr) : expr :=
  foldKB bc (mkAluK0B bc op a b).

Definition mkMdKB (bc : bctx) (op : mulop) (a b : expr) : expr :=
  match is_lit a, op, b with
  | None, M_REMU, ELit m =>
      match pow2_log m with
      | Some k => mkAluKB bc ALU_AND a (ELit (2 ^ k - 1))
      | None => mkMd op a b
      end
  | None, M_DIVU, ELit m =>
      match pow2_log m with
      | Some k => mkAluKB bc ALU_SRL a (ELit k)
      | None => mkMd op a b
      end
  | _, _, _ => mkMd op a b
  end.

Definition zband32B (bc : bctx) (d : expr) : bool :=
  let l := lin_of d in
  match lin_range (erangeB bc) (fst l) (snd l) with
  | Some (lo, hi) => (Z.ltb (- 2 ^ 31) lo && Z.ltb hi (2 ^ 31))%bool
  | None => false
  end.

Definition zband32kB (bc : bctx) (d : expr) : option Z :=
  let l := lin_of d in
  match lin_range (erangeB bc) (fst l) (snd l) with
  | Some (lo, hi) =>
      let k := ((lo + 2 ^ 31) / 2 ^ 32)%Z in
      if (Z.leb (k * 2 ^ 32 - 2 ^ 31) lo && Z.ltb hi (k * 2 ^ 32 + 2 ^ 31))%bool then Some k else None
  | None => None
  end.

(* [comment removed for export] *)
Definition wband32B (bc : bctx) (d : expr) : option (expr * Z) :=
  let l := lin_of d in
  let ts := lred32 (snd l) in
  if terms_same ts (snd l) then None else
  match band_of (fst l) ts (lin_range (erangeB bc) (fst l) ts) with
  | Some x => Some x
  | None => band_of (fst l) ts (match bc_fs bc with
                              | [] => None
                              | _ => lin_rel_multiK (erangeB bc) (bc_fsK bc) (fst l) (kfy ts)   (* [comment removed for export] *)
                              end)
  end.
Definition mkAluwK0_linB (bc : bctx) (op : aluop) (a b : expr) : expr :=
  let d := mkAlu op a b in
  match is_lit d with
  | Some v => ELit (zsx32 v)
  | None => match erangeB bc d with
            | Some (lo, hi) => if sx32_stable lo hi then d else
                               match zband32kB bc d with Some k => zband_fix d k | None =>
                               match wband32B bc d with Some (r, k) => zband_fix r k | None => mkAluw op a b end end
            | None => match zband32kB bc d with Some k => zband_fix d k | None =>
                      match wband32B bc d with Some (r, k) => zband_fix r k | None => mkAluw op a b end end
            end
  end.
Definition mkAluwK0B (bc : bctx) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_ADD | ALU_SUB => mkAluwK0_linB bc op a b
  | ALU_SLL =>
      match b with
      | ELit s => if (Z.leb 0 s && Z.ltb s 32)%bool then mkAluwK0_linB bc op a b else mkAluw op a b
      | _ => mkAluw op a b
      end
  | _ => mkAluw op a b
  end.

Definition mkAluwKB (bc : bctx) (op : aluop) (a b : expr) : expr :=
  foldKB bc (mkAluwK0B bc op a b).

Definition extK0B (bc : bctx) (v : expr) : expr :=
  match v with
  | EExt sx O n e =>
      if Nat.leb n 7 then
        let w := (2 ^ (8 * Z.of_nat n))%Z in
        let viaz :=                                   (* [comment removed for export] *)
          if sx then
            match erangeB bc (EExt false 0 n e) with
            | Some (lo, hi) =>
                if (Z.leb 0 lo && Z.ltb hi (w / 2))%bool then EExt false 0 n e
                else if (Nat.leb 1 n && Z.leb (w / 2) lo && Z.ltb hi w)%bool
                     then mkAlu ALU_ADD (EExt false 0 n e) (ELit (two64 - w)%Z) else v
            | None => v
            end
          else v in
        match erangeB bc e with
        | Some (lo, hi) =>
            if Z.ltb hi (if sx then w / 2 else w) then e
            else if (sx && Nat.leb 1 n && Z.leb (w / 2) lo && Z.ltb hi w)%bool
              then mkAlu ALU_ADD e (ELit (two64 - w)%Z) else viaz
        | None => viaz
        end
      else v
  | _ => v
  end.

Definition extKB (bc : bctx) (v : expr) : expr := foldKB bc (extK0B bc v).

Definition flat_scB (bc : bctx) (a : saddr) (n : nat) : list sidecond :=
  match base_rangeB bc (a_base a) with
  | Some (lo, hi) =>
      if (Z.leb 0 (lo + a_off a) && Z.leb (hi + a_off a + zofn n) two64)%bool
      then [] else [SCFlat a (elen n)]
  | None => [SCFlat a (elen n)]
  end.

Fixpoint wr_coveredB (bc : bctx) (kn : list kentry) (a : saddr) (n : nat) : bool :=
  match kn with
  | [] => false
  | KWr (SA kb kk) len :: rest =>
      if (if (expr_eqb (a_base a) kb && Z.leb kk (a_off a))%bool
          then match xloB bc len with Some l => Z.leb (a_off a + Z.of_nat n) (kk + l) | None => false end
          else false)
      then true
      else if xinsideB bc (a_base a) (a_off a) (ELit (Z.of_nat n)) kb kk len then true
      else wr_coveredB bc rest a n
  | _ :: rest => wr_coveredB bc rest a n
  end.

Definition storeok_scB (bc : bctx) (a : saddr) (n : nat) : list sidecond :=
  if wr_coveredB bc (bc_fk bc) a n then [] else [SCStoreOk a n].

Definition conc_exprB (bc : bctx) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match concretizeB bc e with Some v => ELit v | None => e end
  end.

Definition enum_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
  let '(e, pos) := cond_probe c a b in
  match concretizeB bc e with
  | Some v => let z := Z.eqb (v mod two64) 0 in Some (if pos then negb z else z)
  | None => None
  end.

Definition to_saddrKB (bc : bctx) (e : expr) (imm : Z) : saddr :=
  match split_lit e with
  | (ELit _, _) => to_saddr e imm
  | _ => match concretizeB bc (mkAlu ALU_ADD e (ELit imm)) with
         | Some v => SA (ELit 0) v
         | None => to_saddr e imm
         end
  end.

Definition amo_alignedbB (bc : bctx) (e : expr) (wd : awidth) : bool :=
  match lin_lowbits_knB bc e (match wd with AW => 2 | AD => 3 end) with
  | Some r => Z.eqb r 0
  | None => false
  end.

Definition amo_newvalB (bc : bctx) (wd : awidth) (aop : option aluop) (old src : expr) : expr :=
  match aop with
  | None => src
  | Some o => match wd with AW => mkAluwKB bc o old src | AD => mkAluKB bc o old src end
  end.

(* [comment removed for export] *)
Lemma in_sidesB_eq : forall bc kn b1 k1 n1 b2 k2 n2,
  in_sidesB bc (disj_sidesB bc kn b1 k1 n1) b2 k2 n2 = kdisj_apartB bc kn b1 k1 n1 b2 k2 n2.
Proof.
  intros bc kn b1 k1 n1 b2 k2 n2. rewrite disj_sidesB_ref_eq. induction kn as [|K rest IH]; [reflexivity|].
  destruct K as [| | | | | | |c1 m1 c2 m2| |]; cbn [disj_sidesB_ref kdisj_apartB]; try exact IH.
  rewrite !kd_pre_eq.
  destruct (sub_itvB bc b1 k1 n1 c1 m1), (sub_itvB bc b1 k1 n1 c2 m2); cbn [in_sidesB];
    destruct (sub_itvB bc b2 k2 n2 c2 m2) eqn:E2, (sub_itvB bc b2 k2 n2 c1 m1) eqn:E1;
    rewrite ?E1, ?E2, ?IH; reflexivity.
Qed.
Definition sprepZ (bc : bctx) (b1 : expr) (k1 n1 : Z) : option (Z * Z) * list (saddr * expr) :=
  (base_rangeB bc b1, disj_sidesB bc (bc_fk bc) b1 k1 n1).
Definition ranges_apartBp (bc : bctx) (sp : option (Z * Z) * list (saddr * expr)) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match fst sp, base_rangeB bc b2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
      | _, _ => false
      end) then true
  else if in_sidesB bc (snd sp) b2 k2 n2 then true
  else lin_apartB bc b1 k1 n1 b2 k2 n2.
Lemma ranges_apartBp_eq : forall bc b1 k1 n1 b2 k2 n2,
  ranges_apartBp bc (sprepZ bc b1 k1 n1) b1 k1 n1 b2 k2 n2 = ranges_apartB bc b1 k1 n1 b2 k2 n2.
Proof. intros. unfold ranges_apartBp, sprepZ, ranges_apartB. cbn [fst snd]. rewrite in_sidesB_eq. reflexivity. Qed.
Fixpoint log_lookupBp (bc : bctx) (osp : option (option (Z * Z) * list (saddr * expr))) (log : list sentry) (rb : expr) (rk : Z) (n : nat)
         (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk (zofn n) kb kk (zofn w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupBp bc osp rest rb rk n sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          let sp := match osp with Some sp => sp | None => sprepZ bc rb rk (zofn n) end in
          if ranges_apartBp bc sp rb rk (zofn n) kb kk (zofn w)
          then log_lookupBp bc (Some sp) rest rb rk n sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupBp bc (Some sp) rest rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elenf n) (SA kb kk) (elenf w) :: acc)
          end
      end
  end.
Definition log_lookupBn (bc : bctx) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  log_lookupBp bc None log rb rk n sx hints acc.

Fixpoint log_lookupB (bc : bctx) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk (zofn n) kb kk (zofn w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupB bc rest rb rk n sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          if ranges_apartB bc rb rk (zofn n) kb kk (zofn w)
          then log_lookupB bc rest rb rk n sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupB bc rest rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elenf n) (SA kb kk) (elenf w) :: acc)
          end
      end
  end.

Fixpoint know_lookupA0B (bc : bctx) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  let know_lookup := know_lookupA0B bc in
  match kn with
  | [] => LMiss acc hints
  | K :: rest =>
      match K with
      | KWord (SA kb kk) w v =>
          match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
          | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
          | _ => know_lookup segs rest rb rk n sx hints acc
          end
      | KZero (SA kb kk) len =>
          match len with
          | ELit l0 =>
              match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2^64)%Z with
              | RInside _ => LHit (ELit 0) acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  (* [comment removed for export] *)
                  if xinsideB bc rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
                  match hints with
                  | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinsideB bc rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
              match hints with
              | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | [] => know_lookup segs rest rb rk n sx [] acc
              end
          end
      | KFill (SA kb kk) len c =>
          (* [comment removed for export] *)
          let hit := fill_lit sx n c in
          match len with
          | ELit l0 =>
              match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2^64)%Z with
              | RInside _ => LHit hit acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  if xinsideB bc rb rk (elen n) kb kk len then LHit hit acc hints else
                  match hints with
                  | true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinsideB bc rb rk (elen n) kb kk len then LHit hit acc hints else
              match hints with
              | true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | [] => know_lookup segs rest rb rk n sx [] acc
              end
          end
      | KUnk _ _ => know_lookup segs rest rb rk n sx hints acc   (* [comment removed for export] *)
      | KBlob (SA kb kk) len k =>
          if expr_eqb rb kb then
            (* [comment removed for export] *)
            if Z.leb kk rk then
              match len with
              | ELit l0 =>
                  if Z.leb (rk + Z.of_nat n) (kk + (l0 mod 2^64)%Z)
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else if Z.leb (kk + (l0 mod 2^64)%Z) rk then know_lookup segs rest rb rk n sx hints acc
                  else LStuck
              | _ =>
                  (* [comment removed for export] *)
                  if match erangeB bc len with   (* [comment removed for export] *)
                     | Some (lo, _) => Z.leb (rk + Z.of_nat n) (kk + lo)
                     | None => false
                     end
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else
                  match hints with
                  | true :: hs => LHit (EBlob sx k (rk - kk) n)
                                    (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
            else know_lookup segs rest rb rk n sx hints acc
          else know_lookup segs rest rb rk n sx hints acc
      | KImg lo hi =>
          match rb with
          | ELit 0 =>
              if (Z.leb lo rk && Z.leb (rk + Z.of_nat n) hi)%bool then
                match img_bytes segs rk n with
                | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                | None => LStuck
                end
              else know_lookup segs rest rb rk n sx hints acc
          | _ => know_lookup segs rest rb rk n sx hints acc
          end
      | KAlign _ _ => know_lookup segs rest rb rk n sx hints acc
      | KRange _ _ _ => know_lookup segs rest rb rk n sx hints acc
      | KWr _ _ => know_lookup segs rest rb rk n sx hints acc
      | KDisj _ _ _ _ => know_lookup segs rest rb rk n sx hints acc
      end
  end.
(* [comment removed for export] *)
Fixpoint know_lookupA0F (bc : bctx) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  let know_lookup := know_lookupA0F bc in
  match kn with
  | [] => LMiss acc hints
  | K :: rest =>
      match K with
      | KWord (SA kb kk) w v =>
          match rel_lit rb rk (zofn n) kb kk (zofn w) with
          | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
          | _ => know_lookup segs rest rb rk n sx hints acc
          end
      | KZero (SA kb kk) len =>
          match len with
          | ELit l0 =>
              match rel_lit rb rk (zofn n) kb kk (zm64 l0) with
              | RInside _ => LHit (ELit 0) acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  (* [comment removed for export] *)
                  if xinsideB bc rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
                  match hints with
                  | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinsideB bc rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
              match hints with
              | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | [] => know_lookup segs rest rb rk n sx [] acc
              end
          end
      | KFill (SA kb kk) len c =>
          (* [comment removed for export] *)
          let hit := fill_lit sx n c in
          match len with
          | ELit l0 =>
              match rel_lit rb rk (zofn n) kb kk (zm64 l0) with
              | RInside _ => LHit hit acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  if xinsideB bc rb rk (elen n) kb kk len then LHit hit acc hints else
                  match hints with
                  | true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinsideB bc rb rk (elen n) kb kk len then LHit hit acc hints else
              match hints with
              | true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | [] => know_lookup segs rest rb rk n sx [] acc
              end
          end
      | KUnk _ _ => know_lookup segs rest rb rk n sx hints acc   (* [comment removed for export] *)
      | KBlob (SA kb kk) len k =>
          if expr_eqb rb kb then
            (* [comment removed for export] *)
            if Z.leb kk rk then
              match len with
              | ELit l0 =>
                  if Z.leb (rk + zofn n) (kk + (zm64 l0))
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else if Z.leb (kk + (zm64 l0)) rk then know_lookup segs rest rb rk n sx hints acc
                  else LStuck
              | _ =>
                  (* [comment removed for export] *)
                  if match erangeB bc len with   (* [comment removed for export] *)
                     | Some (lo, _) => Z.leb (rk + zofn n) (kk + lo)
                     | None => false
                     end
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else
                  match hints with
                  | true :: hs => LHit (EBlob sx k (rk - kk) n)
                                    (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
            else know_lookup segs rest rb rk n sx hints acc
          else know_lookup segs rest rb rk n sx hints acc
      | KImg lo hi =>
          match rb with
          | ELit 0 =>
              if (Z.leb lo rk && Z.leb (rk + zofn n) hi)%bool then
                match img_bytes segs rk n with
                | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                | None => LStuck
                end
              else know_lookup segs rest rb rk n sx hints acc
          | _ => know_lookup segs rest rb rk n sx hints acc
          end
      | KAlign _ _ => know_lookup segs rest rb rk n sx hints acc
      | KRange _ _ _ => know_lookup segs rest rb rk n sx hints acc
      | KWr _ _ => know_lookup segs rest rb rk n sx hints acc
      | KDisj _ _ _ _ => know_lookup segs rest rb rk n sx hints acc
      end
  end.
Lemma know_lookupA0F_eq : forall bc segs kn rb rk n sx hints acc,
  know_lookupA0F bc segs kn rb rk n sx hints acc = know_lookupA0B bc segs kn rb rk n sx hints acc.
Proof.
  intros bc segs kn. induction kn as [|K rest IH]; intros rb rk n sx hints acc; [reflexivity|].
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    destruct hints as [|[|] hs]; cbn [know_lookupA0F know_lookupA0B]; rewrite ?zofn_fe, ?zm64_fe; rewrite ?IH; reflexivity.
Qed.

Definition know_lookupAB (bc : bctx) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match know_lookupA0B bc segs kn rb rk n sx hints acc with
  | LMiss acc' hints' =>
      match know_bytes_lit segs kn rb rk n with
      | Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
      | None => LMiss acc' hints'
      end
  | r => r
  end.

Fixpoint split_read_loB (bc : bctx) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (w1 : nat) : option (nat * expr) :=
  match w1 with
  | O => None
  | S w1' =>
      match know_lookupA0B bc segs kn rb rk w1 false [] [] with
      | LHit v [] _ => Some (w1, v)
      | _ => split_read_loB bc segs kn rb rk w1'
      end
  end.

Definition sym_readB (segs : list Segment) (ss : sym_state) (bc : bctx) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match log_lookupBn bc (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
  | LStuck => None
  | LHit v scs hints =>
      Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookupAB bc segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extKB bc v, flat_scB bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
      | LMiss scs' hints' =>
          (* [comment removed for export] *)
          let i := s_next ss in
          match sc_reads scr with
          | e :: reads' => Some (e, flat_scB bc a n ++ SCReadBase a n sx' e :: scs', SCR (sc_dirs scr) reads' hints', S i)
          | [] =>
              match (if sx' then None else split_read_loB bc segs (s_know ss) (a_base a) (a_off a) (Nat.pred n)) with
              | Some (w1, v1) =>
                  let a2 := SA (a_base a) (a_off a + Z.of_nat w1)%Z in
                  let n2 := (n - w1)%nat in
                  let rv2 := xwrap n2 false (EVar i) in
                  Some (split_value (extKB bc v1) w1 rv2, flat_scB bc a n ++ SCReadBase a2 n2 false rv2 :: scs',
                        SCR (sc_dirs scr) [] hints', S i)
              | None =>
                  let rv := xwrap n sx' (EVar i) in
                  Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) [] hints', S i)
              end
          end
      end
  end.

Definition sym_stepB (bc : bctx) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluwKB bc ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluwKB bc op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (sset ss rd (mkMdKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12)))) (p + 4)) [] scr
  | Auipc rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
  | Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
  | Jalr rd rs1 imm =>
      match conc_exprB bc (g rs1) with
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod 2^64)) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
      let a := g rs1 in let b := g rs2 in
      match match decide_branchB bc c a b with
            | Some t => Some t
            | None => match decide_branchB bc c (conc_exprB bc a) (conc_exprB bc b) with
                      | Some t => Some t
                      | None => enum_branchB bc c a b
                      end
            end with
      | Some t => SOk (sjump ss (if t then tk else p + 4)) [] scr
      | None =>
          match sc_dirs scr with
          | [] => SStop
          | t :: dirs' =>
              SOk (sjump ss (if t then tk else p + 4)) [SCBr t c a b]
                  (SCR dirs' (sc_reads scr) (sc_hints scr))
          end
      end
  | Fence _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | FenceI _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in
      (* [comment removed for export] *)
      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrKB bc (g rs) (bv_signed imm) in
      match sym_readB segs ss bc scr a n sx' with
      | None => SStop
      | Some (v, scs, scr', nx') =>
          SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                   (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrKB bc (g rs1) (bv_signed imm) in
      match resv_inval (s_resv ss) a with
      | None => SStop
      | Some r' =>
          SOk (SSR (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) r')
              (flat_scB bc a n ++ storeok_scB bc a n) scr
      end
  (* [comment removed for export] *)
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match sym_readB segs ss bc scr a n (amo_sx wd) with
        | None => SStop
        | Some (v, scs, scr', nx') =>
            SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                     (s_log ss) (s_know ss) nx' (Some a)) scs scr'
        end
      else SStop
  | Sc wd _ _ rd rs1 rs2 =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs1 in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match s_resv ss with
        | Some r =>
            if saddr_eqb r a then
              SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (ELit 0))
                       (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) None)
                  (flat_scB bc a n ++ storeok_scB bc a n) scr
            else SStop   (* [comment removed for export] *)
        | None => SStop
        end
      else SStop
  | Amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | None => SStop
      | Some aop =>
          let n := msize_bytes (amo_sz wd) in
          let e := g rs1 in
          if amo_alignedbB bc e wd then
            let a := to_saddrKB bc e 0 in
            match resv_inval (s_resv ss) a with
            | None => SStop
            | Some r' =>
                match sym_readB segs ss bc scr a n (amo_sx wd) with
                | None => SStop
                | Some (vold, scs, scr', nx') =>
                    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
                             (SE a n (amo_newvalB bc wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
                        (scs ++ storeok_scB bc a n) scr'
                end
            end
          else SStop
      end
  (* [comment removed for export] *)
  | FLoad fmt rd rs imm =>
      let n := ffmt_bytes fmt in
      let a := to_saddrKB bc (g rs) (bv_signed imm) in
      match sym_readB segs ss bc scr a n false with
      | None => SStop
      | Some (_, scs, scr', nx') =>
          SOk (SSR (p + 4) (s_regs ss) (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | Fmv FMV_F_X _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Fsgnj _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Fminmax _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Fari _ _ _ _ _ rm => if rm_okb rm then SOk (sjump ss (p + 4)) [] scr else SStop
  | Fsqrt _ _ _ rm => if rm_okb rm then SOk (sjump ss (p + 4)) [] scr else SStop
  | Fma _ _ _ _ _ _ rm => if rm_okb rm then SOk (sjump ss (p + 4)) [] scr else SStop
  | Fcvt dst src rd rs1 rm =>
      if (fcvt_is_f dst && rm_okb rm)%bool then SOk (sjump ss (p + 4)) [] scr else SStop
  | _ => SStop
  end.

Definition know_lookupB (segs : list Segment) (bc : bctx) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  know_lookupAB bc segs (bc_fk bc) rb rk n sx hints acc.


Local Open Scope Z_scope.
(* [comment removed for export] *)
Definition gran (a : Z) : Z := Z.shiftr a 12.
Definition is_lit0 (e : expr) : bool := match e with ELit 0 => true | _ => false end.
(* [comment removed for export] *)
Definition lit0_extent (K : kentry) : option (Z * Z) :=
  match K with
  | KWord (SA (ELit 0) kk) w _ => Some (kk, kk + Z.of_nat w)
  | KZero (SA (ELit 0) kk) (ELit l0) => Some (kk, kk + zmod64 l0)
  | KFill (SA (ELit 0) kk) (ELit l0) _ => Some (kk, kk + zmod64 l0)
  | KBlob (SA (ELit 0) kk) (ELit l0) _ => Some (kk, kk + zmod64 l0)
  | KImg lo hi => Some (lo, hi)
  | _ => None
  end.
(* [comment removed for export] *)
Definition ext_fits (s e : Z) : bool := if Z.ltb s e then Z.leb (gran (e - 1) - gran s) 1 else false.
Definition ext_has (s e g : Z) : bool := if Z.eqb g (gran s) then true else Z.eqb g (gran (e - 1)).
(* [comment removed for export] *)
Definition kx_wide0 (K : kentry) : bool :=
  match lit0_extent K with
  | Some (s, e) => negb (ext_fits s e)
  | None =>
      match K with
      | KZero (SA kb _) _ | KFill (SA kb _) _ _ => true      (* [comment removed for export] *)
      | KBlob (SA kb _) _ _ => is_lit0 kb                    (* [comment removed for export] *)
      | _ => false
      end
  end.
(* [comment removed for export] *)
Definition kx_cand0 (g : Z) (K : kentry) : bool :=
  match lit0_extent K with
  | Some (s, e) => if ext_fits s e then ext_has s e g else true
  | None => kx_wide0 K
  end.
(* [comment removed for export] *)
Definition kx_candf (K : kentry) : bool :=
  match K with
  | KWord (SA kb _) _ _ | KBlob (SA kb _) _ _ => negb (is_lit0 kb)
  | KZero _ _ | KFill _ _ _ => true
  | _ => false
  end.
(* [comment removed for export] *)
Definition kx_gkey (g : Z) : positive := match g with Z0 => xH | Zpos p => xO p | Zneg p => xI p end.
Record kix : Type := KX {
  kx_kn : list kentry;                              (* [comment removed for export] *)
  kx_w0 : list (positive * kentry);                 (* [comment removed for export] *)
  kx_gran : ptree (list (positive * kentry));       (* [comment removed for export] *)
  kx_wf : list kentry                               (* [comment removed for export] *)
}.
Definition kx_bucket (t : ptree (list (positive * kentry))) (g : Z) : list (positive * kentry) :=
  match pt_get t (kx_gkey g) with Some b => b | None => [] end.
Definition kx_add (g : Z) (x : positive * kentry) (t : ptree (list (positive * kentry))) : ptree (list (positive * kentry)) :=
  pt_set (kx_gkey g) (x :: kx_bucket t g) t.
Fixpoint kx_build (kn : list kentry) (i : positive) : list (positive * kentry) * ptree (list (positive * kentry)) * list kentry :=
  match kn with
  | [] => ([], PTLeaf, [])
  | K :: rest =>
      let '(w0, gr, wf) := kx_build rest (Pos.succ i) in
      let wf' := if kx_candf K then K :: wf else wf in
      match lit0_extent K with
      | Some (s, e) =>
          if ext_fits s e then
            let g1 := gran s in let g2 := gran (e - 1) in
            let gr1 := kx_add g1 (i, K) gr in
            (w0, (if Z.eqb g1 g2 then gr1 else kx_add g2 (i, K) gr1), wf')
          else ((i, K) :: w0, gr, wf')
      | None => if kx_wide0 K then ((i, K) :: w0, gr, wf') else (w0, gr, wf')
      end
  end.
Definition mk_kix (kn : list kentry) : kix :=
  let r := kx_build kn xH in KX kn (fst (fst r)) (snd (fst r)) (snd r).
(* [comment removed for export] *)
Fixpoint kx_merge (l1 : list (positive * kentry)) : list (positive * kentry) -> list kentry :=
  match l1 with
  | [] => fun l2 => List.map snd l2
  | (p1, K1) :: r1 =>
      fix go (l2 : list (positive * kentry)) : list kentry :=
        match l2 with
        | [] => K1 :: List.map snd r1
        | (p2, K2) :: r2 => if Pos.ltb p1 p2 then K1 :: kx_merge r1 l2 else K2 :: go r2
        end
  end.
Definition kx_select (kx : kix) (rb : expr) (rk : Z) : list kentry :=
  if is_lit0 rb then kx_merge (kx_bucket (kx_gran kx) (gran rk)) (kx_w0 kx)
  else kx_wf kx.

Definition know_lookupA0I (bc : bctx) (kx : kix) (segs : list Segment) (rb : expr) (rk : Z)
           (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match hints, n with
  | [], S _ => know_lookupA0F bc segs (kx_select kx rb rk) rb rk n sx [] acc
  | _, _ => know_lookupA0F bc segs (kx_kn kx) rb rk n sx hints acc
  end.

(* [comment removed for export] *)
Lemma gran_div : forall a, gran a = a / 4096.
Proof. intros a. unfold gran. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma gran_mono : forall a b, a <= b -> gran a <= gran b.
Proof. intros a b H. rewrite !gran_div. apply Z.div_le_mono; lia. Qed.
Lemma gran_between : forall s e x,
  s <= x -> x < e -> ext_fits s e = true -> ext_has s e (gran x) = true.
Proof.
  intros s e x Hs He Hf. unfold ext_fits, ext_has in *.
  destruct (Z.ltb s e); [|discriminate]. apply Z.leb_le in Hf.
  pose proof (gran_mono s x Hs) as A. pose proof (gran_mono x (e - 1) ltac:(lia)) as B.
  destruct (Z.eqb_spec (gran x) (gran s)); [reflexivity|].
  destruct (Z.eqb_spec (gran x) (gran (e - 1))); [reflexivity|]. exfalso. lia.
Qed.
Lemma kx_aluop_eqb_refl : forall a, aluop_eqb a a = true. Proof. intros []; reflexivity. Qed.
Lemma kx_mulop_eqb_refl : forall a, mulop_eqb a a = true. Proof. intros []; reflexivity. Qed.
Lemma kx_expr_eqb_refl : forall x, expr_eqb x x = true.
Proof.
  induction x; cbn -[Z.eqb Nat.eqb]; rewrite ?kx_aluop_eqb_refl, ?kx_mulop_eqb_refl, ?IHx, ?IHx1, ?IHx2, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
Qed.

Lemma rel_lit_same : forall rb rk rn kk kl,
  rel_lit rb rk rn rb kk kl =
    if (Z.leb kk rk && Z.leb (rk + rn) (kk + kl))%bool then RInside (rk - kk)
    else if (Z.leb (rk + rn) kk || Z.leb (kk + kl) rk)%bool then RDisjoint else RPartial.
Proof. intros. rewrite rel_lit_eq. unfold rel_lit_ref. rewrite kx_expr_eqb_refl. reflexivity. Qed.

Lemma rel_lit_other : forall rb rk rn kb kk kl,
  expr_eqb rb kb = false -> rel_lit rb rk rn kb kk kl = RUnknown.
Proof. intros rb rk rn kb kk kl H. rewrite rel_lit_eq. unfold rel_lit_ref. rewrite H. reflexivity. Qed.

Lemma is_lit0_eqb : forall rb kb, is_lit0 kb = true -> expr_eqb rb kb = is_lit0 rb.
Proof.
  intros rb kb H. destruct kb as [z| | | | | | |]; try discriminate. cbn in H.
  destruct z; try discriminate.
  destruct rb as [z'| | | | | | |]; cbn; try reflexivity; destruct z'; reflexivity.
Qed.
Lemma expr_eqb_lit0_l : forall kb, expr_eqb (ELit 0) kb = is_lit0 kb.
Proof. intros kb. destruct kb as [z| | | | | | |]; cbn; try reflexivity; destruct z; reflexivity. Qed.
Lemma is_lit0_true : forall e, is_lit0 e = true -> e = ELit 0.
Proof. intros e H. destruct e as [z| | | | | | |]; try discriminate. cbn in H. destruct z; try discriminate. reflexivity. Qed.

(* [comment removed for export] *)
Lemma know_lookupA0B_skip0 : forall bc segs K rest rk n sx acc,
  kx_cand0 (gran rk) K = false ->
  know_lookupA0B bc segs (K :: rest) (ELit 0) rk (S n) sx [] acc = know_lookupA0B bc segs rest (ELit 0) rk (S n) sx [] acc.
Proof.
  intros bc segs K rest rk n sx acc HC.
  cbn [know_lookupA0B].
  unfold kx_cand0, kx_wide0 in HC.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
    cbn [lit0_extent] in HC; rewrite ?zmod64_eq in HC; try reflexivity.
  - (* [comment removed for export] *)
    destruct (is_lit0 kb) eqn:L.
    + apply is_lit0_true in L. subst kb. cbn [lit0_extent] in HC.
      rewrite rel_lit_same.
      destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat (S n)) (kk + Z.of_nat w))%bool eqn:E.
      * exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
        destruct (ext_fits kk (kk + Z.of_nat w)) eqn:F; [|discriminate].
        rewrite (gran_between kk (kk + Z.of_nat w) rk) in HC; [discriminate|lia|lia|exact F].
      * destruct (Z.leb (rk + Z.of_nat (S n)) kk || Z.leb (kk + Z.of_nat w) rk)%bool; reflexivity.
    + destruct kb as [z| | | | | | |]; try (rewrite rel_lit_other by reflexivity; reflexivity).
      cbn in L. destruct z; try discriminate; rewrite rel_lit_other by reflexivity; reflexivity.
  - (* [comment removed for export] *)
    destruct (is_lit0 kb) eqn:L.
    + apply is_lit0_true in L. subst kb. destruct len as [l0| | | | | | |]; cbn [lit0_extent] in HC; rewrite ?zmod64_eq in HC; try discriminate.
      rewrite rel_lit_same.
      destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat (S n)) (kk + l0 mod 2 ^ 64))%bool eqn:E.
      * exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
        destruct (ext_fits kk (kk + l0 mod 2 ^ 64)) eqn:F; [|discriminate].
        rewrite (gran_between kk (kk + l0 mod 2 ^ 64) rk) in HC; [discriminate|lia|lia|exact F].
      * destruct (Z.leb (rk + Z.of_nat (S n)) kk || Z.leb (kk + l0 mod 2 ^ 64) rk)%bool; reflexivity.
    + destruct kb as [z| | | | | | |]; cbn [lit0_extent] in HC; try (destruct len; discriminate).
      cbn in L. destruct z; try discriminate; destruct len; discriminate.
  - (* [comment removed for export] *)
    destruct (is_lit0 kb) eqn:L.
    + apply is_lit0_true in L. subst kb. destruct len as [l0| | | | | | |]; cbn [lit0_extent is_lit0] in HC; rewrite ?zmod64_eq in HC; try discriminate.
      rewrite kx_expr_eqb_refl.
      destruct (ext_fits kk (kk + l0 mod 2 ^ 64)) eqn:F; [|discriminate].
      destruct (Z.leb_spec kk rk) as [H1|H1]; [|reflexivity].
      destruct (Z.leb_spec (rk + Z.of_nat (S n)) (kk + (l0 mod 2 ^ 64))) as [H2|H2].
      * exfalso. rewrite (gran_between kk (kk + l0 mod 2 ^ 64) rk) in HC; [discriminate|lia|lia|exact F].
      * destruct (Z.leb_spec (kk + (l0 mod 2 ^ 64)) rk) as [H3|H3]; [reflexivity|].
        exfalso. rewrite (gran_between kk (kk + l0 mod 2 ^ 64) rk) in HC; [discriminate|lia|lia|exact F].
    + rewrite expr_eqb_lit0_l, L. reflexivity.
  - (* [comment removed for export] *)
    destruct (ext_fits lo hi) eqn:F; [|discriminate].
    destruct (Z.leb lo rk && Z.leb (rk + Z.of_nat (S n)) hi)%bool eqn:E; [|reflexivity].
    exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    rewrite (gran_between lo hi rk) in HC; [discriminate|lia|lia|exact F].
  - (* [comment removed for export] *)
    destruct (is_lit0 kb) eqn:L.
    + apply is_lit0_true in L. subst kb. destruct len as [l0| | | | | | |]; cbn [lit0_extent] in HC; rewrite ?zmod64_eq in HC; try discriminate.
      cbv zeta. rewrite rel_lit_same.
      destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat (S n)) (kk + l0 mod 2 ^ 64))%bool eqn:E.
      * exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
        destruct (ext_fits kk (kk + l0 mod 2 ^ 64)) eqn:F; [|discriminate].
        rewrite (gran_between kk (kk + l0 mod 2 ^ 64) rk) in HC; [discriminate|lia|lia|exact F].
      * destruct (Z.leb (rk + Z.of_nat (S n)) kk || Z.leb (kk + l0 mod 2 ^ 64) rk)%bool; reflexivity.
    + destruct kb as [z| | | | | | |]; cbn [lit0_extent] in HC; try (destruct len; discriminate).
      cbn in L. destruct z; try discriminate; destruct len; discriminate.
Qed.

(* [comment removed for export] *)
Lemma know_lookupA0B_skipf : forall bc segs K rest rb rk n sx acc,
  is_lit0 rb = false -> kx_candf K = false ->
  know_lookupA0B bc segs (K :: rest) rb rk n sx [] acc = know_lookupA0B bc segs rest rb rk n sx [] acc.
Proof.
  intros bc segs K rest rb rk n sx acc Hrb HC.
  cbn [know_lookupA0B]. unfold kx_candf in HC.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
    try reflexivity; try discriminate.
  - (* [comment removed for export] *) destruct (is_lit0 kb) eqn:L; [|discriminate].
    rewrite rel_lit_other; [reflexivity|]. rewrite (is_lit0_eqb rb kb L). exact Hrb.
  - (* [comment removed for export] *) destruct (is_lit0 kb) eqn:L; [|discriminate].
    rewrite (is_lit0_eqb rb kb L), Hrb. reflexivity.
  - (* [comment removed for export] *) destruct rb as [z| | | | | | |]; try reflexivity. cbn in Hrb. destruct z; try reflexivity. discriminate.
Qed.

(* [comment removed for export] *)
Lemma know_lookupA0B_filter0 : forall bc segs l rk n sx acc,
  know_lookupA0B bc segs (List.filter (kx_cand0 (gran rk)) l) (ELit 0) rk (S n) sx [] acc
  = know_lookupA0B bc segs l (ELit 0) rk (S n) sx [] acc.
Proof.
  intros bc segs l rk n sx. induction l as [|K rest IH]; intros acc; [reflexivity|].
  cbn [List.filter]. destruct (kx_cand0 (gran rk) K) eqn:HC.
  - (* [comment removed for export] *)
    cbn [know_lookupA0B]. rewrite !IH.
    destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity.
  - rewrite know_lookupA0B_skip0 by exact HC. apply IH.
Qed.
Lemma know_lookupA0B_filterf : forall bc segs l rb rk n sx acc,
  is_lit0 rb = false ->
  know_lookupA0B bc segs (List.filter kx_candf l) rb rk n sx [] acc = know_lookupA0B bc segs l rb rk n sx [] acc.
Proof.
  intros bc segs l rb rk n sx acc Hrb. revert acc. induction l as [|K rest IH]; intros acc; [reflexivity|].
  cbn [List.filter]. destruct (kx_candf K) eqn:HC.
  - cbn [know_lookupA0B]. rewrite !IH.
    destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity.
  - rewrite know_lookupA0B_skipf by assumption. apply IH.
Qed.


(* [comment removed for export] *)
Fixpoint tagged (kn : list kentry) (i : positive) : list (positive * kentry) :=
  match kn with [] => [] | K :: rest => (i, K) :: tagged rest (Pos.succ i) end.
Definition all_gt (i : positive) (l : list (positive * kentry)) : Prop := Forall (fun t => (i < fst t)%positive) l.

Lemma filter_tagged_gt : forall P kn i j, (j < i)%positive -> all_gt j (List.filter P (tagged kn i)).
Proof.
  intros P kn. induction kn as [|K rest IH]; intros i j Hj; cbn [tagged List.filter]; [constructor|].
  destruct (P (i, K)).
  - constructor; [cbn; lia|]. apply IH. lia.
  - apply IH. lia.
Qed.

Lemma kx_merge_cons_l : forall p K r1 l2,
  all_gt p l2 -> kx_merge ((p, K) :: r1) l2 = K :: kx_merge r1 l2.
Proof.
  intros p K r1 l2 H. destruct l2 as [|[p2 K2] r2]; cbn [kx_merge].
  - destruct r1 as [|[? ?] ?]; reflexivity.
  - apply Forall_inv in H. cbn in H. destruct (Pos.ltb_spec p p2); [reflexivity|lia].
Qed.
Lemma kx_merge_cons_r : forall p K l1 r2,
  all_gt p l1 -> kx_merge l1 ((p, K) :: r2) = K :: kx_merge l1 r2.
Proof.
  intros p K l1 r2 H. destruct l1 as [|[p1 K1] r1]; cbn [kx_merge List.map snd]; [reflexivity|].
  apply Forall_inv in H. cbn in H. destruct (Pos.ltb_spec p1 p); [lia|reflexivity].
Qed.

(* [comment removed for export] *)
Lemma kx_merge_filters : forall (P Q : kentry -> bool) kn i,
  (forall K, P K = true -> Q K = false) ->
  kx_merge (List.filter (fun t => P (snd t)) (tagged kn i)) (List.filter (fun t => Q (snd t)) (tagged kn i))
  = List.filter (fun K => P K || Q K) kn.
Proof.
  intros P Q kn. induction kn as [|K rest IH]; intros i HPQ; [reflexivity|].
  cbn [tagged List.filter snd].
  destruct (P K) eqn:HP.
  - rewrite (HPQ K HP). cbn [orb]. rewrite kx_merge_cons_l; [rewrite IH; [reflexivity|exact HPQ]|].
    apply filter_tagged_gt. lia.
  - destruct (Q K) eqn:HQ; cbn [orb].
    + rewrite kx_merge_cons_r; [rewrite IH; [reflexivity|exact HPQ]|]. apply filter_tagged_gt. lia.
    + apply IH. exact HPQ.
Qed.

(* [comment removed for export] *)
Definition narrow_in (g : Z) (K : kentry) : bool :=
  match lit0_extent K with
  | Some (s, e) => if ext_fits s e then ext_has s e g else false
  | None => false
  end.
Lemma kx_cand0_split : forall g K, kx_cand0 g K = (narrow_in g K || kx_wide0 K).
Proof.
  intros g K. unfold kx_cand0, narrow_in, kx_wide0.
  destruct (lit0_extent K) as [[s e]|]; [|reflexivity].
  destruct (ext_fits s e); cbn [negb orb]; repeat match goal with |- context [if ?x then _ else _] => destruct x end; reflexivity.   (* [comment removed for export] *)
Qed.
Lemma narrow_not_wide : forall g K, narrow_in g K = true -> kx_wide0 K = false.
Proof.
  intros g K. unfold narrow_in, kx_wide0. destruct (lit0_extent K) as [[s e]|]; [|discriminate].
  destruct (ext_fits s e); [reflexivity|discriminate].
Qed.

Lemma kx_gkey_inj : forall a b, kx_gkey a = kx_gkey b -> a = b.
Proof. intros [|a|a] [|b|b] H; cbn in H; congruence. Qed.
Lemma kx_bucket_add_same : forall g x t, kx_bucket (kx_add g x t) g = x :: kx_bucket t g.
Proof. intros. unfold kx_add, kx_bucket at 1. rewrite pt_gss. reflexivity. Qed.
Lemma kx_bucket_add_other : forall g g' x t, g <> g' -> kx_bucket (kx_add g' x t) g = kx_bucket t g.
Proof.
  intros g g' x t H. unfold kx_add. unfold kx_bucket at 1. rewrite pt_gso; [reflexivity|].
  intros E. apply H. apply kx_gkey_inj. exact E.
Qed.
Lemma kx_bucket_leaf : forall g, kx_bucket PTLeaf g = [].
Proof. intros. unfold kx_bucket. rewrite pt_get_leaf. reflexivity. Qed.

Lemma kx_build_spec : forall kn i w0 gr wf,
  kx_build kn i = (w0, gr, wf) ->
  w0 = List.filter (fun t => kx_wide0 (snd t)) (tagged kn i)
  /\ (forall g, kx_bucket gr g = List.filter (fun t => narrow_in g (snd t)) (tagged kn i))
  /\ wf = List.filter kx_candf kn.
Proof.
  induction kn as [|K rest IH]; intros i w0 gr wf H.
  - cbn in H. injection H as <- <- <-. split; [reflexivity|]. split; [intros g; rewrite kx_bucket_leaf; reflexivity | reflexivity].
  - cbn [kx_build] in H. destruct (kx_build rest (Pos.succ i)) as [[w0' gr'] wf'] eqn:Hb.
    destruct (IH (Pos.succ i) w0' gr' wf' Hb) as (A & B & C). clear IH.
    cbn [tagged List.filter snd].
    assert (NW : forall g, narrow_in g K = match lit0_extent K with Some (s, e) => if ext_fits s e then ext_has s e g else false | None => false end) by reflexivity.
    assert (WD : kx_wide0 K = match lit0_extent K with
                              | Some (s, e) => negb (ext_fits s e)
                              | None => match K with
                                        | KZero (SA kb _) _ | KFill (SA kb _) _ _ => true
                                        | KBlob (SA kb _) _ _ => is_lit0 kb
                                        | _ => false
                                        end
                              end) by reflexivity.
    destruct (lit0_extent K) as [[s e]|] eqn:HE.
    + destruct (ext_fits s e) eqn:HF.
      * (* [comment removed for export] *)
        match type of H with (_, ?G, _) = _ => set (gr1 := G) in H end.
        injection H as <- <- <-. rewrite WD. cbn [negb]. split; [exact A|]. split; [|rewrite C; reflexivity].
        intros g. rewrite NW.
        assert (STEP : kx_bucket gr1 g = if ext_has s e g then (i, K) :: kx_bucket gr' g else kx_bucket gr' g).
        { subst gr1. unfold ext_has. destruct (Z.eqb_spec (gran s) (gran (e - 1))) as [EQ|NE].
          - destruct (Z.eqb_spec g (gran s)) as [->|NE1].
            + rewrite kx_bucket_add_same. reflexivity.
            + rewrite kx_bucket_add_other by exact NE1. destruct (Z.eqb_spec g (gran (e - 1))); [congruence|reflexivity].
          - destruct (Z.eqb_spec g (gran s)) as [->|NE1].
            + rewrite kx_bucket_add_other by exact NE. rewrite kx_bucket_add_same. reflexivity.
            + destruct (Z.eqb_spec g (gran (e - 1))) as [->|NE2].
              * rewrite kx_bucket_add_same. rewrite kx_bucket_add_other by exact NE1. reflexivity.
              * rewrite kx_bucket_add_other by exact NE2. rewrite kx_bucket_add_other by exact NE1. reflexivity. }
        rewrite STEP, B. reflexivity.
      * (* [comment removed for export] *)
        injection H as <- <- <-. rewrite WD. cbn [negb]. split; [rewrite A; reflexivity|]. split; [|rewrite C; reflexivity].
        intros g. rewrite NW, B. reflexivity.
    + clear WD. destruct (kx_wide0 K); injection H as <- <- <-.
      * split; [rewrite A; reflexivity|]. split; [|rewrite C; reflexivity]. intros g. rewrite NW, B. reflexivity.
      * split; [exact A|]. split; [|rewrite C; reflexivity]. intros g. rewrite NW, B. reflexivity.
Qed.

Lemma kx_select_eq : forall kn rb rk,
  kx_select (mk_kix kn) rb rk = if is_lit0 rb then List.filter (kx_cand0 (gran rk)) kn else List.filter kx_candf kn.
Proof.
  intros kn rb rk. unfold kx_select, mk_kix.
  destruct (kx_build kn 1%positive) as [[w0 gr] wf] eqn:Hb. cbn [kx_gran kx_w0 kx_wf fst snd].
  destruct (kx_build_spec kn 1%positive w0 gr wf Hb) as (A & B & C).
  destruct (is_lit0 rb); [|exact C].
  rewrite B, A. rewrite (kx_merge_filters (narrow_in (gran rk)) kx_wide0 kn 1%positive (narrow_not_wide (gran rk))).
  apply filter_ext. intros K. symmetry. apply kx_cand0_split.
Qed.

Theorem know_lookupA0I_eq : forall bc kn segs rb rk n sx hints acc,
  know_lookupA0I bc (mk_kix kn) segs rb rk n sx hints acc = know_lookupA0B bc segs kn rb rk n sx hints acc.
Proof.
  intros bc kn segs rb rk n sx hints acc. unfold know_lookupA0I. rewrite !know_lookupA0F_eq.
  destruct hints as [|h hs]; [|reflexivity]. destruct n as [|n]; [reflexivity|].
  rewrite kx_select_eq. destruct (is_lit0 rb) eqn:L.
  - apply is_lit0_true in L. subst rb. apply know_lookupA0B_filter0.
  - apply know_lookupA0B_filterf. exact L.
Qed.

(* [comment removed for export] *)
Definition know_lookupABI (bc : bctx) (kx : kix) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match know_lookupA0I bc kx segs rb rk n sx hints acc with
  | LMiss acc' hints' =>
      match know_bytes_lit segs kn rb rk n with
      | Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
      | None => LMiss acc' hints'
      end
  | r => r
  end.
Lemma know_lookupABI_eq : forall bc kn segs,
  know_lookupABI bc (mk_kix kn) segs kn = know_lookupAB bc segs kn.
Proof.
  intros bc kn segs. bcfe. unfold know_lookupABI, know_lookupAB. rewrite know_lookupA0I_eq. reflexivity.
Qed.
Local Close Scope Z_scope.

Fixpoint split_read_loBI (bc : bctx) (kx : kix) (segs : list Segment) (rb : expr) (rk : Z)
         (w1 : nat) : option (nat * expr) :=
  match w1 with
  | O => None
  | S w1' =>
      match know_lookupA0I bc kx segs rb rk w1 false [] [] with
      | LHit v [] _ => Some (w1, v)
      | _ => split_read_loBI bc kx segs rb rk w1'
      end
  end.
Lemma split_read_loBI_eq : forall bc kn segs rb rk w1,
  split_read_loBI bc (mk_kix kn) segs rb rk w1 = split_read_loB bc segs kn rb rk w1.
Proof.
  intros bc kn segs rb rk w1. induction w1 as [|w1 IH]; [reflexivity|].
  cbn [split_read_loBI split_read_loB]. rewrite know_lookupA0I_eq, IH. reflexivity.
Qed.

Definition sym_readBI (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match log_lookupBn bc (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
  | LStuck => None
  | LHit v scs hints =>
      Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookupABI bc kx segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extKB bc v, flat_scB bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
      | LMiss scs' hints' =>
          (* [comment removed for export] *)
          let i := s_next ss in
          match sc_reads scr with
          | e :: reads' => Some (e, flat_scB bc a n ++ SCReadBase a n sx' e :: scs', SCR (sc_dirs scr) reads' hints', S i)
          | [] =>
              match (if sx' then None else split_read_loBI bc kx segs (a_base a) (a_off a) (Nat.pred n)) with
              | Some (w1, v1) =>
                  let a2 := SA (a_base a) (a_off a + Z.of_nat w1)%Z in
                  let n2 := (n - w1)%nat in
                  let rv2 := xwrap n2 false (EVar i) in
                  Some (split_value (extKB bc v1) w1 rv2, flat_scB bc a n ++ SCReadBase a2 n2 false rv2 :: scs',
                        SCR (sc_dirs scr) [] hints', S i)
              | None =>
                  let rv := xwrap n sx' (EVar i) in
                  Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) [] hints', S i)
              end
          end
      end
  end.


Definition sym_stepBI (bc : bctx) (kx : kix) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bsg imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluwKB bc ALU_ADD (g rs) (ELit (bsg imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluwKB bc op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (sset ss rd (mkMdKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (sset ss rd (ELit (u64 (Z.shiftl (bsg imm) 12))) (p + 4)) [] scr
  | Auipc rd imm => SOk (sset ss rd (ELit (u64 (Z.shiftl (bsg imm) 12 + p))) (p + 4)) [] scr
  | Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (u64 (p + bsg imm))) [] scr
  | Jalr rd rs1 imm =>
      match conc_exprB bc (g rs1) with
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (zm64 (Z.land (w64 z + bsg imm) (-2)))) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let tk := u64 (p + bsg imm) in
      let a := g rs1 in let b := g rs2 in
      match match decide_branchB bc c a b with
            | Some t => Some t
            | None => match decide_branchB bc c (conc_exprB bc a) (conc_exprB bc b) with
                      | Some t => Some t
                      | None => enum_branchB bc c a b
                      end
            end with
      | Some t => SOk (sjump ss (if t then tk else p + 4)) [] scr
      | None =>
          match sc_dirs scr with
          | [] => SStop
          | t :: dirs' =>
              SOk (sjump ss (if t then tk else p + 4)) [SCBr t c a b]
                  (SCR dirs' (sc_reads scr) (sc_hints scr))
          end
      end
  | Fence _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | FenceI _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in
      (* [comment removed for export] *)
      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrKB bc (g rs) (bsg imm) in
      match sym_readBI segs ss bc kx scr a n sx' with
      | None => SStop
      | Some (v, scs, scr', nx') =>
          SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                   (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrKB bc (g rs1) (bsg imm) in
      match resv_inval (s_resv ss) a with
      | None => SStop
      | Some r' =>
          SOk (SSR (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) r')
              (flat_scB bc a n ++ storeok_scB bc a n) scr
      end
  (* [comment removed for export] *)
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match sym_readBI segs ss bc kx scr a n (amo_sx wd) with
        | None => SStop
        | Some (v, scs, scr', nx') =>
            SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                     (s_log ss) (s_know ss) nx' (Some a)) scs scr'
        end
      else SStop
  | Sc wd _ _ rd rs1 rs2 =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs1 in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match s_resv ss with
        | Some r =>
            if saddr_eqb r a then
              SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (ELit 0))
                       (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) None)
                  (flat_scB bc a n ++ storeok_scB bc a n) scr
            else SStop   (* [comment removed for export] *)
        | None => SStop
        end
      else SStop
  | Amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | None => SStop
      | Some aop =>
          let n := msize_bytes (amo_sz wd) in
          let e := g rs1 in
          if amo_alignedbB bc e wd then
            let a := to_saddrKB bc e 0 in
            match resv_inval (s_resv ss) a with
            | None => SStop
            | Some r' =>
                match sym_readBI segs ss bc kx scr a n (amo_sx wd) with
                | None => SStop
                | Some (vold, scs, scr', nx') =>
                    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
                             (SE a n (amo_newvalB bc wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
                        (scs ++ storeok_scB bc a n) scr'
                end
            end
          else SStop
      end
  (* [comment removed for export] *)
  | FLoad fmt rd rs imm =>
      let n := ffmt_bytes fmt in
      let a := to_saddrKB bc (g rs) (bsg imm) in
      match sym_readBI segs ss bc kx scr a n false with
      | None => SStop
      | Some (_, scs, scr', nx') =>
          SOk (SSR (p + 4) (s_regs ss) (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | Fmv FMV_F_X _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Fsgnj _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Fminmax _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Fari _ _ _ _ _ rm => if rm_okb rm then SOk (sjump ss (p + 4)) [] scr else SStop
  | Fsqrt _ _ _ rm => if rm_okb rm then SOk (sjump ss (p + 4)) [] scr else SStop
  | Fma _ _ _ _ _ _ rm => if rm_okb rm then SOk (sjump ss (p + 4)) [] scr else SStop
  | Fcvt dst src rd rs1 rm =>
      if (fcvt_is_f dst && rm_okb rm)%bool then SOk (sjump ss (p + 4)) [] scr else SStop
  | _ => SStop
  end.


Lemma sym_readBI_eqf : forall segs ss bc, sym_readBI segs ss bc (mk_kix (s_know ss)) = sym_readB segs ss bc.
Proof. intros. bcfe. unfold sym_readBI, sym_readB. rewrite know_lookupABI_eq, split_read_loBI_eq. reflexivity. Qed.
Lemma sym_stepBI_eq : forall bc segs i ss scr,
  sym_stepBI bc (mk_kix (s_know ss)) segs i ss scr = sym_stepB bc segs i ss scr.
Proof. intros. unfold sym_stepBI, sym_stepB. rewrite sym_readBI_eqf. rewrite ?bsg_fe, ?u64_fe, ?w64_fe, ?zm64_fe. reflexivity. Qed.

Lemma coeffs_divkB_eqf : forall fk, coeffs_divkB (mkbc fk) = coeffs_divk fk.
Proof.
  intros fk. apply functional_extensionality; intros m. apply functional_extensionality; intros ts. 
  induction ts as [|[k a] rest IH]; intros; bcfe; [reflexivity|].
  cbn [coeffs_divkB coeffs_divk]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite coeffs_divkB_eqf : bceq.
Lemma lin_lowbits_knB_eqf : forall fk, lin_lowbits_knB (mkbc fk) = lin_lowbits_kn fk.
Proof. intros. bcfe. unfold lin_lowbits_knB, lin_lowbits_kn. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_lowbits_knB_eqf : bceq.
Lemma lin_nowrap_lB_eqf : forall fk, lin_nowrap_lB (mkbc fk) = lin_nowrap_l fk.
Proof. intros. bcfe. unfold lin_nowrap_lB, lin_nowrap_l. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_nowrap_lB_eqf : bceq.
Lemma lin_periodB_eqf : forall fk, lin_periodB (mkbc fk) = lin_period fk.
Proof. intros. bcfe. unfold lin_periodB, lin_period. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_periodB_eqf : bceq.
Lemma mkSrlB_eqf : forall fk, mkSrlB (mkbc fk) = mkSrl fk.
Proof. intros. bcfe. unfold mkSrlB, mkSrl. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkSrlB_eqf : bceq.
Lemma lowbitsB_eqf : forall fk, lowbitsB (mkbc fk) = lowbits fk.
Proof.
  intros fk. apply functional_extensionality; intros e.
  induction e; bcfe; cbn [lowbitsB lowbits]; rewrite ?IHe1, ?IHe2, ?IHe; autorewrite with bceq; reflexivity.
Qed.
#[export] Hint Rewrite lowbitsB_eqf : bceq.
Lemma lsplit_divB_eqf : forall fk, lsplit_divB (mkbc fk) = lsplit_div fk.
Proof.
  intros fk. apply functional_extensionality; intros m. apply functional_extensionality; intros ts. 
  induction ts as [|[k a] rest IH]; intros; bcfe; [reflexivity|].
  cbn [lsplit_divB lsplit_div]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite lsplit_divB_eqf : bceq.
Lemma and_high_splitB_eqf : forall fk, and_high_splitB (mkbc fk) = and_high_split fk.
Proof. intros. bcfe. unfold and_high_splitB, and_high_split. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite and_high_splitB_eqf : bceq.
Lemma and_low_splitB_eqf : forall fk, and_low_splitB (mkbc fk) = and_low_split fk.
Proof. intros. bcfe. unfold and_low_splitB, and_low_split. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite and_low_splitB_eqf : bceq.
Lemma narrow_maskB_eqf : forall fk, narrow_maskB (mkbc fk) = narrow_mask fk.
Proof. intros. bcfe. unfold narrow_maskB, narrow_mask. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite narrow_maskB_eqf : bceq.
Lemma mkAnd0B_eqf : forall fk, mkAnd0B (mkbc fk) = mkAnd0 fk.
Proof. intros. bcfe. unfold mkAnd0B, mkAnd0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkAnd0B_eqf : bceq.
Lemma mkAndB_eqf : forall fk, mkAndB (mkbc fk) = mkAnd fk.
Proof. intros. bcfe. unfold mkAndB, mkAnd. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkAndB_eqf : bceq.
Lemma mkAndKB_eqf : forall fk, mkAndKB (mkbc fk) = mkAndK fk.
Proof. intros. bcfe. unfold mkAndKB, mkAndK. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkAndKB_eqf : bceq.
Lemma or_disjointB_eqf : forall fk, or_disjointB (mkbc fk) = or_disjoint fk.
Proof. intros. bcfe. unfold or_disjointB, or_disjoint. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite or_disjointB_eqf : bceq.
Lemma mkOrB_eqf : forall fk, mkOrB (mkbc fk) = mkOr fk.
Proof. intros. bcfe. unfold mkOrB, mkOr. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkOrB_eqf : bceq.
Lemma conc_tryB_eqf : forall fk, conc_tryB (mkbc fk) = conc_try fk.
Proof.
  intros fk. apply functional_extensionality; intros e. apply functional_extensionality; intros cands. 
  induction cands as [|s rest IH]; intros; bcfe; [reflexivity|].
  cbn [conc_tryB conc_try]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite conc_tryB_eqf : bceq.
Lemma concretizeB_eqf : forall fk, concretizeB (mkbc fk) = concretize fk.
Proof. intros. bcfe. unfold concretizeB, concretize. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite concretizeB_eqf : bceq.
Lemma concretize_nrB_eqf : forall fk, concretize_nrB (mkbc fk) = concretize_nr fk.
Proof. intros. bcfe. unfold concretize_nrB, concretize_nr. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite concretize_nrB_eqf : bceq.
Lemma foldKB_eqf : forall fk, foldKB (mkbc fk) = foldK fk.
Proof. intros. bcfe. rewrite foldKB_eq. unfold foldKB_ref, foldK. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite foldKB_eqf : bceq.
Lemma lin_negwrapRB_eqf : forall fk, lin_negwrapRB (mkbc fk) = lin_negwrapR fk.
Proof. intros. bcfe. unfold lin_negwrapRB, lin_negwrapR. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_negwrapRB_eqf : bceq.
Lemma ltu_negwrapB_eqf : forall fk, ltu_negwrapB (mkbc fk) = ltu_negwrap fk.
Proof. intros. bcfe. unfold ltu_negwrapB, ltu_negwrap. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite ltu_negwrapB_eqf : bceq.
Lemma lin_branchB_eqf : forall fk, lin_branchB (mkbc fk) = lin_branch fk.
Proof. intros. bcfe. unfold lin_branchB, lin_branch. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_branchB_eqf : bceq.
Lemma decide_branchB_eqf : forall fk, decide_branchB (mkbc fk) = decide_branch fk.
Proof. intros. bcfe. unfold decide_branchB, decide_branch. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite decide_branchB_eqf : bceq.
Lemma mkSltB_eqf : forall fk, mkSltB (mkbc fk) = mkSlt fk.
Proof. intros. bcfe. unfold mkSltB, mkSlt. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkSltB_eqf : bceq.
Lemma mkAluK0B_eqf : forall fk, mkAluK0B (mkbc fk) = mkAluK0 fk.
Proof. intros. bcfe. unfold mkAluK0B, mkAluK0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkAluK0B_eqf : bceq.
Lemma mkAluKB_eqf : forall fk, mkAluKB (mkbc fk) = mkAluK fk.
Proof. intros. bcfe. unfold mkAluKB, mkAluK. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkAluKB_eqf : bceq.
Lemma mkMdKB_eqf : forall fk, mkMdKB (mkbc fk) = mkMdK fk.
Proof. intros. bcfe. unfold mkMdKB, mkMdK. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkMdKB_eqf : bceq.
Lemma zband32B_eqf : forall fk, zband32B (mkbc fk) = zband32 fk.
Proof. intros. bcfe. unfold zband32B, zband32. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite zband32B_eqf : bceq.
Lemma zband32kB_eqf : forall fk, zband32kB (mkbc fk) = zband32k fk.
Proof. intros. bcfe. unfold zband32kB, zband32k. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite zband32kB_eqf : bceq.
Lemma wband32B_eqf : forall fk, wband32B (mkbc fk) = wband32 fk.
Proof.
  intros. bcfe. unfold wband32B, wband32. rewrite bc_fsK_mkbc, bc_fs_mkbc. autorewrite with bceq.
  destruct (sum_facts fk fk) as [|f r]; [reflexivity|]. rewrite lin_rel_multiK_eq, lin_rel_multiF_fe. reflexivity.
Qed.
#[export] Hint Rewrite wband32B_eqf : bceq.
Lemma mkAluwK0_linB_eqf : forall fk, mkAluwK0_linB (mkbc fk) = mkAluwK0_lin fk.
Proof. intros. bcfe. unfold mkAluwK0_linB, mkAluwK0_lin. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkAluwK0_linB_eqf : bceq.
Lemma mkAluwK0B_eqf : forall fk, mkAluwK0B (mkbc fk) = mkAluwK0 fk.
Proof. intros. bcfe. unfold mkAluwK0B, mkAluwK0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkAluwK0B_eqf : bceq.
Lemma mkAluwKB_eqf : forall fk, mkAluwKB (mkbc fk) = mkAluwK fk.
Proof. intros. bcfe. unfold mkAluwKB, mkAluwK. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkAluwKB_eqf : bceq.
Lemma extK0B_eqf : forall fk, extK0B (mkbc fk) = extK0 fk.
Proof. intros. bcfe. unfold extK0B, extK0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite extK0B_eqf : bceq.
Lemma extKB_eqf : forall fk, extKB (mkbc fk) = extK fk.
Proof. intros. bcfe. unfold extKB, extK. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite extKB_eqf : bceq.
Lemma flat_scB_eqf : forall fk, flat_scB (mkbc fk) = flat_sc fk.
Proof. intros. bcfe. unfold flat_scB, flat_sc. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite flat_scB_eqf : bceq.
Lemma wr_coveredB_eqf : forall fk, wr_coveredB (mkbc fk) = wr_covered fk.
Proof.
  intros fk. apply functional_extensionality; intros kn. 
  induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [wr_coveredB wr_covered]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite wr_coveredB_eqf : bceq.
Lemma storeok_scB_eqf : forall fk, storeok_scB (mkbc fk) = storeok_sc fk.
Proof. intros. bcfe. unfold storeok_scB, storeok_sc. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite storeok_scB_eqf : bceq.
Lemma conc_exprB_eqf : forall fk, conc_exprB (mkbc fk) = conc_expr fk.
Proof. intros. bcfe. unfold conc_exprB, conc_expr. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite conc_exprB_eqf : bceq.
Lemma enum_branchB_eqf : forall fk, enum_branchB (mkbc fk) = enum_branch fk.
Proof. intros. bcfe. unfold enum_branchB, enum_branch. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite enum_branchB_eqf : bceq.
Lemma to_saddrKB_eqf : forall fk, to_saddrKB (mkbc fk) = to_saddrK fk.
Proof. intros. bcfe. unfold to_saddrKB, to_saddrK. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite to_saddrKB_eqf : bceq.
Lemma amo_alignedbB_eqf : forall fk, amo_alignedbB (mkbc fk) = amo_alignedb fk.
Proof. intros. bcfe. unfold amo_alignedbB, amo_alignedb. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite amo_alignedbB_eqf : bceq.
Lemma amo_newvalB_eqf : forall fk, amo_newvalB (mkbc fk) = amo_newval fk.
Proof. intros. bcfe. unfold amo_newvalB, amo_newval. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite amo_newvalB_eqf : bceq.
Lemma log_lookupB_eqf : forall fk, log_lookupB (mkbc fk) = log_lookup fk.
Proof.
  intros fk. apply functional_extensionality; intros log. 
  induction log as [|[[kb kk] w v] rest IH]; intros; bcfe; [reflexivity|].
  cbn [log_lookupB log_lookup]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite log_lookupB_eqf : bceq.
Lemma log_lookupBp_eq : forall bc log rb rk n sx hints acc osp,
  (match osp with Some sp => sp = sprepZ bc rb rk (zofn n) | None => True end) ->
  log_lookupBp bc osp log rb rk n sx hints acc = log_lookupB bc log rb rk n sx hints acc.
Proof.
  intros bc log. induction log as [|[[kb kk] w v] rest IH]; intros rb rk n sx hints acc osp Hsp; [reflexivity|].
  cbn [log_lookupBp log_lookupB].
  destruct (rel_lit rb rk (zofn n) kb kk (zofn w)); try reflexivity; try (apply IH; exact Hsp).
  assert (HS : (match osp with Some sp => sp | None => sprepZ bc rb rk (zofn n) end) = sprepZ bc rb rk (zofn n))
    by (destruct osp; [exact Hsp|reflexivity]).
  cbv zeta. rewrite HS, ranges_apartBp_eq.
  destruct (ranges_apartB bc rb rk (zofn n) kb kk (zofn w)); [apply IH; reflexivity|].
  destruct hints as [|[|] hs]; try reflexivity; apply IH; reflexivity.
Qed.
Lemma log_lookupBn_fe : log_lookupBn = log_lookupB.
Proof. do 8 (apply functional_extensionality; intro). unfold log_lookupBn. apply log_lookupBp_eq. exact I. Qed.
#[export] Hint Rewrite log_lookupBn_fe : bceq.
Lemma know_lookupA0B_eqf : forall fk, know_lookupA0B (mkbc fk) = know_lookupA0 fk.
Proof.
  intros fk. apply functional_extensionality; intros segs. apply functional_extensionality; intros kn. 
  induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [know_lookupA0B know_lookupA0]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite know_lookupA0B_eqf : bceq.
Lemma know_lookupAB_eqf : forall fk, know_lookupAB (mkbc fk) = know_lookupA fk.
Proof. intros. bcfe. unfold know_lookupAB, know_lookupA. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite know_lookupAB_eqf : bceq.
Lemma split_read_loB_eqf : forall fk, split_read_loB (mkbc fk) = split_read_lo fk.
Proof.
  intros. bcfe. generalize x3 as w1. induction w1 as [|w1 IH]; [reflexivity|].
  cbn [split_read_loB split_read_lo]. autorewrite with bceq. rewrite IH. reflexivity.
Qed.
#[export] Hint Rewrite split_read_loB_eqf : bceq.
Lemma sym_readB_eqf : forall fk segs ss, sym_readB segs ss (mkbc fk) = sym_read segs ss fk.
Proof. intros. bcfe. unfold sym_readB, sym_read. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite sym_readB_eqf : bceq.
Lemma know_lookupB_eqf : forall fk segs, know_lookupB segs (mkbc fk) = know_lookup segs fk.
Proof. intros. bcfe. unfold know_lookupB, know_lookup. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite know_lookupB_eqf : bceq.

Lemma sym_stepB_eq : forall segs i ss scr,
  sym_stepB (mkbc (facts_of (s_know ss))) segs i ss scr = sym_step segs i ss scr.
Proof. intros. unfold sym_stepB, sym_step. autorewrite with bceq. reflexivity. Qed.
(* [comment removed for export] *)
Lemma sym_step_know : forall segs i ss scr ss' scs scr',
  sym_step segs i ss scr = SOk ss' scs scr' -> s_know ss' = s_know ss.
Proof.
  intros segs i ss scr ss' scs scr' H. unfold sym_step, sym_read in H.
  destruct i; try discriminate;
  repeat (lazymatch type of H with
          | SOk _ _ _ = SOk _ _ _ => injection H as <- _ _
          | (match ?x with _ => _ end) = _ => destruct x
          | (let (_, _) := ?x in _) = _ => destruct x
          | (if ?x then _ else _) = _ => destruct x
          end); try discriminate; try reflexivity.
Qed.

(* [comment removed for export] *)
Section WithSegs.
Variable segs : list Segment.

Section XdisLazy.   (* [comment removed for export] *)
#[local] Notation "a || b" := (if a then true else b) (at level 50, left associativity, only parsing) : bool_scope.
#[local] Notation "a && b" := (if a then b else false) (at level 40, left associativity, only parsing) : bool_scope.
Definition zf_coversB (bc : bctx) (rb : expr) (rk : Z) (n : nat) (kb : expr) (kk : Z) (len : expr) : bool :=
  (match len with
   | ELit l0 => match rel_lit rb rk (Z.of_nat n) kb kk (zm64 l0) with RInside _ => true | _ => false end
   | _ => false
   end) || xinsideB bc rb rk (elen n) kb kk len.

Definition kentry_overlayB (bc : bctx) (rb : expr) (rk : Z) (n : nat) (K : kentry) : bool :=
  match K with
  | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
      zf_coversB bc rb rk n kb kk len
  | _ => false
  end.

Definition kentry_readableB (bc : bctx) (rb : expr) (rk : Z) (n : nat) (K : kentry) : bool :=
  match K with
  | KWord (SA kb kk) w _ =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with RInside _ => true | _ => false end
  | _ => kentry_overlayB bc rb rk n K
  end.

Definition kn_readableB (bc : bctx) (kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
  existsb_lz (kentry_readableB bc rb rk n) kn || know_bytes_cov segs true kn rb rk n.

Definition kn_overlayB (bc : bctx) (kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
  existsb_lz (kentry_overlayB bc rb rk n) kn || know_bytes_cov segs false kn rb rk n.

Definition x_dischargeableB (bc : bctx) (ss ss' : sym_state) (rb : option (saddr * nat * bool)) (sc : sidecond) : bool :=
  let kn := s_know ss in
  match sc with
  | SCReadBase a n sx rv =>
      match xunwrap rv with
      | Some j =>
      (match rb with
       | Some (a', n', sx') => saddr_eqb a' a && Nat.eqb n' n && Bool.eqb sx' sx
       | None => false
       end)
      && Nat.eqb j (s_next ss) && Nat.ltb j (s_next ss') && evars_lt (s_next ss) (a_base a)
      && Nat.leb 1 n && Nat.leb n 8 && kn_readableB bc kn (a_base a) (a_off a) n && expr_eqb rv (xwrap n sx (EVar j))
      | None => false
      end
  | SCFlat a (ELit z) =>
      Z.leb 1 z && Z.leb z 8 && kn_readableB bc kn (a_base a) (a_off a) (Z.to_nat z)
  | SCStoreOk a n => Nat.leb 1 n && Nat.leb n 8 && kn_overlayB bc kn (a_base a) (a_off a) n
  | _ => false
  end%bool.
End XdisLazy.

Definition x_filterB (bc : bctx) (ss ss' : sym_state) (scs : list sidecond) : list sidecond :=
  match scs with
  | [] => []          (* [comment removed for export] *)
  | _ => let rb := find_readbase (s_next ss) scs in
         List.filter (fun sc => negb (x_dischargeableB bc ss ss' rb sc)) scs
  end.

(* [comment removed for export] *)
Definition xfp_stepB (bc : bctx) (i : instr) (ss : sym_state) (scr : scripts) : option stepres :=
  let p := s_pc ss in
  let i0 := s_next ss in
  let xdef (rd : reg) :=
    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (EVar i0))
             (s_log ss) (s_know ss) (S i0) (s_resv ss)) [] scr in
  match i with
  | FStore fmt rs1 rs2 imm =>
      let n := ffmt_bytes fmt in
      let a := to_saddrKB bc (sr_get (s_regs ss) rs1) (bsg imm) in
      Some match resv_inval (s_resv ss) a with
           | None => SStop
           | Some r' =>
               let ss' := SSR (p + 4) (s_regs ss) (SE a n (EVar i0) :: s_log ss) (s_know ss) (S i0) r' in
               SOk ss' (x_filterB bc ss ss' (flat_scB bc a n ++ storeok_scB bc a n)) scr
           end
  | Fmv FMV_X_F FMT_D rd _ =>   (* [comment removed for export] *)
      Some (SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss
                                else sr_upd (s_regs ss) (ridx rd) (EExt false 0 8 (EVar i0)))
                    (s_log ss) (s_know ss) (S i0) (s_resv ss)) [] scr)
  | Fmv FMV_X_F FMT_S rd _ =>   (* [comment removed for export] *)
      Some (SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss
                                else sr_upd (s_regs ss) (ridx rd) (EExt true 0 4 (EExt false 0 4 (EVar i0))))
                    (s_log ss) (s_know ss) (S i0) (s_resv ss)) [] scr)
  | Fcmp _ _ rd _ _ => Some (xdef rd)
  | Fclass _ rd _ => Some (xdef rd)
  | Fcvt dst src rd rs1 rm =>
      if fcvt_is_f dst then None
      else Some (if (fcvt_is_f src && rm_okb rm)%bool then xdef rd else SStop)
  | _ => None
  end.

Definition sym_stepXB (bc : bctx) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match xfp_stepB bc i ss scr with
  | Some r => r
  | None =>
  match sym_stepB bc segs i ss scr with
  | SOk ss' scs scr' =>
      if Nat.leb (s_next ss) (s_next ss')            (* [comment removed for export] *)
      then SOk (cap_rd K i ss') (x_filterB bc ss ss' scs) scr'
      else SStop
  | SStop => SStop
  end
  end.


Lemma zf_coversB_eqf : forall fk, zf_coversB (mkbc fk) = zf_covers fk.
Proof. intros. bcfe. unfold zf_coversB, zf_covers. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite zf_coversB_eqf : bceq.
Lemma kentry_overlayB_eqf : forall fk, kentry_overlayB (mkbc fk) = kentry_overlay fk.
Proof. intros. bcfe. unfold kentry_overlayB, kentry_overlay. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kentry_overlayB_eqf : bceq.
Lemma kentry_readableB_eqf : forall fk, kentry_readableB (mkbc fk) = kentry_readable fk.
Proof. intros. bcfe. unfold kentry_readableB, kentry_readable. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kentry_readableB_eqf : bceq.
Lemma kn_readableB_eqf : forall fk, kn_readableB (mkbc fk) = kn_readable segs fk.
Proof. intros. bcfe. unfold kn_readableB, kn_readable. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_readableB_eqf : bceq.
Lemma kn_overlayB_eqf : forall fk, kn_overlayB (mkbc fk) = kn_overlay segs fk.
Proof. intros. bcfe. unfold kn_overlayB, kn_overlay. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_overlayB_eqf : bceq.

Lemma x_dischargeableB_eq : forall ss ss' rb sc,
  x_dischargeableB (mkbc (facts_of (s_know ss))) ss ss' rb sc = x_dischargeable segs ss ss' rb sc.
Proof. intros. unfold x_dischargeableB, x_dischargeable. autorewrite with bceq. reflexivity. Qed.
Lemma x_filterB_eq : forall ss ss' scs,
  x_filterB (mkbc (facts_of (s_know ss))) ss ss' scs = x_filter segs ss ss' scs.
Proof.
  intros. unfold x_filterB, x_filter. destruct scs as [|sc rest]; [reflexivity|].
  erewrite filter_ext; [reflexivity|]. intros x. rewrite x_dischargeableB_eq. reflexivity.
Qed.
Lemma cap_rd_know : forall K i ss, s_know (cap_rd K i ss) = s_know ss.
Proof.
  intros K i ss. unfold cap_rd. destruct K; [reflexivity|]. destruct (rd_of i) as [rd|]; [|reflexivity].
  destruct (bv_eqb rd 0); [reflexivity|]. destruct (esize_le (sr_get (s_regs ss) rd) (S K)); reflexivity.
Qed.
Lemma xfp_stepB_eq : forall i ss scr,
  xfp_stepB (mkbc (facts_of (s_know ss))) i ss scr = xfp_step segs (s_know ss) i ss scr.
Proof.
  intros. unfold xfp_stepB, xfp_step. destruct i; try reflexivity.
  autorewrite with bceq.
  destruct (resv_inval (s_resv ss) _) as [r'|]; [|reflexivity]. rewrite x_filterB_eq. reflexivity.
Qed.
Lemma sym_stepXB_eq : forall K i ss scr,
  sym_stepXB (mkbc (facts_of (s_know ss))) K i ss scr = sym_stepX segs K i ss scr.
Proof.
  intros. unfold sym_stepXB, sym_stepX. rewrite xfp_stepB_eq.
  destruct (xfp_step segs (s_know ss) i ss scr) as [r|]; [reflexivity|].
  rewrite sym_stepB_eq.
  destruct (sym_step segs i ss scr) as [ss' scs scr'|]; [|reflexivity]. rewrite x_filterB_eq. reflexivity.
Qed.
Lemma xfp_step_know : forall kn i ss scr ss' scs scr',
  xfp_step segs kn i ss scr = Some (SOk ss' scs scr') -> s_know ss' = s_know ss.
Proof.
  intros kn i ss scr ss' scs scr' H. unfold xfp_step in H.
  destruct i; try discriminate;
  repeat (lazymatch type of H with
          | Some (SOk _ _ _) = Some (SOk _ _ _) => injection H as <- _ _
          | Some (match ?x with _ => _ end) = _ => destruct x
          | Some (if ?x then _ else _) = _ => destruct x
          | (match ?x with _ => _ end) = _ => destruct x
          | (if ?x then _ else _) = _ => destruct x
          end); try discriminate; try reflexivity.
Qed.
Lemma sym_stepX_know : forall K i ss scr ss' scs scr',
  sym_stepX segs K i ss scr = SOk ss' scs scr' -> s_know ss' = s_know ss.
Proof.
  intros K i ss scr ss' scs scr' H. unfold sym_stepX in H.
  destruct (xfp_step segs (s_know ss) i ss scr) as [r|] eqn:EX.
  { subst r. exact (xfp_step_know _ _ _ _ _ _ _ EX). }
  destruct (sym_step segs i ss scr) as [ss1 scs1 scr1|] eqn:E; [|discriminate].
  destruct (Nat.leb (s_next ss) (s_next ss1)); [|discriminate]. injection H as <- _ _.
  rewrite cap_rd_know. exact (sym_step_know _ _ _ _ _ _ _ E).
Qed.




(* [comment removed for export] *)
Lemma sym_execTX_go_know : forall t K fuel first stops ss ck,
  s_know ck = s_know ss ->
  s_know (sym_execTX_go segs t K fuel first stops ss ck) = s_know ss.
Proof.
  intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck Hck.
  - cbn. destruct (s_clean ss); [reflexivity|exact Hck].
  - cbn [sym_execTX_go].
    destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [destruct (s_clean ss); [reflexivity|exact Hck]|].
    destruct (itab_lookup t (s_pc ss)) as [i|]; [|destruct (s_clean ss); [reflexivity|exact Hck]].
    destruct (sym_stepX segs K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|destruct (s_clean ss); [reflexivity|exact Hck]].
    destruct scs; [|destruct (s_clean ss); [reflexivity|exact Hck]].
    pose proof (sym_stepX_know _ _ _ _ _ _ _ E) as HK.
    rewrite IH; [exact HK|]. destruct (s_clean ss'); [reflexivity|]. rewrite Hck, HK. reflexivity.
Qed.
Lemma sym_execTX_know : forall t K fuel first stops ss,
  s_know (sym_execTX segs t K fuel first stops ss) = s_know ss.
Proof.
  intros. unfold sym_execTX. rewrite sym_execTX_go_know; [|reflexivity]. destruct ss; reflexivity.
Qed.
(* [comment removed for export] *)
Definition sym_stepXBI (bc : bctx) (kx : kix) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match xfp_stepB bc i ss scr with
  | Some r => r
  | None =>
  match sym_stepBI bc kx segs i ss scr with
  | SOk ss' scs scr' =>
      if Nat.leb (s_next ss) (s_next ss')
      then SOk (cap_rd K i ss') (x_filterB bc ss ss' scs) scr'
      else SStop
  | SStop => SStop
  end
  end.
Lemma sym_stepXBI_eq : forall K i ss scr,
  sym_stepXBI (mkbc (facts_of (s_know ss))) (mk_kix (s_know ss)) K i ss scr = sym_stepX segs K i ss scr.
Proof.
  intros. unfold sym_stepXBI. rewrite sym_stepBI_eq. fold (sym_stepXB (mkbc (facts_of (s_know ss))) K i ss scr). apply sym_stepXB_eq.
Qed.
Fixpoint sym_execTXBI_go (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_stepXBI bc kx K i ss scr_nil with
          | SOk ss' [] _ => sym_execTXBI_go bc kx t K f false stops ss' (if s_clean ss' then ss' else ck)
          | _ => if s_clean ss then ss else ck
          end
      end
  end.
Definition sym_execTXBI (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  sym_execTXBI_go bc kx t K fuel first stops (clr ss) (clr ss).
Lemma sym_execTXBI_go_eq : forall t K fuel first stops ss ck,
  sym_execTXBI_go (mkbc (facts_of (s_know ss))) (mk_kix (s_know ss)) t K fuel first stops ss ck = sym_execTX_go segs t K fuel first stops ss ck.
Proof.
  intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck; [reflexivity|].
  cbn [sym_execTXBI_go sym_execTX_go].
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
  rewrite sym_stepXBI_eq. destruct (sym_stepX segs K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|reflexivity].
  destruct scs; [|reflexivity].
  rewrite <- (sym_stepX_know _ _ _ _ _ _ _ E). apply IH.
Qed.
Lemma sym_execTXBI_eq : forall kn0 t K fuel first stops ss,
  s_know ss = kn0 ->
  sym_execTXBI (mkbc (facts_of kn0)) (mk_kix kn0) t K fuel first stops ss = sym_execTX segs t K fuel first stops ss.
Proof.
  intros kn0 t K fuel first stops ss <-. unfold sym_execTXBI, sym_execTX.
  replace (s_know ss) with (s_know (clr ss)) by (destruct ss; reflexivity).
  apply sym_execTXBI_go_eq.
Qed.

End WithSegs.

(* [comment removed for export] *)
Definition kcutB (bc : bctx) (mk : saddr -> expr -> kentry) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry :=
  let ws := mkAlu ALU_ADD wb (ELit wk) in
  let ks := mkAlu ALU_ADD kb (ELit kk) in
  (* [comment removed for export] *)
  let low :=
    if (if lin_ge0B bc [(kb, kk)] [(wb, wk)] then false   (* [comment removed for export] *)
        else if lin_ge0B bc [(wb, wk)] [(kb, kk)] then lin_ge0B bc [(kb, kk); (len, 0%Z)] [(wb, wk)] else false)
    then [mk (SA kb kk) (mkAlu ALU_SUB ws ks)] else [] in
  let high :=
    if (if lin_ge0B bc [(kb, kk); (len, 0%Z)] [(wb, wk); (wn, 0%Z)]            (* [comment removed for export] *)
        then if lin_ge0B bc [(wb, wk); (wn, 0%Z)] [(kb, kk)]                    (* [comment removed for export] *)
             then lin_ge0B bc [(ELit 0, (two64 - 1)%Z)] [(kb, kk); (len, 0%Z)]  (* [comment removed for export] *)
             else false
        else false)
    then let we := mkAlu ALU_ADD ws wn in
         let '(hb, ho) := split_lit we in
         let ha := if (lin_ge0B bc [(hb, ho)] [(wb, wk); (wn, 0%Z)] && lin_ge0B bc [(wb, wk); (wn, 0%Z)] [(hb, ho)])%bool
                   then SA hb ho else SA we 0%Z in
         [mk ha (mkAlu ALU_SUB (mkAlu ALU_ADD ks len) we)]
    else [] in
  low ++ high.

Definition kzero_cutB (bc : bctx) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := kcutB bc KZero wb wk wn kb kk len.

Definition kfill_cutB (bc : bctx) (c : Z) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := kcutB bc (fun a n => KFill a n c) wb wk wn kb kk len.

Definition kunk_cutB (bc : bctx) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := kcutB bc KUnk wb wk wn kb kk len.

Definition prune_zfB (bc : bctx) (mk : saddr -> expr -> kentry) (wb : expr) (k : Z) (w : nat)
           (K : kentry) (kb : expr) (kk : Z) (len : expr) (apart : unit -> bool) (hints : list bool)
           (diffbase : unit -> list kentry * list sidecond * list bool)
  : list kentry * list sidecond * list bool :=
  (* [comment removed for export] *)
  if expr_eqb kb wb then
    match len with
    | ELit l0 => (ktrim mk kb kk l0 k w, [], hints)
    | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints)
           else (kcutB bc mk wb k (elen w) kb kk len, [], hints)
    end
  else if apart tt then ([K], [], hints)
  else match kcutB bc mk wb k (elen w) kb kk len with
       | [] => diffbase tt
       | cut => (cut, [], hints)
       end.

Definition prune1pB (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  let k := a_off wa in
  let diffbase (ka : saddr) (kl : expr) :=
    let apart := ranges_apart_pB bc sp (a_base wa) k (elen w) (a_base ka) (a_off ka) kl in
    if apart then ([K], [], hints) else
    match hints with
    | true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)   (* [comment removed for export] *)
    | false :: hs => ([], [], hs)                          (* [comment removed for export] *)
    | [] => ([], [], [])                                   (* [comment removed for export] *)
    end in
  match K with
  | KAlign _ _ => ([K], [], hints)
  | KRange _ _ _ => ([K], [], hints)
  | KWr _ _ => ([K], [], hints)
  | KDisj _ _ _ _ => ([K], [], hints)
  | KImg lo hi =>
      match a_base wa with
      | ELit 0 =>
          let r1 := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
          let lo2 := Z.max lo (k + Z.of_nat w) in
          let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
          (r1 ++ r2, [], hints)
      | _ => if Z.ltb (hi - lo) two64 then diffbase (SA (ELit 0) lo) (ELit (hi - lo))
             else ([], [], hints)
      end
  | KZero (SA kb kk) len =>
      prune_zfB bc KZero (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_pB bc sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KFill (SA kb kk) len c =>
      prune_zfB bc (fun a n => KFill a n c) (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_pB bc sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KUnk (SA kb kk) len => ([K], [], hints)     (* [comment removed for export] *)
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then
        (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool
         then ([K], [], hints) else (kword_cut kb kk w' v k w, [], hints))   (* [comment removed for export] *)
      else if ranges_apart_pB bc sp (a_base wa) k (elen w) kb kk (elen w') then ([K], [], hints)
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool
      then ([K], [], hints)   (* [comment removed for export] *)
      else diffbase (SA kb kk) (elen w')
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then
        match len with
        | ELit l0 =>
            let l := zm64 l0 in
            (if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool
             then ([K], [], hints) else ([], [], hints))
        | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints) else ([], [], hints)
        end
      else diffbase (SA kb kk) len
  end.

Definition ranges_apart_pcB (bc : bctx) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
           (br2 : option (Z * Z)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, br2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then true
      else if in_sidesB bc (sp_D sp) b2 k2 m2 then true
      else lin_apartB bc b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match sp_rng sp, br2, sp_h1 sp, xhiB bc n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else (* [comment removed for export] *)
            if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_xB bc (sp_Dx sp) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

Definition prune1pcB (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
  (br2 : option (Z * Z)) : list kentry * list sidecond * list bool :=
  let k := a_off wa in
  let diffbase (ka : saddr) (kl : expr) :=
    let apart := ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 (a_base ka) (a_off ka) kl in
    if apart then ([K], [], hints) else
    match hints with
    | true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)
    | false :: hs => ([], [], hs)
    | [] => ([], [], [])
    end in
  match K with
  | KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ | KImg _ _ => prune1pB bc sp wa w wv K hints
  | KZero (SA kb kk) len =>
      if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
      else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kzero_cutB bc (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KFill (SA kb kk) len c =>
      if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
      else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kfill_cutB bc c (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KUnk (SA kb kk) len => ([K], [], hints)     (* [comment removed for export] *)
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
      else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk (elen w') then ([K], [], hints)
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool
      then ([K], [], hints)
      else diffbase (SA kb kk) (elen w')
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
      else diffbase (SA kb kk) len
  end.

Fixpoint prunepcB (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (kn : list kentry) (hints : list bool)
  (cache : list (expr * option (Z * Z))) : list kentry * list sidecond * list bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let '(br2, cache') :=
        match kbase K with
        | Some kb => match br_lookup cache kb with
                     | Some r => (r, cache)
                     | None => let r := base_rangeB bc kb in (r, (kb, r) :: cache)
                     end
        | None => (None, cache)
        end in
      let '(kept, scs1, hs1) := prune1pcB bc sp wa w wv K hints br2 in
      let '(r, scs2, hs2) := prunepcB bc sp wa w wv rest hs1 cache' in
      (kept ++ r, scs1 ++ scs2, hs2)
  end.


Lemma kcutB_eqf : forall fk, kcutB (mkbc fk) = (fun mk => kcut mk fk).
Proof. intros. bcfe. unfold kcutB, kcut. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite kcutB_eqf : bceq.
Lemma kzero_cutB_eqf : forall fk, kzero_cutB (mkbc fk) = kzero_cut fk.
Proof. intros. bcfe. unfold kzero_cutB, kzero_cut. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite kzero_cutB_eqf : bceq.
Lemma kfill_cutB_eqf : forall fk, kfill_cutB (mkbc fk) = (fun c => kfill_cut c fk).
Proof. intros. bcfe. unfold kfill_cutB, kfill_cut. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite kfill_cutB_eqf : bceq.
Lemma kunk_cutB_eqf : forall fk, kunk_cutB (mkbc fk) = kunk_cut fk.
Proof. intros. bcfe. unfold kunk_cutB, kunk_cut. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite kunk_cutB_eqf : bceq.
Lemma prune_zfB_eqf : forall fk, prune_zfB (mkbc fk) = (fun mk => prune_zf mk fk).
Proof. intros. bcfe. unfold prune_zfB, prune_zf. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite prune_zfB_eqf : bceq.
Lemma prune1pB_eqf : forall fk, prune1pB (mkbc fk) = prune1p fk.
Proof. intros. bcfe. unfold prune1pB, prune1p. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite prune1pB_eqf : bceq.
Lemma ranges_apart_pcB_eqf : forall fk, ranges_apart_pcB (mkbc fk) = ranges_apart_pc fk.
Proof. intros. bcfe. unfold ranges_apart_pcB, ranges_apart_pc. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite ranges_apart_pcB_eqf : bceq.
Lemma prune1pcB_eqf : forall fk, prune1pcB (mkbc fk) = prune1pc fk.
Proof. intros. bcfe. unfold prune1pcB, prune1pc. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite prune1pcB_eqf : bceq.
Lemma prunepcB_eqf : forall fk, prunepcB (mkbc fk) = prunepc fk.
Proof.
  intros fk. apply functional_extensionality; intros sp. apply functional_extensionality; intros wa. apply functional_extensionality; intros w. apply functional_extensionality; intros wv. apply functional_extensionality; intros kn. 
  induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [prunepcB prunepc]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite prunepcB_eqf : bceq.

(* [comment removed for export] *)
#[export] Hint Rewrite zf_coversB_eqf kentry_overlayB_eqf kentry_readableB_eqf kn_readableB_eqf kn_overlayB_eqf : bceq.

(* [comment removed for export] *)
Lemma filter_nil_app : forall (l1 l2 : list kentry),
  List.filter is_factb l1 = [] -> List.filter is_factb l2 = [] -> List.filter is_factb (l1 ++ l2) = [].
Proof. intros l1 l2 H1 H2. rewrite List.filter_app, H1, H2. reflexivity. Qed.
Lemma filter_if_single : forall (c : bool) K,
  is_factb K = false -> List.filter is_factb (if c then [K] else []) = [].
Proof. intros c K H. destruct c; cbn; rewrite ?H; reflexivity. Qed.

Lemma kcut_nofacts : forall mk kn wb wk wn kb kk len,
  (forall a n, is_factb (mk a n) = false) ->
  List.filter is_factb (kcut mk kn wb wk wn kb kk len) = [].
Proof.
  intros mk kn wb wk wn kb kk len H. unfold kcut.
  apply filter_nil_app.
  - apply filter_if_single. apply H.
  - match goal with |- List.filter is_factb (if ?c then _ else _) = [] => destruct c; [|reflexivity] end.
    destruct (split_lit (mkAlu ALU_ADD (mkAlu ALU_ADD wb (ELit wk)) wn)) as [hb ho].
    cbn [List.filter]. rewrite H. reflexivity.
Qed.
Lemma ktrim_nofacts : forall mk kb kk l0 k w,
  (forall a n, is_factb (mk a n) = false) ->
  List.filter is_factb (ktrim mk kb kk l0 k w) = [].
Proof. intros. unfold ktrim. apply filter_nil_app; apply filter_if_single; apply H. Qed.
Lemma kword_cut_nofacts : forall kb kk w' v k w, List.filter is_factb (kword_cut kb kk w' v k w) = [].
Proof.
  intros. unfold kword_cut. destruct v; try reflexivity.
  apply filter_nil_app; apply filter_if_single; reflexivity.
Qed.
Lemma prune_zf_nofacts : forall mk allkn wb k w K kb kk len apart hints diffbase,
  (forall a n, is_factb (mk a n) = false) -> is_factb K = false ->
  List.filter is_factb (fst (fst (diffbase tt))) = [] ->
  List.filter is_factb (fst (fst (prune_zf mk allkn wb k w K kb kk len apart hints diffbase))) = [].
Proof.
  intros mk allkn wb k w K kb kk len apart hints diffbase Hm HK Hd. unfold prune_zf.
  destruct (expr_eqb kb wb).
  - destruct len; cbn [fst]; try (apply ktrim_nofacts; exact Hm);
      (destruct (Z.leb (k + Z.of_nat w) kk); cbn [fst List.filter]; [rewrite HK; reflexivity | apply kcut_nofacts; exact Hm]).
  - destruct (apart tt); cbn [fst List.filter]; [rewrite HK; reflexivity|].
    destruct (kcut mk allkn wb k (elen w) kb kk len) as [|c cs] eqn:E; [exact Hd|].
    cbn [fst]. rewrite <- E. apply kcut_nofacts. exact Hm.
Qed.

Ltac nfcrush :=
  cbn [fst List.filter is_factb];
  first [ reflexivity
        | apply kword_cut_nofacts
        | (apply filter_nil_app; apply filter_if_single; reflexivity)
        | match goal with
          | |- context [if ?c then _ else _] => destruct c; nfcrush
          | |- context [match ?h with nil => _ | cons _ _ => _ end] => destruct h; nfcrush
          | |- context [match ?h with ELit _ => _ | _ => _ end] => destruct h; nfcrush
          | |- context [match ?h with Z0 => _ | _ => _ end] => destruct h; nfcrush
          end ].

Lemma prune1p_facts : forall allkn sp wa w wv K hints,
  List.filter is_factb (fst (fst (prune1p allkn sp wa w wv K hints))) = List.filter is_factb [K].
Proof.
  intros allkn sp wa w wv K hints. unfold prune1p.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|[kb kk] n|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; cbn [List.filter is_factb];
    try reflexivity;
    try (apply prune_zf_nofacts; [reflexivity|reflexivity|]); nfcrush.
Qed.

Lemma prune1pc_facts : forall allkn sp wa w wv K hints br2,
  List.filter is_factb (fst (fst (prune1pc allkn sp wa w wv K hints br2))) = List.filter is_factb [K].
Proof.
  intros allkn sp wa w wv K hints br2. unfold prune1pc.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|[kb kk] n|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
    try apply prune1p_facts.
  - destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|]. nfcrush.
  - destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|].
    unfold kzero_cut. destruct (ranges_apart_pc _ _ _ _ _ _ _ _ _); [reflexivity|].
    destruct (kcut KZero allkn (a_base wa) (a_off wa) (elen w) kb kk len) eqn:E; [nfcrush|].
    cbn [fst]. rewrite <- E. apply kcut_nofacts. reflexivity.
  - destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|]. nfcrush.
  - destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|].
    unfold kfill_cut. destruct (ranges_apart_pc _ _ _ _ _ _ _ _ _); [reflexivity|].
    destruct (kcut (fun a n => KFill a n c) allkn (a_base wa) (a_off wa) (elen w) kb kk len) eqn:E; [nfcrush|].
    cbn [fst]. rewrite <- E. apply kcut_nofacts. reflexivity.
  - reflexivity.
Qed.

Lemma prunepc_facts : forall allkn sp wa w wv kn hints cache,
  List.filter is_factb (fst (fst (prunepc allkn sp wa w wv kn hints cache))) = List.filter is_factb kn.
Proof.
  intros allkn sp wa w wv kn. induction kn as [|K rest IH]; intros hints cache; [reflexivity|].
  cbn [prunepc].
  destruct (match kbase K with Some kb => match br_lookup cache kb with Some r => (r, cache) | None => (base_range allkn kb, (kb, base_range allkn kb) :: cache) end | None => (None, cache) end) as [br2 cache'].
  destruct (prune1pc allkn sp wa w wv K hints br2) as [[kept scs1] hs1] eqn:E1.
  destruct (prunepc allkn sp wa w wv rest hs1 cache') as [[r scs2] hs2] eqn:E2.
  cbn [fst]. rewrite List.filter_app. pose proof (prune1pc_facts allkn sp wa w wv K hints br2) as H1. rewrite E1 in H1. cbn [fst] in H1.
  rewrite H1. specialize (IH hs1 cache'). rewrite E2 in IH. cbn [fst] in IH. rewrite IH. cbn [List.filter]. destruct (is_factb K); reflexivity.
Qed.

Lemma carry_facts : forall log kn hints,
  List.filter is_factb (fst (fst (carry log kn hints))) = List.filter is_factb kn.
Proof.
  intros log kn hints. induction log as [|[a w v] older IH]; [reflexivity|].
  cbn [carry]. destruct (carry older kn hints) as [[kn1 scs1] hs1]. cbn [fst] in IH.
  destruct (prunepc _ _ _ _ _ kn1 hs1 []) as [[kn2 scs2] hs2] eqn:E.
  cbn [fst List.filter is_factb]. pose proof (prunepc_facts (facts_of kn1) (mk_sprep (facts_of kn1) (a_base a) (a_off a) (elen w)) a w v kn1 hs1 []) as H.
  rewrite E in H. cbn [fst] in H. rewrite H. exact IH.
Qed.

Fixpoint carryB (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log with
  | [] => (kn, [], hints)
  | SE a w v :: older =>
      let '(kn1, scs1, hs1) := carryB bc older kn hints in
      let '(kn2, scs2, hs2) := prunepcB bc (mk_sprepB bc (a_base a) (a_off a) (elen w)) a w v kn1 hs1 [] in
      (KWord a w v :: kn2, scs1 ++ scs2, hs2)
  end.
Lemma carryB_eq : forall log kn hints, carryB (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof.
  intros log kn hints. induction log as [|[a w v] older IH]; [reflexivity|].
  cbn [carryB carry]. rewrite IH.
  pose proof (carry_facts older kn hints) as HF.
  destruct (carry older kn hints) as [[kn1 scs1] hs1]. cbn [fst] in HF.
  rewrite !facts_of_filter, <- HF, <- !facts_of_filter.
  autorewrite with bceq. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p_aluop_eqb_refl : forall a, aluop_eqb a a = true. Proof. intros []; reflexivity. Qed.
Lemma p_mulop_eqb_refl : forall a, mulop_eqb a a = true. Proof. intros []; reflexivity. Qed.
Lemma p_expr_eqb_refl : forall x, expr_eqb x x = true.
Proof.
  induction x; cbn -[Z.eqb Nat.eqb]; rewrite ?p_aluop_eqb_refl, ?p_mulop_eqb_refl, ?IHx, ?IHx1, ?IHx2, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
Qed.
Lemma p_prune1pc_eq : forall allkn sp wa w wv K hints br2,
  match kbase K with Some kb => br2 = base_range allkn kb | None => True end ->
  prune1pc allkn sp wa w wv K hints br2 = prune1p allkn sp wa w wv K hints.
Proof.
  intros allkn sp wa w wv K hints br2 Hb.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    cbn [kbase] in Hb; try reflexivity; subst br2; unfold prune1pc, prune1p, prune_zf, kzero_cut, kfill_cut, kunk_cut;
    destruct (expr_eqb kb (a_base wa)); reflexivity.
Qed.
Definition p_br_cache_ok (allkn : list kentry) (c : list (expr * option (Z * Z))) : Prop :=
  Forall (fun p => snd p = base_range allkn (fst p)) c.
Lemma p_br_lookup_ok : forall allkn c b r, p_br_cache_ok allkn c -> br_lookup c b = Some r -> r = base_range allkn b.
Proof.
  intros allkn c b r Hc. induction c as [|[b' r'] rest IH]; cbn; [discriminate|].
  apply Forall_cons_iff in Hc as [H1 Hc]. cbn in H1.
  destruct (expr_eqb b b') eqn:E.
  - intros H. injection H as <-. apply p_expr_eqb_eq in E. subst b'. exact H1.
  - apply IH. exact Hc.
Qed.
Lemma p_prunepc_eq : forall allkn sp wa w wv kn hints cache,
  p_br_cache_ok allkn cache ->
  prunepc allkn sp wa w wv kn hints cache = prunep allkn sp wa w wv kn hints.
Proof.
  intros allkn sp wa w wv kn. induction kn as [|K rest IH]; intros hints cache Hc; [reflexivity|].
  cbn [prunepc prunep].
  destruct (kbase K) as [kb|] eqn:HK.
  - destruct (br_lookup cache kb) as [r|] eqn:HL.
    + rewrite (p_prune1pc_eq allkn sp wa w wv K hints r) by (rewrite HK; exact (p_br_lookup_ok _ _ _ _ Hc HL)).
      destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1]. rewrite (IH hs1 cache Hc). reflexivity.
    + rewrite (p_prune1pc_eq allkn sp wa w wv K hints (base_range allkn kb)) by (rewrite HK; reflexivity).
      destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1].
      rewrite (IH hs1 ((kb, base_range allkn kb) :: cache)) by (constructor; [reflexivity | exact Hc]). reflexivity.
  - rewrite (p_prune1pc_eq allkn sp wa w wv K hints None) by (rewrite HK; exact I).
    destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1]. rewrite (IH hs1 cache Hc). reflexivity.
Qed.

(* [comment removed for export] *)
Definition g1 (fk : list kentry) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) : list kentry :=
  fst (fst (prune1p fk sp wa w wv K [])).

Ltac pk_crush :=
  cbn [fst snd];
  first [ reflexivity
        | match goal with
          | |- context [if ?c then _ else _] => destruct c; pk_crush
          | |- context [match ?h with ELit _ => _ | _ => _ end] => destruct h; pk_crush
          | |- context [match ?h with Z0 => _ | _ => _ end] => destruct h; pk_crush
          | |- context [match ?h with nil => _ | cons _ _ => _ end] => destruct h; pk_crush
          end ].

Lemma prune1p_nil : forall fk sp wa w wv K,
  prune1p fk sp wa w wv K [] = (g1 fk sp wa w wv K, [], []).
Proof.
  intros. unfold g1, prune1p, prune_zf.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len]; pk_crush.
Qed.
Lemma prunep_nil : forall fk sp wa w wv kn,
  prunep fk sp wa w wv kn [] = (flat_map (g1 fk sp wa w wv) kn, [], []).
Proof.
  intros fk sp wa w wv kn. induction kn as [|K rest IH]; [reflexivity|].
  cbn [prunep flat_map]. rewrite prune1p_nil, IH. reflexivity.
Qed.

(* [comment removed for export] *)
Inductive pk_res := PKeep | PRepl (l : list kentry).
Definition pk_list (K : kentry) (r : pk_res) : list kentry := match r with PKeep => [K] | PRepl l => l end.

(* [comment removed for export] *)
Definition prune1pcK (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
  (br2 : option (Z * Z)) : pk_res :=
  let k := a_off wa in
  let wb := a_base wa in
  let zfK (mk : saddr -> expr -> kentry) (kb : expr) (kk : Z) (len : expr) :=
    if same then
      match len with
      | ELit l0 => PRepl (ktrim mk kb kk l0 k w)
      | _ => if Z.leb (k + zofn w) kk then PKeep else PRepl (kcutB bc mk wb k (elenf w) kb kk len)
      end
    else if ranges_apart_pcB bc sp wb k (elenf w) br2 kb kk len then PKeep
    else match kcutB bc mk wb k (elenf w) kb kk len with
         | [] => if ranges_apart_pcB bc sp wb k (elenf w) br2 kb kk len then PKeep else PRepl []
         | cut => PRepl cut
         end in
  match K with
  | KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ => PKeep
  | KImg lo hi =>
      match wb with
      | ELit 0 =>
          let r1 := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
          let lo2 := Z.max lo (k + zofn w) in
          let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
          PRepl (r1 ++ r2)
      | _ => if Z.ltb (hi - lo) (2 ^ 64) then
               (if ranges_apart_pB bc sp wb k (elenf w) (ELit 0) lo (ELit (hi - lo)) then PKeep else PRepl [])
             else PRepl []
      end
  | KZero (SA kb kk) len => zfK KZero kb kk len
  | KFill (SA kb kk) len c => zfK (fun a n => KFill a n c) kb kk len
  | KUnk (SA kb kk) len => PKeep     (* [comment removed for export] *)
  | KWord (SA kb kk) w' v =>
      if same then (if (Z.leb (kk + zofn w') k || Z.leb (k + zofn w) kk)%bool then PKeep else PRepl (kword_cut kb kk w' v k w))
      else if ranges_apart_pcB bc sp wb k (elenf w) br2 kb kk (elenf w') then PKeep
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool then PKeep
      else if ranges_apart_pcB bc sp wb k (elenf w) br2 kb kk (elenf w') then PKeep else PRepl []
  | KBlob (SA kb kk) len bk =>
      if same then
        match len with
        | ELit l0 => let l := (l0 mod 2 ^ 64)%Z in
                     if (Z.leb (kk + l) k || Z.leb (k + zofn w) kk)%bool then PKeep else PRepl []
        | _ => if Z.leb (k + zofn w) kk then PKeep else PRepl []
        end
      else if ranges_apart_pcB bc sp wb k (elenf w) br2 kb kk len then PKeep else PRepl []
  end.

Lemma prune1pcK_eq : forall fk sp wa w wv K br2 same,
  (match kbase K with Some kb => same = expr_eqb kb (a_base wa) | None => True end) ->
  pk_list K (prune1pcK (mkbc fk) sp wa w wv K same br2) = fst (fst (prune1pc fk sp wa w wv K [] br2)).
Proof.
  intros fk sp wa w wv K br2 same H.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    cbn [kbase] in H; try subst same; unfold prune1pcK, prune1pc, prune1p, prune_zf, kzero_cut, kfill_cut, kunk_cut;
    autorewrite with bceq; cbn [a_base a_off]; pk_crush.
Qed.

(* [comment removed for export] *)
Definition bkey (e : expr) : option nat := first_var e.
Record binfo := BI { bi_base : expr; bi_br : option (Z * Z) }.
Record ntab := NT { nt_vars : list (list (expr * positive)); nt_other : list (expr * positive); nt_next : positive; nt_info : ptree binfo }.
Definition nt_empty : ntab := NT [] [] xH PTLeaf.
Fixpoint alookupE (l : list (expr * positive)) (b : expr) : option positive :=
  match l with
  | [] => None
  | (b', id) :: rest => if expr_eqb b b' then Some id else alookupE rest b
  end.
Definition nt_bucket (t : ntab) (k : option nat) : list (expr * positive) :=
  match k with Some n => lget (nt_vars t) n | None => nt_other t end.
Definition nt_add (t : ntab) (k : option nat) (p : expr * positive) (bi : binfo) : ntab :=
  match k with
  | Some n => NT (lset (nt_vars t) n p) (nt_other t) (Pos.succ (nt_next t)) (pt_set (nt_next t) bi (nt_info t))
  | None => NT (nt_vars t) (p :: nt_other t) (Pos.succ (nt_next t)) (pt_set (nt_next t) bi (nt_info t))
  end.
Definition intern (bc : bctx) (t : ntab) (b : expr) : positive * binfo * ntab :=
  let k := bkey b in
  match alookupE (nt_bucket t k) b with
  | Some id => (id, match pt_get (nt_info t) id with Some bi => bi | None => BI b (base_rangeB bc b) end, t)
  | None => let id := nt_next t in
            let bi := BI b (base_rangeB bc b) in
            (id, bi, nt_add t k (b, id) bi)
  end.

Definition NTI (bc : bctx) (t : ntab) : Prop :=
  (forall k b id, In (b, id) (nt_bucket t k) ->
     k = bkey b /\ pt_get (nt_info t) id = Some (BI b (base_rangeB bc b)) /\ (id < nt_next t)%positive)
  /\ (forall k b id id', In (b, id) (nt_bucket t k) -> In (b, id') (nt_bucket t k) -> id = id').

Lemma nt_bucket_empty : forall k, nt_bucket nt_empty k = [].
Proof. intros [n|]; cbn; [unfold lget; destruct n; reflexivity | reflexivity]. Qed.
Lemma NTI_empty : forall bc, NTI bc nt_empty.
Proof. intros bc. split; intros; rewrite nt_bucket_empty in *; contradiction. Qed.

Lemma alookupE_Some : forall l b id, alookupE l b = Some id -> In (b, id) l.
Proof.
  induction l as [|[b' id'] rest IH]; cbn; intros b id H; [discriminate|].
  destruct (expr_eqb b b') eqn:E.
  - injection H as <-. apply p_expr_eqb_eq in E. subst. left. reflexivity.
  - right. apply IH. exact H.
Qed.
Lemma alookupE_None : forall l b id, alookupE l b = None -> ~ In (b, id) l.
Proof.
  induction l as [|[b' id'] rest IH]; cbn; intros b id H; [tauto|].
  destruct (expr_eqb b b') eqn:E; [discriminate|].
  intros [X|X].
  - injection X as -> ->. rewrite p_expr_eqb_refl in E. discriminate.
  - exact (IH _ _ H X).
Qed.
Lemma nt_add_bucket : forall t k p bi k',
  nt_bucket (nt_add t k p bi) k' = if okey_eqb k' k then p :: nt_bucket t k' else nt_bucket t k'.
Proof.
  intros t [n|] p bi [m|]; cbn [nt_add nt_bucket nt_vars nt_other okey_eqb]; try reflexivity. apply lget_lset.
Qed.
Lemma nt_add_next : forall t k p bi, nt_next (nt_add t k p bi) = Pos.succ (nt_next t).
Proof. intros t [n|] p bi; reflexivity. Qed.
Lemma nt_add_info : forall t k p bi, nt_info (nt_add t k p bi) = pt_set (nt_next t) bi (nt_info t).
Proof. intros t [n|] p bi; reflexivity. Qed.

Lemma intern_ok : forall bc t b id bi t',
  NTI bc t -> intern bc t b = (id, bi, t') ->
  NTI bc t' /\ bi = BI b (base_rangeB bc b) /\ In (b, id) (nt_bucket t' (bkey b))
  /\ (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k)).
Proof.
  intros bc t b id bi t' [HA HB] H. unfold intern in H.
  destruct (alookupE (nt_bucket t (bkey b)) b) as [id0|] eqn:HL.
  - injection H as <- <- <-. pose proof (alookupE_Some _ _ _ HL) as HIn.
    destruct (HA _ _ _ HIn) as (_ & Hinfo & _). rewrite Hinfo.
    split; [split; assumption|]. split; [reflexivity|]. split; [exact HIn|]. intros; assumption.
  - injection H as <- <- <-.
    split; [|split; [reflexivity|split]].
    + split.
      * intros k b0 id0 HIn. rewrite nt_add_bucket in HIn. rewrite nt_add_info, nt_add_next.
        destruct (okey_eqb_spec k (bkey b)) as [->|NE].
        -- destruct HIn as [X|X].
           ++ injection X as <- <-. split; [reflexivity|]. rewrite pt_gss. split; [reflexivity|lia].
           ++ destruct (HA _ _ _ X) as (H1 & H2 & H3). split; [exact H1|].
              rewrite pt_gso by lia. split; [exact H2|lia].
        -- destruct (HA _ _ _ HIn) as (H1 & H2 & H3). split; [exact H1|]. rewrite pt_gso by lia. split; [exact H2|lia].
      * intros k b0 id0 id0' H1 H2. rewrite nt_add_bucket in H1, H2.
        destruct (okey_eqb_spec k (bkey b)) as [->|NE]; [|exact (HB _ _ _ _ H1 H2)].
        destruct H1 as [X1|X1]; destruct H2 as [X2|X2].
        -- congruence.
        -- injection X1 as <- <-. exfalso. exact (alookupE_None _ _ _ HL X2).
        -- injection X2 as <- <-. exfalso. exact (alookupE_None _ _ _ HL X1).
        -- exact (HB _ _ _ _ X1 X2).
    + rewrite nt_add_bucket. destruct (okey_eqb_spec (bkey b) (bkey b)); [|congruence]. left. reflexivity.
    + intros k p HIn. rewrite nt_add_bucket. destruct (okey_eqb_spec k (bkey b)); [right|]; exact HIn.
Qed.

Lemma nt_same_eq : forall bc t b1 id1 b2 id2,
  NTI bc t -> In (b1, id1) (nt_bucket t (bkey b1)) -> In (b2, id2) (nt_bucket t (bkey b2)) ->
  Pos.eqb id1 id2 = expr_eqb b1 b2.
Proof.
  intros bc t b1 id1 b2 id2 [HA HB] H1 H2.
  destruct (HA _ _ _ H1) as (_ & I1 & _). destruct (HA _ _ _ H2) as (_ & I2 & _).
  destruct (Pos.eqb_spec id1 id2) as [<-|NE].
  - rewrite I1 in I2. injection I2 as <-. symmetry. apply p_expr_eqb_refl.
  - destruct (expr_eqb b1 b2) eqn:E; [|reflexivity]. exfalso. apply NE.
    apply p_expr_eqb_eq in E. subst b2. exact (HB _ _ _ _ H1 H2).
Qed.

Record stx := STX { sx_a : saddr; sx_w : nat; sx_v : expr; sx_sp : sprep; sx_bid : positive; sx_br : option (Z * Z) }.

Fixpoint mk_stxs (bc : bctx) (log : list sentry) (t : ntab) : list stx * ntab :=   (* [comment removed for export] *)
  match log with
  | [] => ([], t)
  | SE a w v :: older =>
      let '(sxs, t1) := mk_stxs bc older t in
      let '(r, t2) := intern bc t1 (a_base a) in
      let '(bid, bi) := r in
      (sxs ++ [STX a w v (mk_sprepB bc (a_base a) (a_off a) (elen w)) bid (bi_br bi)], t2)
  end.

(* [comment removed for export] *)
Fixpoint mk_stxsR (bc : bctx) (log : list sentry) (t : ntab) : list stx * ntab :=
  match log with
  | [] => ([], t)
  | SE a w v :: older =>
      let '(rs, t1) := mk_stxsR bc older t in
      let '(r, t2) := intern bc t1 (a_base a) in
      let '(bid, bi) := r in
      (STX a w v (mk_sprepB bc (a_base a) (a_off a) (elen w)) bid (bi_br bi) :: rs, t2)
  end.
Definition mk_stxsF (bc : bctx) (log : list sentry) (t : ntab) : list stx * ntab :=
  let '(rs, t') := mk_stxsR bc log t in (rev_append rs [], t').
Lemma mk_stxsR_eq : forall bc log t, mk_stxsR bc log t = let '(sxs, t') := mk_stxs bc log t in (rev sxs, t').
Proof.
  intros bc log. induction log as [|[a w v] older IH]; intros t; [reflexivity|].
  cbn [mk_stxsR mk_stxs]. rewrite IH. destruct (mk_stxs bc older t) as [sxs t1].
  destruct (intern bc t1 (a_base a)) as [[bid bi] t2]. rewrite rev_app_distr. reflexivity.
Qed.
Lemma mk_stxsF_eq : forall bc log t, mk_stxsF bc log t = mk_stxs bc log t.
Proof.
  intros. unfold mk_stxsF. rewrite mk_stxsR_eq. destruct (mk_stxs bc log t) as [sxs t'].
  rewrite rev_append_rev, app_nil_r, rev_involutive. reflexivity.
Qed.

Definition obrB (bc : bctx) (K : kentry) : option (Z * Z) :=
  match kbase K with Some kb => base_rangeB bc kb | None => None end.
Definition g1cB (bc : bctx) (sx : stx) (K : kentry) : list kentry :=
  fst (fst (prune1pcB bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K [] (obrB bc K))).
Fixpoint chain_slow (bc : bctx) (sxs : list stx) (l : list kentry) : list kentry :=
  match sxs with
  | [] => l
  | sx :: rest => chain_slow bc rest (flat_map (g1cB bc sx) l)
  end.

(* [comment removed for export] *)
Fixpoint chainK2 (bc : bctx) (sxs : list stx) (K : kentry) (okb : option expr) (same_of : positive -> bool) (br2 : option (Z * Z)) : list kentry :=
  match sxs with
  | [] => [K]
  | sx :: rest =>
      match prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
      | PKeep => chainK2 bc rest K okb same_of br2
      | PRepl l =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2 bc rest K' okb same_of br2 else chain_slow bc rest [K']
                                  | None => chain_slow bc rest [K']
                                  end) l
          | None => chain_slow bc rest l
          end
      end
  end.

Fixpoint stores_part (bc : bctx) (sxs : list stx) : list kentry :=   (* [comment removed for export] *)
  match sxs with
  | [] => []
  | sx :: newer => stores_part bc newer ++ chainK2 bc newer (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx)
  end.
(* [comment removed for export] *)
Fixpoint stores_partA (bc : bctx) (sxs : list stx) (acc : list kentry) : list kentry :=
  match sxs with
  | [] => acc
  | sx :: newer => stores_partA bc newer (chainK2 bc newer (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx) ++ acc)
  end.
Lemma stores_partA_eq : forall bc sxs acc, stores_partA bc sxs acc = stores_part bc sxs ++ acc.
Proof.
  intros bc sxs. induction sxs as [|sx newer IH]; intros acc; [reflexivity|].
  cbn [stores_partA stores_part]. rewrite IH, app_assoc. reflexivity.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FM (fk : list kentry) (s : sentry) (l : list kentry) : list kentry :=
  match s with SE a w v => flat_map (g1 fk (mk_sprep fk (a_base a) (a_off a) (elen w)) a w v) l end.
Fixpoint chainRo (fk : list kentry) (sxo : list sentry) (l : list kentry) : list kentry :=
  match sxo with [] => l | s :: newer => chainRo fk newer (FM fk s l) end.
Definition kw (s : sentry) : kentry := match s with SE a w v => KWord a w v end.
Fixpoint SPRo (fk : list kentry) (sxo : list sentry) : list kentry :=
  match sxo with [] => [] | s :: newer => SPRo fk newer ++ chainRo fk newer [kw s] end.

Lemma flat_map_app' : forall (A B : Type) (f : A -> list B) l1 l2, flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof. intros. rewrite !flat_map_concat_map, map_app, concat_app. reflexivity. Qed.
Lemma FM_app : forall fk s l1 l2, FM fk s (l1 ++ l2) = FM fk s l1 ++ FM fk s l2.
Proof. intros fk [a w v] l1 l2. unfold FM. apply flat_map_app'. Qed.
Lemma chainRo_snoc : forall fk sxo s l, chainRo fk (sxo ++ [s]) l = FM fk s (chainRo fk sxo l).
Proof. intros fk sxo. induction sxo as [|x rest IH]; intros; [reflexivity|]. cbn [chainRo app]. apply IH. Qed.
Lemma chainRo_app : forall fk sxo l1 l2, chainRo fk sxo (l1 ++ l2) = chainRo fk sxo l1 ++ chainRo fk sxo l2.
Proof. intros fk sxo. induction sxo as [|x rest IH]; intros; [reflexivity|]. cbn [chainRo]. rewrite FM_app. apply IH. Qed.
Lemma SPRo_snoc : forall fk sxo s, SPRo fk (sxo ++ [s]) = kw s :: FM fk s (SPRo fk sxo).
Proof.
  intros fk sxo s. induction sxo as [|x rest IH]; [destruct s; reflexivity|].
  cbn [SPRo app]. rewrite IH, chainRo_snoc, FM_app. reflexivity.
Qed.

Lemma carry_vertical : forall log kn,
  carry log kn [] = (SPRo (facts_of kn) (rev log) ++ chainRo (facts_of kn) (rev log) kn, [], []).
Proof.
  intros log kn. induction log as [|[a w v] older IH]; [reflexivity|].
  cbn [carry rev]. pose proof (carry_facts older kn []) as HF. rewrite IH in HF |- *. cbn [fst] in HF.
  cbv beta iota zeta. rewrite !facts_of_filter in *. rewrite HF.
  rewrite p_prunepc_eq by constructor. rewrite prunep_nil.
  match goal with |- context [flat_map ?g ?l] => change (flat_map g l) with (FM (List.filter is_factb kn) (SE a w v) l) end.
  rewrite FM_app, SPRo_snoc, chainRo_snoc. reflexivity.
Qed.

(* [comment removed for export] *)
Definition strip (sx : stx) : sentry := SE (sx_a sx) (sx_w sx) (sx_v sx).
Definition SX_OK (bc : bctx) (t : ntab) (sx : stx) : Prop :=
  In (a_base (sx_a sx), sx_bid sx) (nt_bucket t (bkey (a_base (sx_a sx))))
  /\ sx_br sx = base_rangeB bc (a_base (sx_a sx))
  /\ sx_sp sx = mk_sprepB bc (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx)).

Lemma g1cB_eq : forall fk sx,
  sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx)) ->
  flat_map (g1cB (mkbc fk) sx) = FM fk (strip sx).
Proof.
  intros fk sx Hsp. apply functional_extensionality; intros l. unfold FM, strip. f_equal.
  apply functional_extensionality; intros K. unfold g1cB, obrB. rewrite Hsp. autorewrite with bceq.
  rewrite p_prune1pc_eq by (destruct (kbase K); reflexivity). rewrite prune1p_nil. reflexivity.
Qed.
Lemma chain_slow_eq : forall fk sxs l,
  Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))) sxs ->
  chain_slow (mkbc fk) sxs l = chainRo fk (map strip sxs) l.
Proof.
  intros fk sxs. induction sxs as [|sx rest IH]; intros l HF; [reflexivity|].
  apply Forall_cons_iff in HF as [H1 HF]. cbn [chain_slow chainRo map]. rewrite (g1cB_eq _ _ H1). apply IH. exact HF.
Qed.


Lemma flat_map_flat_map : forall (A B C : Type) (f : A -> list B) (g : B -> list C) l,
  flat_map g (flat_map f l) = flat_map (fun x => flat_map g (f x)) l.
Proof. intros. induction l as [|x r IH]; [reflexivity|]. cbn. rewrite flat_map_app', IH. reflexivity. Qed.
Lemma chain_slow_flat_map : forall bc sxs l, chain_slow bc sxs l = flat_map (fun K => chain_slow bc sxs [K]) l.
Proof.
  intros bc sxs. induction sxs as [|sx rest IH]; intros l.
  - cbn. induction l as [|x r IHl]; [reflexivity|]. cbn. rewrite <- IHl. reflexivity.
  - cbn [chain_slow]. rewrite IH. rewrite flat_map_flat_map.
    f_equal. apply functional_extensionality. intros K. cbn [flat_map]. rewrite app_nil_r. rewrite <- IH. reflexivity.
Qed.
Lemma chainK2_eq : forall fk sxs K okb same_of br2,
  Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))) sxs ->
  okb = kbase K ->
  match okb with
  | Some kb => br2 = base_rangeB (mkbc fk) kb /\ Forall (fun sx => same_of (sx_bid sx) = expr_eqb kb (a_base (sx_a sx))) sxs
  | None => br2 = None
  end ->
  chainK2 (mkbc fk) sxs K okb same_of br2 = chain_slow (mkbc fk) sxs [K].
Proof.
  intros fk sxs. induction sxs as [|sx rest IH]; intros K okb same_of br2 HS Hokb HK; [reflexivity|].
  apply Forall_cons_iff in HS as [H1 HS]. cbn [chainK2 chain_slow flat_map]. rewrite app_nil_r.
  unfold g1cB at 1.
  assert (E : pk_list K (prune1pcK (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2)
              = fst (fst (prune1pcB (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K [] (obrB (mkbc fk) K)))).
  { autorewrite with bceq. unfold obrB. rewrite <- Hokb. destruct okb as [kb|].
    - destruct HK as [-> HK]. apply Forall_cons_iff in HK as [HK1 HK]. apply prune1pcK_eq. rewrite <- Hokb. exact HK1.
    - subst br2. apply prune1pcK_eq. rewrite <- Hokb. exact I. }
  destruct (prune1pcK _ _ _ _ _ K _ br2) as [|l]; cbn [pk_list] in E; rewrite <- E.
  - apply IH; [exact HS|exact Hokb|]. destruct okb as [kb|]; [|exact HK].
    destruct HK as [Hbr HK]. apply Forall_cons_iff in HK as [_ HK]. exact (conj Hbr HK).
  - destruct okb as [kb|]; [|reflexivity]. rewrite (chain_slow_flat_map _ rest l).
    f_equal. apply functional_extensionality. intros K'.
    destruct (kbase K') as [kb'|] eqn:HB'; [|reflexivity].
    destruct (expr_eqb kb' kb) eqn:EQ; [|reflexivity].
    apply p_expr_eqb_eq in EQ. subst kb'.
    apply IH; [exact HS|symmetry; exact HB'|].
    destruct HK as [Hbr HK]. apply Forall_cons_iff in HK as [_ HK]. exact (conj Hbr HK).
Qed.



Lemma SX_OK_mono : forall bc t t' sx,
  (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k)) -> SX_OK bc t sx -> SX_OK bc t' sx.
Proof. intros bc t t' sx Hm (H1 & H2 & H3). split; [apply Hm; exact H1|]. split; assumption. Qed.

Lemma mk_stxs_ok : forall fk log t sxs t',
  NTI (mkbc fk) t -> mk_stxs (mkbc fk) log t = (sxs, t') ->
  NTI (mkbc fk) t' /\ Forall (SX_OK (mkbc fk) t') sxs /\ map strip sxs = rev log
  /\ (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k)).
Proof.
  intros fk log. induction log as [|[a w v] older IH]; intros t sxs t' HT H.
  - cbn in H. injection H as <- <-. split; [exact HT|]. split; [constructor|]. split; [reflexivity|]. intros; assumption.
  - cbn [mk_stxs] in H. destruct (mk_stxs (mkbc fk) older t) as [sxs0 t1] eqn:E0.
    destruct (intern (mkbc fk) t1 (a_base a)) as [[bid bi] t2] eqn:EI.
    injection H as <- <-.
    destruct (IH t sxs0 t1 HT E0) as (HT1 & HS & Hmap & Hm1).
    destruct (intern_ok _ _ _ _ _ _ HT1 EI) as (HT2 & -> & HIn & Hm2).
    split; [exact HT2|]. split.
    + apply Forall_app. split.
      * apply Forall_impl with (P := SX_OK (mkbc fk) t1); [|exact HS]. intros sx. apply SX_OK_mono. exact Hm2.
      * constructor; [|constructor]. split; [exact HIn|]. split; reflexivity.
    + split; [rewrite map_app, Hmap; reflexivity|]. intros k p Hp. apply Hm2. apply Hm1. exact Hp.
Qed.

Lemma Forall_SX_sp : forall fk t sxs, Forall (SX_OK (mkbc fk) t) sxs ->
  Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))) sxs.
Proof. intros fk t sxs H. apply Forall_impl with (P := SX_OK (mkbc fk) t); [|exact H]. intros sx (_ & _ & X). exact X. Qed.

Lemma Forall_SX_same : forall fk t sxs kb bid,
  NTI (mkbc fk) t -> In (kb, bid) (nt_bucket t (bkey kb)) -> Forall (SX_OK (mkbc fk) t) sxs ->
  Forall (fun sx => Pos.eqb bid (sx_bid sx) = expr_eqb kb (a_base (sx_a sx))) sxs.
Proof.
  intros fk t sxs kb bid HT HIn H. apply Forall_impl with (P := SX_OK (mkbc fk) t); [|exact H].
  intros sx (H1 & _ & _). exact (nt_same_eq _ _ _ _ _ _ HT HIn H1).
Qed.


Lemma stores_part_eq : forall fk t sxs,
  NTI (mkbc fk) t -> Forall (SX_OK (mkbc fk) t) sxs ->
  stores_part (mkbc fk) sxs = SPRo fk (map strip sxs).
Proof.
  intros fk t sxs HT. induction sxs as [|sx newer IH]; intros HS; [reflexivity|].
  apply Forall_cons_iff in HS as [H1 HS]. cbn [stores_part SPRo map]. rewrite (IH HS). f_equal.
  destruct H1 as (HIn & Hbr & _). destruct (sx_a sx) as [b o] eqn:Ea. cbn [a_base a_off] in HIn, Hbr.
  rewrite chainK2_eq; [unfold kw, strip; rewrite Ea; apply chain_slow_eq; exact (Forall_SX_sp _ _ _ HS) | exact (Forall_SX_sp _ _ _ HS) | reflexivity |].
  cbn [a_base]. split; [exact Hbr|]. exact (Forall_SX_same _ _ _ _ _ HT HIn HS).
Qed.


(* [comment removed for export] *)
Fixpoint pt_map {A B : Type} (f : A -> B) (t : ptree A) : ptree B :=
  match t with
  | PTLeaf => PTLeaf
  | PTNode l o r => PTNode (pt_map f l) (match o with Some a => Some (f a) | None => None end) (pt_map f r)
  end.
Lemma pt_get_map : forall (A B : Type) (f : A -> B) t k,
  pt_get (pt_map f t) k = match pt_get t k with Some a => Some (f a) | None => None end.
Proof. intros A B f t. induction t as [|l IHl o r IHr]; intros k; [destruct k; reflexivity|]. destruct k; cbn; auto. Qed.

(* [comment removed for export] *)
Definition kdescr (K : kentry) : option (expr * Z * option Z) :=
  match K with
  | KWord (SA kb kk) w _ => Some (kb, kk, Some (zlit64 (Z.of_nat w)))
  | KZero (SA kb kk) len | KUnk (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
      Some (kb, kk, match len with ELit z => Some (zlit64 z) | _ => None end)
  | KImg lo hi => Some (ELit 0%Z, lo, if Z.ltb (hi - lo) (2 ^ 64) then Some (zlit64 (hi - lo)) else None)
  | _ => None
  end.
Record einfo := EI { ei_bid : positive; ei_gid : positive; ei_kb : expr; ei_br : option (Z * Z); ei_k : Z; ei_m : option Z }.

(* [comment removed for export] *)
Definition gval : Type := (positive * option (Z * Z) * (Z * Z))%type.
Definition gtab := ptree gval.
Record gst := GST { gs_gid : ptree (ptree positive); gs_next : positive; gs_bnds : gtab }.
Definition gst_empty : gst := GST PTLeaf xH PTLeaf.
Definition gkey (kk : Z) : positive :=
  let g := Z.shiftr kk 16 in Z.to_pos (if Z.leb 0 g then 2 * g + 1 else - (2 * g))%Z.
Definition ggroup (gs : gst) (bid : positive) (kk : Z) : positive * gst :=
  let gk := gkey kk in
  let inner := match pt_get (gs_gid gs) bid with Some i => i | None => PTLeaf end in
  match pt_get inner gk with
  | Some gid => (gid, gs)
  | None => let gid := gs_next gs in
            (gid, GST (pt_set bid (pt_set gk gid inner) (gs_gid gs)) (Pos.succ gid) (gs_bnds gs))
  end.
Definition bnd_add (gs : gst) (gid bid : positive) (obr : option (Z * Z)) (lo hi : Z) : gst :=
  GST (gs_gid gs) (gs_next gs)
      (match pt_get (gs_bnds gs) gid with
       | Some (b, o, (l, h)) => pt_set gid (b, o, (Z.min l lo, Z.max h hi)) (gs_bnds gs)
       | None => pt_set gid (bid, obr, (lo, hi)) (gs_bnds gs)
       end).
Fixpoint scan_entries (bc : bctx) (kn : list kentry) (t : ntab) (gs : gst) : list (option einfo) * ntab * gst :=
  match kn with
  | [] => ([], t, gs)
  | K :: rest =>
      match kdescr K with
      | Some (kb, kk, om) =>
          let '(r, t1) := intern bc t kb in
          let '(bid, bi) := r in
          let '(gid, gs1) := match om with
                             | Some m => let '(gid, gs0) := ggroup gs bid kk in (gid, bnd_add gs0 gid bid (bi_br bi) kk (kk + m)%Z)
                             | None => (xH, gs)
                             end in
          let '(infos, t2, gs2) := scan_entries bc rest t1 gs1 in
          (Some (EI bid gid kb (bi_br bi) kk om) :: infos, t2, gs2)
      | None =>
          let '(infos, t2, gs2) := scan_entries bc rest t gs in
          (None :: infos, t2, gs2)
      end
  end.

Definition sx_m1 (sx : stx) : Z := zlit64 (Z.of_nat (sx_w sx)).
(* [comment removed for export] *)
Definition verdict (sx : stx) (g : gval) : bool :=
  match g with
  | (b, obr, (glo, ghi)) =>
      if Pos.eqb b (sx_bid sx) then false else
      match sp_rng (sx_sp sx), obr with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + a_off (sx_a sx) + sx_m1 sx - lo2) glo || Z.leb ghi (lo1 + a_off (sx_a sx) - hi2))%bool
      | _, _ => false
      end
  end.
(* [comment removed for export] *)
Fixpoint mk_fl (g : gval) (sxs : list stx) : list (stx * list stx) :=
  match sxs with
  | [] => []
  | sx :: rest => if verdict sx g then mk_fl g rest else (sx, rest) :: mk_fl g rest
  end.
Definition gfl : Type := (gval * list (stx * list stx))%type.
Definition mk_gl (bnds : gtab) (sxs : list stx) : ptree gfl := pt_map (fun g => (g, mk_fl g sxs)) bnds.

Definition obr_eqb (a b : option (Z * Z)) : bool :=
  match a, b with
  | Some (x1, y1), Some (x2, y2) => Z.eqb x1 x2 && Z.eqb y1 y2
  | None, None => true
  | _, _ => false
  end%bool.
(* [comment removed for export] *)
Definition inb (g : gval) (ei : einfo) : bool :=
  match ei_m ei, g with
  | Some m, (b, obr, (lo, hi)) =>
      Pos.eqb b (ei_bid ei) && obr_eqb obr (ei_br ei) && Z.leb lo (ei_k ei) && Z.leb (ei_k ei + m) hi
  | _, _ => false
  end%bool.

Fixpoint chainKF (bc : bctx) (fl : list (stx * list stx)) (K : kentry) (okb : option expr) (same_of : positive -> bool)
         (br2 : option (Z * Z)) : list kentry :=
  match fl with
  | [] => [K]
  | (sx, rest) :: fl' =>
      match prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
      | PKeep => chainKF bc fl' K okb same_of br2
      | PRepl l =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2 bc rest K' okb same_of br2 else chain_slow bc rest [K']
                                  | None => chain_slow bc rest [K']
                                  end) l
          | None => chain_slow bc rest l
          end
      end
  end.

Fixpoint entriesG (bc : bctx) (sxs : list stx) (gl : ptree gfl) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | Some ei =>
           let okb := kbase K in
           let same_of := match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end in
           let br2 := match okb with Some _ => ei_br ei | None => None end in
           match pt_get gl (ei_gid ei) with
           | Some (g, fl) => if inb g ei then chainKF bc fl K okb same_of br2 else chainK2 bc sxs K okb same_of br2
           | None => chainK2 bc sxs K okb same_of br2
           end
       | None => chainK2 bc sxs K None (fun _ => false) None
       end) ++ entriesG bc sxs gl rest irest
  | _, _ => []
  end.

Definition carryG (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxsF bc log nt_empty in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, _) := r in
  stores_partA bc sxs (entriesG bc sxs (mk_gl (gs_bnds gs) sxs) kn infos).

(* [comment removed for export] *)
Lemma zlit64_idem : forall z, zlit64 (zlit64 z) = zlit64 z.
Proof.
  intros z. unfold zlit64. destruct (Z.leb 0 z && Z.ltb z two64)%bool eqn:E; [rewrite E; reflexivity|].
  pose proof (Z.mod_pos_bound z two64 ltac:(unfold two64; lia)) as B.
  replace (Z.leb 0 (z mod two64) && Z.ltb (z mod two64) two64)%bool with true; [reflexivity|].
  symmetry. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.

Lemma kdescr_kbase : forall K kb kk om,
  kdescr K = Some (kb, kk, om) -> kbase K = Some kb \/ (exists lo hi, K = KImg lo hi /\ kb = ELit 0%Z /\ kk = lo).
Proof.
  intros K kb kk om H.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [kdescr kbase] in *; try discriminate; try (injection H as <- <- Hm); try (left; reflexivity).
  right. exists lo, hi. repeat split; congruence.
Qed.
Lemma kdescr_None_kbase : forall K, kdescr K = None -> kbase K = None.
Proof.
  intros K H. destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [kdescr kbase] in *; try discriminate; reflexivity.
Qed.

Lemma prune1pcK_keep_based : forall bc sp wa w wv K kb kk m lo1 hi1 lo2 hi2,
  kbase K = Some kb -> kdescr K = Some (kb, kk, Some m) ->
  sp_rng sp = Some (lo1, hi1) -> base_rangeB bc kb = Some (lo2, hi2) ->
  (hi1 + a_off wa + zlit64 (Z.of_nat w) <= lo2 + kk \/ hi2 + kk + m <= lo1 + a_off wa)%Z ->
  prune1pcK bc sp wa w wv K false (base_rangeB bc kb) = PKeep.
Proof.
  intros bc sp wa w wv K kb kk m lo1 hi1 lo2 hi2 HB HD Hsp Hbr Hnum.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [kbase kdescr] in HB, HD; try discriminate; injection HB as ->;
    try (injection HD as <- <-); try (destruct len as [z| | | | | | |]; try discriminate; injection HD as <- <-);
    unfold prune1pcK; rewrite ?elenf_fe, ?zofn_fe; cbn [a_base a_off]; unfold ranges_apart_pcB; cbn [elen]; try reflexivity; rewrite Hsp, Hbr;
    match goal with |- context [if ((?a <=? ?b) || (?c <=? ?d))%Z then _ else _] =>
      replace ((a <=? b) || (c <=? d))%Z%bool with true; [reflexivity|];
      symmetry; apply Bool.orb_true_iff; destruct Hnum as [H|H]; [left|right]; apply Z.leb_le; rewrite ?zlit64_idem; lia end.
Qed.

Lemma prune1pcK_keep_img : forall bc sp wa w wv lo hi m lo1 hi1 lo2 hi2 same br2,
  kdescr (KImg lo hi) = Some (ELit 0%Z, lo, Some m) ->
  expr_eqb (ELit 0%Z) (a_base wa) = false ->
  sp_rng sp = Some (lo1, hi1) -> base_rangeB bc (ELit 0%Z) = Some (lo2, hi2) ->
  (hi1 + a_off wa + zlit64 (Z.of_nat w) <= lo2 + lo \/ hi2 + lo + m <= lo1 + a_off wa)%Z ->
  prune1pcK bc sp wa w wv (KImg lo hi) same br2 = PKeep.
Proof.
  intros bc sp wa w wv lo hi m lo1 hi1 lo2 hi2 same br2 HD Hne Hsp Hbr Hnum.
  cbn [kdescr] in HD. destruct (Z.ltb (hi - lo) (2 ^ 64)) eqn:Hlt; [|discriminate]. injection HD as <-.
  unfold prune1pcK. rewrite ?elenf_fe, ?zofn_fe. destruct wa as [wb k]. cbn [a_base a_off] in *.
  assert (STEP : (if ranges_apart_pB bc sp wb k (elen w) (ELit 0%Z) lo (ELit (hi - lo)) then PKeep else PRepl []) = PKeep).
  { unfold ranges_apart_pB. cbn [elen]. rewrite Hsp, Hbr.
    match goal with |- context [if ((?a <=? ?b) || (?c <=? ?d))%Z then _ else _] =>
      replace ((a <=? b) || (c <=? d))%Z%bool with true; [reflexivity|];
      symmetry; apply Bool.orb_true_iff; destruct Hnum as [H|H]; [left|right]; apply Z.leb_le; rewrite ?zlit64_idem; lia end. }
  rewrite Hlt. destruct wb as [z| | | | | | |]; try exact STEP.
  destruct z; try exact STEP. cbn in Hne. discriminate.
Qed.

(* [comment removed for export] *)
Definition EINF (bc : bctx) (t : ntab) (K : kentry) (oi : option einfo) : Prop :=
  match oi with
  | None => kdescr K = None
  | Some ei => kdescr K = Some (ei_kb ei, ei_k ei, ei_m ei)
               /\ In (ei_kb ei, ei_bid ei) (nt_bucket t (bkey (ei_kb ei)))
               /\ ei_br ei = base_rangeB bc (ei_kb ei)
  end.


Lemma scan_entries_ok : forall fk kn t gs infos t' gs',
  NTI (mkbc fk) t -> scan_entries (mkbc fk) kn t gs = (infos, t', gs') ->
  NTI (mkbc fk) t'
  /\ (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k))
  /\ Forall2 (EINF (mkbc fk) t') kn infos.
Proof.
  intros fk kn. induction kn as [|K rest IH]; intros t gs infos t' gs' HT H.
  - cbn in H. injection H as <- <- <-. split; [exact HT|]. split; [intros; assumption|]. constructor.
  - cbn [scan_entries] in H.
    destruct (kdescr K) as [[[kb kk] om]|] eqn:HD.
    + destruct (intern (mkbc fk) t kb) as [[bid bi] t1] eqn:EI.
      destruct (intern_ok _ _ _ _ _ _ HT EI) as (HT1 & Hbi & HIn & Hm1).
      lazymatch type of H with (let '(_, _) := ?X in _) = _ => destruct X as [gid gs1] end.
      destruct (scan_entries (mkbc fk) rest t1 _) as [[infos2 t2] gs2] eqn:ES.
      injection H as <- <- <-.
      destruct (IH _ _ _ _ _ HT1 ES) as (HT2 & Hm2 & HF).
      split; [exact HT2|]. split; [intros k p Hp; apply Hm2; apply Hm1; exact Hp|].
      constructor; [|exact HF]. cbn [EINF ei_kb ei_k ei_m ei_bid ei_br].
      split; [exact HD|]. split; [apply Hm2; exact HIn|]. rewrite Hbi. reflexivity.
    + destruct (scan_entries (mkbc fk) rest t gs) as [[infos2 t2] gs2] eqn:ES.
      injection H as <- <- <-.
      destruct (IH _ _ _ _ _ HT ES) as (HT2 & Hm2 & HF).
      split; [exact HT2|]. split; [exact Hm2|]. constructor; [exact HD | exact HF].
Qed.

Lemma chainKF_eq : forall bc g sxs K okb same_of br2,
  (forall sx, In sx sxs -> verdict sx g = true ->
     prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 = PKeep) ->
  chainKF bc (mk_fl g sxs) K okb same_of br2 = chainK2 bc sxs K okb same_of br2.
Proof.
  intros bc g sxs. induction sxs as [|sx rest IH]; intros K okb same_of br2 Hf; [reflexivity|].
  cbn [mk_fl chainK2].
  assert (IH' : chainKF bc (mk_fl g rest) K okb same_of br2 = chainK2 bc rest K okb same_of br2)
    by (apply IH; intros; apply Hf; [right|]; assumption).
  destruct (verdict sx g) eqn:Hv.
  - rewrite (Hf sx (or_introl eq_refl) Hv). exact IH'.
  - cbn [chainKF]. destruct (prune1pcK _ _ _ _ _ K _ br2); [exact IH'|reflexivity].
Qed.

(* [comment removed for export] *)
Lemma verdict_inb_num : forall sx g ei m,
  verdict sx g = true -> inb g ei = true -> ei_m ei = Some m ->
  Pos.eqb (ei_bid ei) (sx_bid sx) = false
  /\ exists lo1 hi1 lo2 hi2, sp_rng (sx_sp sx) = Some (lo1, hi1) /\ ei_br ei = Some (lo2, hi2)
     /\ (hi1 + a_off (sx_a sx) + zlit64 (Z.of_nat (sx_w sx)) <= lo2 + ei_k ei \/ hi2 + ei_k ei + m <= lo1 + a_off (sx_a sx))%Z.
Proof.
  intros sx [[b obr] [glo ghi]] ei m Hv Hi Hm. unfold verdict in Hv. unfold inb in Hi. rewrite Hm in Hi.
  apply andb_prop in Hi as [Hi H4]. apply andb_prop in Hi as [Hi H3]. apply andb_prop in Hi as [H1 H2].
  apply Pos.eqb_eq in H1. subst b. apply Z.leb_le in H3. apply Z.leb_le in H4.
  destruct (Pos.eqb (ei_bid ei) (sx_bid sx)); [discriminate|]. split; [reflexivity|].
  destruct (sp_rng (sx_sp sx)) as [[lo1 hi1]|]; [|discriminate].
  destruct obr as [[lo2 hi2]|]; [|discriminate].
  destruct (ei_br ei) as [[x2 y2]|]; [|discriminate]. cbn [obr_eqb] in H2. apply andb_prop in H2 as [X Y].
  apply Z.eqb_eq in X. apply Z.eqb_eq in Y. subst x2 y2.
  exists lo1, hi1, lo2, hi2. split; [reflexivity|]. split; [reflexivity|].
  unfold sx_m1 in Hv. apply Bool.orb_prop in Hv. destruct Hv as [H|H]; apply Z.leb_le in H; lia.
Qed.

Lemma entriesG_eq : forall fk sxs bnds kn infos t1,
  NTI (mkbc fk) t1 -> Forall (SX_OK (mkbc fk) t1) sxs -> Forall2 (EINF (mkbc fk) t1) kn infos ->
  entriesG (mkbc fk) sxs (mk_gl bnds sxs) kn infos = chainRo fk (map strip sxs) kn.
Proof.
  intros fk sxs bnds kn infos t1 HT HS HF. induction HF as [|K oi rest irest HK HF IH].
  - cbn. clear. induction sxs as [|sx r IH]; [reflexivity|]. cbn. destruct (strip sx). exact IH.
  - cbn [entriesG]. change (K :: rest) with ([K] ++ rest). rewrite chainRo_app, IH. f_equal.
    rewrite <- (chain_slow_eq fk sxs [K] (Forall_SX_sp _ _ _ HS)).
    pose proof (Forall_SX_sp _ _ _ HS) as HSP.
    destruct oi as [ei|]; cbn [EINF] in HK.
    + destruct HK as (HD & HIn & Hbr).
      (* [comment removed for export] *)
      assert (FULL : forall okb, okb = kbase K ->
        chainK2 (mkbc fk) sxs K okb
          (match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end)
          (match okb with Some _ => ei_br ei | None => None end) = chain_slow (mkbc fk) sxs [K]).
      { intros okb Hokb. apply chainK2_eq; [exact HSP|exact Hokb|].
        destruct okb as [kb|]; [|reflexivity].
        destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & _ & _)]; [|cbn in Hokb; discriminate].
        rewrite <- Hokb in HB. injection HB as ->.
        split; [exact Hbr|]. exact (Forall_SX_same _ _ _ _ _ HT HIn HS). }
      unfold mk_gl. rewrite pt_get_map.
      destruct (pt_get bnds (ei_gid ei)) as [g|]; [|apply FULL; reflexivity].
      destruct (inb g ei) eqn:Hinb; [|apply FULL; reflexivity].
      rewrite <- (FULL (kbase K) eq_refl). apply chainKF_eq.
      intros sx Hsx Hv.
      assert (Hm : exists m, ei_m ei = Some m).
      { unfold inb in Hinb. destruct (ei_m ei) as [m|]; [exists m; reflexivity|discriminate]. }
      destruct Hm as [m Hm].
      destruct (verdict_inb_num _ _ _ _ Hv Hinb Hm) as (Hne & lo1 & hi1 & lo2 & hi2 & Hsp & Hbr2 & Hnum).
      pose proof (proj1 (Forall_forall _ _) HS sx Hsx) as (SXin & SXbr & SXsp).
      rewrite Hm in HD.
      destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
      * rewrite HB. rewrite Hne. rewrite Hbr. eapply prune1pcK_keep_based; [exact HB|exact HD|exact Hsp| | exact Hnum].
        rewrite <- Hbr. exact Hbr2.
      * cbn [kbase]. rewrite Hkb, Hk in *.
        eapply prune1pcK_keep_img; [exact HD| |exact Hsp| rewrite <- Hbr; exact Hbr2 | exact Hnum].
        rewrite <- (nt_same_eq _ _ _ _ _ _ HT HIn SXin). exact Hne.
    + apply chainK2_eq; [exact HSP| symmetry; apply kdescr_None_kbase; exact HK | reflexivity].
Qed.

Lemma carryG_eq : forall log kn,
  carryG (mkbc (facts_of kn)) log kn = SPRo (facts_of kn) (rev log) ++ chainRo (facts_of kn) (rev log) kn.
Proof.
  intros log kn. unfold carryG. rewrite mk_stxsF_eq.
  destruct (mk_stxs (mkbc (facts_of kn)) log nt_empty) as [sxs t0] eqn:E.
  destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT0 & HS0 & Hmap & _).
  destruct (scan_entries (mkbc (facts_of kn)) kn t0 gst_empty) as [[infos t1] gs] eqn:ES.
  destruct (scan_entries_ok _ _ _ _ _ _ _ HT0 ES) as (HT1 & Hm & HF).
  assert (HS1 : Forall (SX_OK (mkbc (facts_of kn)) t1) sxs).
  { apply Forall_impl with (P := SX_OK (mkbc (facts_of kn)) t0); [|exact HS0]. intros sx. apply SX_OK_mono. exact Hm. }
  rewrite stores_partA_eq.
  rewrite (stores_part_eq _ _ _ HT0 HS0), (entriesG_eq _ _ _ _ _ _ HT1 HS1 HF), Hmap. reflexivity.
Qed.

Definition carryK (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryG bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma carryK_eq : forall log kn hints,
  carryK (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof.
  intros log kn hints. unfold carryK. destruct log as [|s older]; [reflexivity|].
  destruct hints as [|h hs]; [|apply carryB_eq].
  rewrite carry_vertical, carryG_eq. reflexivity.
Qed.

End AX2B.
