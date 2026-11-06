(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec AxSymExec3.
Import ListNotations.
Open Scope bv_scope.

Module AX2B.
Import AX2.
Create HintDb bceq discriminated.

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
Definition find_rangeI (ri : rindex) (e : expr) : option (Z * Z) := find_range (ri_bucket ri (vkey_of e)) e.

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
  intros fk e. unfold find_rangeI. induction fk as [|K rest IH].
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

Record bctx : Type := BC {
  bc_fk : list kentry;      (* [comment removed for export] *)
  bc_ffk : list kentry;     (* [comment removed for export] *)
  bc_fs : list sfact;       (* [comment removed for export] *)
  bc_ri : rindex            (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition mkbc0 (fk : list kentry) (fs : list sfact) : bctx :=
  BC fk (facts_of fk) fs (mk_ri (facts_of fk)).

Lemma lin_range_ext : forall r1 r2 c ts, (forall a, r1 a = r2 a) -> lin_range r1 c ts = lin_range r2 c ts.
Proof. intros r1 r2 c ts H. induction ts as [|[k a] rest IH]; [reflexivity|]. cbn [lin_range]. rewrite H, IH. reflexivity. Qed.

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
                     let m' := (m mod two64)%Z in
                     let j := Z.log2 (m' + 1) in
                     if (Z.eqb (m' + 1) (2 ^ j) && Z.leb (al / 2 ^ j) (ah / 2 ^ j) && Z.eqb (al / 2 ^ j) (ah / 2 ^ j))%bool
                     then Some ((al mod 2 ^ j)%Z, (ah mod 2 ^ j)%Z)
                     else let jh := Z.log2 (two64 - m') in
                          if (Z.eqb (two64 - m') (2 ^ jh) && Z.ltb jh 64)%bool
                          then Some ((al - al mod 2 ^ jh)%Z, (ah - ah mod 2 ^ jh)%Z)
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
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s => Some ((al / 2 ^ s)%Z, (ah / 2 ^ s)%Z)
          | _, _ => None
          end
      | ALU_SRA =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              if Z.ltb ah (2 ^ 63) then Some ((al / 2 ^ s)%Z, (ah / 2 ^ s)%Z) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              if Z.ltb (ah * 2 ^ s) two64 then Some ((al * 2 ^ s)%Z, (ah * 2 ^ s)%Z) else None
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
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb (ah * 2 ^ s') (2 ^ 31) then Some ((al * 2 ^ s')%Z, (ah * 2 ^ s')%Z) else None
          | _, _ => None
          end
      | ALU_SRL =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if (Z.ltb ah (2 ^ 32) && (Z.ltb 0 s' || Z.ltb ah (2 ^ 31)))%bool
              then Some ((al / 2 ^ s')%Z, (ah / 2 ^ s')%Z) else None
          | _, _ => None
          end
      | ALU_SRA =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb ah (2 ^ 31) then Some ((al / 2 ^ s')%Z, (ah / 2 ^ s')%Z) else None
          | _, _ => None
          end
      | _ => None
      end
  | EMd op a b =>
      match op with
      | M_MUL =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl && Z.ltb (ah * bh) two64)%bool
              then Some ((al * bl)%Z, (ah * bh)%Z) else None
          | _, _ => None
          end
      | M_MULHU =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl)%bool
              then Some ((al * bl / two64)%Z, (ah * bh / two64)%Z) else None
          | _, _ => None
          end
      | M_DIVU =>
          match erange bc a, b with
          | Some (al, ah), ELit d =>
              let d' := (d mod two64)%Z in
              if Z.ltb 0 d' then Some ((al / d')%Z, (ah / d')%Z) else None
          | _, _ => None
          end
      | M_REMU =>
          match erange bc a, b with
          | Some (al, ah), ELit d =>
              let d' := (d mod two64)%Z in
              if Z.ltb 0 d' then Some (0%Z, Z.min ah (d' - 1)) else None
          | _, _ => None
          end
      | _ => None
      end
  | EMdw _ _ _ => None
  | EExt sx lo n a =>
      let w := (2 ^ (8 * Z.of_nat n))%Z in
      if sx then
        match lo, erange bc a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah (w / 2))%bool then Some (al, ah)
            else if (Nat.leb 1 n && Nat.leb n 8 && Z.leb (w / 2) al && Z.ltb ah w)%bool
                 then Some ((two64 - w + al)%Z, (two64 - w + ah)%Z) else None
        | _, _ => None
        end
      else
        match lo, erange bc a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah w)%bool then Some (al, ah) else Some (0%Z, Z.min (w - 1) (two64 - 1))
        | _, _ => Some (0%Z, Z.min (w - 1) (two64 - 1))
        end
  | EBlob sx k i n =>
      (* [comment removed for export] *)
      if sx then Some (0%Z, two64m1) else Some (0%Z, Z.min (2 ^ (8 * Z.of_nat n) - 1) (two64 - 1))%Z
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

Definition ealignB (bc : bctx) (e : expr) : Z := Z.max (ealign0 (bc_ffk bc) e) (pageup_align e).

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
          let m := (2 ^ ((s mod two64) mod 64))%Z in
          if (Z.eqb (k mod m)%Z 0%Z && lin_nowrapB bc e)%bool then
            let q := (k / m)%Z in
            let le := lin_of e in
            if Z.leb ((s mod two64) mod 64) (ealignB bc e) then   (* [comment removed for export] *)
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

Definition sum_fact_xB (bc : bctx) (ts : list (Z * expr)) (lo hi : Z) : list sfact :=
  let '(c2, ts2) := srl_expandB bc ts in
  match ts2 with
  | _ :: _ => if Z.eqb c2 0 then [] else [(ts2, ((lo - c2)%Z, (hi - c2)%Z))]
  | [] => []
  end.

Fixpoint sum_factsB (bc : bctx) (kn : list kentry) : list sfact :=
  match kn with
  | [] => []
  | KRange e lo hi :: rest =>
      match e with
      | EVar _ => sum_factsB bc rest
      | _ =>
        match lin_of e with
        | (c, (_ :: _ :: _) as ts) =>
            if fact_nowrapB bc e hi then (ts, ((lo - c)%Z, (hi - c)%Z)) :: sum_fact_xB bc ts (lo - c)%Z (hi - c)%Z ++ sum_factsB bc rest
            else sum_factsB bc rest
        | _ => sum_factsB bc rest
        end
      end
  | _ :: rest => sum_factsB bc rest
  end.


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
Proof. intros. bcfe. unfold ealignB, ealign. autorewrite with bceq. reflexivity. Qed.
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
Lemma sum_fact_xB_eqf0 : forall fk fs, sum_fact_xB (mkbc0 fk fs) = sum_fact_x fk.
Proof. intros. bcfe. unfold sum_fact_xB, sum_fact_x. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite sum_fact_xB_eqf0 : bceq.
Lemma sum_factsB_eqf0 : forall fk fs, sum_factsB (mkbc0 fk fs) = sum_facts fk.
Proof.
  intros fk fs. apply functional_extensionality; intros kn. 
  induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [sum_factsB sum_facts]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite sum_factsB_eqf0 : bceq.


(* [comment removed for export] *)
Definition mkbc (fk : list kentry) : bctx := mkbc0 fk (sum_factsB (mkbc0 fk []) fk).
Lemma bc_fk_mkbc : forall fk, bc_fk (mkbc fk) = fk. Proof. reflexivity. Qed.
Lemma bc_ffk_mkbc : forall fk, bc_ffk (mkbc fk) = facts_of fk. Proof. reflexivity. Qed.
Lemma bc_fs_mkbc : forall fk, bc_fs (mkbc fk) = sum_facts fk fk.
Proof. intros. unfold mkbc. cbn [bc_fs mkbc0]. rewrite sum_factsB_eqf0. reflexivity. Qed.
Lemma find_rangeI_mkbc : forall fk, find_rangeI (bc_ri (mkbc fk)) = find_range (facts_of fk).
Proof. intros. unfold mkbc. apply find_rangeI_mkbc0. Qed.
#[export] Hint Rewrite bc_fk_mkbc bc_ffk_mkbc bc_fs_mkbc find_rangeI_mkbc : bceq.
Lemma erange_fB_eqf : forall fk fuel, erange_fB fuel (mkbc fk) = erange_f fuel (facts_of fk).
Proof. intros. unfold mkbc. apply erange_fB_eqf0. Qed.
#[export] Hint Rewrite erange_fB_eqf : bceq.

Lemma erange0B_eqf : forall fk, erange0B (mkbc fk) = erange0 fk.
Proof. intros. unfold mkbc. apply erange0B_eqf0. Qed.
#[export] Hint Rewrite erange0B_eqf : bceq.
Lemma erangeB_eqf : forall fk, erangeB (mkbc fk) = erange fk.
Proof. intros. unfold mkbc. apply erangeB_eqf0. Qed.
#[export] Hint Rewrite erangeB_eqf : bceq.
Lemma base_rangeB_eqf : forall fk, base_rangeB (mkbc fk) = base_range fk.
Proof. intros. unfold mkbc. apply base_rangeB_eqf0. Qed.
#[export] Hint Rewrite base_rangeB_eqf : bceq.
Lemma ealignB_eqf : forall fk, ealignB (mkbc fk) = ealign fk.
Proof. intros. unfold mkbc. apply ealignB_eqf0. Qed.
#[export] Hint Rewrite ealignB_eqf : bceq.
Lemma lin_nowrapB_eqf : forall fk, lin_nowrapB (mkbc fk) = lin_nowrap fk.
Proof. intros. unfold mkbc. apply lin_nowrapB_eqf0. Qed.
#[export] Hint Rewrite lin_nowrapB_eqf : bceq.
Lemma srl_expandB_eqf : forall fk, srl_expandB (mkbc fk) = srl_expand fk.
Proof. intros. unfold mkbc. apply srl_expandB_eqf0. Qed.
#[export] Hint Rewrite srl_expandB_eqf : bceq.
Lemma fact_nowrapB_eqf : forall fk, fact_nowrapB (mkbc fk) = fact_nowrap fk.
Proof. intros. unfold mkbc. apply fact_nowrapB_eqf0. Qed.
#[export] Hint Rewrite fact_nowrapB_eqf : bceq.
Lemma sum_fact_xB_eqf : forall fk, sum_fact_xB (mkbc fk) = sum_fact_x fk.
Proof. intros. unfold mkbc. apply sum_fact_xB_eqf0. Qed.
#[export] Hint Rewrite sum_fact_xB_eqf : bceq.
Lemma sum_factsB_eqf : forall fk, sum_factsB (mkbc fk) = sum_facts fk.
Proof. intros. unfold mkbc. apply sum_factsB_eqf0. Qed.
#[export] Hint Rewrite sum_factsB_eqf : bceq.

Definition lin_test_relB (bc : bctx) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match bc_fs bc with
  | [] => false
  | fs =>
      match sum_subst fs ts 0 0 false with
      | (ts', (lo0, hi0), true) =>
          match lin_range (erangeB bc) c ts' with
          | Some (lo, hi) => test (lo + lo0)%Z (hi + hi0)%Z
          | None => false
          end
      | _ => false
      end
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
  | fs =>
      match sum_subst fs (snd l) 0 0 false with
      | (ts', (lo0, hi0), true) =>
          match lin_range (erangeB bc) (fst l) ts' with
          | Some (lo, hi) =>
              let lo' := (lo + lo0)%Z in let hi' := (hi + hi0)%Z in
              if (Z.leb 0 lo' && Z.ltb hi' two64)%bool then Some (lo', hi') else None
          | None => None
          end
      | _ => None
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

Fixpoint lin_alignB (bc : bctx) (ts : list (Z * expr)) : Z :=
  match ts with [] => 60 | (k, a) :: r => Z.min (zctz k + ealignB bc a) (lin_alignB bc r) end.
Definition lin_jB (bc : bctx) (c : Z) (ts : list (Z * expr)) : Z := Z.max 0 (Z.min (zctz c) (lin_alignB bc ts)).
Definition lin_ge0_saB (bc : bctx) (c : Z) (ts : list (Z * expr)) (j a : Z) : bool :=
  let sc := (2 ^ a)%Z in
  let ts' := List.map (fun t => ((sc * fst t)%Z, snd t)) ts in
  let '(c2, t2) := srl_expandB bc ts' in
  let '(c3, t3) := (if has_srl t2 then srl_expandB bc t2 else (0%Z, t2)) in
  lin_testB bc (sc * c + c2 + c3)%Z t3 (fun lo _ => Z.ltb (- 2 ^ (a + j)) lo).
Definition lin_ge0B (bc : bctx) (pos neg : xterms) : bool :=
  (xt_nowrapB bc pos && xt_nowrapB bc neg &&
   (let c := (xt_const pos - xt_const neg)%Z in
    let ts := lsub_e (xt_lin pos) (xt_lin neg) in
    (* [comment removed for export] *)
    if match lin_range (erangeB bc) c ts with Some (_, hi) => Z.ltb hi 0 | None => false end then false else
    let run := fun (ok : Z -> Z -> bool) =>
      if lin_testB bc c ts ok then true
      else let '(c2, t2) := srl_expandB bc ts in
           if lin_testB bc (c + c2)%Z t2 ok then true
           else if has_srl t2 then (let '(c3, t3) := srl_expandB bc t2 in lin_testB bc (c + c2 + c3)%Z t3 ok)
           else false in
    if run (fun lo _ => Z.leb 0 lo) then true
    else if lin_ge0_scaledB bc c ts then true
    else let j := lin_jB bc c ts in
         if (if Z.ltb 0 j then run (fun lo _ => Z.ltb (- 2 ^ j) lo) else false) then true
         else if has_srl ts then (if lin_ge0_saB bc c ts j 3 then true else lin_ge0_saB bc c ts j 12) else false))%bool.

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
  else if novars b2 then (if xinside_numB bc b1 k1 n1 b2 k2 n2 then true else xinside0B bc b1 k1 n1 b2 k2 n2) else false.   (* [comment removed for export] *)

Definition sub_itvB (bc : bctx) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
  if (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
        match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
      else false)
  then true
  else (* [comment removed for export] *)
    if (Z.leb 0 n && Z.ltb n two64)%bool then xinsideB bc b k (ELit n) (a_base c) (a_off c) m else false.

Fixpoint kdisj_apartB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itvB bc b1 k1 n1 c1 m1 then sub_itvB bc b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itvB bc b1 k1 n1 c2 m2 then sub_itvB bc b2 k2 n2 c1 m1 else false) then true
      else kdisj_apartB bc rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apartB bc rest b1 k1 n1 b2 k2 n2
  end.

Definition ranges_apartB (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match base_rangeB bc b1, base_rangeB bc b2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
      | _, _ => false
      end) then true
  else if lin_apartB bc b1 k1 n1 b2 k2 n2 then true   (* [comment removed for export] *)
  else kdisj_apartB bc (bc_fk bc) b1 k1 n1 b2 k2 n2.

Definition sub_itv_xB (bc : bctx) (b : expr) (k : Z) (n : expr) (c : saddr) (m : expr) : bool :=
  xinsideB bc b k n (a_base c) (a_off c) m.

Fixpoint kdisj_apart_xB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itv_xB bc b1 k1 n1 c1 m1 then sub_itv_xB bc b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itv_xB bc b1 k1 n1 c2 m2 then sub_itv_xB bc b2 k2 n2 c1 m1 else false) then true
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
    else if (if negb (shares_var b1 b2) then false   (* [comment removed for export] *)
             else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
             else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]) then true
    else kdisj_apart_xB bc (bc_fk bc) b1 k1 n1 b2 k2 n2
  end.

Fixpoint disj_sidesB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sidesB bc rest b1 k1 n1 in
      let r1 := if sub_itvB bc b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itvB bc b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sidesB bc rest b1 k1 n1
  end.

Fixpoint disj_sides_xB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sides_xB bc rest b1 k1 n1 in
      let r1 := if sub_itv_xB bc b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itv_xB bc b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sides_xB bc rest b1 k1 n1
  end.

(* [comment removed for export] *)
Definition sub_quickB (bc : bctx) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
  if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
    match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
  else false.
Fixpoint disj_sides2B (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) * list (saddr * expr) :=
  match kn with
  | [] => ([], [])
  | KDisj c1 m1 c2 m2 :: rest =>
      let '(r, rx) := disj_sides2B bc rest b1 k1 n1 in
      let x2 := xinsideB bc b1 k1 (ELit n1) (a_base c2) (a_off c2) m2 in
      let q2 := if sub_quickB bc b1 k1 n1 c2 m2 then true else x2 in
      let x1 := xinsideB bc b1 k1 (ELit n1) (a_base c1) (a_off c1) m1 in
      let q1 := if sub_quickB bc b1 k1 n1 c1 m1 then true else x1 in
      let r1 := if q2 then (c1, m1) :: r else r in
      let rx1 := if x2 then (c1, m1) :: rx else rx in
      ((if q1 then (c2, m2) :: r1 else r1), (if x1 then (c2, m2) :: rx1 else rx1))
  | _ :: rest => disj_sides2B bc rest b1 k1 n1
  end.
Lemma sub_itvB_split : forall bc b k n c m, (0 <= n < two64)%Z ->
  sub_itvB bc b k n c m = (if sub_quickB bc b k n c m then true else xinsideB bc b k (ELit n) (a_base c) (a_off c) m).
Proof.
  intros bc b k n c m Hn. unfold sub_itvB, sub_quickB.
  replace ((0 <=? n) && (n <? two64))%Z%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  reflexivity.
Qed.
Lemma disj_sides2B_eq : forall bc kn b1 k1 n1, (0 <= n1 < two64)%Z ->
  disj_sides2B bc kn b1 k1 n1 = (disj_sidesB bc kn b1 k1 n1, disj_sides_xB bc kn b1 k1 (ELit n1)).
Proof.
  intros bc kn b1 k1 n1 Hn. induction kn as [|K rest IH]; [reflexivity|].
  destruct K as [a w v|a l|a l bk|lo hi|e1 m|e' lo hi|a n|c1 m1 c2 m2|a l c|a l]; cbn [disj_sides2B disj_sidesB disj_sides_xB]; try exact IH.
  rewrite IH. unfold sub_itv_xB. rewrite !(sub_itvB_split bc b1 k1 n1) by exact Hn. reflexivity.
Qed.

(* [comment removed for export] *)
Local Open Scope Z_scope.
(* [comment removed for export] *)
Definition oshift (r : option (Z * Z)) (c : Z) : option (Z * Z) :=
  match r with Some (lo, hi) => Some (lo + c, hi + c) | None => None end.
Lemma lin_range_shift : forall rng c ts, lin_range rng c ts = oshift (lin_range rng 0 ts) c.
Proof.
  intros rng c ts. induction ts as [|[k a] rest IH]; cbn [lin_range].
  - cbn. reflexivity.
  - rewrite IH. destruct (rng a) as [[al ah]|]; [|reflexivity].
    destruct (lin_range rng 0 rest) as [[lo hi]|]; [|reflexivity].
    cbn [oshift]. destruct (Z.leb 0 k); cbn [oshift]; f_equal; f_equal; ring.
Qed.

(* [comment removed for export] *)
Definition trel (bc : bctx) (ts : list (Z * expr)) : option (Z * Z) :=
  match bc_fs bc with
  | [] => None
  | fs => match sum_subst fs ts 0 0 false with
          | (ts', (lo0, hi0), true) =>
              match lin_range (erangeB bc) 0 ts' with Some (lo, hi) => Some (lo + lo0, hi + hi0) | None => None end
          | _ => None
          end
  end.
Definition tprof : Type := (option (Z * Z) * option (Z * Z))%type.   (* [comment removed for export] *)
Definition mk_tprof (bc : bctx) (ts : list (Z * expr)) : tprof := (lin_range (erangeB bc) 0 ts, trel bc ts).
Definition lin_testP (p : tprof) (c : Z) (test : Z -> Z -> bool) : bool :=
  let relP := match snd p with Some (lo, hi) => test (lo + c) (hi + c) | None => false end in
  match fst p with
  | Some (lo, hi) => if test (lo + c) (hi + c) then true else relP
  | None => relP
  end.
Lemma lin_test_relB_prof : forall bc c ts test,
  lin_test_relB bc c ts test = match trel bc ts with Some (lo, hi) => test (lo + c) (hi + c) | None => false end.
Proof.
  intros. unfold lin_test_relB, trel. destruct (bc_fs bc) as [|f fs]; [reflexivity|].
  destruct (sum_subst (f :: fs) ts 0 0 false) as [[ts' [lo0 hi0]] [|]]; [|reflexivity].
  rewrite lin_range_shift. destruct (lin_range (erangeB bc) 0 ts') as [[lo hi]|]; cbn [oshift]; [|reflexivity].
  f_equal; lia.
Qed.
Lemma lin_testB_prof : forall bc c ts test, lin_testB bc c ts test = lin_testP (mk_tprof bc ts) c test.
Proof.
  intros. unfold lin_testB, lin_testP, mk_tprof. cbn [fst snd]. rewrite lin_range_shift, lin_test_relB_prof.
  destruct (lin_range (erangeB bc) 0 ts) as [[lo hi]|]; reflexivity.
Qed.

(* [comment removed for export] *)
Record gprof : Type := GP {
  g_p0 : tprof;                       (* [comment removed for export] *)
  g_c2 : Z; g_p2 : tprof;             (* [comment removed for export] *)
  g_hs2 : bool; g_c3 : Z; g_p3 : tprof;   (* [comment removed for export] *)
  g_sc_ok : bool; g_sc : Z; g_csc : Z; g_psc : tprof;   (* [comment removed for export] *)
  g_al : Z;                           (* [comment removed for export] *)
  g_hs : bool;                        (* [comment removed for export] *)
  g_c3a : Z; g_p3a : tprof;           (* [comment removed for export] *)
  g_c12a : Z; g_p12a : tprof          (* [comment removed for export] *)
}.
Definition sa_prof (bc : bctx) (ts : list (Z * expr)) (a : Z) : Z * tprof :=
  let sc := (2 ^ a)%Z in
  let ts' := List.map (fun t => ((sc * fst t)%Z, snd t)) ts in
  let '(c2, t2) := srl_expandB bc ts' in
  let '(c3, t3) := (if has_srl t2 then srl_expandB bc t2 else (0%Z, t2)) in
  ((c2 + c3)%Z, mk_tprof bc t3).
Definition mk_gprof (bc : bctx) (ts : list (Z * expr)) : gprof :=
  let '(c2, t2) := srl_expandB bc ts in
  let '(c3, t3) := srl_expandB bc t2 in
  let j := srl_scale_need ts in
  let sc_ok := (if Z.ltb 0 j then Z.leb j 24 else false) in
  let '(csc, psc) := (if sc_ok then sa_prof bc ts j else (0%Z, (None, None))) in
  let '(c3a, p3a) := sa_prof bc ts 3 in
  let '(c12a, p12a) := sa_prof bc ts 12 in
  GP (mk_tprof bc ts) c2 (mk_tprof bc t2) (has_srl t2) c3 (mk_tprof bc t3)
     sc_ok (2 ^ j)%Z csc psc (lin_alignB bc ts) (has_srl ts) c3a p3a c12a p12a.

Definition ge0_core (bc : bctx) (c : Z) (ts : list (Z * expr)) : bool :=
    if match lin_range (erangeB bc) c ts with Some (_, hi) => Z.ltb hi 0 | None => false end then false else
    let run := fun (ok : Z -> Z -> bool) =>
      if lin_testB bc c ts ok then true
      else let '(c2, t2) := srl_expandB bc ts in
           if lin_testB bc (c + c2)%Z t2 ok then true
           else if has_srl t2 then (let '(c3, t3) := srl_expandB bc t2 in lin_testB bc (c + c2 + c3)%Z t3 ok)
           else false in
    if run (fun lo _ => Z.leb 0 lo) then true
    else if lin_ge0_scaledB bc c ts then true
    else let j := lin_jB bc c ts in
         if (if Z.ltb 0 j then run (fun lo _ => Z.ltb (- 2 ^ j) lo) else false) then true
         else if has_srl ts then (if lin_ge0_saB bc c ts j 3 then true else lin_ge0_saB bc c ts j 12) else false.
Lemma lin_ge0B_core : forall bc pos neg,
  lin_ge0B bc pos neg = (xt_nowrapB bc pos && xt_nowrapB bc neg && ge0_core bc (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)))%bool.
Proof. reflexivity. Qed.

Definition ge0_coreP (g : gprof) (c : Z) : bool :=
    if match fst (g_p0 g) with Some (_, hi) => Z.ltb (hi + c) 0 | None => false end then false else
    let run := fun (ok : Z -> Z -> bool) =>
      if lin_testP (g_p0 g) c ok then true
      else if lin_testP (g_p2 g) (c + g_c2 g)%Z ok then true
      else if g_hs2 g then lin_testP (g_p3 g) (c + g_c2 g + g_c3 g)%Z ok else false in
    if run (fun lo _ => Z.leb 0 lo) then true
    else if (if g_sc_ok g then lin_testP (g_psc g) (g_sc g * c + g_csc g)%Z (fun lo _ => Z.leb 0 lo) else false) then true
    else let j := Z.max 0 (Z.min (zctz c) (g_al g)) in
         if (if Z.ltb 0 j then run (fun lo _ => Z.ltb (- 2 ^ j) lo) else false) then true
         else if g_hs g then (if lin_testP (g_p3a g) (2 ^ 3 * c + g_c3a g)%Z (fun lo _ => Z.ltb (- 2 ^ (3 + j)) lo) then true
                             else lin_testP (g_p12a g) (2 ^ 12 * c + g_c12a g)%Z (fun lo _ => Z.ltb (- 2 ^ (12 + j)) lo)) else false.

Lemma sa_prof_eq : forall bc c ts j a,
  lin_ge0_saB bc c ts j a = (let '(ca, pa) := sa_prof bc ts a in lin_testP pa (2 ^ a * c + ca)%Z (fun lo _ => Z.ltb (- 2 ^ (a + j)) lo)).
Proof.
  intros. unfold lin_ge0_saB, sa_prof.
  destruct (srl_expandB bc _) as [c2 t2]. destruct (if has_srl t2 then srl_expandB bc t2 else (0%Z, t2)) as [c3 t3].
  rewrite lin_testB_prof. f_equal. lia.
Qed.
Lemma scaled_prof_eq : forall bc c ts,
  lin_ge0_scaledB bc c ts =
  (let j := srl_scale_need ts in
   if (if Z.ltb 0 j then Z.leb j 24 else false) then (let '(ca, pa) := sa_prof bc ts j in lin_testP pa (2 ^ j * c + ca)%Z (fun lo _ => Z.leb 0 lo)) else false).
Proof.
  intros. unfold lin_ge0_scaledB, sa_prof.
  destruct (if (0 <? srl_scale_need ts)%Z then (srl_scale_need ts <=? 24)%Z else false); [|reflexivity].
  destruct (srl_expandB bc _) as [c2 t2]. destruct (if has_srl t2 then srl_expandB bc t2 else (0%Z, t2)) as [c3 t3].
  rewrite lin_testB_prof. f_equal. lia.
Qed.

Lemma ge0_coreP_eq : forall bc c ts, ge0_core bc c ts = ge0_coreP (mk_gprof bc ts) c.
Proof.
  intros. unfold ge0_core, ge0_coreP, mk_gprof, lin_jB.
  destruct (srl_expandB bc ts) as [c2 t2] eqn:E2. destruct (srl_expandB bc t2) as [c3 t3] eqn:E3.
  rewrite scaled_prof_eq. cbv zeta.
  destruct (if (0 <? srl_scale_need ts)%Z then (srl_scale_need ts <=? 24)%Z else false);
  destruct (sa_prof bc ts (srl_scale_need ts)) as [csc psc] eqn:ESC;
  rewrite !sa_prof_eq; destruct (sa_prof bc ts 3) as [c3a p3a]; destruct (sa_prof bc ts 12) as [c12a p12a];
  cbn [g_p0 g_c2 g_p2 g_hs2 g_c3 g_p3 g_sc_ok g_sc g_csc g_psc g_al g_hs g_c3a g_p3a g_c12a g_p12a fst snd];
  rewrite !lin_testB_prof; rewrite lin_range_shift; unfold mk_tprof; cbn [fst snd];
  (destruct (lin_range (erangeB bc) 0 ts) as [[lo0 hi0]|]; cbn [oshift fst snd]);
  rewrite ?(Z.mul_comm (2 ^ 3) c), ?(Z.mul_comm (2 ^ 12) c), ?(Z.mul_comm (2 ^ srl_scale_need ts) c); try reflexivity.
Qed.

(* [comment removed for export] *)
Record sprof : Type := SPF {
  pf_b1 : expr; pf_k1 : Z; pf_n1 : Z;
  pf_nw1 : bool;            (* [comment removed for export] *)
  pf_nw2 : bool;            (* [comment removed for export] *)
  pf_g1 : gprof;            (* [comment removed for export] *)
  pf_g2 : gprof;            (* [comment removed for export] *)
  pf_br : option (Z * Z);   (* [comment removed for export] *)
  pf_h1 : option Z          (* [comment removed for export] *)
}.
Definition mk_sprof (bc : bctx) (b1 : expr) (k1 n1 : Z) : sprof :=
  SPF b1 k1 n1 (xt_nowrapB bc [(b1, k1)]) (xt_nowrapB bc [(b1, k1); (ELit n1, 0%Z)])
      (mk_gprof bc (xt_lin [(b1, k1)])) (mk_gprof bc (lsub_e [] (xt_lin [(b1, k1)])))
      (base_rangeB bc b1) (xhiB bc (ELit n1)).
Definition xinside0PB (bc : bctx) (p : sprof) (zb ck zm : Z) : bool :=
  if (pf_nw1 p && xt_nowrapB bc [(ELit zb, ck)] &&
      ge0_coreP (pf_g1 p) (xt_const [(pf_b1 p, pf_k1 p)] - xt_const [(ELit zb, ck)]))%bool
  then (xt_nowrapB bc [(ELit zb, ck); (ELit zm, 0%Z)] && pf_nw2 p &&
        ge0_coreP (pf_g2 p) (xt_const [(ELit zb, ck); (ELit zm, 0%Z)] - xt_const [(pf_b1 p, pf_k1 p); (ELit (pf_n1 p), 0%Z)]))%bool
  else false.
Lemma xinside0PB_eq : forall bc b1 k1 n1 zb ck zm,
  xinside0PB bc (mk_sprof bc b1 k1 n1) zb ck zm = xinside0B bc b1 k1 (ELit n1) (ELit zb) ck (ELit zm).
Proof.
  intros. unfold xinside0B. rewrite !lin_ge0B_core. unfold xinside0PB, mk_sprof.
  cbn [pf_nw1 pf_nw2 pf_g1 pf_g2 pf_b1 pf_k1 pf_n1].
  rewrite <- !ge0_coreP_eq. reflexivity.
Qed.
Definition xinside_numPB (bc : bctx) (p : sprof) (zb ck zm : Z) : bool :=
  match xloB bc (ELit zb), xhiB bc (ELit zb) with
  | Some lo2, Some hi2 =>
      if Z.eqb lo2 hi2 then
        match pf_br p, pf_h1 p, xloB bc (ELit zm) with
        | Some (lo1, hi1), Some h1, Some l2 => Z.leb (lo2 + ck) (lo1 + pf_k1 p) && Z.leb (hi1 + pf_k1 p + h1) (lo2 + ck + l2)
        | _, _, _ => false
        end
      else false
  | _, _ => false
  end.
Definition xinsidePB (bc : bctx) (p : sprof) (cb : expr) (ck : Z) (m : expr) : bool :=
  match cb, m with
  | ELit zb, ELit zm => if xinside_numPB bc p zb ck zm then true else xinside0PB bc p zb ck zm
  | _, _ => xinsideB bc (pf_b1 p) (pf_k1 p) (ELit (pf_n1 p)) cb ck m
  end.
Lemma xinsidePB_eq : forall bc b1 k1 n1 cb ck m,
  xinsidePB bc (mk_sprof bc b1 k1 n1) cb ck m = xinsideB bc b1 k1 (ELit n1) cb ck m.
Proof.
  intros. unfold xinsidePB. destruct cb as [zb| | | | | | |]; try reflexivity. destruct m as [zm| | | | | | |]; try reflexivity.
  rewrite xinside0PB_eq. unfold xinsideB. cbn [shares_var novars]. unfold xinside_numPB, xinside_numB, mk_sprof.
  cbn [pf_br pf_h1 pf_k1]. reflexivity.
Qed.
(* [comment removed for export] *)
Fixpoint disj_sides2PB (bc : bctx) (kn : list kentry) (p : sprof) : list (saddr * expr) * list (saddr * expr) :=
  match kn with
  | [] => ([], [])
  | KDisj c1 m1 c2 m2 :: rest =>
      let '(r, rx) := disj_sides2PB bc rest p in
      let x2 := xinsidePB bc p (a_base c2) (a_off c2) m2 in
      let q2 := if sub_quickB bc (pf_b1 p) (pf_k1 p) (pf_n1 p) c2 m2 then true else x2 in
      let x1 := xinsidePB bc p (a_base c1) (a_off c1) m1 in
      let q1 := if sub_quickB bc (pf_b1 p) (pf_k1 p) (pf_n1 p) c1 m1 then true else x1 in
      let r1 := if q2 then (c1, m1) :: r else r in
      let rx1 := if x2 then (c1, m1) :: rx else rx in
      ((if q1 then (c2, m2) :: r1 else r1), (if x1 then (c2, m2) :: rx1 else rx1))
  | _ :: rest => disj_sides2PB bc rest p
  end.
Lemma disj_sides2PB_eq : forall bc kn b1 k1 n1, disj_sides2PB bc kn (mk_sprof bc b1 k1 n1) = disj_sides2B bc kn b1 k1 n1.
Proof.
  intros. induction kn as [|K rest IH]; [reflexivity|].
  destruct K as [a w v|a l|a l bk|lo hi|e1 m|e' lo hi|a n|c1 m1 c2 m2|a l c|a l]; cbn [disj_sides2PB disj_sides2B]; try exact IH.
  rewrite IH, !xinsidePB_eq. reflexivity.
Qed.
Local Close Scope Z_scope.

(* [comment removed for export] *)
Local Open Scope Z_scope.
(* [comment removed for export] *)
Definition mkey_eqb (c c' : saddr) (m m' : expr) : bool :=
  (expr_eqb (a_base c) (a_base c') && Z.eqb (a_off c) (a_off c') && expr_eqb m m')%bool.
Fixpoint memo_get (l : list (saddr * expr * bool)) (c : saddr) (m : expr) : option bool :=
  match l with
  | [] => None
  | (c', m', v) :: r => if mkey_eqb c c' m m' then Some v else memo_get r c m
  end.
Definition MOK (bc : bctx) (p : sprof) (l : list (saddr * expr * bool)) : Prop :=
  Forall (fun t => match t with (c, m, v) => v = xinsidePB bc p (a_base c) (a_off c) m end) l.
Lemma memo_get_ok : forall bc p l c m v, MOK bc p l -> memo_get l c m = Some v -> v = xinsidePB bc p (a_base c) (a_off c) m.
Proof.
  intros bc p l c m v HM. induction l as [|[[c' m'] v'] r IH]; cbn [memo_get]; intros H; [discriminate|].
  apply Forall_cons_iff in HM as [H1 HM].
  destruct (mkey_eqb c c' m m') eqn:E.
  - injection H as <-. unfold mkey_eqb in E. apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
    apply p_expr_eqb_eq in E1. apply Z.eqb_eq in E2. apply p_expr_eqb_eq in E3. subst m'. rewrite E1, E2. exact H1.
  - exact (IH HM H).
Qed.
Definition xinsideMB (bc : bctx) (p : sprof) (memo : list (saddr * expr * bool)) (c : saddr) (m : expr)
  : bool * list (saddr * expr * bool) :=
  if (shares_var (pf_b1 p) (a_base c) || novars (a_base c))%bool then   (* [comment removed for export] *)
    match memo_get memo c m with
    | Some v => (v, memo)
    | None => let v := xinsidePB bc p (a_base c) (a_off c) m in (v, (c, m, v) :: memo)
    end
  else (xinsidePB bc p (a_base c) (a_off c) m, memo).
Lemma xinsideMB_ok : forall bc p memo c m v memo',
  MOK bc p memo -> xinsideMB bc p memo c m = (v, memo') -> v = xinsidePB bc p (a_base c) (a_off c) m /\ MOK bc p memo'.
Proof.
  intros bc p memo c m v memo' HM H. unfold xinsideMB in H.
  destruct (shares_var (pf_b1 p) (a_base c) || novars (a_base c))%bool.
  - destruct (memo_get memo c m) as [v0|] eqn:HG.
    + injection H as <- <-. split; [exact (memo_get_ok _ _ _ _ _ _ HM HG) | exact HM].
    + injection H as <- <-. split; [reflexivity|]. constructor; [reflexivity | exact HM].
  - injection H as <- <-. split; [reflexivity | exact HM].
Qed.
Fixpoint disj_sides2MB (bc : bctx) (kn : list kentry) (p : sprof) (memo : list (saddr * expr * bool))
  : list (saddr * expr) * list (saddr * expr) * list (saddr * expr * bool) :=
  match kn with
  | [] => ([], [], memo)
  | KDisj c1 m1 c2 m2 :: rest =>
      let '(r, rx, mo) := disj_sides2MB bc rest p memo in
      let '(x2, mo2) := xinsideMB bc p mo c2 m2 in
      let q2 := if sub_quickB bc (pf_b1 p) (pf_k1 p) (pf_n1 p) c2 m2 then true else x2 in
      let '(x1, mo1) := xinsideMB bc p mo2 c1 m1 in
      let q1 := if sub_quickB bc (pf_b1 p) (pf_k1 p) (pf_n1 p) c1 m1 then true else x1 in
      let r1 := if q2 then (c1, m1) :: r else r in
      let rx1 := if x2 then (c1, m1) :: rx else rx in
      ((if q1 then (c2, m2) :: r1 else r1), (if x1 then (c2, m2) :: rx1 else rx1), mo1)
  | _ :: rest => disj_sides2MB bc rest p memo
  end.
Lemma disj_sides2MB_eq : forall bc kn p memo,
  MOK bc p memo ->
  let '(r, rx, mo) := disj_sides2MB bc kn p memo in (r, rx) = disj_sides2PB bc kn p /\ MOK bc p mo.
Proof.
  intros bc kn p memo HM. induction kn as [|K rest IH].
  - cbn. split; [reflexivity | exact HM].
  - destruct K as [a w v|a l|a l bk|lo hi|e1 m|e' lo hi|a n|c1 m1 c2 m2|a l c|a l]; cbn [disj_sides2MB disj_sides2PB]; try exact IH.
    destruct (disj_sides2MB bc rest p memo) as [[r rx] mo] eqn:ER. destruct IH as [IH1 IH2].
    destruct (xinsideMB bc p mo c2 m2) as [x2 mo2] eqn:E2.
    destruct (xinsideMB_ok _ _ _ _ _ _ _ IH2 E2) as [-> M2].
    destruct (xinsideMB bc p mo2 c1 m1) as [x1 mo1] eqn:E1.
    destruct (xinsideMB_ok _ _ _ _ _ _ _ M2 E1) as [-> M1].
    destruct (disj_sides2PB bc rest p) as [r' rx']. injection IH1 as <- <-. split; [reflexivity | exact M1].
Qed.
Definition disj_sides2M (bc : bctx) (kn : list kentry) (p : sprof) : list (saddr * expr) * list (saddr * expr) :=
  let '(r, rx, _) := disj_sides2MB bc kn p [] in (r, rx).
Lemma disj_sides2M_eq : forall bc kn p, disj_sides2M bc kn p = disj_sides2PB bc kn p.
Proof.
  intros. unfold disj_sides2M. pose proof (disj_sides2MB_eq bc kn p [] (Forall_nil _)) as H.
  destruct (disj_sides2MB bc kn p []) as [[r rx] mo]. destruct H as [H _]. exact H.
Qed.
Local Close Scope Z_scope.

(* [comment removed for export] *)
Local Open Scope Z_scope.
(* [comment removed for export] *)
Definition lin_ge0_plainB (bc : bctx) (pos neg : xterms) : bool :=
  (xt_nowrapB bc pos && xt_nowrapB bc neg &&
   match lin_range (erangeB bc) (xt_const pos - xt_const neg) (lsub_e (xt_lin pos) (xt_lin neg)) with
   | Some (lo, hi) => Z.leb 0 lo && Z.leb lo hi
   | None => false
   end)%bool.
Lemma lin_ge0_plain_sound : forall bc pos neg, lin_ge0_plainB bc pos neg = true -> lin_ge0B bc pos neg = true.
Proof.
  intros bc pos neg H. unfold lin_ge0_plainB in H. rewrite lin_ge0B_core.
  apply andb_prop in H as [H12 H3]. rewrite H12. cbn [andb]. unfold ge0_core.
  destruct (lin_range (erangeB bc) (xt_const pos - xt_const neg) (lsub_e (xt_lin pos) (xt_lin neg))) as [[lo hi]|] eqn:HR; [|discriminate].
  apply andb_prop in H3 as [H3 H4]. apply Z.leb_le in H3. apply Z.leb_le in H4.
  replace (hi <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  unfold lin_testB. rewrite HR. replace (0 <=? lo) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.
Definition xinside_plainB (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 : Z) (m : expr) : bool :=
  ((shares_var b1 b2 || novars b2) &&
   lin_ge0_plainB bc [(b1, k1)] [(b2, k2)] && lin_ge0_plainB bc [(b2, k2); (m, 0)] [(b1, k1); (ELit n1, 0)])%bool.
Lemma xinside_plain_sound : forall bc b1 k1 n1 b2 k2 m,
  xinside_plainB bc b1 k1 n1 b2 k2 m = true -> xinsideB bc b1 k1 (ELit n1) b2 k2 m = true.
Proof.
  intros bc b1 k1 n1 b2 k2 m H. unfold xinside_plainB in H.
  apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
  apply lin_ge0_plain_sound in H1. apply lin_ge0_plain_sound in H2.
  unfold xinsideB, xinside0B. rewrite H1, H2.
  destruct (shares_var b1 b2); [reflexivity|]. cbn [orb] in H0. rewrite H0. destruct (xinside_numB _ _ _ _ _ _ _); reflexivity.
Qed.
(* [comment removed for export] *)
Lemma snorm_small : forall n, 0 <= n < 2 ^ 63 -> snorm n = n.
Proof.
  intros n Hn. unfold snorm, mtwo63z, two63z.
  replace ((- 2 ^ 63 <=? n)%Z) with true by (symmetry; apply Z.leb_le; lia).
  replace ((n <? 2 ^ 63)%Z) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma lin_nowrapRB_lit : forall bc n, 0 <= n < 2 ^ 63 -> lin_nowrapRB bc (ELit n) = true.
Proof.
  intros bc n Hn. unfold lin_nowrapRB. cbn [lin_of fst snd srl_expandB]. rewrite (snorm_small n Hn).
  unfold lin_testB. cbn [lin_range].
  replace ((0 <=? n + 0) && (n + 0 <? two64))%Z%bool with true; [reflexivity|].
  symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; unfold two64; lia.
Qed.
(* [comment removed for export] *)
Lemma xt_nowrapB_1 : forall bc e a, xt_nowrapB bc [(e, a)] = (lin_nowrapRB bc e && true)%bool. Proof. reflexivity. Qed.
Lemma xt_nowrapB_2 : forall bc e a e' b, xt_nowrapB bc [(e, a); (e', b)] = (lin_nowrapRB bc e && (lin_nowrapRB bc e' && true))%bool. Proof. reflexivity. Qed.
Lemma xt_const_1 : forall e a, xt_const [(e, a)] = fst (lin_of e) + a + 0. Proof. reflexivity. Qed.
Lemma xt_const_2 : forall e a e' b, xt_const [(e, a); (e', b)] = fst (lin_of e) + a + (fst (lin_of e') + b + 0). Proof. reflexivity. Qed.
Lemma xt_lin_1 : forall e a, xt_lin [(e, a)] = xt_lin [(e, 0)]. Proof. reflexivity. Qed.
Lemma xt_lin_2 : forall e a e' b, xt_lin [(e, a); (e', b)] = xt_lin [(e, 0); (e', 0)]. Proof. reflexivity. Qed.
Lemma xt_lin_lit2 : forall e a n, xt_lin [(e, a); (ELit n, 0)] = xt_lin [(e, 0)]. Proof. reflexivity. Qed.
Lemma fst_lin_of_lit : forall n, fst (lin_of (ELit n)) = snorm n. Proof. reflexivity. Qed.
Lemma xinside_plain_mono : forall bc b1 glo gn b2 k2 m k n,
  xinside_plainB bc b1 glo gn b2 k2 m = true ->
  0 <= gn < 2 ^ 63 -> glo <= k -> 0 <= n -> k + n <= glo + gn ->
  xinside_plainB bc b1 k n b2 k2 m = true.
Proof.
  intros bc b1 glo gn b2 k2 m k n H Hgn Hk Hn Hkn. unfold xinside_plainB in H |- *.
  apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1]. rewrite H0. cbn [andb].
  unfold lin_ge0_plainB in H1, H2 |- *.
  rewrite ?xt_nowrapB_1, ?xt_nowrapB_2, ?xt_const_1, ?xt_const_2 in H1. rewrite ?xt_nowrapB_1, ?xt_nowrapB_2, ?xt_const_1, ?xt_const_2 in H2. rewrite ?xt_nowrapB_1, ?xt_nowrapB_2, ?xt_const_1, ?xt_const_2.
  rewrite (xt_lin_1 b1 glo), (xt_lin_1 b2 k2) in H1. rewrite (xt_lin_1 b1 k), (xt_lin_1 b2 k2).
  rewrite (xt_lin_2 b2 k2 m 0), (xt_lin_lit2 b1 glo gn) in H2. rewrite (xt_lin_2 b2 k2 m 0), (xt_lin_lit2 b1 k n).
  rewrite ?fst_lin_of_lit in H2. rewrite ?fst_lin_of_lit.
  assert (Hn63 : 0 <= n < 2 ^ 63) by lia.
  rewrite (snorm_small gn Hgn) in H2. rewrite (snorm_small n Hn63).
  apply andb_prop in H1 as [N1 R1]. apply andb_prop in H2 as [N2 R2].
  apply andb_prop in N2 as [N2a N2b]. apply andb_prop in N2b as [N2b N2c].
  rewrite N1, N2a, N2b, (lin_nowrapRB_lit bc n Hn63). cbn [andb].
  rewrite lin_range_shift in R1. rewrite lin_range_shift in R2.
  rewrite (lin_range_shift (erangeB bc) (fst (lin_of b1) + k + 0 - (fst (lin_of b2) + k2 + 0))).
  rewrite (lin_range_shift (erangeB bc) (fst (lin_of b2) + k2 + (fst (lin_of m) + 0 + 0) - (fst (lin_of b1) + k + (n + 0 + 0)))).
  destruct (lin_range (erangeB bc) 0 (lsub_e (xt_lin [(b1, 0)]) (xt_lin [(b2, 0)]))) as [[L1 U1]|]; [|discriminate].
  destruct (lin_range (erangeB bc) 0 (lsub_e (xt_lin [(b2, 0); (m, 0)]) (xt_lin [(b1, 0)]))) as [[L2 U2]|]; [|discriminate].
  cbn [oshift] in R1, R2 |- *.
  apply andb_prop in R1 as [A1 B1]. apply andb_prop in R2 as [A2 B2].
  apply Z.leb_le in A1. apply Z.leb_le in B1. apply Z.leb_le in A2. apply Z.leb_le in B2.
  apply andb_true_intro; split; apply andb_true_intro; split; apply Z.leb_le; lia.
Qed.

Local Close Scope Z_scope.

Fixpoint in_sidesB (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itvB bc b2 k2 n2 c m then true else in_sidesB bc r b2 k2 n2
  end.

(* [comment removed for export] *)
Fixpoint in_sides_q (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
  match D with
  | [] => false
  | (c, m) :: r =>
      if (if (expr_eqb b2 (a_base c) && Z.leb (a_off c) k2)%bool then
            match xloB bc m with Some ml => Z.leb (k2 + n2) (a_off c + ml) | None => false end
          else false)
      then true else in_sides_q bc r b2 k2 n2
  end.
Definition in_sidesQ (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
  if in_sides_q bc D b2 k2 n2 then true else in_sidesB bc D b2 k2 n2.
Lemma in_sidesQ_eqB : in_sidesQ = in_sidesB.
Proof.
  apply functional_extensionality; intros bc. apply functional_extensionality; intros D.
  apply functional_extensionality; intros b2. apply functional_extensionality; intros k2.
  apply functional_extensionality; intros n2. unfold in_sidesQ.
  induction D as [|[c m] r IH]; [reflexivity|].
  cbn [in_sides_q in_sidesB].
  lazymatch goal with |- (if (if ?q then true else _) then true else _) = _ =>
    destruct q eqn:Hq end.
  - assert (Hs : sub_itvB bc b2 k2 n2 c m = true) by (unfold sub_itvB; rewrite Hq; reflexivity).
    rewrite Hs. reflexivity.
  - destruct (sub_itvB bc b2 k2 n2 c m); [destruct (in_sides_q bc r b2 k2 n2); reflexivity|]. exact IH.
Qed.
#[export] Hint Rewrite in_sidesQ_eqB : bceq.

(* [comment removed for export] *)
Record qix : Type := QX { qx_vars : list (list (saddr * Z)); qx_other : list (saddr * Z) }.
Definition qix_empty : qix := QX [] [].
Definition qx_bucket (q : qix) (k : option nat) : list (saddr * Z) :=
  match k with Some n => lget (qx_vars q) n | None => qx_other q end.
Definition qx_add (k : option nat) (x : saddr * Z) (q : qix) : qix :=
  match k with Some n => QX (lset (qx_vars q) n x) (qx_other q) | None => QX (qx_vars q) (x :: qx_other q) end.
Fixpoint mk_qix (bc : bctx) (D : list (saddr * expr)) : qix :=
  match D with
  | [] => qix_empty
  | (c, m) :: r =>
      let q := mk_qix bc r in
      match xloB bc m with Some ml => qx_add (fvar (a_base c)) (c, ml) q | None => q end
  end.
Fixpoint qsides_hit (l : list (saddr * Z)) (b2 : expr) (k2 n2 : Z) : bool :=
  match l with
  | [] => false
  | (c, ml) :: r =>
      if (if (Z.leb (a_off c) k2 && Z.leb (k2 + n2) (a_off c + ml))%bool then expr_eqb b2 (a_base c) else false)
      then true else qsides_hit r b2 k2 n2
  end.
Definition qix_hit (q : qix) (b2 : expr) (k2 n2 : Z) : bool := qsides_hit (qx_bucket q (fvar b2)) b2 k2 n2.

Lemma qx_bucket_add : forall k x q k', qx_bucket (qx_add k x q) k' = if okeq k' k then x :: qx_bucket q k' else qx_bucket q k'.
Proof. intros [n|] x q [m|]; cbn [qx_add qx_bucket qx_vars qx_other okeq]; try reflexivity. apply lget_lset. Qed.
Lemma qx_bucket_empty : forall k, qx_bucket qix_empty k = [].
Proof. intros [n|]; cbn; [unfold lget; destruct n; reflexivity | reflexivity]. Qed.
Lemma okeq_spec : forall a b, reflect (a = b) (okeq a b).
Proof.
  intros [x|] [y|]; cbn; try (constructor; congruence).
  destruct (Nat.eqb_spec x y); constructor; congruence.
Qed.
Lemma qix_hit_in_sidesB : forall bc D b2 k2 n2, qix_hit (mk_qix bc D) b2 k2 n2 = true -> in_sidesB bc D b2 k2 n2 = true.
Proof.
  intros bc D b2 k2 n2. unfold qix_hit. induction D as [|[c m] r IH]; intros H.
  - cbn [mk_qix] in H. rewrite qx_bucket_empty in H. cbn in H. discriminate.
  - cbn [mk_qix] in H. cbn [in_sidesB].
    destruct (xloB bc m) as [ml|] eqn:Hml.
    + rewrite qx_bucket_add in H. destruct (okeq_spec (fvar b2) (fvar (a_base c))) as [EQ|NE].
      * cbn [qsides_hit] in H.
        destruct ((a_off c <=? k2)%Z && (k2 + n2 <=? a_off c + ml)%Z)%bool eqn:Hoff.
        -- destruct (expr_eqb b2 (a_base c)) eqn:Heq.
           ++ assert (Hs : sub_itvB bc b2 k2 n2 c m = true).
              { unfold sub_itvB. rewrite Heq. apply andb_prop in Hoff as [H1 H2]. rewrite H1. cbn [andb]. rewrite Hml, H2. reflexivity. }
              rewrite Hs. reflexivity.
           ++ rewrite (IH H). destruct (sub_itvB bc b2 k2 n2 c m); reflexivity.
        -- rewrite (IH H). destruct (sub_itvB bc b2 k2 n2 c m); reflexivity.
      * rewrite (IH H). destruct (sub_itvB bc b2 k2 n2 c m); reflexivity.
    + rewrite (IH H). destruct (sub_itvB bc b2 k2 n2 c m); reflexivity.
Qed.

Fixpoint in_sides_xB (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv_xB bc b2 k2 n2 c m then true else in_sides_xB bc r b2 k2 n2
  end.

Definition mk_sprepB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) : sprep :=
  match n1 with
  | ELit z1 =>
      if (Z.leb 0 z1 && Z.ltb z1 two64)%bool then   (* [comment removed for export] *)
        let '(D, Dx) := disj_sides2M bc (bc_fk bc) (mk_sprof bc b1 k1 z1) in SPrep (base_rangeB bc b1) (xhiB bc n1) D Dx   (* [comment removed for export] *)
      else SPrep (base_rangeB bc b1) (xhiB bc n1) (disj_sidesB bc (bc_fk bc) b1 k1 (zlit64 z1)) (disj_sides_xB bc (bc_fk bc) b1 k1 n1)
  | _ => SPrep (base_rangeB bc b1) (xhiB bc n1) [] (disj_sides_xB bc (bc_fk bc) b1 k1 n1)
  end.

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
      else if in_sidesQ bc (sp_D sp) b2 k2 m2 then true   (* [comment removed for export] *)
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
Proof. intros. bcfe. unfold lin_test_relB, lin_test_rel. autorewrite with bceq. reflexivity. Qed.
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
Lemma lin_brangeB_eqf : forall fk, lin_brangeB (mkbc fk) = lin_brange fk.
Proof. intros. bcfe. unfold lin_brangeB, lin_brange. autorewrite with bceq. reflexivity. Qed.
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
Lemma lin_alignB_eqf : forall fk, lin_alignB (mkbc fk) = lin_align fk.
Proof. intros. apply functional_extensionality. intros ts. induction ts as [|[k a] r IH]; cbn [lin_alignB lin_align]; [reflexivity|]. rewrite ealignB_eqf, IH. reflexivity. Qed.
#[export] Hint Rewrite lin_alignB_eqf : bceq.
Lemma lin_jB_eqf : forall fk, lin_jB (mkbc fk) = lin_j fk.
Proof. intros. bcfe. unfold lin_jB, lin_j. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_jB_eqf : bceq.
Lemma lin_ge0_saB_eqf : forall fk, lin_ge0_saB (mkbc fk) = lin_ge0_sa fk.
Proof. intros. bcfe. unfold lin_ge0_saB, lin_ge0_sa. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_ge0_saB_eqf : bceq.
Lemma lin_ge0B_eqf : forall fk, lin_ge0B (mkbc fk) = lin_ge0 fk.
Proof. intros. bcfe. unfold lin_ge0B, lin_ge0. autorewrite with bceq. reflexivity. Qed.
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
  cbn [kdisj_apartB kdisj_apart]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite kdisj_apartB_eqf : bceq.
Lemma ranges_apartB_eqf : forall fk, ranges_apartB (mkbc fk) = ranges_apart fk.
Proof.
  intros. bcfe. unfold ranges_apartB, ranges_apart. autorewrite with bceq.
  lazymatch goal with |- (if ?m then true else _) = _ => destruct m; [reflexivity|] end.
  destruct (kdisj_apart _ _ _ _ _ _ _ _), (lin_apart _ _ _ _ _ _ _); reflexivity.   (* [comment removed for export] *)
Qed.
#[export] Hint Rewrite ranges_apartB_eqf : bceq.
Lemma sub_itv_xB_eqf : forall fk, sub_itv_xB (mkbc fk) = sub_itv_x fk.
Proof. intros. bcfe. unfold sub_itv_xB, sub_itv_x. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite sub_itv_xB_eqf : bceq.
Lemma kdisj_apart_xB_eqf : forall fk, kdisj_apart_xB (mkbc fk) = kdisj_apart_x fk.
Proof.
  intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2. 
  revert b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kdisj_apart_xB kdisj_apart_x]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite kdisj_apart_xB_eqf : bceq.
Lemma end_hiB_eqf : forall fk, end_hiB (mkbc fk) = end_hi fk.
Proof. intros. bcfe. unfold end_hiB, end_hi. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite end_hiB_eqf : bceq.
Lemma ranges_apart_xB_eqf : forall fk, ranges_apart_xB (mkbc fk) = ranges_apart_x fk.
Proof.
  intros fk. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1.
  apply functional_extensionality; intros n1. apply functional_extensionality; intros b2.
  apply functional_extensionality; intros k2. apply functional_extensionality; intros n2.
  unfold ranges_apart_xB, ranges_apart_x. autorewrite with bceq.
  destruct n1, n2; try reflexivity;
  (lazymatch goal with |- (if ?m then true else _) = _ => destruct m; [reflexivity|] end;
   destruct (kdisj_apart_x _ _ _ _ _ _ _ _), (shares_var _ _); cbn [negb]; try reflexivity;
   destruct (lin_ge0 _ _ _); try reflexivity; destruct (lin_ge0 _ _ _); reflexivity).   (* [comment removed for export] *)
Qed.
#[export] Hint Rewrite ranges_apart_xB_eqf : bceq.
Lemma disj_sidesB_eqf : forall fk, disj_sidesB (mkbc fk) = disj_sides fk.
Proof.
  intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1. 
  revert b1 k1 n1. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [disj_sidesB disj_sides]. rewrite IH. autorewrite with bceq. reflexivity.
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
Proof.
  intros. bcfe. unfold mk_sprepB, mk_sprep.
  lazymatch goal with |- _ = SPrep _ _ (match ?n1 with _ => _ end) _ =>
    destruct n1 as [z1| | | | | | |]; try (autorewrite with bceq; reflexivity) end.
  destruct ((0 <=? z1) && (z1 <? two64))%Z%bool eqn:Hz; [|autorewrite with bceq; reflexivity].
  assert (Hn : (0 <= z1 < two64)%Z).
  { apply andb_prop in Hz as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. }
  rewrite disj_sides2M_eq, disj_sides2PB_eq, (disj_sides2B_eq _ _ _ _ _ Hn).
  replace (zlit64 z1) with z1 by (unfold zlit64; rewrite Hz; reflexivity).
  autorewrite with bceq. reflexivity.
Qed.   (* [comment removed for export] *)
#[export] Hint Rewrite mk_sprepB_eqf : bceq.
Lemma ranges_apart_pB_eqf : forall fk, ranges_apart_pB (mkbc fk) = ranges_apart_p fk.
Proof. intros. bcfe. unfold ranges_apart_pB, ranges_apart_p. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite ranges_apart_pB_eqf : bceq.

(* [comment removed for export] *)
Definition ranges_apart_pqB (bc : bctx) (sp : sprep) (q : qix) (b1 : expr) (k1 : Z) (n1 : expr)
           (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit _, ELit z2 => if qix_hit q b2 k2 (zlit64 z2) then true else ranges_apart_pB bc sp b1 k1 n1 b2 k2 n2
  | _, _ => ranges_apart_pB bc sp b1 k1 n1 b2 k2 n2
  end.
Lemma ranges_apart_pqB_eq : forall bc sp, ranges_apart_pqB bc sp (mk_qix bc (sp_D sp)) = ranges_apart_pB bc sp.
Proof.
  intros bc sp. bcfe. unfold ranges_apart_pqB.
  lazymatch goal with |- _ = ranges_apart_pB _ _ ?b1 ?k1 ?n1 ?b2 ?k2 ?n2 =>
    destruct n1 as [z1| | | | | | |]; try reflexivity; destruct n2 as [z2| | | | | | |]; try reflexivity;
    destruct (qix_hit (mk_qix bc (sp_D sp)) b2 k2 (zlit64 z2)) eqn:Hq; [|reflexivity];
    apply qix_hit_in_sidesB in Hq; unfold ranges_apart_pB; rewrite in_sidesQ_eqB, Hq
  end.
  lazymatch goal with |- true = (if ?c then true else true) => destruct c; reflexivity end.
Qed.

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

Definition mkSrlB (bc : bctx) (a : expr) (s : Z) : expr :=
  let l := lin_of a in
  let m := (2 ^ s)%Z in
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
    end.

Fixpoint lowbitsB (bc : bctx) (e : expr) (j : Z) {struct e} : option Z :=
  let m := (2 ^ j)%Z in
  let dflt := if Z.leb j (ealignB bc e) then Some 0%Z else lin_lowbits_knB bc e j in
  match e with
  | ELit z => Some ((z mod two64) mod m)%Z
  | EAlu ALU_AND a (ELit c) =>
      if Z.eqb ((c mod two64) mod m) 0 then Some 0%Z else
      match lowbitsB bc a j with Some v => Some (Z.land v ((c mod two64) mod m)) | None => dflt end
  | EAlu ALU_OR a (ELit c) =>
      match lowbitsB bc a j with Some v => Some (Z.lor v ((c mod two64) mod m)) | None => dflt end
  | EAlu ALU_XOR a (ELit c) =>
      match lowbitsB bc a j with Some v => Some (Z.lxor v ((c mod two64) mod m)) | None => dflt end
  | EAlu ALU_ADD a b =>
      match lowbitsB bc a j, lowbitsB bc b j with Some x, Some y => Some ((x + y) mod m)%Z | _, _ => dflt end
  | EAlu ALU_SUB a b =>
      match lowbitsB bc a j, lowbitsB bc b j with Some x, Some y => Some ((x - y) mod m)%Z | _, _ => dflt end
  | EMd M_MUL (ELit c) a =>
      if Z.eqb ((c mod two64) mod m) 0 then Some 0%Z else
      match lowbitsB bc a j with Some v => Some ((c * v) mod m)%Z | None => dflt end
  | _ => dflt
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

Fixpoint conc_tryB (bc : bctx) (e : expr) (cands : list expr) : option Z :=
  match cands with
  | [] => None
  | s :: rest =>
      if closedb s then conc_tryB bc e rest else
      if negb (evalS_def s e) then conc_tryB bc e rest else
      match erangeB bc s with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            match evalS s (wrap64 lo) e with
            | Some v =>
                if (if Z.ltb hi lo then true
                     else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2)%Z else false) then
                  if all_eval_toS s e v lo (Z.to_nat (hi - lo + 1)) then Some v
                  else conc_tryB bc e rest
                else conc_tryB bc e rest
            | None => conc_tryB bc e rest
            end
          else conc_tryB bc e rest
      | None => conc_tryB bc e rest
      end
  end.

Definition concretizeB (bc : bctx) (e : expr) : option Z :=
  if closedb e then eval_closed e else conc_tryB bc e (nubE (subexprs e)).

Definition foldKB (bc : bctx) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match erangeB bc e with
         | Some (lo, hi) => if Z.eqb lo hi then ELit lo
                            else match concretizeB bc e with Some v => ELit v | None => e end
         | None => match concretizeB bc e with Some v => ELit v | None => e end   (* [comment removed for export] *)
         end
  end.

Definition lin_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
  let ltu := if lin_ge0B bc [(b, (-1)%Z)] [(a, 0%Z)] then Some true
             else if lin_ge0B bc [(a, 0%Z)] [(b, 0%Z)] then Some false else None in
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
  | ELit x, ELit y => Some (lit_branch c x y)
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

Definition mkAluwK0B (bc : bctx) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_ADD | ALU_SUB =>
      let d := mkAlu op a b in
      match is_lit d with
      | Some v => ELit (zsx32 v)
      | None => match erangeB bc d with
                | Some (lo, hi) => if sx32_stable lo hi then d else if zband32B bc d then d else mkAluw op a b
                | None => if zband32B bc d then d else mkAluw op a b
                end
      end
  | _ => mkAluw op a b
  end.

Definition mkAluwKB (bc : bctx) (op : aluop) (a b : expr) : expr :=
  foldKB bc (mkAluwK0B bc op a b).

Definition extK0B (bc : bctx) (v : expr) : expr :=
  match v with
  | EExt sx O n e =>
      if Nat.leb n 7 then
        match erangeB bc e with
        | Some (lo, hi) => if Z.ltb hi (if sx then 2 ^ (8 * Z.of_nat n) / 2 else 2 ^ (8 * Z.of_nat n)) then e else v
        | None => v
        end
      else v
  | _ => v
  end.

Definition extKB (bc : bctx) (v : expr) : expr := foldKB bc (extK0B bc v).

Definition flat_scB (bc : bctx) (a : saddr) (n : nat) : list sidecond :=
  match base_rangeB bc (a_base a) with
  | Some (lo, hi) =>
      if (Z.leb 0 (lo + a_off a) && Z.leb (hi + a_off a + Z.of_nat n) (2 ^ 64))%bool
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

Fixpoint log_lookupB (bc : bctx) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupB bc rest rb rk n sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          if ranges_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w)
          then log_lookupB bc rest rb rk n sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupB bc rest rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
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

Definition sym_readB (segs : list Segment) (ss : sym_state) (bc : bctx) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match log_lookupB bc (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
  | LStuck => None
  | LHit v scs hints =>
      Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookupAB bc segs (ksel (a_base a) (s_know ss)) (a_base a) (a_off a) n sx' hints scs with   (* [comment removed for export] *)
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extKB bc v, flat_scB bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
      | LMiss scs' hints' =>
          (* [comment removed for export] *)
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
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
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
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
  kx_wf : rindex                                    (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition kwkey (K : kentry) : option nat := match kskey K with Some k => k | None => None end.
Definition wx_add (key : option nat) (K : kentry) (t : rindex) : rindex :=
  match key with Some n => RI (lset (ri_vars t) n K) (ri_other t) | None => RI (ri_vars t) (K :: ri_other t) end.
Lemma ri_bucket_wadd : forall key K t k,
  ri_bucket (wx_add key K t) k = if okeq k key then K :: ri_bucket t k else ri_bucket t k.
Proof. intros [n|] K t [m|]; cbn [wx_add ri_bucket ri_vars ri_other okeq]; try reflexivity. apply lget_lset. Qed.
Lemma ksel_test_key : forall K k, kx_candf K = true -> ksel_test k K = okeq k (kwkey K).
Proof.
  intros K k H. destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
    cbn in H |- *; try reflexivity; discriminate.
Qed.
Lemma ksel_notlit0 : forall rb kn, is_lit0 rb = false -> ksel rb kn = ksel_by (fvar rb) kn.
Proof. intros rb kn H. destruct rb as [z| | | | | | |]; try reflexivity. destruct z; [discriminate|reflexivity|reflexivity]. Qed.
Lemma filter_andb : forall (A : Type) (P Q : A -> bool) l,
  List.filter (fun x => P x && Q x) l = List.filter P (List.filter Q l).
Proof.
  intros A P Q l. induction l as [|x r IH]; [reflexivity|]. cbn [List.filter]. rewrite IH.
  destruct (Q x); cbn [andb List.filter]; destruct (P x); reflexivity.
Qed.
Definition kx_bucket (t : ptree (list (positive * kentry))) (g : Z) : list (positive * kentry) :=
  match pt_get t (kx_gkey g) with Some b => b | None => [] end.
Definition kx_add (g : Z) (x : positive * kentry) (t : ptree (list (positive * kentry))) : ptree (list (positive * kentry)) :=
  pt_set (kx_gkey g) (x :: kx_bucket t g) t.
Fixpoint kx_build (kn : list kentry) (i : positive) : list (positive * kentry) * ptree (list (positive * kentry)) * rindex :=
  match kn with
  | [] => ([], PTLeaf, RI [] [])
  | K :: rest =>
      let '(w0, gr, wf) := kx_build rest (Pos.succ i) in
      let wf' := if kx_candf K then wx_add (kwkey K) K wf else wf in   (* [comment removed for export] *)
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
  else ri_bucket (kx_wf kx) (fvar rb).   (* [comment removed for export] *)

Definition know_lookupA0I (bc : bctx) (kx : kix) (segs : list Segment) (rb : expr) (rk : Z)
           (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match hints, n with
  | [], S _ => know_lookupA0B bc segs (kx_select kx rb rk) rb rk n sx [] acc
  | _, _ => know_lookupA0B bc segs (ksel rb (kx_kn kx)) rb rk n sx hints acc   (* [comment removed for export] *)
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
Proof. intros. unfold rel_lit. rewrite kx_expr_eqb_refl. reflexivity. Qed.

Lemma rel_lit_other : forall rb rk rn kb kk kl,
  expr_eqb rb kb = false -> rel_lit rb rk rn kb kk kl = RUnknown.
Proof. intros rb rk rn kb kk kl H. unfold rel_lit. rewrite H. reflexivity. Qed.

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

Lemma kx_merge_nil_l : forall l2, kx_merge [] l2 = List.map snd l2.
Proof. reflexivity. Qed.
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
  destruct (ext_fits s e); cbn [negb orb]; [rewrite Bool.orb_false_r|]; reflexivity.
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
  /\ (forall k, ri_bucket wf k = List.filter (fun K => kx_candf K && ksel_test k K) kn).   (* [comment removed for export] *)
Proof.
  induction kn as [|K rest IH]; intros i w0 gr wf H.
  - cbn in H. injection H as <- <- <-. split; [reflexivity|]. split; [intros g; rewrite kx_bucket_leaf; reflexivity |].
    intros [n|]; cbn; [unfold lget; destruct n; reflexivity | reflexivity].
  - cbn [kx_build] in H. destruct (kx_build rest (Pos.succ i)) as [[w0' gr'] wf'] eqn:Hb.
    destruct (IH (Pos.succ i) w0' gr' wf' Hb) as (A & B & C). clear IH.
    assert (CW : forall k, ri_bucket (if kx_candf K then wx_add (kwkey K) K wf' else wf') k
                           = List.filter (fun K0 => kx_candf K0 && ksel_test k K0) (K :: rest)).
    { intros k. cbn [List.filter]. destruct (kx_candf K) eqn:HCf; cbn [andb].
      - rewrite ri_bucket_wadd, !C, (ksel_test_key K k HCf). reflexivity.
      - apply C. }
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
        injection H as <- <- <-. rewrite WD. cbn [negb]. split; [exact A|]. split; [|exact CW].
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
        injection H as <- <- <-. rewrite WD. cbn [negb]. split; [rewrite A; reflexivity|]. split; [|exact CW].
        intros g. rewrite NW, B. reflexivity.
    + clear WD. destruct (kx_wide0 K); injection H as <- <- <-.
      * split; [rewrite A; reflexivity|]. split; [|exact CW]. intros g. rewrite NW, B. reflexivity.
      * split; [exact A|]. split; [|exact CW]. intros g. rewrite NW, B. reflexivity.
Qed.

Lemma kx_select_eq : forall kn rb rk,
  kx_select (mk_kix kn) rb rk = if is_lit0 rb then List.filter (kx_cand0 (gran rk)) kn
                                else List.filter (fun K => kx_candf K && ksel_test (fvar rb) K) kn.   (* [comment removed for export] *)
Proof.
  intros kn rb rk. unfold kx_select, mk_kix.
  destruct (kx_build kn 1%positive) as [[w0 gr] wf] eqn:Hb. cbn [kx_gran kx_w0 kx_wf fst snd].
  destruct (kx_build_spec kn 1%positive w0 gr wf Hb) as (A & B & C).
  destruct (is_lit0 rb); [|apply C].
  rewrite B, A. rewrite (kx_merge_filters (narrow_in (gran rk)) kx_wide0 kn 1%positive (narrow_not_wide (gran rk))).
  apply filter_ext. intros K. symmetry. apply kx_cand0_split.
Qed.

Theorem know_lookupA0I_eq : forall bc kn segs rb rk n sx hints acc,
  know_lookupA0I bc (mk_kix kn) segs rb rk n sx hints acc = know_lookupA0B bc segs (ksel rb kn) rb rk n sx hints acc.   (* [comment removed for export] *)
Proof.
  intros bc kn segs rb rk n sx hints acc. unfold know_lookupA0I.
  destruct hints as [|h hs]; [|reflexivity]. destruct n as [|n]; [reflexivity|].
  rewrite kx_select_eq. destruct (is_lit0 rb) eqn:L.
  - apply is_lit0_true in L. subst rb. apply know_lookupA0B_filter0.
  - rewrite (ksel_notlit0 rb kn L). unfold ksel_by. rewrite (filter_andb _ kx_candf (ksel_test (fvar rb))).
    apply know_lookupA0B_filterf. exact L.
Qed.

(* [comment removed for export] *)
Definition know_lookupABI (bc : bctx) (kx : kix) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match know_lookupA0I bc kx segs rb rk n sx hints acc with
  | LMiss acc' hints' =>
      match know_bytes_lit segs (ksel rb kn) rb rk n with   (* [comment removed for export] *)
      | Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
      | None => LMiss acc' hints'
      end
  | r => r
  end.
Lemma know_lookupABI_eq : forall bc kn segs rb,
  know_lookupABI bc (mk_kix kn) segs kn rb = know_lookupAB bc segs (ksel rb kn) rb.   (* [comment removed for export] *)
Proof.
  intros bc kn segs rb. bcfe. unfold know_lookupABI, know_lookupAB. rewrite know_lookupA0I_eq. reflexivity.
Qed.
Local Close Scope Z_scope.

(* [comment removed for export] *)
Definition ranges_apart_cB (bc : bctx) (br1 : option (Z * Z)) (b1 : expr) (k1 n1 : Z) (br2 : option (Z * Z)) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match br1, br2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
      | _, _ => false
      end) then true
  else if lin_apartB bc b1 k1 n1 b2 k2 n2 then true
  else kdisj_apartB bc (bc_fk bc) b1 k1 n1 b2 k2 n2.
Lemma ranges_apart_cB_eq : forall bc b1 k1 n1 b2 k2 n2,
  ranges_apart_cB bc (base_rangeB bc b1) b1 k1 n1 (base_rangeB bc b2) b2 k2 n2 = ranges_apartB bc b1 k1 n1 b2 k2 n2.
Proof. reflexivity. Qed.
Fixpoint log_lookupCB (bc : bctx) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) (br1 : option (Z * Z)) (cb : expr) (cr : option (Z * Z)) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupCB bc rest rb rk n sx hints acc br1 cb cr
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          let cr' := if expr_eqb kb cb then cr else base_rangeB bc kb in
          if ranges_apart_cB bc br1 rb rk (Z.of_nat n) cr' kb kk (Z.of_nat w)
          then log_lookupCB bc rest rb rk n sx hints acc br1 kb cr'
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupCB bc rest rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc) br1 kb cr'
          end
      end
  end.
Lemma log_lookupCB_eq : forall bc log rb rk n sx hints acc cb cr,
  cr = base_rangeB bc cb ->
  log_lookupCB bc log rb rk n sx hints acc (base_rangeB bc rb) cb cr = log_lookupB bc log rb rk n sx hints acc.
Proof.
  intros bc log rb rk n sx. induction log as [|[[kb kk] w v] rest IH]; intros hints acc cb cr Hcr; [reflexivity|].
  cbn [log_lookupCB log_lookupB].
  destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)); try reflexivity; [apply IH; exact Hcr|].
  assert (Hcr' : (if expr_eqb kb cb then cr else base_rangeB bc kb) = base_rangeB bc kb).
  { destruct (expr_eqb kb cb) eqn:E; [|reflexivity]. apply p_expr_eqb_eq in E. subst cb. exact Hcr. }
  rewrite Hcr', ranges_apart_cB_eq.
  destruct (ranges_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w)); [apply IH; reflexivity|].
  destruct hints as [|[|] hs]; cbn [tl]; try reflexivity; apply IH; reflexivity.
Qed.

(* [comment removed for export] *)
Local Open Scope Z_scope.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dqe : Type := (saddr * Z * saddr * option Z)%type.   (* [comment removed for export] *)
Record dqix : Type := DQ { dq_vars : list (list dqe); dq_other : list dqe }.
Definition dq_bucket (q : dqix) (k : option nat) : list dqe := match k with Some n => lget (dq_vars q) n | None => dq_other q end.
Definition dq_add (k : option nat) (x : dqe) (q : dqix) : dqix :=
  match k with Some n => DQ (lset (dq_vars q) n x) (dq_other q) | None => DQ (dq_vars q) (x :: dq_other q) end.
Definition dq_add1 (bc : bctx) (c : saddr) (m : expr) (pc : saddr) (pm : expr) (q : dqix) : dqix :=
  match xloB bc m with Some ml => dq_add (fvar (a_base c)) (c, ml, pc, xloB bc pm) q | None => q end.
Fixpoint mk_dqix (bc : bctx) (kn : list kentry) : dqix :=
  match kn with
  | [] => DQ [] []
  | KDisj c1 m1 c2 m2 :: r => dq_add1 bc c1 m1 c2 m2 (dq_add1 bc c2 m2 c1 m1 (mk_dqix bc r))
  | _ :: r => mk_dqix bc r
  end.
(* [comment removed for export] *)
Definition dq_fit (x : dqe) (kb : expr) (kk n : Z) (gkb : expr) (lo hi : Z) : bool :=
  match x with (c, ml, pc, pml) =>
    if (Z.leb (a_off c) kk && Z.leb (kk + n) (a_off c + ml))%bool then
      if expr_eqb kb (a_base c) then
        match pml with
        | Some l => if (Z.leb (a_off pc) lo && Z.leb hi (a_off pc + l))%bool then expr_eqb gkb (a_base pc) else false
        | None => false
        end
      else false
    else false
  end.
Fixpoint dqes_fit (l : list dqe) (kb : expr) (kk n : Z) (gkb : expr) (lo hi : Z) : bool :=
  match l with [] => false | x :: r => if dq_fit x kb kk n gkb lo hi then true else dqes_fit r kb kk n gkb lo hi end.
Definition dq_witness (q : dqix) (kb : expr) (kk n : Z) (gkb : expr) (lo hi : Z) : bool :=
  dqes_fit (dq_bucket q (fvar kb)) kb kk n gkb lo hi.

Lemma dq_bucket_add : forall k x q k', dq_bucket (dq_add k x q) k' = if okeq k' k then x :: dq_bucket q k' else dq_bucket q k'.
Proof. intros [n|] x q [m|]; cbn [dq_add dq_bucket dq_vars dq_other okeq]; try reflexivity. apply lget_lset. Qed.
(* [comment removed for export] *)
Definition DQOK (bc : bctx) (kn : list kentry) (x : dqe) : Prop :=
  match x with (c, ml, pc, pml) =>
    exists m pm, (In (KDisj c m pc pm) kn \/ In (KDisj pc pm c m) kn) /\ xloB bc m = Some ml /\ pml = xloB bc pm end.
Lemma mk_dqix_ok : forall bc kn k x, In x (dq_bucket (mk_dqix bc kn) k) -> DQOK bc kn x.
Proof.
  intros bc kn. induction kn as [|K r IH]; intros k x H.
  - destruct k as [n|]; cbn in H; [unfold lget in H; destruct n; cbn in H; destruct H | destruct H].
  - assert (MONO : forall y, DQOK bc r y -> DQOK bc (K :: r) y).
    { intros [[[c ml] pc] pml] (m & pm & A & B & C). exists m, pm. split; [|split; assumption]. destruct A; [left|right]; right; assumption. }
    destruct K as [a w v|a l|a l bk|lo hi|e1 m0|e' lo hi|a n|c1 m1 c2 m2|a l cc|a l]; cbn [mk_dqix] in H; try (apply MONO; exact (IH _ _ H)).
    unfold dq_add1 in H.
    assert (STEP : forall q c m pc pm y kk,
      (forall y', In y' (dq_bucket q kk) -> DQOK bc (KDisj c1 m1 c2 m2 :: r) y') ->
      ((c = c1 /\ m = m1 /\ pc = c2 /\ pm = m2) \/ (c = c2 /\ m = m2 /\ pc = c1 /\ pm = m1)) ->
      In y (dq_bucket (match xloB bc m with Some ml => dq_add (fvar (a_base c)) (c, ml, pc, xloB bc pm) q | None => q end) kk) ->
      DQOK bc (KDisj c1 m1 c2 m2 :: r) y).
    { intros q c m pc pm y kk Hq Hc Hy. destruct (xloB bc m) as [ml|] eqn:Hml; [|exact (Hq _ Hy)].
      rewrite dq_bucket_add in Hy. destruct (okeq kk (fvar (a_base c))); [|exact (Hq _ Hy)].
      destruct Hy as [<-|Hy]; [|exact (Hq _ Hy)].
      exists m, pm. split; [|split; [exact Hml|reflexivity]].
      destruct Hc as [(-> & -> & -> & ->)|(-> & -> & -> & ->)]; [left|right]; left; reflexivity. }
    eapply STEP; [|left; repeat split; reflexivity|exact H].
    intros y' Hy'. eapply STEP; [|right; repeat split; reflexivity|exact Hy'].
    intros y'' Hy''. apply MONO. exact (IH _ _ Hy'').
Qed.
Lemma dqes_fit_In : forall l kb kk n gkb lo hi, dqes_fit l kb kk n gkb lo hi = true -> exists x, In x l /\ dq_fit x kb kk n gkb lo hi = true.
Proof.
  induction l as [|x r IH]; cbn; intros; [discriminate|].
  destruct (dq_fit x kb kk n gkb lo hi) eqn:E. - exists x. auto. - destruct (IH _ _ _ _ _ _ H) as (y & A & B). exists y. auto.
Qed.
(* [comment removed for export] *)
Lemma disj_sidesB_In : forall bc kn b k n c1 m1 c2 m2,
  In (KDisj c1 m1 c2 m2) kn ->
  (sub_itvB bc b k n c1 m1 = true -> In (c2, m2) (disj_sidesB bc kn b k n)) /\
  (sub_itvB bc b k n c2 m2 = true -> In (c1, m1) (disj_sidesB bc kn b k n)).
Proof.
  intros bc kn b k n c1 m1 c2 m2. induction kn as [|K r IH]; intros H; [destruct H|].
  assert (TL : forall x, In x (disj_sidesB bc r b k n) -> In x (disj_sidesB bc (K :: r) b k n)).
  { intros x Hx. destruct K as [a w v|a l|a l bk|lo hi|e1 m0|e' lo hi|a n0|d1 n1 d2 n2|a l cc|a l]; cbn [disj_sidesB]; try exact Hx.
    destruct (sub_itvB bc b k n d1 n1); [right|]; destruct (sub_itvB bc b k n d2 n2); try right; exact Hx. }
  destruct H as [->|H].
  - cbn [disj_sidesB]. split; intros Hs; rewrite Hs.
    + left. reflexivity.
    + destruct (sub_itvB bc b k n c1 m1); [right|]; left; reflexivity.
  - destruct (IH H) as [A B]. split; intros Hs; apply TL; auto.
Qed.
Lemma qix_hit_In : forall bc D c m ml kb kk n,
  In (c, m) D -> xloB bc m = Some ml -> expr_eqb kb (a_base c) = true -> a_off c <= kk -> kk + n <= a_off c + ml ->
  qix_hit (mk_qix bc D) kb kk n = true.
Proof.
  intros bc D c m ml kb kk n HIn Hml Heq H1 H2. unfold qix_hit. induction D as [|[c' m'] r IH]; [destruct HIn|].
  cbn [mk_qix]. destruct HIn as [E|HIn].
  - injection E as -> ->. rewrite Hml, qx_bucket_add.
    replace (fvar kb) with (fvar (a_base c)) by (apply p_expr_eqb_eq in Heq; rewrite Heq; reflexivity).
    destruct (okeq_spec (fvar (a_base c)) (fvar (a_base c))) as [_|NE]; [|congruence].
    cbn [qsides_hit]. replace ((a_off c <=? kk) && (kk + n <=? a_off c + ml))%bool with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
    rewrite Heq. reflexivity.
  - specialize (IH HIn). destruct (xloB bc m') as [ml'|]; [|exact IH]. rewrite qx_bucket_add.
    destruct (okeq (fvar kb) (fvar (a_base c'))); [|exact IH]. cbn [qsides_hit].
    destruct (if (_ && _)%bool then _ else _); [reflexivity | exact IH].
Qed.
Lemma sp_D_mk_sprepB : forall bc b k w, sp_D (mk_sprepB bc b k (elen w)) = disj_sidesB bc (bc_fk bc) b k (zlit64 (Z.of_nat w)).
Proof.
  intros. unfold mk_sprepB, elen.
  destruct ((0 <=? Z.of_nat w) && (Z.of_nat w <? two64))%Z%bool eqn:Hz; [|reflexivity].
  rewrite disj_sides2M_eq, disj_sides2PB_eq.
  assert (Hn : 0 <= Z.of_nat w < two64) by (apply andb_prop in Hz as [A B]; apply Z.leb_le in A; apply Z.ltb_lt in B; lia).
  rewrite (disj_sides2B_eq _ _ _ _ _ Hn). cbn [sp_D]. unfold zlit64. rewrite Hz. reflexivity.
Qed.
Lemma zlit64_small : forall w, zlit64 (Z.of_nat w) <= Z.of_nat w.
Proof. intros. unfold zlit64. destruct (_ && _)%bool; [lia|]. apply Z.mod_le; [lia|]. unfold two64. lia. Qed.
Local Close Scope Z_scope.

(* [comment removed for export] *)
Local Open Scope Z_scope.
Definition lgrp : Type := (expr * option (Z * Z) * Z * Z)%type.
Fixpoint lg_add (bc : bctx) (lg : list lgrp) (e : sentry) : list lgrp :=
  match e with SE (SA kb kk) w _ =>
  match lg with
  | [] => [(kb, base_rangeB bc kb, kk, kk + Z.of_nat w)]
  | (b, obr, lo, hi) :: r =>
      if expr_eqb kb b then (b, obr, Z.min lo kk, Z.max hi (kk + Z.of_nat w)) :: r else (b, obr, lo, hi) :: lg_add bc r e
  end end.
Definition lg_upd (bc : bctx) (lg : list lgrp) (log : list sentry) : list lgrp :=
  match log with [] => lg | e :: _ => lg_add bc lg e end.
Fixpoint lg_of (bc : bctx) (log : list sentry) : list lgrp :=
  match log with [] => [] | e :: r => lg_add bc (lg_of bc r) e end.
Definition lg_skip1 (dq : dqix) (rb : expr) (br : option (Z * Z)) (rk n : Z) (g : lgrp) : bool :=
  match g with (b, obr, lo, hi) =>
    if expr_eqb rb b then true
    else if match br, obr with
            | Some (lo1, hi1), Some (lo2, hi2) => (Z.leb (hi1 + rk + n) (lo2 + lo) || Z.leb (hi2 + hi) (lo1 + rk))%bool
            | _, _ => false
            end then true
    else dq_witness dq rb rk n b lo hi   (* [comment removed for export] *)
  end.
Fixpoint log_lookup_sameB (bc : bctx) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookup_sameB bc rest rb rk n sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown => log_lookup_sameB bc rest rb rk n sx hints acc
      end
  end.
(* [comment removed for export] *)
Definition lgran (kk : Z) : Z := Z.shiftr kk 6.
Record lix : Type := LX { lx_t : ptree (list (positive * list sentry)); lx_ok : bool }.
Definition lix_empty : lix := LX PTLeaf true.
Definition lix_bucket (x : lix) (g : Z) : list (positive * list sentry) :=
  match pt_get (lx_t x) (kx_gkey g) with Some b => b | None => [] end.
(* [comment removed for export] *)
Definition lix_lit (s : list sentry) : option (Z * bool) :=
  match s with SE (SA (ELit 0) kk) w _ :: _ => Some (lgran kk, Nat.leb w 8) | _ => None end.
Definition lix_ins (x : lix) (np : positive) (log : list sentry) : lix :=
  match lix_lit log with
  | Some (g, true) => LX (pt_set (kx_gkey g) ((np, log) :: lix_bucket x g) (lx_t x)) (lx_ok x)
  | Some (_, false) => LX (lx_t x) false
  | None => x
  end.
(* [comment removed for export] *)
Definition log_grows (i : instr) : bool :=
  match i with Store _ _ _ _ => true | Sc _ _ _ _ _ _ => true | Amo _ _ _ _ _ _ _ => true | _ => false end.
Definition lix_upd (x : lix) (np : positive) (i : instr) (log : list sentry) : lix * positive :=
  if log_grows i then (lix_ins x np log, Pos.succ np) else (x, np).
Fixpoint lix_of (log : list sentry) : lix * positive :=
  match log with
  | [] => (lix_empty, 1%positive)
  | _ :: r => let '(x, np) := lix_of r in (lix_ins x np log, Pos.succ np)
  end.
(* [comment removed for export] *)
Fixpoint lix_merge (l1 : list (positive * list sentry)) : list (positive * list sentry) -> list (positive * list sentry) :=
  match l1 with
  | [] => fun l2 => l2
  | (p1, s1) :: r1 =>
      fix go (l2 : list (positive * list sentry)) : list (positive * list sentry) :=
        match l2 with
        | [] => l1
        | (p2, s2) :: r2 => if Pos.ltb p2 p1 then (p1, s1) :: lix_merge r1 l2 else (p2, s2) :: go r2
        end
  end.
Definition lix_cands (x : lix) (rk : Z) : list (positive * list sentry) :=
  let g := lgran rk in lix_merge (lix_bucket x (g + 1)) (lix_merge (lix_bucket x g) (lix_bucket x (g - 1))).
Fixpoint log_lookup_ixB (cands : list (positive * list sentry)) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match cands with
  | [] => LMiss acc hints
  | (_, s) :: cands' =>
      match s with
      | SE (SA kb kk) w v :: _ =>
          match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
          | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
          | RDisjoint => log_lookup_ixB cands' rb rk n sx hints acc
          | RPartial => match log_bytes_lit s rb rk n with
                        | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                        | None => LStuck
                        end
          | RUnknown => log_lookup_ixB cands' rb rk n sx hints acc
          end
      | [] => log_lookup_ixB cands' rb rk n sx hints acc
      end
  end.
Definition lix_use (x : lix) (rb : expr) (n : nat) : bool :=
  (is_lit0 rb && lx_ok x && Nat.leb n 8 && Nat.leb 1 n)%bool.

Definition log_lookupGB (bc : bctx) (dq : dqix) (lg : list lgrp) (x : lix) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
           (hints : list bool) (acc : list sidecond) : lres :=
  let br := base_rangeB bc rb in
  if forallb (lg_skip1 dq rb br rk (Z.of_nat n)) lg then
    (if lix_use x rb n then log_lookup_ixB (lix_cands x rk) rb rk n sx hints acc   (* [comment removed for export] *)
     else log_lookup_sameB bc log rb rk n sx hints acc)
  else log_lookupCB bc log rb rk n sx hints acc br rb br.
Definition LGOK (bc : bctx) (lg : list lgrp) : Prop :=
  Forall (fun g => match g with (b, obr, _, _) => obr = base_rangeB bc b end) lg.
Definition ECOV (bc : bctx) (lg : list lgrp) (e : sentry) : Prop :=
  match e with SE (SA kb kk) w _ => exists lo hi, In (kb, base_rangeB bc kb, lo, hi) lg /\ lo <= kk /\ kk + Z.of_nat w <= hi end.
Definition LGCOV (bc : bctx) (lg : list lgrp) (log : list sentry) : Prop := LGOK bc lg /\ Forall (ECOV bc lg) log.
Lemma lg_add_ok : forall bc lg e, LGOK bc lg -> LGOK bc (lg_add bc lg e).
Proof.
  intros bc lg [[kb kk] w v]. induction lg as [|[[[b obr] lo] hi] r IH]; intros H; cbn [lg_add].
  - constructor; [reflexivity|constructor].
  - apply Forall_cons_iff in H as [H1 H]. destruct (expr_eqb kb b); constructor; [exact H1 | exact H | exact H1 | exact (IH H)].
Qed.
Lemma lg_add_old : forall bc lg e e', ECOV bc lg e' -> ECOV bc (lg_add bc lg e) e'.
Proof.
  intros bc lg [[eb ek] ew ev] [[kb kk] w v]. unfold ECOV. induction lg as [|[[[b obr] lo0] hi0] r IH]; intros (lo & hi & HIn & A & B); [destruct HIn|].
  cbn [lg_add]. destruct HIn as [E|HIn].
  - injection E as -> -> -> ->. destruct (expr_eqb eb kb).
    + eexists _, _. split; [left; reflexivity|]. lia.
    + exists lo, hi. split; [left; reflexivity|]. lia.
  - destruct (expr_eqb eb b).
    + exists lo, hi. split; [right; exact HIn|]. lia.
    + destruct (IH (ex_intro _ lo (ex_intro _ hi (conj HIn (conj A B))))) as (lo' & hi' & HIn' & A' & B').
      exists lo', hi'. split; [right; exact HIn'|]. lia.
Qed.
Lemma lg_add_new : forall bc lg e, LGOK bc lg -> ECOV bc (lg_add bc lg e) e.
Proof.
  intros bc lg [[kb kk] w v]. unfold ECOV. induction lg as [|[[[b obr] lo0] hi0] r IH]; intros HOK; cbn [lg_add].
  - eexists _, _. split; [left; reflexivity|]. lia.
  - apply Forall_cons_iff in HOK as [H1 HOK]. destruct (expr_eqb kb b) eqn:E.
    + apply p_expr_eqb_eq in E. subst b. subst obr. eexists _, _. split; [left; reflexivity|]. lia.
    + destruct (IH HOK) as (lo & hi & HIn & A & B). exists lo, hi. split; [right; exact HIn|]. lia.
Qed.
Lemma lg_upd_cov : forall bc lg ss ss',
  LGCOV bc lg (s_log ss) -> (s_log ss' = s_log ss \/ exists e, s_log ss' = e :: s_log ss) ->
  LGCOV bc (lg_upd bc lg (s_log ss')) (s_log ss').
Proof.
  intros bc lg ss ss' [HOK HC] HL. unfold lg_upd.
  destruct HL as [E|[e E]]; rewrite E.
  - destruct (s_log ss) as [|e0 r] eqn:EL; [split; [exact HOK|constructor]|].
    split; [apply lg_add_ok; exact HOK|]. apply Forall_impl with (P := ECOV bc lg); [intros a; apply lg_add_old | exact HC].
  - split; [apply lg_add_ok; exact HOK|]. constructor; [apply lg_add_new; exact HOK|].
    apply Forall_impl with (P := ECOV bc lg); [intros a; apply lg_add_old | exact HC].
Qed.
Lemma lg_of_cov : forall bc log, LGCOV bc (lg_of bc log) log.
Proof.
  intros bc log. induction log as [|e r [IH1 IH2]]; cbn [lg_of].
  - split; constructor.
  - split; [apply lg_add_ok; exact IH1|]. constructor; [apply lg_add_new; exact IH1|].
    apply Forall_impl with (P := ECOV bc (lg_of bc r)); [intros a; apply lg_add_old | exact IH2].
Qed.
Lemma kdisj_apartB_In : forall bc kn b1 k1 n1 b2 k2 n2 c1 m1 c2 m2,
  In (KDisj c1 m1 c2 m2) kn ->
  (sub_itvB bc b1 k1 n1 c1 m1 = true -> sub_itvB bc b2 k2 n2 c2 m2 = true -> kdisj_apartB bc kn b1 k1 n1 b2 k2 n2 = true) /\
  (sub_itvB bc b1 k1 n1 c2 m2 = true -> sub_itvB bc b2 k2 n2 c1 m1 = true -> kdisj_apartB bc kn b1 k1 n1 b2 k2 n2 = true).
Proof.
  intros bc kn b1 k1 n1 b2 k2 n2 c1 m1 c2 m2. induction kn as [|K r IH]; intros H; [destruct H|].
  assert (TL : kdisj_apartB bc r b1 k1 n1 b2 k2 n2 = true -> kdisj_apartB bc (K :: r) b1 k1 n1 b2 k2 n2 = true).
  { intros Hr. destruct K as [a w v|a l|a l bk|lo hi|e1 m0|e' lo hi|a n0|d1 e1 d2 e2|a l cc|a l]; cbn [kdisj_apartB]; try exact Hr.
    rewrite Hr. repeat (lazymatch goal with |- (if ?c then _ else _) = true => destruct c; [reflexivity|] end). reflexivity. }
  destruct H as [->|H].
  - cbn [kdisj_apartB]. split; intros X Y; rewrite X, Y; [reflexivity|].
    lazymatch goal with |- (if ?c then _ else _) = true => destruct c; reflexivity end.
  - destruct (IH H) as [A B]. split; intros X Y; apply TL; auto.
Qed.
Lemma dq_witness_kdisj : forall bc rb rk n kb lo hi kk w,
  dq_witness (mk_dqix bc (bc_fk bc)) rb rk n kb lo hi = true -> lo <= kk -> kk + w <= hi ->
  kdisj_apartB bc (bc_fk bc) rb rk n kb kk w = true.
Proof.
  intros bc rb rk n kb lo hi kk w Hw Hlo Hhi.
  unfold dq_witness in Hw. destruct (dqes_fit_In _ _ _ _ _ _ _ Hw) as ([[[c ml] pc] pml] & HIn & Hfit).
  destruct (mk_dqix_ok _ _ _ _ HIn) as (m & pm & Hdisj & Hml & ->).
  unfold dq_fit in Hfit.
  destruct ((a_off c <=? rk) && (rk + n <=? a_off c + ml))%Z%bool eqn:H1; [|discriminate].
  destruct (expr_eqb rb (a_base c)) eqn:H2; [|discriminate].
  destruct (xloB bc pm) as [pl|] eqn:Hpl; [|discriminate].
  destruct ((a_off pc <=? lo) && (hi <=? a_off pc + pl))%Z%bool eqn:H3; [|discriminate].
  apply andb_prop in H3 as [H3a H3b]. apply Z.leb_le in H3a. apply Z.leb_le in H3b.
  assert (S1 : sub_itvB bc rb rk n c m = true).
  { unfold sub_itvB. rewrite H2, Hml. cbn [andb]. apply andb_prop in H1 as [X Y]. rewrite X, Y. reflexivity. }
  assert (S2 : sub_itvB bc kb kk w pc pm = true).
  { unfold sub_itvB. rewrite Hfit. replace (a_off pc <=? kk)%Z with true by (symmetry; apply Z.leb_le; lia).
    cbn [andb]. rewrite Hpl. replace (kk + w <=? a_off pc + pl)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  destruct Hdisj as [Hd|Hd].
  - exact (proj1 (kdisj_apartB_In bc _ _ _ _ _ _ _ _ _ _ _ Hd) S1 S2).
  - exact (proj2 (kdisj_apartB_In bc _ _ _ _ _ _ _ _ _ _ _ Hd) S1 S2).
Qed.
Lemma log_lookup_sameB_eq : forall bc lg log rb rk n sx hints acc,
  Forall (ECOV bc lg) log -> forallb (lg_skip1 (mk_dqix bc (bc_fk bc)) rb (base_rangeB bc rb) rk (Z.of_nat n)) lg = true ->
  log_lookup_sameB bc log rb rk n sx hints acc = log_lookupB bc log rb rk n sx hints acc.
Proof.
  intros bc lg log rb rk n sx. induction log as [|[[kb kk] w v] rest IH]; intros hints acc HC HS; [reflexivity|].
  apply Forall_cons_iff in HC as [H1 HC]. cbn [log_lookup_sameB log_lookupB].
  unfold rel_lit at 1 2. destruct (expr_eqb rb kb) eqn:Erb.
  - destruct ((kk <=? rk) && (rk + Z.of_nat n <=? kk + Z.of_nat w))%bool; [reflexivity|].
    destruct ((rk + Z.of_nat n <=? kk) || (kk + Z.of_nat w <=? rk))%bool; [apply IH; assumption|reflexivity].
  - (* [comment removed for export] *)
    destruct H1 as (lo & hi & HIn & A & B).
    pose proof (proj1 (forallb_forall _ _) HS _ HIn) as G. cbn [lg_skip1] in G. rewrite Erb in G.
    replace (ranges_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w)) with true; [apply IH; assumption|].
    symmetry.
    assert (KD : dq_witness (mk_dqix bc (bc_fk bc)) rb rk (Z.of_nat n) kb lo hi = true -> ranges_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w) = true).
    { intros Hw. pose proof (dq_witness_kdisj bc rb rk (Z.of_nat n) kb lo hi kk (Z.of_nat w) Hw A B) as KD.
      unfold ranges_apartB. rewrite KD.
      repeat (lazymatch goal with |- (if ?c then _ else _) = true => destruct c; [reflexivity|] end). reflexivity. }
    lazymatch type of G with (if ?num then true else _) = true => destruct num eqn:Hnum; [|exact (KD G)] end.
    clear G KD. unfold ranges_apartB.
    destruct (base_rangeB bc rb) as [[lo1 hi1]|]; [|discriminate]. destruct (base_rangeB bc kb) as [[lo2 hi2]|]; [|discriminate].
    replace ((hi1 + rk + Z.of_nat n <=? lo2 + kk) || (hi2 + kk + Z.of_nat w <=? lo1 + rk))%bool with true; [reflexivity|].
    symmetry. apply Bool.orb_true_iff. apply Bool.orb_true_iff in Hnum. destruct Hnum as [G|G]; apply Z.leb_le in G; [left|right]; apply Z.leb_le; lia.
Qed.   (* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint tsufs (log : list sentry) : list (positive * list sentry) :=
  match log with [] => [] | _ :: r => (Pos.of_succ_nat (length r), log) :: tsufs r end.
Definition lcand (g : Z) (s : list sentry) : bool :=
  match lix_lit s with Some (g', true) => Z.eqb g' g | _ => false end.
Definition lwide (s : list sentry) : bool :=
  match lix_lit s with Some (_, false) => true | _ => false end.
Definition LIXINV (x : lix) (np : positive) (log : list sentry) : Prop :=
  np = Pos.of_succ_nat (length log)
  /\ (forall g, lix_bucket x g = List.filter (fun ts => lcand g (snd ts)) (tsufs log))
  /\ (lx_ok x = true -> forall ts, In ts (tsufs log) -> lwide (snd ts) = false).

Lemma lix_bucket_empty : forall g, lix_bucket lix_empty g = [].
Proof. intros g. unfold lix_bucket, lix_empty. cbn [lx_t]. rewrite pt_get_leaf. reflexivity. Qed.
Lemma LIXINV_empty : LIXINV lix_empty 1%positive [].
Proof.
  split; [reflexivity|]. split; [intros g; rewrite lix_bucket_empty; reflexivity|]. intros _ ts [].
Qed.
Lemma lcand_uniq : forall g g' s, lcand g s = true -> lcand g' s = true -> g = g'.
Proof.
  intros g g' s. unfold lcand. destruct (lix_lit s) as [[g0 [|]]|]; try discriminate.
  intros A B. apply Z.eqb_eq in A. apply Z.eqb_eq in B. lia.
Qed.
Lemma lix_ins_inv : forall x np log e,
  LIXINV x np log -> LIXINV (lix_ins x np (e :: log)) (Pos.succ np) (e :: log).
Proof.
  intros x np log e (Hnp & Hb & Hw). unfold lix_ins.
  assert (TS : tsufs (e :: log) = (Pos.of_succ_nat (length log), e :: log) :: tsufs log) by reflexivity.
  split; [rewrite Hnp; reflexivity|].
  destruct (lix_lit (e :: log)) as [[g0 [|]]|] eqn:HL.
  - (* [comment removed for export] *)
    split.
    + intros g. rewrite TS. cbn [List.filter snd].
      replace (lcand g (e :: log)) with (Z.eqb g0 g) by (unfold lcand; rewrite HL; reflexivity).
      unfold lix_bucket. cbn [lx_t].
      destruct (Z.eqb_spec g0 g) as [<-|NE].
      * rewrite pt_gss. rewrite <- Hnp. f_equal. apply Hb.
      * rewrite pt_gso by (intros E; apply NE; symmetry; exact (kx_gkey_inj _ _ E)). apply Hb.
    + cbn [lx_ok]. intros Hok ts. rewrite TS. intros [<-|HIn]; [|exact (Hw Hok ts HIn)].
      cbn [snd]. unfold lwide. rewrite HL. reflexivity.
  - (* [comment removed for export] *)
    split.
    + intros g. rewrite TS. cbn [List.filter snd].
      replace (lcand g (e :: log)) with false by (unfold lcand; rewrite HL; reflexivity). unfold lix_bucket. cbn [lx_t]. apply Hb.
    + cbn [lx_ok]. intros; discriminate.
  - (* [comment removed for export] *)
    split.
    + intros g. rewrite TS. cbn [List.filter snd].
      replace (lcand g (e :: log)) with false by (unfold lcand; rewrite HL; reflexivity). apply Hb.
    + intros Hok ts. rewrite TS. intros [<-|HIn]; [|exact (Hw Hok ts HIn)]. cbn [snd]. unfold lwide. rewrite HL. reflexivity.
Qed.
Lemma lix_of_inv : forall log, let '(x, np) := lix_of log in LIXINV x np log.
Proof.
  induction log as [|e r IH]; cbn [lix_of]; [exact LIXINV_empty|].
  destruct (lix_of r) as [x np]. apply lix_ins_inv. exact IH.
Qed.

(* [comment removed for export] *)
Lemma tsufs_tags_lt : forall log ts, In ts (tsufs log) -> (fst ts < Pos.of_succ_nat (length log))%positive.
Proof.
  induction log as [|e r IH]; intros ts HIn; [destruct HIn|].
  cbn [tsufs] in HIn. change (length (e :: r)) with (S (length r)). cbn [Pos.of_succ_nat].
  destruct HIn as [<-|HIn]; [cbn [fst]; lia|]. specialize (IH ts HIn). lia.
Qed.
Lemma filter_tsufs_lt : forall P r ts, In ts (List.filter P (tsufs r)) -> (fst ts < Pos.of_succ_nat (length r))%positive.
Proof. intros P r ts H. apply filter_In in H as [H _]. exact (tsufs_tags_lt _ _ H). Qed.

Lemma lix_merge_nil_l : forall l2, lix_merge [] l2 = l2.
Proof. reflexivity. Qed.
Lemma lix_merge_cons_l : forall p s r1 l2,
  Forall (fun ts => (fst ts < p)%positive) l2 -> lix_merge ((p, s) :: r1) l2 = (p, s) :: lix_merge r1 l2.
Proof.
  intros p s r1 l2 H. destruct l2 as [|[p2 s2] r2]; cbn [lix_merge].
  - destruct r1 as [|[? ?] ?]; reflexivity.
  - apply Forall_inv in H. cbn in H. destruct (Pos.ltb_spec p2 p); [reflexivity|lia].
Qed.
Lemma lix_merge_cons_r : forall p s l1 r2,
  Forall (fun ts => (fst ts < p)%positive) l1 -> lix_merge l1 ((p, s) :: r2) = (p, s) :: lix_merge l1 r2.
Proof.
  intros p s l1 r2 H. destruct l1 as [|[p1 s1] r1]; cbn [lix_merge]; [reflexivity|].
  apply Forall_inv in H. cbn in H. destruct (Pos.ltb_spec p p1); [lia|reflexivity].
Qed.
Lemma lix_merge_filters : forall (P Q : list sentry -> bool) log,
  (forall s, P s = true -> Q s = false) ->
  lix_merge (List.filter (fun ts => P (snd ts)) (tsufs log)) (List.filter (fun ts => Q (snd ts)) (tsufs log))
  = List.filter (fun ts => P (snd ts) || Q (snd ts)) (tsufs log).
Proof.
  intros P Q log. induction log as [|e r IH]; intros HPQ; [reflexivity|].
  cbn [tsufs List.filter snd].
  assert (LT : forall R, Forall (fun ts => (fst ts < Pos.of_succ_nat (length r))%positive) (List.filter R (tsufs r))).
  { intros R. apply Forall_forall. intros ts H. exact (filter_tsufs_lt _ _ _ H). }
  destruct (P (e :: r)) eqn:HP.
  - rewrite (HPQ _ HP). cbn [orb]. rewrite lix_merge_cons_l by apply LT. rewrite IH by exact HPQ. reflexivity.
  - destruct (Q (e :: r)) eqn:HQ; cbn [orb].
    + rewrite lix_merge_cons_r by apply LT. rewrite IH by exact HPQ. reflexivity.
    + apply IH. exact HPQ.
Qed.
Lemma lix_cands_eq : forall x np log rk,
  LIXINV x np log ->
  lix_cands x rk = List.filter (fun ts => lcand (lgran rk + 1) (snd ts) || (lcand (lgran rk) (snd ts) || lcand (lgran rk - 1) (snd ts)))
                               (tsufs log).
Proof.
  intros x np log rk (_ & Hb & _). unfold lix_cands. cbv zeta. rewrite !Hb.
  rewrite (lix_merge_filters (lcand (lgran rk)) (lcand (lgran rk - 1)) log)
    by (intros s A; destruct (lcand (lgran rk - 1) s) eqn:B; [|reflexivity]; pose proof (lcand_uniq _ _ _ A B); lia).
  rewrite (lix_merge_filters (lcand (lgran rk + 1)) (fun s => lcand (lgran rk) s || lcand (lgran rk - 1) s) log); [reflexivity|].
  intros s A. destruct (lcand (lgran rk) s) eqn:B; [pose proof (lcand_uniq _ _ _ A B); lia|].
  destruct (lcand (lgran rk - 1) s) eqn:C; [pose proof (lcand_uniq _ _ _ A C); lia|]. reflexivity.
Qed.

Lemma lgran_bounds : forall z, (64 * lgran z <= z < 64 * lgran z + 64)%Z.
Proof.
  intros z. unfold lgran. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 6)%Z with 64%Z.
  pose proof (Z.div_mod z 64 ltac:(lia)). pose proof (Z.mod_pos_bound z 64 ltac:(lia)). lia.
Qed.
(* [comment removed for export] *)
Lemma log_lookup_ixB_filter : forall bc log rk n sx hints acc,
  (1 <= n <= 8)%nat ->
  (forall ts, In ts (tsufs log) -> lwide (snd ts) = false) ->
  log_lookup_ixB (List.filter (fun ts => lcand (lgran rk + 1) (snd ts) || (lcand (lgran rk) (snd ts) || lcand (lgran rk - 1) (snd ts)))
                              (tsufs log)) (ELit 0%Z) rk n sx hints acc
  = log_lookup_sameB bc log (ELit 0%Z) rk n sx hints acc.
Proof.
  intros bc log rk n sx. induction log as [|e r IH]; intros hints acc Hn Hw; [reflexivity|].
  cbn [tsufs List.filter snd].
  assert (Hw' : forall ts, In ts (tsufs r) -> lwide (snd ts) = false) by (intros ts H; apply Hw; right; exact H).
  destruct e as [[kb kk] w v].
  match goal with |- log_lookup_ixB (if ?c then _ else _) _ _ _ _ _ _ = _ => destruct c eqn:HC end.
  - (* [comment removed for export] *)
    cbn [log_lookup_ixB log_lookup_sameB].
    destruct (rel_lit (ELit 0%Z) rk (Z.of_nat n) kb kk (Z.of_nat w)); try reflexivity; apply IH; assumption.
  - (* [comment removed for export] *)
    cbn [log_lookup_sameB].
    assert (SKIP : rel_lit (ELit 0%Z) rk (Z.of_nat n) kb kk (Z.of_nat w) = RDisjoint
                   \/ rel_lit (ELit 0%Z) rk (Z.of_nat n) kb kk (Z.of_nat w) = RUnknown).
    { unfold rel_lit. destruct (expr_eqb (ELit 0%Z) kb) eqn:Ekb; [|right; reflexivity]. left.
      apply p_expr_eqb_eq in Ekb. subst kb.
      pose proof (Hw _ (or_introl eq_refl)) as W. cbn [snd lwide lcand lix_lit] in W, HC.
      destruct (Nat.leb w 8) eqn:Hw8; [|discriminate W]. apply Nat.leb_le in Hw8.
      apply Bool.orb_false_iff in HC as [C1 HC]. apply Bool.orb_false_iff in HC as [C2 C3].
      apply Z.eqb_neq in C1. apply Z.eqb_neq in C2. apply Z.eqb_neq in C3.
      pose proof (lgran_bounds kk) as Bk. pose proof (lgran_bounds rk) as Br.
      assert (D : (lgran kk <= lgran rk - 2 \/ lgran rk + 2 <= lgran kk)%Z) by lia.
      assert (NI : ((kk <=? rk) && (rk + Z.of_nat n <=? kk + Z.of_nat w))%bool = false).
      { apply Bool.andb_false_iff. destruct D as [D|D].
        - right. apply Z.leb_gt. lia.
        - left. apply Z.leb_gt. lia. }
      rewrite NI.
      assert (DJ : ((rk + Z.of_nat n <=? kk) || (kk + Z.of_nat w <=? rk))%bool = true).
      { apply Bool.orb_true_iff. destruct D as [D|D]; [right|left]; apply Z.leb_le; lia. }
      rewrite DJ. reflexivity. }
    destruct SKIP as [-> | ->]; apply IH; assumption.
Qed.
Lemma log_lookup_ixB_eq : forall bc x np log rb rk n sx hints acc,
  LIXINV x np log -> lix_use x rb n = true ->
  log_lookup_ixB (lix_cands x rk) rb rk n sx hints acc = log_lookup_sameB bc log rb rk n sx hints acc.
Proof.
  intros bc x np log rb rk n sx hints acc HI HU. unfold lix_use in HU.
  apply andb_prop in HU as [HU H1]. apply andb_prop in HU as [HU H8]. apply andb_prop in HU as [HL Hok].
  apply is_lit0_true in HL. subst rb. apply Nat.leb_le in H8. apply Nat.leb_le in H1.
  rewrite (lix_cands_eq _ _ _ _ HI). destruct HI as (_ & _ & Hw).
  apply log_lookup_ixB_filter; [lia|]. exact (Hw Hok).
Qed.

Lemma log_lookupGB_eq : forall bc lg x np log rb rk n sx hints acc,
  LGCOV bc lg log -> LIXINV x np log ->
  log_lookupGB bc (mk_dqix bc (bc_fk bc)) lg x log rb rk n sx hints acc = log_lookupB bc log rb rk n sx hints acc.
Proof.
  intros bc lg x np log rb rk n sx hints acc [HOK HC] HX. unfold log_lookupGB. cbv zeta.
  destruct (forallb (lg_skip1 (mk_dqix bc (bc_fk bc)) rb (base_rangeB bc rb) rk (Z.of_nat n)) lg) eqn:HS.
  - destruct (lix_use x rb n) eqn:HU.
    + rewrite (log_lookup_ixB_eq bc x np log rb rk n sx hints acc HX HU). apply (log_lookup_sameB_eq bc lg); assumption.
    + apply (log_lookup_sameB_eq bc lg); assumption.
  - apply log_lookupCB_eq. reflexivity.
Qed.
Local Close Scope Z_scope.

Definition sym_readBI (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  let br := base_rangeB bc (a_base a) in   (* [comment removed for export] *)
  match log_lookupCB bc (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] br (a_base a) br with
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
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
      end
  end.


Definition sym_stepBI (bc : bctx) (kx : kix) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluwKB bc ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
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
      match sym_readBI segs ss bc kx scr a n sx' with
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
  | _ => SStop
  end.


Lemma sym_readBI_eqf : forall segs ss bc, sym_readBI segs ss bc (mk_kix (s_know ss)) = sym_readB segs ss bc.
Proof. intros. bcfe. unfold sym_readBI, sym_readB. cbv zeta. rewrite log_lookupCB_eq by reflexivity. rewrite know_lookupABI_eq. reflexivity. Qed.   (* [comment removed for export] *)
Lemma sym_stepBI_eq : forall bc segs i ss scr,
  sym_stepBI bc (mk_kix (s_know ss)) segs i ss scr = sym_stepB bc segs i ss scr.
Proof. intros. unfold sym_stepBI, sym_stepB. rewrite sym_readBI_eqf. reflexivity. Qed.

(* [comment removed for export] *)
Definition sym_readBG (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (dq : dqix) (lg : list lgrp) (x : lix) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match log_lookupGB bc dq lg x (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with   (* [comment removed for export] *)
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
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
      end
  end.


Definition sym_stepBG (bc : bctx) (kx : kix) (dq : dqix) (lg : list lgrp) (x : lix) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluwKB bc ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
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
      match sym_readBG segs ss bc kx dq lg x scr a n sx' with
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
        match sym_readBG segs ss bc kx dq lg x scr a n (amo_sx wd) with
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
                match sym_readBG segs ss bc kx dq lg x scr a n (amo_sx wd) with
                | None => SStop
                | Some (vold, scs, scr', nx') =>
                    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
                             (SE a n (amo_newvalB bc wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
                        (scs ++ storeok_scB bc a n) scr'
                end
            end
          else SStop
      end
  | _ => SStop
  end.



Lemma sym_readBG_eq : forall segs ss bc kx lg x np, LGCOV bc lg (s_log ss) -> LIXINV x np (s_log ss) -> sym_readBG segs ss bc kx (mk_dqix bc (bc_fk bc)) lg x = sym_readBI segs ss bc kx.
Proof.
  intros segs ss bc kx lg x np H HX. bcfe. unfold sym_readBG, sym_readBI. cbv zeta.
  rewrite (log_lookupGB_eq _ _ _ _ _ _ _ _ _ _ _ H HX). rewrite log_lookupCB_eq by reflexivity. reflexivity.
Qed.
Lemma sym_stepBG_eq : forall bc kx lg x np segs i ss scr, LGCOV bc lg (s_log ss) -> LIXINV x np (s_log ss) -> sym_stepBG bc kx (mk_dqix bc (bc_fk bc)) lg x segs i ss scr = sym_stepBI bc kx segs i ss scr.
Proof. intros bc kx lg x np segs i ss scr H HX. unfold sym_stepBG, sym_stepBI. rewrite (sym_readBG_eq segs ss bc kx lg x np H HX). reflexivity. Qed.
(* [comment removed for export] *)
Definition LOGSTEP (ss ss' : sym_state) : Prop := s_log ss' = s_log ss \/ exists e, s_log ss' = e :: s_log ss.
Ltac peel_step H :=
  lazymatch type of H with
  | SStop = SOk _ _ _ => discriminate H
  | SOk _ _ _ = SOk _ _ _ => idtac
  | (match ?x with _ => _ end) = _ => destruct x; peel_step H
  | (let _ := ?x in _) = _ => cbv zeta in H; peel_step H
  | _ = _ => cbv beta zeta in H; peel_step H
  end.
Lemma sym_stepBI_log : forall bc kx segs i ss scr ss' scs scr',
  sym_stepBI bc kx segs i ss scr = SOk ss' scs scr' -> LOGSTEP ss ss'.
Proof.
  intros bc kx segs i ss scr ss' scs scr' H. unfold LOGSTEP. unfold sym_stepBI in H. cbv beta zeta in H.
  destruct i; try discriminate H;
  repeat (lazymatch type of H with
          | SStop = SOk _ _ _ => discriminate H
          | SOk _ _ _ = SOk _ _ _ => injection H as <- E2 E3
          | (match ?x with _ => _ end) = _ => destruct x
          end);
  cbn [s_log sset sjump]; first [left; reflexivity | right; eexists; reflexivity].
Qed.
Lemma cap_rd_log : forall K i ss, s_log (cap_rd K i ss) = s_log ss.
Proof.
  intros K i ss. unfold cap_rd. destruct K; [reflexivity|]. destruct (rd_of i) as [rd|]; [|reflexivity].
  repeat (lazymatch goal with |- s_log (if ?c then _ else _) = _ => destruct c end); reflexivity.
Qed.

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
Lemma foldKB_eqf : forall fk, foldKB (mkbc fk) = foldK fk.
Proof. intros. bcfe. unfold foldKB, foldK. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite foldKB_eqf : bceq.
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

Definition zf_coversB (bc : bctx) (rb : expr) (rk : Z) (n : nat) (kb : expr) (kk : Z) (len : expr) : bool :=
  if (match len with
      | ELit l0 => match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2 ^ 64)%Z with RInside _ => true | _ => false end
      | _ => false
      end) then true else xinsideB bc rb rk (elen n) kb kk len.   (* [comment removed for export] *)

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
  existsb (kentry_readableB bc rb rk n) kn || know_bytes_cov segs true kn rb rk n.

Definition kn_overlayB (bc : bctx) (kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
  existsb (kentry_overlayB bc rb rk n) kn || know_bytes_cov segs false kn rb rk n.

(* [comment removed for export] *)
Definition zf_quick (rb : expr) (rk : Z) (n : nat) (kb : expr) (kk : Z) (len : expr) : bool :=
  match len with
  | ELit l0 => match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2 ^ 64)%Z with RInside _ => true | _ => false end
  | _ => false
  end.
Definition kentry_overlayQ (rb : expr) (rk : Z) (n : nat) (K : kentry) : bool :=
  match K with
  | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ => zf_quick rb rk n kb kk len
  | _ => false
  end.
Definition kentry_readableQ (rb : expr) (rk : Z) (n : nat) (K : kentry) : bool :=
  match K with
  | KWord (SA kb kk) w _ => match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with RInside _ => true | _ => false end
  | _ => kentry_overlayQ rb rk n K
  end.
Fixpoint kexistsL (f : kentry -> bool) (kn : list kentry) : bool :=
  match kn with [] => false | K :: r => if f K then true else kexistsL f r end.
Lemma kexistsL_eq : forall f kn, kexistsL f kn = existsb f kn.
Proof. intros f kn. induction kn as [|K r IH]; [reflexivity|]. cbn [kexistsL existsb]. rewrite IH. destruct (f K); reflexivity. Qed.
Lemma kexistsL_impl : forall (f g : kentry -> bool) kn, (forall K, f K = true -> g K = true) -> kexistsL f kn = true -> existsb g kn = true.
Proof.
  intros f g kn Hfg. induction kn as [|K r IH]; cbn [kexistsL existsb]; intros H; [discriminate|].
  destruct (f K) eqn:HF. - rewrite (Hfg K HF). reflexivity. - rewrite (IH H). destruct (g K); reflexivity.
Qed.
Lemma kentry_overlayQ_impl : forall bc rb rk n K, kentry_overlayQ rb rk n K = true -> kentry_overlayB bc rb rk n K = true.
Proof.
  intros bc rb rk n K H. destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
    cbn [kentry_overlayQ kentry_overlayB] in H |- *; try discriminate; unfold zf_coversB; unfold zf_quick in H; rewrite H; reflexivity.
Qed.
Lemma kentry_readableQ_impl : forall bc rb rk n K, kentry_readableQ rb rk n K = true -> kentry_readableB bc rb rk n K = true.
Proof.
  intros bc rb rk n K H. destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
    cbn [kentry_readableQ kentry_readableB] in H |- *; try exact H; apply (kentry_overlayQ_impl bc); exact H.
Qed.
Definition kn_readableLB (bc : bctx) (kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
  if kexistsL (kentry_readableQ rb rk n) kn then true
  else if kexistsL (kentry_readableB bc rb rk n) kn then true else know_bytes_cov segs true kn rb rk n.
Definition kn_overlayLB (bc : bctx) (kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
  if kexistsL (kentry_overlayQ rb rk n) kn then true
  else if kexistsL (kentry_overlayB bc rb rk n) kn then true else know_bytes_cov segs false kn rb rk n.
Lemma kn_readableLB_eq : forall bc, kn_readableLB bc = kn_readableB bc.
Proof.
  intros bc. apply functional_extensionality; intros kn. apply functional_extensionality; intros rb.
  apply functional_extensionality; intros rk. apply functional_extensionality; intros n.
  unfold kn_readableLB, kn_readableB. rewrite (kexistsL_eq (kentry_readableB bc rb rk n)).
  destruct (kexistsL (kentry_readableQ rb rk n) kn) eqn:HQ; [|reflexivity].
  rewrite (kexistsL_impl _ _ kn (kentry_readableQ_impl bc rb rk n) HQ). reflexivity.
Qed.
Lemma kn_overlayLB_eq : forall bc, kn_overlayLB bc = kn_overlayB bc.
Proof.
  intros bc. apply functional_extensionality; intros kn. apply functional_extensionality; intros rb.
  apply functional_extensionality; intros rk. apply functional_extensionality; intros n.
  unfold kn_overlayLB, kn_overlayB. rewrite (kexistsL_eq (kentry_overlayB bc rb rk n)).
  destruct (kexistsL (kentry_overlayQ rb rk n) kn) eqn:HQ; [|reflexivity].
  rewrite (kexistsL_impl _ _ kn (kentry_overlayQ_impl bc rb rk n) HQ). reflexivity.
Qed.

Definition x_dischargeableB (bc : bctx) (ss ss' : sym_state) (rb : option (saddr * nat * bool)) (sc : sidecond) : bool :=
  let kn := s_know ss in
  match sc with
  | SCReadBase a n sx (EVar j) =>
      (match rb with
       | Some (a', n', sx') => saddr_eqb a' a && Nat.eqb n' n && Bool.eqb sx' sx
       | None => false
       end)
      && Nat.eqb j (s_next ss) && Nat.ltb j (s_next ss') && evars_lt (s_next ss) (a_base a)
      && Nat.leb 1 n && Nat.leb n 8 && kn_readableLB bc kn (a_base a) (a_off a) n
  | SCFlat a (ELit z) =>
      Z.leb 1 z && Z.leb z 8 && kn_readableLB bc kn (a_base a) (a_off a) (Z.to_nat z)
  | SCStoreOk a n => Nat.leb 1 n && Nat.leb n 8 && kn_overlayLB bc kn (a_base a) (a_off a) n
  | _ => false
  end%bool.

Definition x_filterB (bc : bctx) (ss ss' : sym_state) (scs : list sidecond) : list sidecond :=
  match scs with
  | [] => []          (* [comment removed for export] *)
  | _ => let rb := find_readbase (s_next ss) scs in
         List.filter (fun sc => negb (x_dischargeableB bc ss ss' rb sc)) scs
  end.

Definition sym_stepXB (bc : bctx) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match sym_stepB bc segs i ss scr with
  | SOk ss' scs scr' =>
      if Nat.leb (s_next ss) (s_next ss')            (* [comment removed for export] *)
      then SOk (cap_rd K i ss') (x_filterB bc ss ss' scs) scr'
      else SStop
  | SStop => SStop
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
Proof. intros. unfold x_dischargeableB, x_dischargeable. rewrite ?kn_readableLB_eq, ?kn_overlayLB_eq. autorewrite with bceq. reflexivity. Qed.   (* [comment removed for export] *)
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
Lemma sym_stepXB_eq : forall K i ss scr,
  sym_stepXB (mkbc (facts_of (s_know ss))) K i ss scr = sym_stepX segs K i ss scr.
Proof.
  intros. unfold sym_stepXB, sym_stepX. rewrite sym_stepB_eq.
  destruct (sym_step segs i ss scr) as [ss' scs scr'|]; [|reflexivity]. rewrite x_filterB_eq. reflexivity.
Qed.
Lemma sym_stepX_know : forall K i ss scr ss' scs scr',
  sym_stepX segs K i ss scr = SOk ss' scs scr' -> s_know ss' = s_know ss.
Proof.
  intros K i ss scr ss' scs scr' H. unfold sym_stepX in H.
  destruct (sym_step segs i ss scr) as [ss1 scs1 scr1|] eqn:E; [|discriminate].
  destruct (Nat.leb (s_next ss) (s_next ss1)); [|discriminate]. injection H as <- _ _.
  rewrite cap_rd_know. exact (sym_step_know _ _ _ _ _ _ _ E).
Qed.

(* [comment removed for export] *)
Fixpoint sym_execTXB_go (bc : bctx) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_stepXB bc K i ss scr_nil with
          | SOk ss' [] _ => sym_execTXB_go bc t K f false stops ss' (if s_clean ss' then ss' else ck)
          | _ => if s_clean ss then ss else ck
          end
      end
  end.
Definition sym_execTXB (bc : bctx) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  sym_execTXB_go bc t K fuel first stops (clr ss) (clr ss).

Lemma sym_execTXB_go_eq : forall t K fuel first stops ss ck,
  sym_execTXB_go (mkbc (facts_of (s_know ss))) t K fuel first stops ss ck = sym_execTX_go segs t K fuel first stops ss ck.
Proof.
  intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck; [reflexivity|].
  cbn [sym_execTXB_go sym_execTX_go].
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
  rewrite sym_stepXB_eq. destruct (sym_stepX segs K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|reflexivity].
  destruct scs; [|reflexivity].
  rewrite <- (sym_stepX_know _ _ _ _ _ _ _ E). apply IH.
Qed.
Lemma sym_execTXB_eq : forall kn0 t K fuel first stops ss,
  s_know ss = kn0 ->
  sym_execTXB (mkbc (facts_of kn0)) t K fuel first stops ss = sym_execTX segs t K fuel first stops ss.
Proof.
  intros kn0 t K fuel first stops ss <-. unfold sym_execTXB, sym_execTX.
  replace (s_know ss) with (s_know (clr ss)) by (destruct ss; reflexivity).
  apply sym_execTXB_go_eq.
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
  match sym_stepBI bc kx segs i ss scr with
  | SOk ss' scs scr' =>
      if Nat.leb (s_next ss) (s_next ss')
      then SOk (cap_rd K i ss') (x_filterB bc ss ss' scs) scr'
      else SStop
  | SStop => SStop
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

(* [comment removed for export] *)
Lemma sym_stepXBI_log : forall bc kx K i ss scr ss' scs scr',
  sym_stepXBI bc kx K i ss scr = SOk ss' scs scr' -> LOGSTEP ss ss'.
Proof.
  intros bc kx K i ss scr ss' scs scr' H. unfold sym_stepXBI in H.
  destruct (sym_stepBI bc kx segs i ss scr) as [ss1 scs1 scr1|] eqn:E; [|discriminate].
  destruct (Nat.leb (s_next ss) (s_next ss1)); [|discriminate]. injection H as <- _ _.
  unfold LOGSTEP. rewrite cap_rd_log. exact (sym_stepBI_log _ _ _ _ _ _ _ _ _ E).
Qed.

(* [comment removed for export] *)
Lemma sym_readBI_next : forall ss bc kx scr a n sx v scs scr' nx,
  sym_readBI segs ss bc kx scr a n sx = Some (v, scs, scr', nx) -> nx = s_next ss \/ nx = S (s_next ss).
Proof.
  intros ss bc kx scr a n sx v scs scr' nx H. unfold sym_readBI in H. cbv zeta in H.
  repeat (lazymatch type of H with
          | None = Some _ => discriminate H
          | Some _ = Some _ => injection H as _ _ _ <-
          | (match ?y with _ => _ end) = _ => destruct y
          | (let _ := ?y in _) = _ => cbv zeta in H
          end); first [left; reflexivity | right; reflexivity].
Qed.
Lemma sym_stepBI_next : forall bc kx i ss scr ss' scs scr',
  sym_stepBI bc kx segs i ss scr = SOk ss' scs scr' -> Nat.leb (s_next ss) (s_next ss') = true.
Proof.
  intros bc kx i ss scr ss' scs scr' H. unfold sym_stepBI in H. cbv beta zeta in H.
  destruct i; try discriminate H;
  repeat (lazymatch type of H with
          | SStop = SOk _ _ _ => discriminate H
          | SOk _ _ _ = SOk _ _ _ => injection H as <- E2 E3
          | (match sym_readBI ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 with _ => _ end) = _ =>
              let R := fresh "R" in
              destruct (sym_readBI a1 a2 a3 a4 a5 a6 a7 a8) as [[[[? ?] ?] ?]|] eqn:R;
              [apply sym_readBI_next in R|]
          | (match ?y with _ => _ end) = _ => destruct y
          | (let _ := ?y in _) = _ => cbv zeta in H
          end);
  cbn [s_next sset sjump];
  first [apply Nat.leb_refl
        | lazymatch goal with R : ?nx = _ \/ ?nx = _ |- _ => destruct R as [-> | ->]; apply Nat.leb_le; lia end].
Qed.
Definition sym_stepXBG (bc : bctx) (kx : kix) (dq : dqix) (lg : list lgrp) (x : lix) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match sym_stepBG bc kx dq lg x segs i ss scr with
  | SOk ss' scs scr' => SOk (cap_rd K i ss') (x_filterB bc ss ss' scs) scr'   (* [comment removed for export] *)
  | SStop => SStop
  end.
Lemma sym_stepXBG_eq : forall bc kx lg x np K i ss scr, LGCOV bc lg (s_log ss) -> LIXINV x np (s_log ss) -> sym_stepXBG bc kx (mk_dqix bc (bc_fk bc)) lg x K i ss scr = sym_stepXBI bc kx K i ss scr.
Proof.
  intros bc kx lg x np K i ss scr H HX. unfold sym_stepXBG, sym_stepXBI. rewrite (sym_stepBG_eq _ _ _ _ _ _ _ _ _ H HX).
  destruct (sym_stepBI bc kx segs i ss scr) as [ss' scs scr'|] eqn:E; [|reflexivity].
  rewrite (sym_stepBI_next _ _ _ _ _ _ _ _ E). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma sym_stepBI_logc : forall bc kx i ss scr ss' scs scr',
  sym_stepBI bc kx segs i ss scr = SOk ss' scs scr' ->
  if log_grows i then exists e, s_log ss' = e :: s_log ss else s_log ss' = s_log ss.
Proof.
  intros bc kx i ss scr ss' scs scr' H. unfold sym_stepBI in H. cbv beta zeta in H.
  destruct i; cbn [log_grows]; try discriminate H;
  repeat (lazymatch type of H with
          | SStop = SOk _ _ _ => discriminate H
          | SOk _ _ _ = SOk _ _ _ => injection H as <- E2 E3
          | (match ?x with _ => _ end) = _ => destruct x
          end);
  cbn [s_log sset sjump]; first [reflexivity | eexists; reflexivity].
Qed.
Lemma sym_stepXBI_logc : forall bc kx K i ss scr ss' scs scr',
  sym_stepXBI bc kx K i ss scr = SOk ss' scs scr' ->
  if log_grows i then exists e, s_log ss' = e :: s_log ss else s_log ss' = s_log ss.
Proof.
  intros bc kx K i ss scr ss' scs scr' H. unfold sym_stepXBI in H.
  destruct (sym_stepBI bc kx segs i ss scr) as [ss1 scs1 scr1|] eqn:E; [|discriminate].
  destruct (Nat.leb (s_next ss) (s_next ss1)); [|discriminate]. injection H as <- _ _.
  rewrite cap_rd_log. exact (sym_stepBI_logc _ _ _ _ _ _ _ _ E).
Qed.
Lemma lix_upd_inv : forall bc kx K i ss scr ss' scs scr' x np,
  LIXINV x np (s_log ss) -> sym_stepXBI bc kx K i ss scr = SOk ss' scs scr' ->
  LIXINV (fst (lix_upd x np i (s_log ss'))) (snd (lix_upd x np i (s_log ss'))) (s_log ss').
Proof.
  intros bc kx K i ss scr ss' scs scr' x np HI E. unfold lix_upd.
  pose proof (sym_stepXBI_logc _ _ _ _ _ _ _ _ _ E) as L.
  destruct (log_grows i).
  - destruct L as [e He]. rewrite He. cbn [fst snd]. apply lix_ins_inv. exact HI.
  - rewrite L. cbn [fst snd]. exact HI.
Qed.
Fixpoint sym_execTXBG_go (bc : bctx) (kx : kix) (dq : dqix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  (lg : list lgrp) (x : lix) (np : positive) : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_stepXBG bc kx dq lg x K i ss scr_nil with
          | SOk ss' [] _ =>
              let xn := lix_upd x np i (s_log ss') in   (* [comment removed for export] *)
              sym_execTXBG_go bc kx dq t K f false stops ss' (if s_clean ss' then ss' else ck) (lg_upd bc lg (s_log ss')) (fst xn) (snd xn)
          | _ => if s_clean ss then ss else ck
          end
      end
  end.
Definition sym_execTXBG (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  let xn := lix_of (s_log (clr ss)) in   (* [comment removed for export] *)
  sym_execTXBG_go bc kx (mk_dqix bc (bc_fk bc)) t K fuel first stops (clr ss) (clr ss) (lg_of bc (s_log (clr ss))) (fst xn) (snd xn).   (* [comment removed for export] *)
Lemma sym_execTXBG_go_eq : forall bc kx t K fuel first stops ss ck lg x np,
  LGCOV bc lg (s_log ss) -> LIXINV x np (s_log ss) ->
  sym_execTXBG_go bc kx (mk_dqix bc (bc_fk bc)) t K fuel first stops ss ck lg x np = sym_execTXBI_go bc kx t K fuel first stops ss ck.
Proof.
  intros bc kx t K fuel. induction fuel as [|f IH]; intros first stops ss ck lg x np H HX; [reflexivity|].
  cbn [sym_execTXBG_go sym_execTXBI_go].
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
  rewrite (sym_stepXBG_eq _ _ _ _ _ _ _ _ _ H HX).
  destruct (sym_stepXBI bc kx K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|reflexivity].
  destruct scs; [|reflexivity]. cbv zeta.
  apply IH. apply (lg_upd_cov bc lg ss ss' H). exact (sym_stepXBI_log _ _ _ _ _ _ _ _ _ E).
  exact (lix_upd_inv _ _ _ _ _ _ _ _ _ _ _ HX E).
Qed.
Lemma sym_execTXBG_eq : forall bc kx t K fuel first stops ss,
  sym_execTXBG bc kx t K fuel first stops ss = sym_execTXBI bc kx t K fuel first stops ss.
Proof.
  intros. unfold sym_execTXBG, sym_execTXBI. cbv zeta.
  pose proof (lix_of_inv (s_log (clr ss))) as HX. destruct (lix_of (s_log (clr ss))) as [x np]. cbn [fst snd].
  apply sym_execTXBG_go_eq. apply lg_of_cov. exact HX.
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
      | _ => if Z.ltb (hi - lo) (2 ^ 64) then diffbase (SA (ELit 0) lo) (ELit (hi - lo))
             else ([], [], hints)
      end
  | KZero (SA kb kk) len =>
      prune_zfB bc KZero (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_pB bc sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KFill (SA kb kk) len c =>
      prune_zfB bc (fun a n => KFill a n c) (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_pB bc sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KUnk (SA kb kk) len =>
      prune_zfB bc KUnk (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_pB bc sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
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
            let l := (l0 mod 2 ^ 64)%Z in
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
      else if in_sidesQ bc (sp_D sp) b2 k2 m2 then true   (* [comment removed for export] *)
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
  | KUnk (SA kb kk) len =>
      if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
      else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kunk_cutB bc (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
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

(* [comment removed for export] *)
Definition ranges_apart_pcqB (bc : bctx) (sp : sprep) (q : qix) (b1 : expr) (k1 : Z) (n1 : expr)
           (br2 : option (Z * Z)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, br2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then true
      else if qix_hit q b2 k2 m2 then true
      else ranges_apart_pcB bc sp b1 k1 n1 br2 b2 k2 n2
  | _, _ => ranges_apart_pcB bc sp b1 k1 n1 br2 b2 k2 n2
  end.
Lemma ranges_apart_pcqB_eq : forall bc sp, ranges_apart_pcqB bc sp (mk_qix bc (sp_D sp)) = ranges_apart_pcB bc sp.
Proof.
  intros bc sp. bcfe. unfold ranges_apart_pcqB.
  lazymatch goal with |- _ = ranges_apart_pcB _ _ ?b1 ?k1 ?n1 ?br2 ?b2 ?k2 ?n2 =>
    destruct n1 as [z1| | | | | | |]; try reflexivity; destruct n2 as [z2| | | | | | |]; try reflexivity;
    unfold ranges_apart_pcB; rewrite in_sidesQ_eqB;
    lazymatch goal with |- (if ?num then true else _) = _ => destruct num; [reflexivity|] end;
    destruct (qix_hit (mk_qix bc (sp_D sp)) b2 k2 (zlit64 z2)) eqn:Hq; [|reflexivity];
    apply qix_hit_in_sidesB in Hq; rewrite Hq; reflexivity
  end.
Qed.
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
  - destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|].
    unfold kunk_cut. destruct (ranges_apart_pc _ _ _ _ _ _ _ _ _); [reflexivity|].
    destruct (kcut KUnk allkn (a_base wa) (a_off wa) (elen w) kb kk len) eqn:E; [nfcrush|].
    cbn [fst]. rewrite <- E. apply kcut_nofacts. reflexivity.
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
Definition prune1pcK0 (bc : bctx) (sp : sprep) (q : qix) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
  (br2 : option (Z * Z)) : pk_res :=
  let k := a_off wa in
  let wb := a_base wa in
  let zfK (mk : saddr -> expr -> kentry) (kb : expr) (kk : Z) (len : expr) :=
    if same then
      match len with
      | ELit l0 => PRepl (ktrim mk kb kk l0 k w)
      | _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl (kcutB bc mk wb k (elen w) kb kk len)
      end
    else if ranges_apart_pcqB bc sp q wb k (elen w) br2 kb kk len then PKeep
    else match kcutB bc mk wb k (elen w) kb kk len with
         | [] => if ranges_apart_pcqB bc sp q wb k (elen w) br2 kb kk len then PKeep else PRepl []
         | cut => PRepl cut
         end in
  match K with
  | KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ => PKeep
  | KImg lo hi =>
      match wb with
      | ELit 0 =>
          let r1 := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
          let lo2 := Z.max lo (k + Z.of_nat w) in
          let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
          PRepl (r1 ++ r2)
      | _ => if Z.ltb (hi - lo) (2 ^ 64) then
               (if ranges_apart_pqB bc sp q wb k (elen w) (ELit 0) lo (ELit (hi - lo)) then PKeep else PRepl [])
             else PRepl []
      end
  | KZero (SA kb kk) len => zfK KZero kb kk len
  | KFill (SA kb kk) len c => zfK (fun a n => KFill a n c) kb kk len
  | KUnk (SA kb kk) len => zfK KUnk kb kk len
  | KWord (SA kb kk) w' v =>
      if same then (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool then PKeep else PRepl (kword_cut kb kk w' v k w))
      else if ranges_apart_pcqB bc sp q wb k (elen w) br2 kb kk (elen w') then PKeep
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool then PKeep
      else if ranges_apart_pcqB bc sp q wb k (elen w) br2 kb kk (elen w') then PKeep else PRepl []
  | KBlob (SA kb kk) len bk =>
      if same then
        match len with
        | ELit l0 => let l := (l0 mod 2 ^ 64)%Z in
                     if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool then PKeep else PRepl []
        | _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl []
        end
      else if ranges_apart_pcqB bc sp q wb k (elen w) br2 kb kk len then PKeep else PRepl []
  end.

Lemma prune1pcK0_eq : forall fk sp q wa w wv K br2 same,
  q = mk_qix (mkbc fk) (sp_D sp) ->   (* [comment removed for export] *)
  (match kbase K with Some kb => same = expr_eqb kb (a_base wa) | None => True end) ->
  pk_list K (prune1pcK0 (mkbc fk) sp q wa w wv K same br2) = fst (fst (prune1pc fk sp wa w wv K [] br2)).
Proof.
  intros fk sp q wa w wv K br2 same -> H.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    cbn [kbase] in H; try subst same; unfold prune1pcK0, prune1pc, prune1p, prune_zf, kzero_cut, kfill_cut, kunk_cut;
    rewrite ?ranges_apart_pcqB_eq, ?ranges_apart_pqB_eq;
    autorewrite with bceq; cbn [a_base a_off]; pk_crush.
Qed.

(* [comment removed for export] *)
Definition zf_keep (kk l0 k : Z) (w : nat) : bool :=
  (Z.ltb 0 l0 && Z.ltb l0 two64 && (Z.leb (kk + l0) k || Z.leb (k + Z.of_nat w) kk))%bool.
Lemma ktrim_keep : forall mk kb kk l0 k w,
  zf_keep kk l0 k w = true -> ktrim mk kb kk l0 k w = [mk (SA kb kk) (ELit l0)].
Proof.
  intros mk kb kk l0 k w H. unfold zf_keep in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. unfold two64 in H2.
  unfold ktrim. rewrite (Z.mod_small l0 (2 ^ 64)) by lia.
  apply Bool.orb_prop in H3. destruct H3 as [H3|H3]; apply Z.leb_le in H3.
  - rewrite (Z.min_r k (kk + l0)%Z) by lia.
    replace (kk <? kk + l0)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite (Z.max_r kk (k + Z.of_nat w)%Z) by lia.
    replace (k + Z.of_nat w <? kk + l0)%Z with false by (symmetry; apply Z.ltb_ge; lia).
    cbn [app]. replace (kk + l0 - kk)%Z with l0 by lia. reflexivity.
  - rewrite (Z.min_l k (kk + l0)%Z) by lia.
    replace (kk <? k)%Z with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite (Z.max_l kk (k + Z.of_nat w)%Z) by lia.
    replace (kk <? kk + l0)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [app]. replace (kk + l0 - kk)%Z with l0 by lia. reflexivity.
Qed.
Definition prune1pcK (bc : bctx) (sp : sprep) (q : qix) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
  (br2 : option (Z * Z)) : pk_res :=
  if (if same then match K with
                   | KZero (SA _ kk) (ELit l0) | KFill (SA _ kk) (ELit l0) _ | KUnk (SA _ kk) (ELit l0) => zf_keep kk l0 (a_off wa) w
                   | _ => false
                   end else false)
  then PKeep else prune1pcK0 bc sp q wa w wv K same br2.
Lemma prune1pcK_keep0 : forall bc sp q wa w wv K same br2,
  pk_list K (prune1pcK bc sp q wa w wv K same br2) = pk_list K (prune1pcK0 bc sp q wa w wv K same br2).
Proof.
  intros. unfold prune1pcK. destruct same; [|reflexivity].
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    try reflexivity; destruct len as [l0| | | | | | |]; try reflexivity;
    destruct (zf_keep kk l0 (a_off wa) w) eqn:HK; try reflexivity;
    cbn [pk_list]; unfold prune1pcK0; cbn [pk_list]; rewrite (ktrim_keep _ kb kk l0 (a_off wa) w HK); reflexivity.
Qed.
Lemma prune1pcK_eq : forall fk sp q wa w wv K br2 same,
  q = mk_qix (mkbc fk) (sp_D sp) ->
  (match kbase K with Some kb => same = expr_eqb kb (a_base wa) | None => True end) ->
  pk_list K (prune1pcK (mkbc fk) sp q wa w wv K same br2) = fst (fst (prune1pc fk sp wa w wv K [] br2)).
Proof. intros. rewrite prune1pcK_keep0. apply prune1pcK0_eq; assumption. Qed.

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

Record stx := STX { sx_a : saddr; sx_w : nat; sx_v : expr; sx_sp : sprep; sx_bid : positive; sx_br : option (Z * Z); sx_q : qix (* [comment removed for export] *) }.

Fixpoint mk_stxs (bc : bctx) (log : list sentry) (t : ntab) : list stx * ntab :=   (* [comment removed for export] *)
  match log with
  | [] => ([], t)
  | SE a w v :: older =>
      let '(sxs, t1) := mk_stxs bc older t in
      let '(r, t2) := intern bc t1 (a_base a) in
      let '(bid, bi) := r in
      let sp := mk_sprepB bc (a_base a) (a_off a) (elen w) in
      (sxs ++ [STX a w v sp bid (bi_br bi) (mk_qix bc (sp_D sp))], t2)   (* [comment removed for export] *)
  end.

Definition obrB (bc : bctx) (K : kentry) : option (Z * Z) :=
  match kbase K with Some kb => base_rangeB bc kb | None => None end.
Definition g1cB (bc : bctx) (sx : stx) (K : kentry) : list kentry :=
  fst (fst (prune1pcB bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K [] (obrB bc K))).
Fixpoint chain_slow (bc : bctx) (sxs : list stx) (l : list kentry) : list kentry :=
  match sxs with
  | [] => l
  | sx :: rest => chain_slow bc rest (flat_map (g1cB bc sx) l)
  end.
Fixpoint chainK (bc : bctx) (sxs : list stx) (K : kentry) (same_of : positive -> bool) (br2 : option (Z * Z)) : list kentry :=
  match sxs with
  | [] => [K]
  | sx :: rest =>
      match prune1pcK bc (sx_sp sx) (sx_q sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
      | PKeep => chainK bc rest K same_of br2
      | PRepl l => chain_slow bc rest l
      end
  end.
(* [comment removed for export] *)
Fixpoint chainK2 (bc : bctx) (sxs : list stx) (K : kentry) (okb : option expr) (same_of : positive -> bool) (br2 : option (Z * Z)) : list kentry :=
  match sxs with
  | [] => [K]
  | sx :: rest =>
      match prune1pcK bc (sx_sp sx) (sx_q sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
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


Fixpoint entriesV (bc : bctx) (sxs : list stx) (kn : list kentry) (t : ntab) : list kentry :=
  match kn with
  | [] => []
  | K :: rest =>
      match kbase K with
      | Some kb => let '(r, t') := intern bc t kb in
                   let '(bid, bi) := r in
                   chainK2 bc sxs K (Some kb) (Pos.eqb bid) (bi_br bi) ++ entriesV bc sxs rest t'
      | None => chainK2 bc sxs K None (fun _ => false) None ++ entriesV bc sxs rest t
      end
  end.
Fixpoint stores_part (bc : bctx) (sxs : list stx) : list kentry :=   (* [comment removed for export] *)
  match sxs with
  | [] => []
  | sx :: newer => stores_part bc newer ++ chainK2 bc newer (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx)
  end.
Definition carryV (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t) := mk_stxs bc log nt_empty in
  stores_part bc sxs ++ entriesV bc sxs kn t.
(* [comment removed for export] *)
Definition carryK0 (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryV bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.

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
  /\ sx_sp sx = mk_sprepB bc (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))
  /\ sx_q sx = mk_qix bc (sp_D (sx_sp sx)).   (* [comment removed for export] *)

Lemma g1cB_eq : forall fk sx,
  sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx)) ->
  flat_map (g1cB (mkbc fk) sx) = FM fk (strip sx).
Proof.
  intros fk sx Hsp. apply functional_extensionality; intros l. unfold FM, strip. f_equal.
  apply functional_extensionality; intros K. unfold g1cB, obrB. rewrite Hsp. autorewrite with bceq.
  rewrite p_prune1pc_eq by (destruct (kbase K); reflexivity). rewrite prune1p_nil. reflexivity.
Qed.
Lemma chain_slow_eq : forall fk sxs l,
  Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))
                    /\ sx_q sx = mk_qix (mkbc fk) (sp_D (sx_sp sx))) sxs ->
  chain_slow (mkbc fk) sxs l = chainRo fk (map strip sxs) l.
Proof.
  intros fk sxs. induction sxs as [|sx rest IH]; intros l HF; [reflexivity|].
  apply Forall_cons_iff in HF as [[H1 H1q] HF]. cbn [chain_slow chainRo map]. rewrite (g1cB_eq _ _ H1). apply IH. exact HF.
Qed.
Lemma chainK_eq : forall fk sxs K same_of br2,
  Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))
                    /\ sx_q sx = mk_qix (mkbc fk) (sp_D (sx_sp sx))) sxs ->
  match kbase K with
  | Some kb => br2 = base_rangeB (mkbc fk) kb /\ Forall (fun sx => same_of (sx_bid sx) = expr_eqb kb (a_base (sx_a sx))) sxs
  | None => br2 = None
  end ->
  chainK (mkbc fk) sxs K same_of br2 = chain_slow (mkbc fk) sxs [K].
Proof.
  intros fk sxs. induction sxs as [|sx rest IH]; intros K same_of br2 HS HK; [reflexivity|].
  apply Forall_cons_iff in HS as [[H1 H1q] HS]. cbn [chainK chain_slow flat_map]. rewrite app_nil_r.
  unfold g1cB at 1.
  assert (E : pk_list K (prune1pcK (mkbc fk) (sx_sp sx) (sx_q sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2)
              = fst (fst (prune1pcB (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K [] (obrB (mkbc fk) K)))).
  { autorewrite with bceq. destruct (kbase K) as [kb|] eqn:HB.
    - destruct HK as [-> HK]. apply Forall_cons_iff in HK as [HK1 HK].
      unfold obrB. rewrite HB. apply (prune1pcK_eq _ _ _ _ _ _ _ _ _ H1q). rewrite HB. exact HK1.
    - unfold obrB. rewrite HB. subst br2. apply (prune1pcK_eq _ _ _ _ _ _ _ _ _ H1q). rewrite HB. exact I. }
  destruct (prune1pcK _ _ _ _ _ _ K _ br2) as [|l]; cbn [pk_list] in E.
  - rewrite <- E. apply IH; [exact HS|]. destruct (kbase K) as [kb|]; [|exact HK].
    destruct HK as [Hbr HK]. apply Forall_cons_iff in HK as [_ HK]. exact (conj Hbr HK).
  - rewrite <- E. reflexivity.
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
  Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))
                    /\ sx_q sx = mk_qix (mkbc fk) (sp_D (sx_sp sx))) sxs ->
  okb = kbase K ->
  match okb with
  | Some kb => br2 = base_rangeB (mkbc fk) kb /\ Forall (fun sx => same_of (sx_bid sx) = expr_eqb kb (a_base (sx_a sx))) sxs
  | None => br2 = None
  end ->
  chainK2 (mkbc fk) sxs K okb same_of br2 = chain_slow (mkbc fk) sxs [K].
Proof.
  intros fk sxs. induction sxs as [|sx rest IH]; intros K okb same_of br2 HS Hokb HK; [reflexivity|].
  apply Forall_cons_iff in HS as [[H1 H1q] HS]. cbn [chainK2 chain_slow flat_map]. rewrite app_nil_r.
  unfold g1cB at 1.
  assert (E : pk_list K (prune1pcK (mkbc fk) (sx_sp sx) (sx_q sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2)
              = fst (fst (prune1pcB (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K [] (obrB (mkbc fk) K)))).
  { autorewrite with bceq. unfold obrB. rewrite <- Hokb. destruct okb as [kb|].
    - destruct HK as [-> HK]. apply Forall_cons_iff in HK as [HK1 HK]. apply (prune1pcK_eq _ _ _ _ _ _ _ _ _ H1q). rewrite <- Hokb. exact HK1.
    - subst br2. apply (prune1pcK_eq _ _ _ _ _ _ _ _ _ H1q). rewrite <- Hokb. exact I. }
  destruct (prune1pcK _ _ _ _ _ _ K _ br2) as [|l]; cbn [pk_list] in E; rewrite <- E.
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
Proof. intros bc t t' sx Hm (H1 & H2 & H3 & H4). split; [apply Hm; exact H1|]. repeat split; assumption. Qed.

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
      * constructor; [|constructor]. split; [exact HIn|]. split; [reflexivity|]. split; reflexivity.
    + split; [rewrite map_app, Hmap; reflexivity|]. intros k p Hp. apply Hm2. apply Hm1. exact Hp.
Qed.

Lemma Forall_SX_sp : forall fk t sxs, Forall (SX_OK (mkbc fk) t) sxs ->
  Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))
                    /\ sx_q sx = mk_qix (mkbc fk) (sp_D (sx_sp sx))) sxs.   (* [comment removed for export] *)
Proof. intros fk t sxs H. apply Forall_impl with (P := SX_OK (mkbc fk) t); [|exact H]. intros sx (_ & _ & X & Y). exact (conj X Y). Qed.

Lemma Forall_SX_same : forall fk t sxs kb bid,
  NTI (mkbc fk) t -> In (kb, bid) (nt_bucket t (bkey kb)) -> Forall (SX_OK (mkbc fk) t) sxs ->
  Forall (fun sx => Pos.eqb bid (sx_bid sx) = expr_eqb kb (a_base (sx_a sx))) sxs.
Proof.
  intros fk t sxs kb bid HT HIn H. apply Forall_impl with (P := SX_OK (mkbc fk) t); [|exact H].
  intros sx (H1 & _ & _). exact (nt_same_eq _ _ _ _ _ _ HT HIn H1).
Qed.

Lemma entriesV_eq : forall fk sxs kn t,
  NTI (mkbc fk) t -> Forall (SX_OK (mkbc fk) t) sxs ->
  entriesV (mkbc fk) sxs kn t = chainRo fk (map strip sxs) kn.
Proof.
  intros fk sxs kn. induction kn as [|K rest IH]; intros t HT HS.
  - cbn. clear. induction sxs as [|sx r IH]; [reflexivity|]. cbn. destruct (strip sx). exact IH.
  - cbn [entriesV]. change (K :: rest) with ([K] ++ rest). rewrite chainRo_app.
    destruct (kbase K) as [kb|] eqn:HB.
    + destruct (intern (mkbc fk) t kb) as [[bid bi] t'] eqn:EI.
      destruct (intern_ok _ _ _ _ _ _ HT EI) as (HT' & -> & HIn & Hm).
      assert (HS' : Forall (SX_OK (mkbc fk) t') sxs).
      { apply Forall_impl with (P := SX_OK (mkbc fk) t); [|exact HS]. intros sx. apply SX_OK_mono. exact Hm. }
      rewrite (IH t' HT' HS'). f_equal.
      rewrite chainK2_eq; [apply chain_slow_eq; exact (Forall_SX_sp _ _ _ HS) | exact (Forall_SX_sp _ _ _ HS) | symmetry; exact HB |].
      cbn [bi_br]. split; [reflexivity|]. exact (Forall_SX_same _ _ _ _ _ HT' HIn HS').
    + rewrite (IH t HT HS). f_equal.
      rewrite chainK2_eq; [apply chain_slow_eq; exact (Forall_SX_sp _ _ _ HS) | exact (Forall_SX_sp _ _ _ HS) | symmetry; exact HB |].
      reflexivity.
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

Lemma carryK0_eq : forall log kn hints,
  carryK0 (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof.
  intros log kn hints. unfold carryK0. destruct log as [|s older]; [reflexivity|].
  destruct hints as [|h hs]; [|apply carryB_eq].
  rewrite carry_vertical. unfold carryV.
  destruct (mk_stxs (mkbc (facts_of kn)) (s :: older) nt_empty) as [sxs t] eqn:E.
  destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT & HS & Hmap & _).
  rewrite (stores_part_eq _ _ _ HT HS), (entriesV_eq _ _ _ _ HT HS), Hmap. reflexivity.
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
Definition gval : Type := (positive * option (Z * Z) * (Z * Z) * expr)%type.   (* [comment removed for export] *)
Definition gtab := ptree (gval * positive).   (* [comment removed for export] *)
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
Definition bnd_add (gs : gst) (gid bid : positive) (obr : option (Z * Z)) (lo hi : Z) (kb : expr) : gst :=
  GST (gs_gid gs) (gs_next gs)
      (match pt_get (gs_bnds gs) gid with
       | Some ((b, o, (l, h), e), n) => pt_set gid ((b, o, (Z.min l lo, Z.max h hi), e), Pos.succ n) (gs_bnds gs)   (* [comment removed for export] *)
       | None => pt_set gid ((bid, obr, (lo, hi), kb), xH) (gs_bnds gs)
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
                             | Some m => let '(gid, gs0) := ggroup gs bid kk in (gid, bnd_add gs0 gid bid (bi_br bi) kk (kk + m)%Z kb)
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
  | (b, obr, (glo, ghi), _) =>
      if Pos.eqb b (sx_bid sx) then false else
      match sp_rng (sx_sp sx), obr with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + a_off (sx_a sx) + sx_m1 sx - lo2) glo || Z.leb ghi (lo1 + a_off (sx_a sx) - hi2))%bool
      | _, _ => false
      end
  end.
(* [comment removed for export] *)
Definition wverdict (sx : stx) (g : gval) : bool :=
  match g with
  | (b, _, (glo, ghi), gkb) => if Pos.eqb b (sx_bid sx) then false else qix_hit (sx_q sx) gkb glo (ghi - glo)
  end.
Local Open Scope Z_scope.
Definition pside_fit (bc : bctx) (gkb : expr) (glo gn : Z) (cm : saddr * expr) : bool :=
  xinside_plainB bc gkb glo gn (a_base (fst cm)) (a_off (fst cm)) (snd cm).
Definition pverdict (bc : bctx) (sx : stx) (g : gval) : bool :=
  match g with (b, _, (glo, ghi), gkb) =>
    if Pos.eqb b (sx_bid sx) then false
    else if ((0 <=? ghi - glo) && (ghi - glo <? 2 ^ 63))%bool then existsb (pside_fit bc gkb glo (ghi - glo)) (sp_D (sx_sp sx)) else false
  end.
Local Close Scope Z_scope.
Definition gverdict (bc : bctx) (sx : stx) (g : gval) : bool := if verdict sx g then true else if wverdict sx g then true else pverdict bc sx g.   (* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint mk_fl (bc : bctx) (g : gval) (sxs : list stx) : list (stx * list stx) :=
  match sxs with
  | [] => []
  | sx :: rest => if gverdict bc sx g then mk_fl bc g rest else (sx, rest) :: mk_fl bc g rest
  end.
Definition gfl : Type := (gval * list (stx * list stx))%type.
(* [comment removed for export] *)
Fixpoint mk_flv (v : stx -> bool) (sxs : list stx) : list (stx * list stx) :=
  match sxs with
  | [] => []
  | sx :: rest => if v sx then mk_flv v rest else (sx, rest) :: mk_flv v rest
  end.
Lemma mk_fl_flv : forall bc g sxs, mk_fl bc g sxs = mk_flv (fun sx => gverdict bc sx g) sxs.
Proof. intros bc g sxs. induction sxs as [|sx rest IH]; [reflexivity|]. cbn [mk_fl mk_flv]. rewrite IH. reflexivity. Qed.
Definition GMIN : positive := 6%positive.
Definition mk_gl (bc : bctx) (bnds : gtab) (sxs : list stx) : ptree gfl :=
  pt_map (fun gn : gval * positive => let '(g, n) := gn in (g, if Pos.ltb n GMIN then mk_flv (fun _ => false) sxs else mk_fl bc g sxs)) bnds.

Definition obr_eqb (a b : option (Z * Z)) : bool :=
  match a, b with
  | Some (x1, y1), Some (x2, y2) => Z.eqb x1 x2 && Z.eqb y1 y2
  | None, None => true
  | _, _ => false
  end%bool.
(* [comment removed for export] *)
Definition inb (g : gval) (ei : einfo) : bool :=
  match ei_m ei, g with
  | Some m, (b, obr, (lo, hi), gkb) =>
      Pos.eqb b (ei_bid ei) && expr_eqb gkb (ei_kb ei) && obr_eqb obr (ei_br ei) && Z.leb lo (ei_k ei) && Z.leb (ei_k ei + m) hi
  | _, _ => false
  end%bool.

Fixpoint chainKF (bc : bctx) (fl : list (stx * list stx)) (K : kentry) (okb : option expr) (same_of : positive -> bool)
         (br2 : option (Z * Z)) : list kentry :=
  match fl with
  | [] => [K]
  | (sx, rest) :: fl' =>
      match prune1pcK bc (sx_sp sx) (sx_q sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
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

(* [comment removed for export] *)
Local Open Scope Z_scope.
Definition sgrp : Type := (positive * option (Z * Z) * Z * Z * expr)%type.   (* [comment removed for export] *)
Definition sx_e (sx : stx) : Z := a_off (sx_a sx) + Z.of_nat (sx_w sx).
Fixpoint sh_add (h : list sgrp) (sx : stx) : list sgrp :=
  match h with
  | [] => [(sx_bid sx, sx_br sx, a_off (sx_a sx), sx_e sx, a_base (sx_a sx))]
  | (b, obr, lo, hi, gkb) :: r =>
      if (Pos.eqb b (sx_bid sx) && obr_eqb obr (sx_br sx) && expr_eqb gkb (a_base (sx_a sx)))%bool
      then (b, obr, Z.min lo (a_off (sx_a sx)), Z.max hi (sx_e sx), gkb) :: r
      else (b, obr, lo, hi, gkb) :: sh_add r sx
  end.
Definition sh_skip1 (dq : dqix) (sx : stx) (g : sgrp) : bool :=
  match g with (b, obr, lo, hi, gkb) =>
  let kk := a_off (sx_a sx) in
  if Pos.eqb (sx_bid sx) b then (Z.leb (kk + Z.of_nat (sx_w sx)) lo || Z.leb hi kk)%bool
  else if match obr, sx_br sx with
          | Some (lo1, hi1), Some (lo2, hi2) => (Z.leb (hi1 + hi) (lo2 + kk) || Z.leb (hi2 + kk + zlit64 (Z.of_nat (sx_w sx))) (lo1 + lo))%bool
          | _, _ => false
          end then true
  else dq_witness dq (a_base (sx_a sx)) kk (zlit64 (Z.of_nat (sx_w sx))) gkb lo hi   (* [comment removed for export] *)
  end.
Definition sh_skip (dq : dqix) (sx : stx) (h : list sgrp) : bool := forallb (sh_skip1 dq sx) h.
Definition SH_COV (h : list sgrp) (sx : stx) : Prop :=
  exists lo hi, In (sx_bid sx, sx_br sx, lo, hi, a_base (sx_a sx)) h /\ lo <= a_off (sx_a sx) /\ sx_e sx <= hi.
Fixpoint stores_partH (bc : bctx) (dq : dqix) (sxs : list stx) : list kentry * list sgrp :=
  match sxs with
  | [] => ([], [])
  | sx :: newer =>
      let '(res, h) := stores_partH bc dq newer in
      let K := KWord (sx_a sx) (sx_w sx) (sx_v sx) in
      (res ++ (if sh_skip dq sx h then [K] else chainK2 bc newer K (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx)),
       sh_add h sx)
  end.
Local Close Scope Z_scope.

(* [comment removed for export] *)
Local Open Scope Z_scope.
Definition gkey3 : Type := (positive * option (Z * Z) * expr)%type.
Definition key_of (sx : stx) : gkey3 := (sx_bid sx, sx_br sx, a_base (sx_a sx)).
Definition key_eqb (a b : gkey3) : bool :=
  match a, b with (b1, r1, e1), (b2, r2, e2) => (Pos.eqb b1 b2 && obr_eqb r1 r2 && expr_eqb e1 e2)%bool end.
Fixpoint mk_flb (k : gkey3) (sxs : list stx) : list (stx * list stx) :=
  match sxs with
  | [] => []
  | sxj :: rest => if key_eqb k (key_of sxj) then (sxj, rest) :: mk_flb k rest else mk_flb k rest
  end.
Record grp3 := G3 { g_bid : positive; g_br : option (Z * Z); g_kb : expr; g_lo : Z; g_hi : Z;
                    g_D : list (saddr * expr); g_fl : list (stx * list stx) }.
Definition g_key (g : grp3) : gkey3 := (g_bid g, g_br g, g_kb g).
Definition g_same (g : grp3) (sx : stx) : bool := key_eqb (g_key g) (key_of sx).
Definition side_eqb (x y : saddr * expr) : bool :=
  match x, y with (c, m), (c', m') => mkey_eqb c c' m m' end.
Definition Dmeet (D1 D2 : list (saddr * expr)) : list (saddr * expr) := List.filter (fun x => existsb (side_eqb x) D2) D1.
Fixpoint sh3_add (h : list grp3) (sx : stx) (newer : list stx) (found : bool) : list grp3 :=
  match h with
  | [] => if found then []
          else [G3 (sx_bid sx) (sx_br sx) (a_base (sx_a sx)) (a_off (sx_a sx)) (sx_e sx) (sp_D (sx_sp sx))
                   ((sx, newer) :: mk_flb (key_of sx) newer)]
  | g :: r =>
      if g_same g sx
      then G3 (g_bid g) (g_br g) (g_kb g) (Z.min (g_lo g) (a_off (sx_a sx))) (Z.max (g_hi g) (sx_e sx))
              (Dmeet (g_D g) (sp_D (sx_sp sx))) ((sx, newer) :: g_fl g) :: sh3_add r sx newer true
      else g :: sh3_add r sx newer found
  end.
Fixpoint sh3_of (sxs : list stx) : list grp3 :=
  match sxs with [] => [] | sx :: newer => sh3_add (sh3_of newer) sx newer false end.
Definition sideK_fit (bc : bctx) (kb : expr) (kk n : Z) (x : saddr * expr) : bool :=
  match x with (c, m) => sub_itvB bc kb kk n c m end.
(* [comment removed for export] *)
Definition gskip3 (bc : bctx) (sx : stx) (g : grp3) : bool :=
  let kb := a_base (sx_a sx) in let kk := a_off (sx_a sx) in let n := zlit64 (Z.of_nat (sx_w sx)) in
  if Pos.eqb (sx_bid sx) (g_bid g) then false
  else if match g_br g, sx_br sx with
          | Some (lo1, hi1), Some (lo2, hi2) => (Z.leb (hi1 + g_hi g) (lo2 + kk) || Z.leb (hi2 + kk + n) (lo1 + g_lo g))%bool
          | _, _ => false
          end then true
  else if existsb (fun x => if okeq (fvar kb) (fvar (a_base (fst x))) then sideK_fit bc kb kk n x else false) (g_D g) then true
  else existsb (fun x => if okeq (fvar kb) (fvar (a_base (fst x))) then false else sideK_fit bc kb kk n x) (g_D g).
Definition off_apart (sx sxj : stx) : bool :=
  (Z.leb (a_off (sx_a sx) + Z.of_nat (sx_w sx)) (a_off (sx_a sxj)) || Z.leb (a_off (sx_a sxj) + Z.of_nat (sx_w sxj)) (a_off (sx_a sx)))%bool.
(* [comment removed for export] *)
Fixpoint walk3 (bc : bctx) (sx : stx) (fl : list (stx * list stx)) (K : kentry) : list kentry :=
  match fl with
  | [] => [K]
  | (sxj, rest) :: fl' =>
      if (Pos.eqb (sx_bid sx) (sx_bid sxj) && off_apart sx sxj)%bool then walk3 bc sx fl' K
      else
        match prune1pcK bc (sx_sp sxj) (sx_q sxj) (sx_a sxj) (sx_w sxj) (sx_v sxj) K (Pos.eqb (sx_bid sx) (sx_bid sxj)) (sx_br sx) with
        | PKeep => walk3 bc sx fl' K
        | PRepl l =>
            flat_map (fun K' => match kbase K' with
                                | Some kb' => if expr_eqb kb' (a_base (sx_a sx))
                                              then chainK2 bc rest K' (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx)
                                              else chain_slow bc rest [K']
                                | None => chain_slow bc rest [K']
                                end) l
        end
  end.
Definition chain3 (bc : bctx) (h : list grp3) (sx : stx) (newer : list stx) : list kentry :=
  let K := KWord (sx_a sx) (sx_w sx) (sx_v sx) in
  if forallb (fun g => if g_same g sx then true else gskip3 bc sx g) h then
    match List.find (fun g => g_same g sx) h with
    | None => [K]
    | Some g => if (Z.leb (a_off (sx_a sx) + Z.of_nat (sx_w sx)) (g_lo g) || Z.leb (g_hi g) (a_off (sx_a sx)))%bool then [K]
                else walk3 bc sx (g_fl g) K
    end
  else chainK2 bc newer K (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx).
Fixpoint stores_part3 (bc : bctx) (sxs : list stx) : list kentry * list grp3 :=
  match sxs with
  | [] => ([], [])
  | sx :: newer => let '(res, h) := stores_part3 bc newer in (res ++ chain3 bc h sx newer, sh3_add h sx newer false)
  end.
Local Close Scope Z_scope.

Definition carryG (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxs bc log nt_empty in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, _) := r in
  fst (stores_part3 bc sxs) ++ entriesG bc sxs (mk_gl bc (gs_bnds gs) sxs) kn infos.   (* [comment removed for export] *)

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

Lemma prune1pcK0_keep_based : forall bc sp q wa w wv K kb kk m lo1 hi1 lo2 hi2,
  kbase K = Some kb -> kdescr K = Some (kb, kk, Some m) ->
  sp_rng sp = Some (lo1, hi1) -> base_rangeB bc kb = Some (lo2, hi2) ->
  (hi1 + a_off wa + zlit64 (Z.of_nat w) <= lo2 + kk \/ hi2 + kk + m <= lo1 + a_off wa)%Z ->
  prune1pcK0 bc sp q wa w wv K false (base_rangeB bc kb) = PKeep.
Proof.
  intros bc sp q wa w wv K kb kk m lo1 hi1 lo2 hi2 HB HD Hsp Hbr Hnum.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [kbase kdescr] in HB, HD; try discriminate; injection HB as ->;
    try (injection HD as <- <-); try (destruct len as [z| | | | | | |]; try discriminate; injection HD as <- <-);
    unfold prune1pcK0; cbn [a_base a_off]; unfold ranges_apart_pcqB; cbn [elen]; rewrite Hsp, Hbr;
    match goal with |- context [if ((?a <=? ?b) || (?c <=? ?d))%Z then _ else _] =>
      replace ((a <=? b) || (c <=? d))%Z%bool with true; [reflexivity|];
      symmetry; apply Bool.orb_true_iff; destruct Hnum as [H|H]; [left|right]; apply Z.leb_le; rewrite ?zlit64_idem; lia end.
Qed.

Lemma prune1pcK0_keep_img : forall bc sp q wa w wv lo hi m lo1 hi1 lo2 hi2 same br2,
  kdescr (KImg lo hi) = Some (ELit 0%Z, lo, Some m) ->
  expr_eqb (ELit 0%Z) (a_base wa) = false ->
  sp_rng sp = Some (lo1, hi1) -> base_rangeB bc (ELit 0%Z) = Some (lo2, hi2) ->
  (hi1 + a_off wa + zlit64 (Z.of_nat w) <= lo2 + lo \/ hi2 + lo + m <= lo1 + a_off wa)%Z ->
  prune1pcK0 bc sp q wa w wv (KImg lo hi) same br2 = PKeep.
Proof.
  intros bc sp q wa w wv lo hi m lo1 hi1 lo2 hi2 same br2 HD Hne Hsp Hbr Hnum.
  cbn [kdescr] in HD. destruct (Z.ltb (hi - lo) (2 ^ 64)) eqn:Hlt; [|discriminate]. injection HD as <-.
  unfold prune1pcK0. destruct wa as [wb k]. cbn [a_base a_off] in *.
  assert (STEP : (if ranges_apart_pqB bc sp q wb k (elen w) (ELit 0%Z) lo (ELit (hi - lo)) then PKeep else PRepl []) = PKeep).
  { unfold ranges_apart_pqB, ranges_apart_pB. cbn [elen]. destruct (qix_hit q (ELit 0%Z) lo (zlit64 (hi - lo))); [reflexivity|]. rewrite Hsp, Hbr.
    match goal with |- context [if ((?a <=? ?b) || (?c <=? ?d))%Z then _ else _] =>
      replace ((a <=? b) || (c <=? d))%Z%bool with true; [reflexivity|];
      symmetry; apply Bool.orb_true_iff; destruct Hnum as [H|H]; [left|right]; apply Z.leb_le; rewrite ?zlit64_idem; lia end. }
  rewrite Hlt. destruct wb as [z| | | | | | |]; try exact STEP.
  destruct z; try exact STEP. cbn in Hne. discriminate.
Qed.

(* [comment removed for export] *)
Lemma prune1pcK_keep_based : forall bc sp q wa w wv K kb kk m lo1 hi1 lo2 hi2,
  kbase K = Some kb -> kdescr K = Some (kb, kk, Some m) ->
  sp_rng sp = Some (lo1, hi1) -> base_rangeB bc kb = Some (lo2, hi2) ->
  (hi1 + a_off wa + zlit64 (Z.of_nat w) <= lo2 + kk \/ hi2 + kk + m <= lo1 + a_off wa)%Z ->
  prune1pcK bc sp q wa w wv K false (base_rangeB bc kb) = PKeep.
Proof. intros. unfold prune1pcK. eapply prune1pcK0_keep_based; eassumption. Qed.
Lemma prune1pcK_keep_img : forall bc sp q wa w wv lo hi m lo1 hi1 lo2 hi2 same br2,
  kdescr (KImg lo hi) = Some (ELit 0%Z, lo, Some m) ->
  expr_eqb (ELit 0%Z) (a_base wa) = false ->
  sp_rng sp = Some (lo1, hi1) -> base_rangeB bc (ELit 0%Z) = Some (lo2, hi2) ->
  (hi1 + a_off wa + zlit64 (Z.of_nat w) <= lo2 + lo \/ hi2 + lo + m <= lo1 + a_off wa)%Z ->
  prune1pcK bc sp q wa w wv (KImg lo hi) same br2 = PKeep.
Proof. intros. unfold prune1pcK. destruct same; eapply prune1pcK0_keep_img; eassumption. Qed.

(* [comment removed for export] *)
Definition EINF (bc : bctx) (t : ntab) (K : kentry) (oi : option einfo) : Prop :=
  match oi with
  | None => kdescr K = None
  | Some ei => kdescr K = Some (ei_kb ei, ei_k ei, ei_m ei)
               /\ In (ei_kb ei, ei_bid ei) (nt_bucket t (bkey (ei_kb ei)))
               /\ ei_br ei = base_rangeB bc (ei_kb ei)
  end.
Lemma EINF_mono : forall bc t t' K oi,
  (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k)) -> EINF bc t K oi -> EINF bc t' K oi.
Proof. intros bc t t' K [ei|] Hm H; cbn [EINF] in *; [|exact H]. destruct H as (A & B & C). split; [exact A|]. split; [apply Hm; exact B| exact C]. Qed.

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

Lemma chainKF_eqv : forall bc (v : stx -> bool) sxs K okb same_of br2,
  (forall sx, In sx sxs -> v sx = true ->
     prune1pcK bc (sx_sp sx) (sx_q sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 = PKeep) ->
  chainKF bc (mk_flv v sxs) K okb same_of br2 = chainK2 bc sxs K okb same_of br2.
Proof.
  intros bc v sxs. induction sxs as [|sx rest IH]; intros K okb same_of br2 Hf; [reflexivity|].
  cbn [mk_flv chainK2].
  assert (IH' : chainKF bc (mk_flv v rest) K okb same_of br2 = chainK2 bc rest K okb same_of br2)
    by (apply IH; intros; apply Hf; [right|]; assumption).
  destruct (v sx) eqn:Hv.
  - rewrite (Hf sx (or_introl eq_refl) Hv). exact IH'.
  - cbn [chainKF]. destruct (prune1pcK _ _ _ _ _ _ K _ br2); [exact IH'|reflexivity].
Qed.
Lemma chainKF_eq : forall bc g sxs K okb same_of br2,
  (forall sx, In sx sxs -> gverdict bc sx g = true ->
     prune1pcK bc (sx_sp sx) (sx_q sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 = PKeep) ->
  chainKF bc (mk_fl bc g sxs) K okb same_of br2 = chainK2 bc sxs K okb same_of br2.
Proof. intros. rewrite mk_fl_flv. apply chainKF_eqv. assumption. Qed.

(* [comment removed for export] *)
Lemma verdict_inb_num : forall sx g ei m,
  verdict sx g = true -> inb g ei = true -> ei_m ei = Some m ->
  Pos.eqb (ei_bid ei) (sx_bid sx) = false
  /\ exists lo1 hi1 lo2 hi2, sp_rng (sx_sp sx) = Some (lo1, hi1) /\ ei_br ei = Some (lo2, hi2)
     /\ (hi1 + a_off (sx_a sx) + zlit64 (Z.of_nat (sx_w sx)) <= lo2 + ei_k ei \/ hi2 + ei_k ei + m <= lo1 + a_off (sx_a sx))%Z.
Proof.
  intros sx [[[b obr] [glo ghi]] gkb] ei m Hv Hi Hm. unfold verdict in Hv. unfold inb in Hi. rewrite Hm in Hi.
  apply andb_prop in Hi as [Hi H4]. apply andb_prop in Hi as [Hi H3]. apply andb_prop in Hi as [Hi H2]. apply andb_prop in Hi as [H1 H1e].
  apply Pos.eqb_eq in H1. subst b. apply Z.leb_le in H3. apply Z.leb_le in H4.
  destruct (Pos.eqb (ei_bid ei) (sx_bid sx)); [discriminate|]. split; [reflexivity|].
  destruct (sp_rng (sx_sp sx)) as [[lo1 hi1]|]; [|discriminate].
  destruct obr as [[lo2 hi2]|]; [|discriminate].
  destruct (ei_br ei) as [[x2 y2]|]; [|discriminate]. cbn [obr_eqb] in H2. apply andb_prop in H2 as [X Y].
  apply Z.eqb_eq in X. apply Z.eqb_eq in Y. subst x2 y2.
  exists lo1, hi1, lo2, hi2. split; [reflexivity|]. split; [reflexivity|].
  unfold sx_m1 in Hv. apply Bool.orb_prop in Hv. destruct Hv as [H|H]; apply Z.leb_le in H; lia.
Qed.

(* [comment removed for export] *)
Lemma qsides_hit_mono : forall l b lo n k m,
  qsides_hit l b lo n = true -> (lo <= k)%Z -> (k + m <= lo + n)%Z -> qsides_hit l b k m = true.
Proof.
  intros l b lo n k m H Hlo Hhi. induction l as [|[c ml] r IH]; [cbn in H; discriminate|].
  cbn [qsides_hit] in H |- *.
  destruct ((a_off c <=? lo)%Z && (lo + n <=? a_off c + ml)%Z)%bool eqn:Hoff.
  - destruct (expr_eqb b (a_base c)) eqn:Heq.
    + apply andb_prop in Hoff as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
      replace ((a_off c <=? k)%Z && (k + m <=? a_off c + ml)%Z)%bool with true; [reflexivity|].
      symmetry. apply andb_true_intro. split; apply Z.leb_le; lia.
    + rewrite (IH H). destruct (if (_ && _)%bool then _ else _); reflexivity.
  - rewrite (IH H). destruct (if (_ && _)%bool then _ else _); reflexivity.
Qed.
Lemma wverdict_inb : forall sx g ei m,
  wverdict sx g = true -> inb g ei = true -> ei_m ei = Some m ->
  Pos.eqb (ei_bid ei) (sx_bid sx) = false /\ qix_hit (sx_q sx) (ei_kb ei) (ei_k ei) m = true.
Proof.
  intros sx [[[b obr] [glo ghi]] gkb] ei m Hv Hi Hm. unfold wverdict in Hv. unfold inb in Hi. rewrite Hm in Hi.
  apply andb_prop in Hi as [Hi H4]. apply andb_prop in Hi as [Hi H3]. apply andb_prop in Hi as [Hi H2]. apply andb_prop in Hi as [H1 H1e].
  apply Pos.eqb_eq in H1. subst b. apply p_expr_eqb_eq in H1e. subst gkb. apply Z.leb_le in H3. apply Z.leb_le in H4.
  destruct (Pos.eqb (ei_bid ei) (sx_bid sx)); [discriminate|]. split; [reflexivity|].
  unfold qix_hit in Hv |- *. eapply qsides_hit_mono; [exact Hv | lia | lia].
Qed.
Lemma prune1pcK_keep_win : forall bc sp q wa w wv K kb kk m br2,
  kbase K = Some kb -> kdescr K = Some (kb, kk, Some m) -> qix_hit q kb kk m = true ->
  prune1pcK bc sp q wa w wv K false br2 = PKeep.
Proof.
  intros bc sp q wa w wv K kb kk m br2 HB HD Hq.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [kbase kdescr] in HB, HD; try discriminate; injection HB as ->;
    try (injection HD as <- <-); try (destruct len as [z| | | | | | |]; try discriminate; injection HD as <- <-);
    unfold prune1pcK, prune1pcK0; cbn [a_base a_off]; unfold ranges_apart_pcqB; cbn [elen]; rewrite Hq;
    repeat match goal with |- context [if (match ?x with _ => _ end) then true else true] => destruct x end;
    repeat match goal with |- context [if (if ?c then true else true) then _ else _] => destruct c end; try reflexivity.
Qed.
Lemma prune1pcK_keep_win_img : forall bc sp q wa w wv lo hi m same br2,
  kdescr (KImg lo hi) = Some (ELit 0%Z, lo, Some m) -> expr_eqb (ELit 0%Z) (a_base wa) = false ->
  qix_hit q (ELit 0%Z) lo m = true -> prune1pcK bc sp q wa w wv (KImg lo hi) same br2 = PKeep.
Proof.
  intros bc sp q wa w wv lo hi m same br2 HD Hne Hq.
  cbn [kdescr] in HD. destruct (Z.ltb (hi - lo) (2 ^ 64)) eqn:Hlt; [|discriminate]. injection HD as <-.
  unfold prune1pcK, prune1pcK0. destruct wa as [wb k]. cbn [a_base a_off] in *.
  assert (STEP : (if ranges_apart_pqB bc sp q wb k (elen w) (ELit 0%Z) lo (ELit (hi - lo)) then PKeep else PRepl []) = PKeep).
  { unfold ranges_apart_pqB. cbn [elen]. rewrite Hq. reflexivity. }
  rewrite Hlt. destruct same; (destruct wb as [z| | | | | | |]; try exact STEP; destruct z; try exact STEP; cbn in Hne; discriminate).
Qed.

(* [comment removed for export] *)
Local Open Scope Z_scope.
Lemma in_sidesB_In : forall bc D b k n c m, In (c, m) D -> sub_itvB bc b k n c m = true -> in_sidesB bc D b k n = true.
Proof.
  intros bc D b k n c m HIn Hs. induction D as [|[c' m'] r IH]; [destruct HIn|].
  cbn [in_sidesB]. destruct HIn as [E|HIn].
  - injection E as -> ->. rewrite Hs. reflexivity.
  - rewrite (IH HIn). destruct (sub_itvB bc b k n c' m'); reflexivity.
Qed.
Lemma kdescr_m_range : forall K kb kk m, kdescr K = Some (kb, kk, Some m) -> 0 <= m < two64.
Proof.
  assert (R : forall z, 0 <= zlit64 z < two64).
  { intros z. unfold zlit64. destruct ((0 <=? z) && (z <? two64))%bool eqn:E.
    - apply andb_prop in E as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia.
    - pose proof (Z.mod_pos_bound z two64 ltac:(unfold two64; lia)). lia. }
  intros K kb kk m H.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [kdescr] in H; try discriminate; try (injection H as <- <- <-; apply R);
    try (destruct len as [z| | | | | | |]; try discriminate; injection H as <- <- <-; apply R).
  destruct (Z.ltb (hi - lo) (2 ^ 64)); [|discriminate]. injection H as <- <- <-. apply R.
Qed.
Lemma pverdict_inb : forall bc sx g ei m,
  pverdict bc sx g = true -> inb g ei = true -> ei_m ei = Some m -> 0 <= m < two64 ->
  Pos.eqb (ei_bid ei) (sx_bid sx) = false /\ in_sidesB bc (sp_D (sx_sp sx)) (ei_kb ei) (ei_k ei) m = true.
Proof.
  intros bc sx [[[b obr] [glo ghi]] gkb] ei m Hv Hi Hm Hmr. unfold pverdict in Hv. unfold inb in Hi. rewrite Hm in Hi.
  apply andb_prop in Hi as [Hi H4]. apply andb_prop in Hi as [Hi H3]. apply andb_prop in Hi as [Hi H2]. apply andb_prop in Hi as [H1 H1e].
  apply Pos.eqb_eq in H1. subst b. apply p_expr_eqb_eq in H1e. subst gkb. apply Z.leb_le in H3. apply Z.leb_le in H4.
  destruct (Pos.eqb (ei_bid ei) (sx_bid sx)); [discriminate|]. split; [reflexivity|].
  destruct ((0 <=? ghi - glo) && (ghi - glo <? 2 ^ 63))%bool eqn:Hg; [|discriminate].
  apply andb_prop in Hg as [G1 G2]. apply Z.leb_le in G1. apply Z.ltb_lt in G2.
  apply existsb_exists in Hv as ([c mm] & HIn & Hf). unfold pside_fit in Hf. cbn [fst snd] in Hf.
  apply (in_sidesB_In bc _ _ _ _ c mm HIn). unfold sub_itvB.
  lazymatch goal with |- (if ?q then true else _) = true => destruct q; [reflexivity|] end.
  replace ((0 <=? m) && (m <? two64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  apply xinside_plain_sound. eapply xinside_plain_mono; [exact Hf | lia | lia | lia | lia].
Qed.
Lemma prune1pcK_keep_ins : forall bc sp q wa w wv K kb kk m br2,
  kbase K = Some kb -> kdescr K = Some (kb, kk, Some m) -> in_sidesB bc (sp_D sp) kb kk m = true ->
  prune1pcK bc sp q wa w wv K false br2 = PKeep.
Proof.
  intros bc sp q wa w wv K kb kk m br2 HB HD Hs.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [kbase kdescr] in HB, HD; try discriminate; injection HB as ->;
    try (injection HD as <- <-); try (destruct len as [z| | | | | | |]; try discriminate; injection HD as <- <-);
    unfold prune1pcK, prune1pcK0; cbn [a_base a_off]; unfold ranges_apart_pcqB, ranges_apart_pcB; cbn [elen]; rewrite in_sidesQ_eqB, Hs;
    repeat match goal with |- context [if (match ?x with _ => _ end) then true else _] => destruct x end;
    repeat match goal with |- context [if (if ?c then true else _) then _ else _] => destruct c end; try reflexivity.
Qed.
Lemma prune1pcK_keep_ins_img : forall bc sp q wa w wv lo hi m same br2,
  kdescr (KImg lo hi) = Some (ELit 0, lo, Some m) -> expr_eqb (ELit 0) (a_base wa) = false ->
  in_sidesB bc (sp_D sp) (ELit 0) lo m = true -> prune1pcK bc sp q wa w wv (KImg lo hi) same br2 = PKeep.
Proof.
  intros bc sp q wa w wv lo hi m same br2 HD Hne Hs.
  cbn [kdescr] in HD. destruct (Z.ltb (hi - lo) (2 ^ 64)) eqn:Hlt; [|discriminate]. injection HD as <-.
  unfold prune1pcK, prune1pcK0. destruct wa as [wb k]. cbn [a_base a_off] in *.
  assert (STEP : (if ranges_apart_pqB bc sp q wb k (elen w) (ELit 0) lo (ELit (hi - lo)) then PKeep else PRepl []) = PKeep).
  { unfold ranges_apart_pqB, ranges_apart_pB. cbn [elen]. rewrite in_sidesQ_eqB, Hs.
    destruct (qix_hit q (ELit 0) lo (zlit64 (hi - lo))); [reflexivity|].
    lazymatch goal with |- (if (if ?num then true else _) then _ else _) = _ => destruct num; reflexivity end. }
  rewrite Hlt. destruct same; (destruct wb as [z| | | | | | |]; try exact STEP; destruct z; try exact STEP; cbn in Hne; discriminate).
Qed.
Local Close Scope Z_scope.

Lemma entriesG_eq : forall fk sxs bnds kn infos t1,
  NTI (mkbc fk) t1 -> Forall (SX_OK (mkbc fk) t1) sxs -> Forall2 (EINF (mkbc fk) t1) kn infos ->
  entriesG (mkbc fk) sxs (mk_gl (mkbc fk) bnds sxs) kn infos = chainRo fk (map strip sxs) kn.
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
      destruct (pt_get bnds (ei_gid ei)) as [[g n]|]; [|apply FULL; reflexivity].
      destruct (inb g ei) eqn:Hinb; [|apply FULL; reflexivity].
      rewrite <- (FULL (kbase K) eq_refl).
      destruct (Pos.ltb n GMIN); [apply chainKF_eqv; intros sx Hsx Hv; discriminate Hv|].   (* [comment removed for export] *)
      apply chainKF_eq.
      intros sx Hsx Hv.
      assert (Hm : exists m, ei_m ei = Some m).
      { unfold inb in Hinb. destruct (ei_m ei) as [m|]; [exists m; reflexivity|discriminate]. }
      destruct Hm as [m Hm].
      pose proof (proj1 (Forall_forall _ _) HS sx Hsx) as (SXin & SXbr & SXsp & SXq).
      rewrite Hm in HD.
      unfold gverdict in Hv. destruct (verdict sx g) eqn:Hv0.
      * clear Hv. rename Hv0 into Hv.
        destruct (verdict_inb_num _ _ _ _ Hv Hinb Hm) as (Hne & lo1 & hi1 & lo2 & hi2 & Hsp & Hbr2 & Hnum).
        destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
        -- rewrite HB. rewrite Hne. rewrite Hbr. eapply prune1pcK_keep_based; [exact HB|exact HD|exact Hsp| | exact Hnum].
           rewrite <- Hbr. exact Hbr2.
        -- cbn [kbase]. rewrite Hkb, Hk in *.
           eapply prune1pcK_keep_img; [exact HD| |exact Hsp| rewrite <- Hbr; exact Hbr2 | exact Hnum].
           rewrite <- (nt_same_eq _ _ _ _ _ _ HT HIn SXin). exact Hne.
      * destruct (wverdict sx g) eqn:Hw.
        -- (* [comment removed for export] *)
        clear Hv. rename Hw into Hv.
        destruct (wverdict_inb _ _ _ _ Hv Hinb Hm) as [Hne Hq].
        destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
        ++ rewrite HB. rewrite Hne. eapply prune1pcK_keep_win; [exact HB|exact HD|exact Hq].
        ++ cbn [kbase]. rewrite Hkb, Hk in *.
           eapply prune1pcK_keep_win_img; [exact HD| |exact Hq].
           rewrite <- (nt_same_eq _ _ _ _ _ _ HT HIn SXin). exact Hne.
        -- (* [comment removed for export] *)
        destruct (pverdict_inb _ _ _ _ _ Hv Hinb Hm (kdescr_m_range _ _ _ _ HD)) as [Hne Hs].
        destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
        ++ rewrite HB. rewrite Hne. eapply prune1pcK_keep_ins; [exact HB|exact HD|exact Hs].
        ++ cbn [kbase]. rewrite Hkb, Hk in *.
           eapply prune1pcK_keep_ins_img; [exact HD| |exact Hs].
           rewrite <- (nt_same_eq _ _ _ _ _ _ HT HIn SXin). exact Hne.
    + apply chainK2_eq; [exact HSP| symmetry; apply kdescr_None_kbase; exact HK | reflexivity].
Qed.

(* [comment removed for export] *)
Local Open Scope Z_scope.
Lemma obr_eqb_eq : forall a b, obr_eqb a b = true -> a = b.
Proof.
  intros [[x1 y1]|] [[x2 y2]|]; cbn; intros H; try discriminate; try reflexivity.
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.
Lemma sh_add_old : forall h sx sxj, SH_COV h sxj -> SH_COV (sh_add h sx) sxj.
Proof.
  intros h sx sxj (lo & hi & HIn & A & B). revert lo hi HIn A B.
  induction h as [|[[[[b0 obr0] lo0] hi0] kb0] r IH]; intros lo hi HIn A B; [destruct HIn|].
  cbn [sh_add]. destruct HIn as [E|HIn].
  - injection E as -> -> -> -> ->. destruct (Pos.eqb (sx_bid sxj) (sx_bid sx) && obr_eqb (sx_br sxj) (sx_br sx) && expr_eqb (a_base (sx_a sxj)) (a_base (sx_a sx)))%bool.
    + eexists _, _. split; [left; reflexivity|]. lia.
    + exists lo, hi. split; [left; reflexivity|]. lia.
  - destruct (Pos.eqb b0 (sx_bid sx) && obr_eqb obr0 (sx_br sx) && expr_eqb kb0 (a_base (sx_a sx)))%bool.
    + exists lo, hi. split; [right; exact HIn|]. lia.
    + destruct (IH lo hi HIn A B) as (lo' & hi' & HIn' & A' & B'). exists lo', hi'. split; [right; exact HIn'|]. lia.
Qed.
Lemma sh_add_new : forall h sx, SH_COV (sh_add h sx) sx.
Proof.
  induction h as [|[[[[b0 obr0] lo0] hi0] kb0] r IH]; intros sx; cbn [sh_add].
  - eexists _, _. split; [left; reflexivity|]. lia.
  - destruct (Pos.eqb b0 (sx_bid sx) && obr_eqb obr0 (sx_br sx) && expr_eqb kb0 (a_base (sx_a sx)))%bool eqn:E.
    + apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2]. apply Pos.eqb_eq in E1. apply obr_eqb_eq in E2.
      apply p_expr_eqb_eq in E3. subst b0 obr0 kb0.
      eexists _, _. split; [left; reflexivity|]. lia.
    + destruct (IH sx) as (lo & hi & HIn & A & B). exists lo, hi. split; [right; exact HIn|]. lia.
Qed.
Lemma zlit64_le : forall z, 0 <= z -> zlit64 z <= z.
Proof. intros z Hz. unfold zlit64. destruct (_ && _)%bool; [lia|]. apply Z.mod_le; [lia|]. unfold two64. lia. Qed.
Definition SXP (sx : stx) : Prop := sp_rng (sx_sp sx) = sx_br sx.
Definition SXQ (bc : bctx) (sx : stx) : Prop :=
  sx_sp sx = mk_sprepB bc (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx)) /\ sx_q sx = mk_qix bc (sp_D (sx_sp sx)).
Lemma dq_witness_keep : forall bc sx sxj kb kk lo hi,
  sx_a sx = SA kb kk -> SXQ bc sxj ->
  lo <= a_off (sx_a sxj) -> a_off (sx_a sxj) + Z.of_nat (sx_w sxj) <= hi ->
  dq_witness (mk_dqix bc (bc_fk bc)) kb kk (zlit64 (Z.of_nat (sx_w sx))) (a_base (sx_a sxj)) lo hi = true ->
  prune1pcK bc (sx_sp sxj) (sx_q sxj) (sx_a sxj) (sx_w sxj) (sx_v sxj) (KWord (sx_a sx) (sx_w sx) (sx_v sx)) false (sx_br sx) = PKeep.
Proof.
  intros bc sx sxj kb kk lo hi Ha [Qsp Qq] Hlo Hhi Hw.
  unfold dq_witness in Hw. destruct (dqes_fit_In _ _ _ _ _ _ _ Hw) as ([[[c ml] pc] pml] & HIn & Hfit).
  destruct (mk_dqix_ok _ _ _ _ HIn) as (m & pm & Hdisj & Hml & ->).
  unfold dq_fit in Hfit.
  destruct ((a_off c <=? kk) && (kk + zlit64 (Z.of_nat (sx_w sx)) <=? a_off c + ml))%Z%bool eqn:H1; [|discriminate].
  destruct (expr_eqb kb (a_base c)) eqn:H2; [|discriminate].
  destruct (xloB bc pm) as [pl|] eqn:Hpl; [|discriminate].
  destruct ((a_off pc <=? lo) && (hi <=? a_off pc + pl))%Z%bool eqn:H3; [|discriminate].
  apply andb_prop in H1 as [H1a H1b]. apply Z.leb_le in H1a. apply Z.leb_le in H1b.
  apply andb_prop in H3 as [H3a H3b]. apply Z.leb_le in H3a. apply Z.leb_le in H3b.
  (* [comment removed for export] *)
  assert (Hsub : sub_itvB bc (a_base (sx_a sxj)) (a_off (sx_a sxj)) (zlit64 (Z.of_nat (sx_w sxj))) pc pm = true).
  { unfold sub_itvB. rewrite Hfit. replace (a_off pc <=? a_off (sx_a sxj))%Z with true by (symmetry; apply Z.leb_le; lia).
    cbn [andb]. rewrite Hpl. replace (a_off (sx_a sxj) + zlit64 (Z.of_nat (sx_w sxj)) <=? a_off pc + pl)%Z with true; [reflexivity|].
    symmetry. apply Z.leb_le. pose proof (zlit64_small (sx_w sxj)). lia. }
  (* [comment removed for export] *)
  assert (HD : In (c, m) (sp_D (sx_sp sxj))).
  { rewrite Qsp, sp_D_mk_sprepB. destruct Hdisj as [Hd|Hd].
    - exact (proj2 (disj_sidesB_In bc _ _ _ _ _ _ _ _ Hd) Hsub).
    - exact (proj1 (disj_sidesB_In bc _ _ _ _ _ _ _ _ Hd) Hsub). }
  rewrite Ha. eapply prune1pcK_keep_win; [reflexivity|reflexivity|].
  rewrite Qq. eapply qix_hit_In; [exact HD | exact Hml | exact H2 | lia | lia].
Qed.

Lemma chainK2_skip : forall bc dq newer sx h,
  dq = mk_dqix bc (bc_fk bc) -> Forall (SXQ bc) newer ->
  Forall (SH_COV h) newer -> Forall SXP newer -> sh_skip dq sx h = true ->
  sx_br sx = base_rangeB bc (a_base (sx_a sx)) ->
  chainK2 bc newer (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx)
  = [KWord (sx_a sx) (sx_w sx) (sx_v sx)].
Proof.
  intros bc dq newer sx h Hdq HQ HC HP Hs Hbr. induction newer as [|sxj rest IH]; [reflexivity|].
  apply Forall_cons_iff in HC as [Hj HC]. apply Forall_cons_iff in HP as [Pj HP]. apply Forall_cons_iff in HQ as [Qj HQ].
  cbn [chainK2].
  destruct Hj as (lo & hi & HIn & A & B). unfold sx_e in B.
  unfold sh_skip in Hs. pose proof (proj1 (forallb_forall _ _) Hs _ HIn) as S1. cbn [sh_skip1] in S1.
  assert (STEP : prune1pcK bc (sx_sp sxj) (sx_q sxj) (sx_a sxj) (sx_w sxj) (sx_v sxj) (KWord (sx_a sx) (sx_w sx) (sx_v sx))
                   (Pos.eqb (sx_bid sx) (sx_bid sxj)) (sx_br sx) = PKeep).
  { destruct (Pos.eqb (sx_bid sx) (sx_bid sxj)) eqn:E.
    - (* [comment removed for export] *)
      unfold prune1pcK, prune1pcK0. destruct (sx_a sx) as [kb kk] eqn:Ea. destruct (sx_a sxj) as [wb k] eqn:Ej. cbn [a_base a_off] in *.
      replace ((kk + Z.of_nat (sx_w sx) <=? k) || (k + Z.of_nat (sx_w sxj) <=? kk))%Z%bool with true; [reflexivity|].
      symmetry. apply Bool.orb_true_iff. apply Bool.orb_true_iff in S1.
      destruct S1 as [S1|S1]; apply Z.leb_le in S1; [left|right]; apply Z.leb_le; lia.
    - (* [comment removed for export] *)
      lazymatch type of S1 with (if ?num then true else _) = true => destruct num eqn:Enum end.
      2: { destruct (sx_a sx) as [kb kk] eqn:Ea. cbn [a_base a_off] in S1. rewrite <- Ea.
           subst dq. eapply (dq_witness_keep bc sx sxj kb kk lo hi Ea Qj A B). exact S1. }
      clear S1. rename Enum into S1.
      destruct (sx_br sxj) as [[lo1 hi1]|] eqn:Ebrj; [|discriminate].
      destruct (sx_br sx) as [[lo2 hi2]|] eqn:Ebr; [|discriminate].
      destruct (sx_a sx) as [kb kk] eqn:Ea. cbn [a_base a_off] in *.
      rewrite Hbr. eapply prune1pcK_keep_based.
      + reflexivity. + reflexivity.
      + unfold SXP in Pj. rewrite Pj. first [exact Ebrj | reflexivity].
      + symmetry. exact Hbr.
      + pose proof (zlit64_le (Z.of_nat (sx_w sxj)) ltac:(lia)) as Hz.
        apply Bool.orb_true_iff in S1. destruct S1 as [S1|S1]; apply Z.leb_le in S1; [left|right]; lia. }
  rewrite STEP. apply IH; assumption.
Qed.
Lemma stores_partH_eq : forall bc sxs,
  Forall (SXQ bc) sxs ->
  Forall SXP sxs -> Forall (fun sx => sx_br sx = base_rangeB bc (a_base (sx_a sx))) sxs ->
  fst (stores_partH bc (mk_dqix bc (bc_fk bc)) sxs) = stores_part bc sxs /\ Forall (SH_COV (snd (stores_partH bc (mk_dqix bc (bc_fk bc)) sxs))) sxs.
Proof.
  intros bc sxs HQ HP HB. induction sxs as [|sx newer IH]; [split; [reflexivity|constructor]|].
  apply Forall_cons_iff in HQ as [Q1 HQ]. apply Forall_cons_iff in HP as [P1 HP]. apply Forall_cons_iff in HB as [B1 HB].
  destruct (IH HQ HP HB) as [IH1 IH2]. cbn [stores_partH stores_part].
  destruct (stores_partH bc (mk_dqix bc (bc_fk bc)) newer) as [res h]. cbn [fst snd] in *. subst res. split.
  - f_equal. destruct (sh_skip (mk_dqix bc (bc_fk bc)) sx h) eqn:Hs; [|reflexivity]. symmetry.
    apply (chainK2_skip bc _ newer sx h eq_refl HQ IH2 HP Hs B1).
  - constructor; [apply sh_add_new|]. apply Forall_impl with (P := SH_COV h); [intros a; apply sh_add_old | exact IH2].
Qed.
Lemma sp_rng_mk_sprepB : forall bc b k n, sp_rng (mk_sprepB bc b k n) = base_rangeB bc b.
Proof.
  intros. unfold mk_sprepB. destruct n; try reflexivity.
  lazymatch goal with |- sp_rng (if ?c then _ else _) = _ => destruct c; [|reflexivity] end.
  lazymatch goal with |- sp_rng (let '(_, _) := ?x in _) = _ => destruct x; reflexivity end.
Qed.
Lemma Forall_SX_br : forall bc t sxs, Forall (SX_OK bc t) sxs -> Forall (fun sx => sx_br sx = base_rangeB bc (a_base (sx_a sx))) sxs.
Proof. intros bc t sxs H. apply Forall_impl with (P := SX_OK bc t); [|exact H]. intros sx (_ & X & _). exact X. Qed.
Lemma Forall_SXP : forall bc t sxs, Forall (SX_OK bc t) sxs -> Forall SXP sxs.
Proof.
  intros bc t sxs H. apply Forall_impl with (P := SX_OK bc t); [|exact H]. intros sx (_ & X & Y & _).
  unfold SXP. rewrite Y, sp_rng_mk_sprepB. symmetry. exact X.
Qed.
Local Close Scope Z_scope.

(* [comment removed for export] *)
Local Open Scope Z_scope.
Lemma obr_eqb_refl : forall a, obr_eqb a a = true.
Proof. intros [[x y]|]; unfold obr_eqb; [rewrite !Z.eqb_refl|]; reflexivity. Qed.
Lemma key_eqb_refl : forall a, key_eqb a a = true.
Proof. intros [[b r] e]. unfold key_eqb. rewrite Pos.eqb_refl, obr_eqb_refl, kx_expr_eqb_refl. reflexivity. Qed.
Lemma key_eqb_eq : forall a b, key_eqb a b = true -> a = b.
Proof.
  intros [[b1 r1] e1] [[b2 r2] e2] H. unfold key_eqb in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Pos.eqb_eq in H1. apply obr_eqb_eq in H2. apply p_expr_eqb_eq in H3. subst. reflexivity.
Qed.
Lemma side_eqb_eq : forall x y, side_eqb x y = true -> x = y.
Proof.
  intros [[cb co] m] [[cb' co'] m'] H. unfold side_eqb, mkey_eqb in H. cbn in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply p_expr_eqb_eq in H1. apply Z.eqb_eq in H2. apply p_expr_eqb_eq in H3. subst. reflexivity.
Qed.
Lemma Dmeet_l : forall D1 D2 x, In x (Dmeet D1 D2) -> In x D1.
Proof. intros D1 D2 x H. unfold Dmeet in H. apply filter_In in H as [H _]. exact H. Qed.
Lemma Dmeet_r : forall D1 D2 x, In x (Dmeet D1 D2) -> In x D2.
Proof.
  intros D1 D2 x H. unfold Dmeet in H. apply filter_In in H as [_ H].
  apply existsb_exists in H as (y & HIn & E). apply side_eqb_eq in E. subst y. exact HIn.
Qed.
(* [comment removed for export] *)
Definition COV3 (h : list grp3) (sxj : stx) : Prop :=
  match List.find (fun g => g_same g sxj) h with
  | Some g => g_lo g <= a_off (sx_a sxj) /\ sx_e sxj <= g_hi g /\ incl (g_D g) (sp_D (sx_sp sxj))
  | None => False
  end.
Lemma sh3_add_cov_old : forall h sx newer found sxj, COV3 h sxj -> COV3 (sh3_add h sx newer found) sxj.
Proof.
  intros h sx newer. induction h as [|g r IH]; intros found sxj H; [cbn in H; destruct H|].
  unfold COV3 in H |- *. cbn [List.find] in H. cbn [sh3_add].
  destruct (g_same g sx) eqn:Es; cbn [List.find].
  - lazymatch goal with |- context [g_same ?g' sxj] => replace (g_same g' sxj) with (g_same g sxj) by reflexivity end.
    destruct (g_same g sxj) eqn:Ej; cbn iota in H |- *.
    + cbn [g_lo g_hi g_D]. destruct H as (A & B & C). split; [lia|]. split; [lia|].
      intros x Hx. apply C. exact (Dmeet_l _ _ _ Hx).
    + exact (IH true sxj H).
  - destruct (g_same g sxj) eqn:Ej; cbn iota in H |- *; [exact H|]. exact (IH found sxj H).
Qed.
Lemma sh3_add_cov_new : forall h sx newer found,
  (found = false \/ existsb (fun g => g_same g sx) h = true) -> COV3 (sh3_add h sx newer found) sx.
Proof.
  intros h sx newer. induction h as [|g r IH]; intros found Hf.
  - destruct Hf as [->|Hf]; [|cbn in Hf; discriminate]. unfold COV3. cbn [sh3_add List.find].
    lazymatch goal with |- context [g_same ?g' sx] => replace (g_same g' sx) with true by (symmetry; apply key_eqb_refl) end.
    cbn iota. cbn [g_lo g_hi g_D]. split; [lia|]. split; [lia|]. apply incl_refl.
  - unfold COV3 in IH |- *. cbn [sh3_add]. destruct (g_same g sx) eqn:Es; cbn [List.find].
    + lazymatch goal with |- context [g_same ?g' sx] => replace (g_same g' sx) with (g_same g sx) by reflexivity end.
      rewrite Es. cbn iota. cbn [g_lo g_hi g_D]. split; [lia|]. split; [lia|]. intros x Hx. exact (Dmeet_r _ _ _ Hx).
    + rewrite Es. apply IH. destruct Hf as [Hf|Hf]; [left; exact Hf|right]. cbn [existsb] in Hf. rewrite Es in Hf. exact Hf.
Qed.
Lemma sh3_of_cov : forall sxs, Forall (COV3 (sh3_of sxs)) sxs.
Proof.
  induction sxs as [|sx newer IH]; [constructor|]. cbn [sh3_of]. constructor.
  - apply sh3_add_cov_new. left. reflexivity.
  - apply Forall_impl with (P := COV3 (sh3_of newer)); [|exact IH]. intros a. apply sh3_add_cov_old.
Qed.
(* [comment removed for export] *)
Lemma sh3_add_fl : forall h sx newer found,
  Forall (fun g => g_fl g = mk_flb (g_key g) newer) h ->
  Forall (fun g => g_fl g = mk_flb (g_key g) (sx :: newer)) (sh3_add h sx newer found).
Proof.
  intros h sx newer. induction h as [|g r IH]; intros found H.
  - cbn [sh3_add]. destruct found; [constructor|]. constructor; [|constructor].
    cbn [g_fl mk_flb]. lazymatch goal with |- _ = (if ?b then _ else _) => replace b with true by (symmetry; apply key_eqb_refl) end.
    reflexivity.
  - apply Forall_cons_iff in H as [H1 H]. cbn [sh3_add]. destruct (g_same g sx) eqn:Es.
    + constructor; [|exact (IH true H)]. cbn [g_fl mk_flb].
      lazymatch goal with |- _ = (if ?b then _ else _) => replace b with (g_same g sx) by reflexivity end.
      rewrite Es, H1. reflexivity.
    + constructor; [|exact (IH found H)]. cbn [mk_flb]. change (key_eqb (g_key g) (key_of sx)) with (g_same g sx).
      rewrite Es. exact H1.
Qed.
Lemma sh3_of_fl : forall sxs, Forall (fun g => g_fl g = mk_flb (g_key g) sxs) (sh3_of sxs).
Proof. induction sxs as [|sx newer IH]; [constructor|]. cbn [sh3_of]. apply sh3_add_fl. exact IH. Qed.

(* [comment removed for export] *)
Lemma prune1pcK_keep_sameoff : forall bc sp q wa wj wv ka w v br2,
  (a_off ka + Z.of_nat w <= a_off wa \/ a_off wa + Z.of_nat wj <= a_off ka) ->
  prune1pcK bc sp q wa wj wv (KWord ka w v) true br2 = PKeep.
Proof.
  intros bc sp q [wb k] wj wv [kb kk] w v br2 H. cbn [a_off] in H. unfold prune1pcK, prune1pcK0. cbn [a_base a_off].
  replace ((kk + Z.of_nat w <=? k) || (k + Z.of_nat wj <=? kk))%bool with true; [reflexivity|].
  symmetry. apply Bool.orb_true_iff. destruct H as [H|H]; [left|right]; apply Z.leb_le; exact H.
Qed.
Lemma chainK2_keep_all : forall bc sxs K okb same_of br2,
  (forall sxj, In sxj sxs -> prune1pcK bc (sx_sp sxj) (sx_q sxj) (sx_a sxj) (sx_w sxj) (sx_v sxj) K (same_of (sx_bid sxj)) br2 = PKeep) ->
  chainK2 bc sxs K okb same_of br2 = [K].
Proof.
  intros bc sxs K okb same_of br2. induction sxs as [|sxj rest IH]; intros H; [reflexivity|].
  cbn [chainK2]. rewrite (H sxj (or_introl eq_refl)). apply IH. intros x Hx. apply H. right. exact Hx.
Qed.
Lemma gskip3_keep : forall bc sx sxj g,
  gskip3 bc sx g = true -> g_same g sxj = true ->
  g_lo g <= a_off (sx_a sxj) -> sx_e sxj <= g_hi g -> incl (g_D g) (sp_D (sx_sp sxj)) ->
  SXP sxj -> sx_br sx = base_rangeB bc (a_base (sx_a sx)) ->
  prune1pcK bc (sx_sp sxj) (sx_q sxj) (sx_a sxj) (sx_w sxj) (sx_v sxj) (KWord (sx_a sx) (sx_w sx) (sx_v sx))
    (Pos.eqb (sx_bid sx) (sx_bid sxj)) (sx_br sx) = PKeep.
Proof.
  intros bc sx sxj g Hg Hs Hlo Hhi HD HP Hbr. unfold sx_e in Hhi.
  unfold g_same in Hs. apply key_eqb_eq in Hs. unfold g_key, key_of in Hs. injection Hs as Hb Hr Hk.
  unfold gskip3 in Hg. rewrite Hb in Hg.
  destruct (Pos.eqb (sx_bid sx) (sx_bid sxj)) eqn:En; [discriminate|]. cbn iota in Hg.
  destruct (sx_a sx) as [kb kk] eqn:Ea. cbn [a_base a_off] in Hg, Hbr |- *.
  lazymatch type of Hg with (if ?num then true else _) = true => destruct num eqn:Enum end.
  - (* [comment removed for export] *)
    clear Hg. destruct (g_br g) as [[lo1 hi1]|] eqn:Eg; destruct (sx_br sx) as [[lo2 hi2]|] eqn:Ebr; try discriminate.
    rewrite Hbr. eapply prune1pcK_keep_based.
    + reflexivity. + reflexivity.
    + unfold SXP in HP. rewrite HP, <- Hr. reflexivity.
    + symmetry. exact Hbr.
    + pose proof (zlit64_small (sx_w sxj)) as Hz.
      apply Bool.orb_true_iff in Enum. destruct Enum as [E|E]; apply Z.leb_le in E; [left|right]; lia.
  - (* [comment removed for export] *)
    cbn iota in Hg.
    assert (HX : exists x, In x (g_D g) /\ sideK_fit bc kb kk (zlit64 (Z.of_nat (sx_w sx))) x = true).
    { lazymatch type of Hg with (if existsb ?f1 ?D then true else existsb ?f2 _) = true =>
        destruct (existsb f1 D) eqn:E1 end.
      - apply existsb_exists in E1 as (x & HIn & Hx). cbn beta in Hx. exists x. split; [exact HIn|].
        destruct (okeq (fvar kb) (fvar (a_base (fst x)))); [exact Hx|discriminate].
      - cbn iota in Hg. apply existsb_exists in Hg as (x & HIn & Hx). cbn beta in Hx. exists x. split; [exact HIn|].
        destruct (okeq (fvar kb) (fvar (a_base (fst x)))); [discriminate|exact Hx]. }
    destruct HX as ([c m] & HIn & Hx). unfold sideK_fit in Hx.
    eapply prune1pcK_keep_ins; [reflexivity|reflexivity|].
    exact (in_sidesB_In bc _ _ _ _ c m (HD _ HIn) Hx).
Qed.
Lemma walk3_eq : forall bc sx sxs,
  (forall sxj, In sxj sxs -> key_eqb (key_of sx) (key_of sxj) = false ->
     prune1pcK bc (sx_sp sxj) (sx_q sxj) (sx_a sxj) (sx_w sxj) (sx_v sxj) (KWord (sx_a sx) (sx_w sx) (sx_v sx))
       (Pos.eqb (sx_bid sx) (sx_bid sxj)) (sx_br sx) = PKeep) ->
  walk3 bc sx (mk_flb (key_of sx) sxs) (KWord (sx_a sx) (sx_w sx) (sx_v sx))
  = chainK2 bc sxs (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx).
Proof.
  intros bc sx sxs. induction sxs as [|sxj rest IH]; intros H; [reflexivity|].
  assert (IH' : walk3 bc sx (mk_flb (key_of sx) rest) (KWord (sx_a sx) (sx_w sx) (sx_v sx))
                = chainK2 bc rest (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx)).
  { apply IH. intros x Hx Hk. apply H; [right; exact Hx | exact Hk]. }
  cbn [mk_flb chainK2]. destruct (key_eqb (key_of sx) (key_of sxj)) eqn:Ek.
  - cbn [walk3]. destruct (Pos.eqb (sx_bid sx) (sx_bid sxj) && off_apart sx sxj)%bool eqn:Eo.
    + apply andb_prop in Eo as [E1 E2]. rewrite E1.
      rewrite prune1pcK_keep_sameoff; [exact IH'|].
      unfold off_apart in E2. apply Bool.orb_true_iff in E2. destruct E2 as [E|E]; apply Z.leb_le in E; [left|right]; exact E.
    + destruct (prune1pcK bc (sx_sp sxj) (sx_q sxj) (sx_a sxj) (sx_w sxj) (sx_v sxj) _ _ _) as [|l]; [exact IH'|reflexivity].
  - rewrite (H sxj (or_introl eq_refl) Ek). exact IH'.
Qed.
Lemma chain3_eq : forall bc sx newer,
  Forall SXP newer -> sx_br sx = base_rangeB bc (a_base (sx_a sx)) ->
  chain3 bc (sh3_of newer) sx newer
  = chainK2 bc newer (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx).
Proof.
  intros bc sx newer HP Hbr. unfold chain3.
  lazymatch goal with |- (if ?c then _ else _) = _ => destruct c eqn:Hall; [|reflexivity] end.
  pose proof (sh3_of_cov newer) as HC. pose proof (sh3_of_fl newer) as HF.
  assert (KEEP : forall sxj, In sxj newer -> key_eqb (key_of sx) (key_of sxj) = false ->
     prune1pcK bc (sx_sp sxj) (sx_q sxj) (sx_a sxj) (sx_w sxj) (sx_v sxj) (KWord (sx_a sx) (sx_w sx) (sx_v sx))
       (Pos.eqb (sx_bid sx) (sx_bid sxj)) (sx_br sx) = PKeep).
  { intros sxj Hin Hk. pose proof (proj1 (Forall_forall _ _) HC sxj Hin) as Hc. unfold COV3 in Hc.
    destruct (List.find (fun g => g_same g sxj) (sh3_of newer)) as [g|] eqn:Hf; [|destruct Hc].
    apply find_some in Hf as [Hg Hs]. destruct Hc as (A & B & C).
    pose proof (proj1 (forallb_forall _ _) Hall g Hg) as Hgs. cbn beta in Hgs.
    destruct (g_same g sx) eqn:Es.
    - exfalso. unfold g_same in Es, Hs. apply key_eqb_eq in Es. apply key_eqb_eq in Hs.
      rewrite <- Es, Hs, key_eqb_refl in Hk. discriminate.
    - exact (gskip3_keep bc sx sxj g Hgs Hs A B C (proj1 (Forall_forall _ _) HP sxj Hin) Hbr). }
  destruct (List.find (fun g => g_same g sx) (sh3_of newer)) as [g|] eqn:Hf.
  - pose proof (find_some _ _ Hf) as [Hg Hs].
    assert (Hk : g_key g = key_of sx) by (apply key_eqb_eq; exact Hs).
    lazymatch goal with |- (if ?c then _ else _) = _ => destruct c eqn:Hhull end.
    + (* [comment removed for export] *)
      symmetry. apply chainK2_keep_all. intros sxj Hin.
      destruct (key_eqb (key_of sx) (key_of sxj)) eqn:Ek; [|exact (KEEP sxj Hin Ek)].
      pose proof (proj1 (Forall_forall _ _) HC sxj Hin) as Hc. unfold COV3 in Hc.
      apply key_eqb_eq in Ek.
      replace (List.find (fun g0 => g_same g0 sxj) (sh3_of newer)) with (List.find (fun g0 => g_same g0 sx) (sh3_of newer)) in Hc
        by (unfold g_same; rewrite Ek; reflexivity).
      rewrite Hf in Hc. destruct Hc as (A & B & _). unfold sx_e in B.
      unfold key_of in Ek. injection Ek as Eb Er Ekb. rewrite <- Eb, Pos.eqb_refl.
      apply prune1pcK_keep_sameoff.
      apply Bool.orb_true_iff in Hhull. destruct Hhull as [E|E]; apply Z.leb_le in E; [left|right]; lia.
    + (* [comment removed for export] *)
      rewrite (proj1 (Forall_forall _ _) HF g Hg), Hk. apply walk3_eq. exact KEEP.
  - (* [comment removed for export] *)
    symmetry. apply chainK2_keep_all. intros sxj Hin.
    destruct (key_eqb (key_of sx) (key_of sxj)) eqn:Ek; [|exact (KEEP sxj Hin Ek)].
    exfalso. pose proof (proj1 (Forall_forall _ _) HC sxj Hin) as Hc. unfold COV3 in Hc.
    destruct (List.find (fun g => g_same g sxj) (sh3_of newer)) as [g|] eqn:Hf2; [|destruct Hc].
    apply find_some in Hf2 as [Hg Hs]. pose proof (find_none _ _ Hf g Hg) as Hn. cbn beta in Hn.
    unfold g_same in Hn, Hs. apply key_eqb_eq in Hs. apply key_eqb_eq in Ek. rewrite Hs, <- Ek, key_eqb_refl in Hn. discriminate.
Qed.
Lemma stores_part3_eq : forall bc sxs,
  Forall SXP sxs -> Forall (fun sx => sx_br sx = base_rangeB bc (a_base (sx_a sx))) sxs ->
  fst (stores_part3 bc sxs) = stores_part bc sxs /\ snd (stores_part3 bc sxs) = sh3_of sxs.
Proof.
  intros bc sxs HP HB. induction sxs as [|sx newer IH]; [split; reflexivity|].
  apply Forall_cons_iff in HP as [P1 HP]. apply Forall_cons_iff in HB as [B1 HB].
  destruct (IH HP HB) as [IH1 IH2]. cbn [stores_part3 stores_part sh3_of].
  destruct (stores_part3 bc newer) as [res h]. cbn [fst snd] in *. subst res h. split; [|reflexivity].
  f_equal. apply chain3_eq; assumption.
Qed.
Local Close Scope Z_scope.

Lemma carryG_eq : forall log kn,
  carryG (mkbc (facts_of kn)) log kn = SPRo (facts_of kn) (rev log) ++ chainRo (facts_of kn) (rev log) kn.
Proof.
  intros log kn. unfold carryG.
  destruct (mk_stxs (mkbc (facts_of kn)) log nt_empty) as [sxs t0] eqn:E.
  destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT0 & HS0 & Hmap & _).
  destruct (scan_entries (mkbc (facts_of kn)) kn t0 gst_empty) as [[infos t1] gs] eqn:ES.
  destruct (scan_entries_ok _ _ _ _ _ _ _ HT0 ES) as (HT1 & Hm & HF).
  assert (HS1 : Forall (SX_OK (mkbc (facts_of kn)) t1) sxs).
  { apply Forall_impl with (P := SX_OK (mkbc (facts_of kn)) t0); [|exact HS0]. intros sx. apply SX_OK_mono. exact Hm. }
  rewrite (proj1 (stores_part3_eq _ _ (Forall_SXP _ _ _ HS0) (Forall_SX_br _ _ _ HS0))).   (* [comment removed for export] *)
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
