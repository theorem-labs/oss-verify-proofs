(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
      | H : (if ?c then _ else false) = true |- _ => let E := fresh "E" in destruct c eqn:E; [|discriminate H]
      end;
    repeat match goal with
      | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
      | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
      | H : N.eqb _ _ = true |- _ => apply N.eqb_eq in H
      | H : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in H
      | H : aluop_eqb _ _ = true |- _ => apply p_aluop_eqb_eq in H
      | H : mulop_eqb _ _ = true |- _ => apply p_mulop_eqb_eq in H
      | H : expr_eqb ?a _ = true, IH : forall y, expr_eqb ?a y = true -> _ |- _ => apply IH in H
      end; subst; reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint first_var (e : expr) : option N :=
  match e with
  | ELit _ => None
  | EVar n => Some n
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b =>
      match first_var a with Some n => Some n | None => first_var b end
  | EExt _ _ _ a => first_var a
  | EBlob _ _ _ _ => None
  end.
Definition vkey_of (e : expr) : option N := first_var (fst (lit_strip e)).    
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
(* [comment removed for export] *)
Definition lget2 {A : Type} (t : ptree (list A)) (n : N) : list A := match pt_get t (pos_fast n) with Some b => b | None => [] end.
Definition lset2 {A : Type} (t : ptree (list A)) (n : N) (x : A) : ptree (list A) :=
  let p := pos_fast n in pt_set p (x :: match pt_get t p with Some b => b | None => [] end) t.
(* [comment removed for export] *)
Lemma lget2_lset2 : forall (A : Type) (t : ptree (list A)) n x m,
  lget2 (lset2 t n x) m = if N.eqb m n then x :: lget2 t m else lget2 t m.
Proof.
  intros A t n x m. unfold lget2, lset2. destruct (N.eqb_spec m n) as [->|NE].
  - rewrite pt_gss. reflexivity.
  - rewrite pt_gso by (intros E; apply NE; apply pos_fast_inj; exact E). reflexivity.
Qed.
Lemma lget2_leaf : forall (A : Type) n, lget2 (@PTLeaf (list A)) n = [].
Proof. intros A n. unfold lget2. rewrite pt_get_leaf. reflexivity. Qed.
Record rindex := RI { ri_vars : ptree (list kentry); ri_other : list kentry }.
Definition ri_bucket (ri : rindex) (k : option N) : list kentry :=
  match k with Some n => lget2 (ri_vars ri) n | None => ri_other ri end.
Fixpoint mk_ri (fk : list kentry) : rindex :=
  match fk with
  | [] => RI PTLeaf []
  | K :: rest =>
      let t := mk_ri rest in
      match K with
      | KRange e' _ _ =>
          match vkey_of e' with
          | Some n => RI (lset2 (ri_vars t) n K) (ri_other t)
          | None => RI (ri_vars t) (K :: ri_other t)
          end
      | _ => t
      end
  end.
Definition find_rangeI (ri : rindex) (e : expr) : option (Z * Z) := find_range (ri_bucket ri (vkey_of e)) e.

Definition okey_eqb (a b : option N) : bool :=
  match a, b with Some x, Some y => N.eqb x y | None, None => true | _, _ => false end.
Lemma okey_eqb_spec : forall a b, reflect (a = b) (okey_eqb a b).
Proof.
  intros [x|] [y|]; cbn; try (constructor; congruence).
  destruct (N.eqb_spec x y); constructor; congruence.
Qed.
Lemma ri_bucket_cons : forall t K e' lo hi k,
  K = KRange e' lo hi ->
  ri_bucket (match vkey_of e' with
             | Some n => RI (lset2 (ri_vars t) n K) (ri_other t)
             | None => RI (ri_vars t) (K :: ri_other t)
             end) k
  = if okey_eqb k (vkey_of e') then K :: ri_bucket t k else ri_bucket t k.
Proof.
  intros t K e' lo hi k ->. destruct (vkey_of e') as [n|] eqn:Ev; destruct k as [m|]; cbn [ri_bucket ri_vars ri_other okey_eqb]; try reflexivity.
  apply lget2_lset2.
Qed.
Lemma find_rangeI_eq : forall fk e, find_rangeI (mk_ri fk) e = find_range fk e.
Proof.
  intros fk e. unfold find_rangeI. induction fk as [|K rest IH].
  - cbn [mk_ri]. destruct (vkey_of e) as [n|]; cbn [ri_bucket ri_vars ri_other]; [rewrite lget2_leaf; reflexivity | reflexivity].
  - cbn [mk_ri]. destruct K as [a w v|a l|a l bk|lo hi|e1 m|e' lo hi|a n|a1 n1 a2 n2|a l c|a l|pt prs pargs pk];
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
Definition atom_key (e : expr) : option positive := match e with EVar v => Some (pos_fast v) | _ => None end.   (* [comment removed for export] *)
Definition fact_keys (f : sfact) : list (option positive) := List.map (fun t => atom_key (snd t)) (fst f).
(* [comment removed for export] *)
Fixpoint ekeys (e : expr) (acc : list positive) : list positive :=
  match e with
  | ELit _ | EBlob _ _ _ _ => acc
  | EVar v => pos_fast v :: acc   (* [comment removed for export] *)
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => ekeys a (ekeys b acc)
  | EExt _ _ _ a => ekeys a acc
  end.
Definition keys_meet (ka kb : list positive) : bool := existsb (fun p => existsb (Pos.eqb p) kb) ka.
Definition cand (kb ks : list positive) (ls : bool) : bool := if ls then true else keys_meet kb ks.
Record kdx : Type := KDX { kd_c1 : saddr; kd_m1 : expr; kd_c2 : saddr; kd_m2 : expr;
                           kd_k1 : list positive; kd_l1 : bool; kd_k2 : list positive; kd_l2 : bool }.
Fixpoint mk_kdx (kn : list kentry) : list kdx :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: r =>
      KDX c1 m1 c2 m2 (ekeys (a_base c1) []) (novars (a_base c1)) (ekeys (a_base c2) []) (novars (a_base c2)) :: mk_kdx r
  | _ :: r => mk_kdx r
  end.
Record bctx : Type := BC {
  bc_fk : list kentry;      (* [comment removed for export] *)
  bc_ffk : list kentry;     (* [comment removed for export] *)
  bc_fs : list sfact;       (* [comment removed for export] *)
  bc_ri : rindex;           (* [comment removed for export] *)
  bc_fsk : list (sfact * list (option positive));    
  bc_kd : list kdx          (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition mkbc0 (fk : list kentry) (fs : list sfact) (kd : list kdx) : bctx :=
  BC fk (facts_of fk) fs (mk_ri (facts_of fk)) (List.map (fun f => (f, fact_keys f)) fs) kd.

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

(* [comment removed for export] *)
Definition zpow2 (s : Z) : Z := if Z.leb 0 s then Z.shiftl 1 s else (2 ^ s)%Z.
Lemma zpow2_eqf : zpow2 = (fun s => (2 ^ s)%Z).
Proof. apply functional_extensionality; intros s. unfold zpow2. destruct (Z.leb_spec 0 s); [|reflexivity]. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.
Definition zshr (a s : Z) : Z := if Z.leb 0 s then Z.shiftr a s else (a / 2 ^ s)%Z.
Lemma zshr_eqf : zshr = (fun a s => (a / 2 ^ s)%Z).
Proof. repeat (apply functional_extensionality; intros ?). unfold zshr. destruct (Z.leb_spec 0 x0); [|reflexivity]. apply Z.shiftr_div_pow2. lia. Qed.
Definition zlow (a s : Z) : Z := if Z.leb 0 s then Z.land a (Z.ones s) else (a mod 2 ^ s)%Z.
Lemma zlow_eqf : zlow = (fun a s => (a mod 2 ^ s)%Z).
Proof. repeat (apply functional_extensionality; intros ?). unfold zlow. destruct (Z.leb_spec 0 x0); [|reflexivity]. apply Z.land_ones. lia. Qed.
Definition lit_shamtB (e : expr) : option Z :=
  match e with ELit s => Some (if (Z.leb 0 s && Z.ltb s 64)%bool then s else (s mod 64)%Z) | _ => None end.
Lemma lit_shamtB_eqf : lit_shamtB = lit_shamt.
Proof.
  apply functional_extensionality; intros e. unfold lit_shamtB, lit_shamt. destruct e; try reflexivity. f_equal.
  destruct (Z.leb_spec 0 z); destruct (Z.ltb_spec z 64); cbn [andb]; try reflexivity. symmetry. apply Z.mod_small. lia.
Qed.
Definition zm32 (s : Z) : Z := if (Z.leb 0 s && Z.ltb s 32)%bool then s else (s mod 32)%Z.
Lemma zm32_eqf : zm32 = (fun s => (s mod 32)%Z).
Proof.
  apply functional_extensionality; intros s. unfold zm32.
  destruct (Z.leb_spec 0 s); destruct (Z.ltb_spec s 32); cbn [andb]; try reflexivity. symmetry. apply Z.mod_small. lia.
Qed.
Lemma zmod64_eqf : zmod64 = (fun z => (z mod two64)%Z).
Proof. apply functional_extensionality; intros z. apply zmod64_eq2. Qed.

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
          let ra := erange bc a in   (* [comment removed for export] *)
          match (match b, ra with
                 | ELit m, Some (al, ah) =>
                     let m' := zmod64 m in
                     let j := Z.log2 (m' + 1) in
                     if (Z.eqb (m' + 1) (zpow2 j) && Z.leb (zshr al j) (zshr ah j) && Z.eqb (zshr al j) (zshr ah j))%bool
                     then Some (zlow al j, zlow ah j)
                     else let jh := Z.log2 (two64 - m') in
                          if (Z.eqb (two64 - m') (zpow2 jh) && Z.ltb jh 64)%bool
                          then Some ((al - zlow al jh)%Z, (ah - zlow ah jh)%Z)
                          else None
                 | _, _ => None
                 end) with
          | Some r => Some r
          | None =>
          match ra, erange bc b with
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
          | Some (al, ah), Some s => Some (zshr al s, zshr ah s)
          | None, Some s => Some (0%Z, zshr (two64 - 1) s)   (* [comment removed for export] *)
          | _, _ => None
          end
      | ALU_SRA =>
          match erange bc a, lit_shamtB b with
          | Some (al, ah), Some s =>
              if Z.ltb ah two63z then Some (zshr al s, zshr ah s) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange bc a, lit_shamtB b with
          | Some (al, ah), Some s =>
              if Z.ltb (ah * zpow2 s) two64 then Some ((al * zpow2 s)%Z, (ah * zpow2 s)%Z) else None
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
              if (Z.ltb ah two63z && Z.ltb bh two63z)%bool then
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
              if (Z.leb 0 (al + bl') && Z.ltb (ah + bh') two31z)%bool
              then Some ((al + bl')%Z, (ah + bh')%Z) else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb bh al && Z.ltb (ah - bl) two31z)%bool
              then Some ((al - bh)%Z, (ah - bl)%Z) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange bc a, lit_shamtB b with
          | Some (al, ah), Some s =>
              let s' := zm32 s in
              if Z.ltb (ah * zpow2 s') two31z then Some ((al * zpow2 s')%Z, (ah * zpow2 s')%Z) else None
          | _, _ => None
          end
      | ALU_SRL =>
          match erange bc a, lit_shamtB b with
          | Some (al, ah), Some s =>
              let s' := zm32 s in
              if (Z.ltb ah two32z && (Z.ltb 0 s' || Z.ltb ah two31z))%bool
              then Some (zshr al s', zshr ah s') else None
          | _, _ => None
          end
      | ALU_SRA =>
          match erange bc a, lit_shamtB b with
          | Some (al, ah), Some s =>
              let s' := zm32 s in
              if Z.ltb ah two31z then Some (zshr al s', zshr ah s') else None
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
      let w := zpow2 (8 * Z.of_nat n) in
      if sx then
        match lo, erange bc a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah (zshr w 1))%bool then Some (al, ah)
            else if (Nat.leb 1 n && Nat.leb n 8 && Z.leb (zshr w 1) al && Z.ltb ah w)%bool
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
      if sx then Some (0%Z, two64m1) else Some (0%Z, Z.min (zpow2 (8 * Z.of_nat n) - 1) (two64 - 1))%Z
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
  match e with ELit z => let v := (zmod64 z) in Some (v, v) | _ => erangeB bc e end.

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
          if (if Z.eqb (k mod m)%Z 0%Z then lin_nowrapB bc e else false) then   (* [comment removed for export] *)
            let q := (k / m)%Z in
            let le := lin_of e in
            if Z.leb ((s mod two64) mod 64) (ealignB bc e) then   (* [comment removed for export] *)
              ((c + q * fst le)%Z, fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le))
            else
            ((c + q * fst le)%Z,
             lins_e (- q)%Z (srl_rem e m) (fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le)))
          else keep
      | EAlu ALU_AND e (ELit mk) =>
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
  sum_fact_x1 c2 ts2 lo hi ++
  (if has_srl ts2 then let '(c3, ts3) := srl_expandB bc ts2 in sum_fact_x1 (c2 + c3)%Z ts3 lo hi else []).

Fixpoint sum_factsB_m (bc : bctx) (kn : list kentry) : list sfact :=
  match kn with
  | [] => []
  | KRange e lo hi :: rest =>
      match e with
      | EVar _ => sum_factsB_m bc rest
      | _ =>
        match lin_of e with
        | (c, (_ :: _ :: _) as ts) =>
            if fact_nowrapB bc e hi then (ts, ((lo - c)%Z, (hi - c)%Z)) :: sum_fact_div ts (lo - c)%Z (hi - c)%Z ++ sum_fact_xB bc ts (lo - c)%Z (hi - c)%Z ++ sum_factsB_m bc rest
            else sum_factsB_m bc rest
        | _ => sum_factsB_m bc rest
        end
      end
  | _ :: rest => sum_factsB_m bc rest
  end.
Fixpoint sum_facts1B (bc : bctx) (kn : list kentry) : list sfact :=
  match kn with
  | [] => []
  | KRange e lo hi :: rest =>
      match e with
      | EVar _ => sum_facts1B bc rest
      | _ =>
        match lin_of e with
        | (c, [t]) => if fact_nowrapB bc e hi then ([t], ((lo - c)%Z, (hi - c)%Z)) :: sum_facts1B bc rest else sum_facts1B bc rest
        | _ => sum_facts1B bc rest
        end
      end
  | _ :: rest => sum_facts1B bc rest
  end.
Definition sum_factsB (bc : bctx) (kn : list kentry) : list sfact := sum_factsB_m bc kn ++ sum_facts1B bc kn.


(* [comment removed for export] *)
Lemma bc_fk_mkbc0 : forall fk fs kd, bc_fk (mkbc0 fk fs kd) = fk. Proof. reflexivity. Qed.
Lemma bc_ffk_mkbc0 : forall fk fs kd, bc_ffk (mkbc0 fk fs kd) = facts_of fk. Proof. reflexivity. Qed.
Lemma find_rangeI_mkbc0 : forall fk fs kd, find_rangeI (bc_ri (mkbc0 fk fs kd)) = find_range (facts_of fk).
Proof. intros. apply functional_extensionality. intros e. apply find_rangeI_eq. Qed.
#[export] Hint Rewrite bc_fk_mkbc0 bc_ffk_mkbc0 find_rangeI_mkbc0 : bceq.
Ltac bcfe := repeat (apply functional_extensionality; intros ?).

Lemma erange_fB_eqf0 : forall fk fs kd fuel, erange_fB fuel (mkbc0 fk fs kd) = erange_f fuel (facts_of fk).
Proof.
  intros fk fs kd fuel. induction fuel as [|f IH]; bcfe; [reflexivity|].
  cbn [erange_fB erange_f]. rewrite ?zpow2_eqf, ?zshr_eqf, ?zlow_eqf, ?lit_shamtB_eqf, ?zm32_eqf, ?zmod64_eqf. cbv beta.   (* [comment removed for export] *)
  rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite erange_fB_eqf0 : bceq.

Lemma erange0B_eqf0 : forall fk fs kd, erange0B (mkbc0 fk fs kd) = erange0 fk.
Proof. intros. bcfe. unfold erange0B, erange0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite erange0B_eqf0 : bceq.
Lemma erangeB_eqf0 : forall fk fs kd, erangeB (mkbc0 fk fs kd) = erange fk.
Proof. intros. bcfe. unfold erangeB, erange. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite erangeB_eqf0 : bceq.
Lemma base_rangeB_eqf0 : forall fk fs kd, base_rangeB (mkbc0 fk fs kd) = base_range fk.
Proof. intros. bcfe. unfold base_rangeB, base_range. autorewrite with bceq. rewrite ?zmod64_eqf; cbv beta. reflexivity. Qed.
#[export] Hint Rewrite base_rangeB_eqf0 : bceq.
Lemma ealignB_eqf0 : forall fk fs kd, ealignB (mkbc0 fk fs kd) = ealign fk.
Proof. intros. bcfe. unfold ealignB, ealign. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite ealignB_eqf0 : bceq.
Lemma lin_nowrapB_eqf0 : forall fk fs kd, lin_nowrapB (mkbc0 fk fs kd) = lin_nowrap fk.
Proof. intros. bcfe. unfold lin_nowrapB, lin_nowrap. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_nowrapB_eqf0 : bceq.
Lemma srl_expandB_eqf0 : forall fk fs kd, srl_expandB (mkbc0 fk fs kd) = srl_expand fk.
Proof.
  intros fk fs kd. apply functional_extensionality; intros ts. 
  induction ts as [|[k a] rest IH]; intros; bcfe; [reflexivity|].
  cbn [srl_expandB srl_expand]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite srl_expandB_eqf0 : bceq.
Lemma fact_nowrapB_eqf0 : forall fk fs kd, fact_nowrapB (mkbc0 fk fs kd) = fact_nowrap fk.
Proof. intros. bcfe. unfold fact_nowrapB, fact_nowrap. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite fact_nowrapB_eqf0 : bceq.
Lemma sum_fact_xB_eqf0 : forall fk fs kd, sum_fact_xB (mkbc0 fk fs kd) = sum_fact_x fk.
Proof. intros. bcfe. unfold sum_fact_xB, sum_fact_x. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite sum_fact_xB_eqf0 : bceq.
Lemma sum_factsB_m_eqf0 : forall fk fs kd, sum_factsB_m (mkbc0 fk fs kd) = sum_facts_m fk.
Proof.
  intros fk fs kd. apply functional_extensionality; intros kn. 
  induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [sum_factsB_m sum_facts_m]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
Lemma sum_facts1B_eqf0 : forall fk fs kd, sum_facts1B (mkbc0 fk fs kd) = sum_facts1 fk.
Proof.
  intros fk fs kd. apply functional_extensionality; intros kn. 
  induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [sum_facts1B sum_facts1]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
Lemma sum_factsB_eqf0 : forall fk fs kd, sum_factsB (mkbc0 fk fs kd) = sum_facts fk.
Proof.
  intros fk fs kd. apply functional_extensionality; intros kn. unfold sum_factsB, sum_facts.
  rewrite sum_factsB_m_eqf0, sum_facts1B_eqf0. reflexivity.
Qed.
#[export] Hint Rewrite sum_factsB_eqf0 : bceq.


(* [comment removed for export] *)
Definition mkbc (fk : list kentry) : bctx := mkbc0 fk (sum_factsB (mkbc0 fk [] []) fk) (mk_kdx fk).
Lemma bc_fk_mkbc : forall fk, bc_fk (mkbc fk) = fk. Proof. reflexivity. Qed.
Lemma bc_ffk_mkbc : forall fk, bc_ffk (mkbc fk) = facts_of fk. Proof. reflexivity. Qed.
Lemma bc_kd_mkbc : forall fk, bc_kd (mkbc fk) = mk_kdx fk. Proof. reflexivity. Qed.
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

Definition lin_test_relB0 (bc : bctx) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  let fs := bc_fs bc in
  if lin_test_rel0 (erangeB bc) fs c ts test then true
  else let fsP := List.flat_map (project_fact (erangeB bc) ts) fs in
       if lin_test_rel0 (erangeB bc) (fs ++ fsP) c ts test then true
       else if lin_test_rel0 (erangeB bc) fsP c ts test then true
       else if existsb (fun f => lin_test_rel0 (erangeB bc) [f] c ts test) fsP then true
       else lin_test_relq (erangeB bc) (fs ++ fsP) c ts test.
(* [comment removed for export] *)
Definition fact_rel (ts : list (Z * expr)) (f : sfact) : bool := existsb (fun t => negb (Z.eqb (coef_of (snd t) ts) 0)) (fst f).
Definition ts_keys (ts : list (Z * expr)) : list positive :=
  List.flat_map (fun t => match atom_key (snd t) with Some p => [p] | None => [] end) ts.
Definition key_in (tsk : list positive) (k : option positive) : bool :=
  match k with None => true | Some p => existsb (Pos.eqb p) tsk end.
Definition relk (tsk : list positive) (ks : list (option positive)) : bool := existsb (key_in tsk) ks.
Definition lin_test_relB (bc : bctx) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  let tsk := ts_keys ts in
  let fs := List.map fst (List.filter (fun p => relk tsk (snd p)) (bc_fsk bc)) in
  if lin_test_rel0 (erangeB bc) fs c ts test then true
  else let fsP := List.flat_map (project_fact (erangeB bc) ts) fs in
       if lin_test_rel0 (erangeB bc) (fs ++ fsP) c ts test then true      (* [comment removed for export] *)
       else if lin_test_rel0 (erangeB bc) fsP c ts test then true
       else if existsb (fun f => lin_test_rel0 (erangeB bc) [f] c ts test) fsP then true   (* [comment removed for export] *)
       else lin_test_relq (erangeB bc) (fs ++ fsP) c ts test.

Definition lin_testB (bc : bctx) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match lin_range (erangeB bc) c ts with
  | Some (lo, hi) => if test lo hi then true else lin_test_relB bc c ts test
  | None => lin_test_relB bc c ts test
  end.

Definition lin_srangeB (bc : bctx) (e : expr) : option (Z * Z) :=
  let l := lin_of e in
  let j := srl_scale_need (snd l) in
  if (if Z.leb 0 j then Z.leb j 24 else false) then    
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
  else  
    match lin_srangeB bc e with Some _ => true | None => false end.

Definition lin_apart0B (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if lin_nowrapRB bc b1 then if lin_nowrapRB bc b2 then   (* [comment removed for export] *)
   let l1 := lin_of b1 in let l2 := lin_of b2 in
   lin_testB bc (fst l2 + k2 - fst l1 - k1)%Z (lsub_e (snd l2) (snd l1))
            (fun lo hi => (Z.leb n1 lo || Z.leb hi (- n2))%bool)
  else false else false.

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
                   | None => match lin_srangeB bc e with Some (lo, _) => Some lo | None => None end    
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
                   | None => match lin_srangeB bc e with Some (_, hi) => Some hi | None => None end    
                   end
         end
  end.

Fixpoint xt_nowrapB (bc : bctx) (ts : xterms) : bool :=
  match ts with [] => true | (e, _) :: r => if lin_nowrapRB bc e then xt_nowrapB bc r else false end.   (* [comment removed for export] *)

Definition lin_ge0_scaledB (bc : bctx) (c : Z) (ts : list (Z * expr)) : bool :=
  let j := srl_scale_need ts in
  if (if Z.ltb 0 j then Z.leb j 24 else false) then
    let sc := (2 ^ j)%Z in
    let ts' := List.map (fun t => ((sc * fst t)%Z, snd t)) ts in
    let '(c2, t2) := srl_expandB bc ts' in
    let '(c3, t3) := (if has_srl t2 then srl_expandB bc t2 else (0%Z, t2)) in
    lin_testB bc (sc * c + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
  else false.

Definition lin_ge0B (bc : bctx) (pos neg : xterms) : bool :=
  if xt_nowrapB bc pos then if xt_nowrapB bc neg then   (* [comment removed for export] *)
  (
   (* [comment removed for export] *)
   (if lin_testB bc (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) (fun lo _ => Z.leb 0 lo) then true
    else let '(c2, t2) := srl_expandB bc (lsub_e (xt_lin pos) (xt_lin neg)) in
         if lin_testB bc (xt_const pos - xt_const neg + c2)%Z t2 (fun lo _ => Z.leb 0 lo) then true
         else  
         if (if has_srl t2 then
               let '(c3, t3) := srl_expandB bc t2 in
               lin_testB bc (xt_const pos - xt_const neg + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
             else false) then true
         else  
           lin_ge0_scaledB bc (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg))))%bool
  else false else false.

Definition xinside_refutedB (bc : bctx) (b1 : expr) (k1 : Z) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match base_rangeB bc b1, base_rangeB bc b2 with
  | Some (lo1, hi1), Some (lo2, hi2) =>
      if Z.ltb (hi1 + k1) (lo2 + k2) then true
      else match xhiB bc n2 with Some h2 => Z.ltb (hi2 + k2 + h2) (lo1 + k1) | None => false end
  | _, _ => false
  end.
Definition xinside0B (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if xinside_refutedB bc b1 k1 b2 k2 n2 then false   (* [comment removed for export] *)
  else if lin_ge0B bc [(b1, k1)] [(b2, k2)] then lin_ge0B bc [(b2, k2); (n2, 0%Z)] [(b1, k1); (n1, 0%Z)] else false.

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
  else if novars b2 then (if xinside_numB bc b1 k1 n1 b2 k2 n2 then true
                           else match n1 with ELit _ => false | _ => xinside0B bc b1 k1 n1 b2 k2 n2 end) else false.   (* [comment removed for export] *)

Definition sub_itvB (bc : bctx) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
  if (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
        match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
      else false)
  then true
  else if scale_clash b (a_base c) then false   (* [comment removed for export] *)
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

Fixpoint kdisj_apartBX (bc : bctx) (ds : list kdx) (kb1 kb2 : list positive) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  match ds with
  | [] => false
  | d :: rest =>
      if (if cand kb1 (kd_k1 d) (kd_l1 d) then if cand kb2 (kd_k2 d) (kd_l2 d) then
            (if sub_itvB bc b1 k1 n1 (kd_c1 d) (kd_m1 d) then sub_itvB bc b2 k2 n2 (kd_c2 d) (kd_m2 d) else false)
          else false else false) then true
      else if (if cand kb1 (kd_k2 d) (kd_l2 d) then if cand kb2 (kd_k1 d) (kd_l1 d) then
            (if sub_itvB bc b1 k1 n1 (kd_c2 d) (kd_m2 d) then sub_itvB bc b2 k2 n2 (kd_c1 d) (kd_m1 d) else false)
          else false else false) then true
      else kdisj_apartBX bc rest kb1 kb2 b1 k1 n1 b2 k2 n2
  end.

(* [comment removed for export] *)
Definition lin_apart2B (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if apart_gate b1 b2 then false
  else if lin_ge0B bc [(b2, k2)] [(b1, (k1 + n1)%Z)] then true
  else lin_ge0B bc [(b1, k1)] [(b2, (k2 + n2)%Z)].

Definition ranges_apartB (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match base_rangeB bc b1, base_rangeB bc b2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
      | _, _ => false
      end) then true
  else if kdisj_apartBX bc (bc_kd bc) (ekeys b1 []) (ekeys b2 []) b1 k1 n1 b2 k2 n2 then true   (* [comment removed for export] *)
  else if lin_apartB bc b1 k1 n1 b2 k2 n2 then true
  else lin_apart2B bc b1 k1 n1 b2 k2 n2.

Definition sub_itv_xB (bc : bctx) (b : expr) (k : Z) (n : expr) (c : saddr) (m : expr) : bool :=
  if scale_clash b (a_base c) then false else   (* [comment removed for export] *)
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

Fixpoint kdisj_apart_xBX (bc : bctx) (ds : list kdx) (kb1 kb2 : list positive) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match ds with
  | [] => false
  | d :: rest =>
      if (if cand kb1 (kd_k1 d) (kd_l1 d) then if cand kb2 (kd_k2 d) (kd_l2 d) then
            (if sub_itv_xB bc b1 k1 n1 (kd_c1 d) (kd_m1 d) then sub_itv_xB bc b2 k2 n2 (kd_c2 d) (kd_m2 d) else false)
          else false else false) then true
      else if (if cand kb1 (kd_k2 d) (kd_l2 d) then if cand kb2 (kd_k1 d) (kd_l1 d) then
            (if sub_itv_xB bc b1 k1 n1 (kd_c2 d) (kd_m2 d) then sub_itv_xB bc b2 k2 n2 (kd_c1 d) (kd_m1 d) else false)
          else false else false) then true
      else kdisj_apart_xBX bc rest kb1 kb2 b1 k1 n1 b2 k2 n2
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
            else  
            if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if kdisj_apart_xBX bc (bc_kd bc) (ekeys b1 []) (ekeys b2 []) b1 k1 n1 b2 k2 n2 then true   (* [comment removed for export] *)
    else if apart_gate b1 b2 then false   (* [comment removed for export] *)
    else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
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
Fixpoint disj_sidesBX (bc : bctx) (ds : list kdx) (kb1 : list positive) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) :=
  match ds with
  | [] => []
  | d :: rest =>
      let r := disj_sidesBX bc rest kb1 b1 k1 n1 in
      let r1 := if (if cand kb1 (kd_k2 d) (kd_l2 d) then sub_itvB bc b1 k1 n1 (kd_c2 d) (kd_m2 d) else false) then (kd_c1 d, kd_m1 d) :: r else r in
      if (if cand kb1 (kd_k1 d) (kd_l1 d) then sub_itvB bc b1 k1 n1 (kd_c1 d) (kd_m1 d) else false) then (kd_c2 d, kd_m2 d) :: r1 else r1
  end.
Fixpoint disj_sides_xBX (bc : bctx) (ds : list kdx) (kb1 : list positive) (b1 : expr) (k1 : Z) (n1 : expr) : list (saddr * expr) :=
  match ds with
  | [] => []
  | d :: rest =>
      let r := disj_sides_xBX bc rest kb1 b1 k1 n1 in
      let r1 := if (if cand kb1 (kd_k2 d) (kd_l2 d) then sub_itv_xB bc b1 k1 n1 (kd_c2 d) (kd_m2 d) else false) then (kd_c1 d, kd_m1 d) :: r else r in
      if (if cand kb1 (kd_k1 d) (kd_l1 d) then sub_itv_xB bc b1 k1 n1 (kd_c1 d) (kd_m1 d) else false) then (kd_c2 d, kd_m2 d) :: r1 else r1
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
        (match n1 with ELit z1 => disj_sidesBX bc (bc_kd bc) (ekeys b1 []) b1 k1 (zlit64 z1) | _ => [] end)   (* [comment removed for export] *)
        (disj_sides_xBX bc (bc_kd bc) (ekeys b1 []) b1 k1 n1).

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
      else if lin_apartB bc b1 k1 m1 b2 k2 m2 then true
      else lin_apart2B bc b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match sp_rng sp, base_rangeB bc b2, sp_h1 sp, xhiB bc n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else  
            if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_xB bc (sp_Dx sp) b2 k2 n2 then true
    else if apart_gate b1 b2 then false   (* [comment removed for export] *)
    else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

(* [comment removed for export] *)
Section FactFilter.
Local Open Scope Z_scope.
Lemma aluop_eqb_sp : forall a b, aluop_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.
Lemma mulop_eqb_sp : forall a b, mulop_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.
Lemma expr_eqb_eqB : forall x y, expr_eqb x y = true -> x = y.
Proof.
  induction x; destruct y; cbn; intros H; try discriminate;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      | H : (if ?c then _ else false) = true |- _ => let E := fresh "E" in destruct c eqn:E; [|discriminate H]
      end;
    repeat match goal with
      | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
      | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
      | H : N.eqb _ _ = true |- _ => apply N.eqb_eq in H
      | H : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in H
      | H : aluop_eqb _ _ = true |- _ => apply aluop_eqb_sp in H
      | H : mulop_eqb _ _ = true |- _ => apply mulop_eqb_sp in H
      | H : expr_eqb ?a _ = true, IH : forall y, expr_eqb ?a y = true -> _ |- _ => apply IH in H
      end; subst; reflexivity.
Qed.

Lemma coef_of_lins_e_other : forall k a b ts, expr_eqb a b = false -> coef_of a (lins_e k b ts) = coef_of a ts.
Proof.
  intros k a b ts H. induction ts as [|[k' a'] rest IH]; cbn [lins_e].
  - destruct (Z.eqb k 0); cbn [coef_of]; [reflexivity|]. rewrite H. reflexivity.
  - destruct (expr_eqb b a') eqn:Hb.
    + apply expr_eqb_eqB in Hb. subst a'. destruct (Z.eqb (k + k') 0); cbn [coef_of]; rewrite H; reflexivity.
    + cbn [coef_of]. destruct (expr_eqb a a'); [reflexivity | exact IH].
Qed.

Lemma fact_quot_present : forall fts ts acc q, fact_quot fts ts acc = Some q ->
  forall k b, In (k, b) fts -> coef_of b ts <> 0.
Proof.
  induction fts as [|[k0 a0] r IH]; intros ts acc q H k b Hin; [destruct Hin|].
  cbn [fact_quot] in H.
  destruct (Z.eqb k0 0); [discriminate|].
  destruct (Z.eqb (coef_of a0 ts) 0) eqn:HK; [discriminate|].
  match type of H with (match ?x with Some _ => _ | None => _ end) = _ => destruct x as [q1|]; [|discriminate] end.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. apply Z.eqb_neq in HK. exact HK.
  - destruct acc as [q0|].
    + destruct (Z.eqb q0 q1); [exact (IH _ _ _ H k b Hin) | discriminate].
    + exact (IH _ _ _ H k b Hin).
Qed.

Lemma coef_of_sub_fact_zero : forall q fts ts a,
  (forall k b, In (k, b) fts -> coef_of b ts <> 0) -> coef_of a ts = 0 -> coef_of a (sub_fact q fts ts) = 0.
Proof.
  intros q fts ts a Hp Ha. unfold sub_fact.
  assert (NE : forall k b, In (k, b) fts -> expr_eqb a b = false).
  { intros k b Hin. destruct (expr_eqb a b) eqn:E; [|reflexivity]. apply expr_eqb_eqB in E. subst b.
    exfalso. exact (Hp k a Hin Ha). }
  clear Hp. induction fts as [|[k0 b0] r IH]; cbn [fold_right]; [exact Ha|].
  cbn [fst snd]. rewrite coef_of_lins_e_other by exact (NE k0 b0 (or_introl eq_refl)).
  apply IH. intros k b Hin. exact (NE k b (or_intror Hin)).
Qed.

Lemma fact_quot_irrel : forall fts ts acc,
  (forall k b, In (k, b) fts -> coef_of b ts = 0) -> fts <> [] -> fact_quot fts ts acc = None.
Proof.
  intros [|[k0 a0] r] ts acc H Hne; [exfalso; apply Hne; reflexivity|].
  cbn [fact_quot]. destruct (Z.eqb k0 0); [reflexivity|].
  rewrite (H k0 a0 (or_introl eq_refl)). reflexivity.
Qed.

(* [comment removed for export] *)
Inductive drop_nr (ts0 : list (Z * expr)) : list sfact -> list sfact -> Prop :=
| dn_nil : drop_nr ts0 [] []
| dn_keep : forall f l1 l2, drop_nr ts0 l1 l2 -> drop_nr ts0 (f :: l1) (f :: l2)
| dn_drop : forall f l1 l2, fact_rel ts0 f = false -> drop_nr ts0 l1 l2 -> drop_nr ts0 l1 (f :: l2).

Lemma drop_nr_filter : forall ts0 l, drop_nr ts0 (List.filter (fact_rel ts0) l) l.
Proof.
  intros ts0 l. induction l as [|f r IH]; cbn [List.filter]; [constructor|].
  destruct (fact_rel ts0 f) eqn:E; [apply dn_keep; exact IH | apply dn_drop; [exact E | exact IH]].
Qed.
Lemma drop_nr_app : forall ts0 l1 l2 m, drop_nr ts0 l1 l2 -> drop_nr ts0 (l1 ++ m) (l2 ++ m).
Proof.
  intros ts0 l1 l2 m H. induction H; cbn [app].
  - induction m as [|f r IH]; [constructor | apply dn_keep; exact IH].
  - apply dn_keep. exact IHdrop_nr.
  - apply dn_drop; assumption.
Qed.

Lemma fact_rel_false_coef : forall ts0 f, fact_rel ts0 f = false -> forall k b, In (k, b) (fst f) -> coef_of b ts0 = 0.
Proof.
  intros ts0 f H k b Hin. unfold fact_rel in H.
  destruct (Z.eqb (coef_of b ts0) 0) eqn:E; [apply Z.eqb_eq; exact E|].
  exfalso. assert (X : existsb (fun t => negb (Z.eqb (coef_of (snd t) ts0) 0)) (fst f) = true).
  { apply existsb_exists. exists (k, b). split; [exact Hin|]. cbn [snd]. rewrite E. reflexivity. }
  rewrite X in H. discriminate.
Qed.

Lemma sum_subst_drop_nr : forall ts0 l1 l2, drop_nr ts0 l1 l2 ->
  forall ts lo hi hit, (forall a, coef_of a ts0 = 0 -> coef_of a ts = 0) -> sum_subst l1 ts lo hi hit = sum_subst l2 ts lo hi hit.
Proof.
  intros ts0 l1 l2 H. induction H as [|f l1 l2 H IH|f l1 l2 Hf H IH]; intros ts lo hi hit Hsub.
  - reflexivity.
  - destruct f as [fts [flo fhi]]. cbn [sum_subst].
    destruct (fact_quot fts ts None) as [q|] eqn:Hq; [|apply IH; exact Hsub].
    assert (INV : forall a, coef_of a ts0 = 0 -> coef_of a (sub_fact q fts ts) = 0).
    { intros a Ha. apply coef_of_sub_fact_zero; [exact (fact_quot_present _ _ _ _ Hq) | exact (Hsub a Ha)]. }
    destruct (Z.leb 0 q); apply IH; exact INV.
  - destruct f as [fts [flo fhi]]. cbn [sum_subst].
    destruct fts as [|t r] eqn:Hfts.
    + cbn [fact_quot]. apply IH. exact Hsub.
    + rewrite (fact_quot_irrel (t :: r) ts None); [apply IH; exact Hsub | | discriminate].
      intros k b Hin. apply Hsub. exact (fact_rel_false_coef ts0 (t :: r, (flo, fhi)) Hf k b Hin).
Qed.

Lemma lin_test_rel0_drop_nr : forall er ts0 l1 l2 c test, drop_nr ts0 l1 l2 ->
  lin_test_rel0 er l1 c ts0 test = lin_test_rel0 er l2 c ts0 test.
Proof.
  intros er ts0 l1 l2 c test H. unfold lin_test_rel0.
  assert (E : sum_subst l1 ts0 0 0 false = sum_subst l2 ts0 0 0 false) by (apply (sum_subst_drop_nr ts0); [exact H | auto]).
  destruct l1 as [|f1 r1]; destruct l2 as [|f2 r2]; try reflexivity.
  - (* [comment removed for export] *)
    rewrite <- E. cbn [sum_subst]. reflexivity.
  - inversion H.
  - rewrite E. reflexivity.
Qed.

Lemma project_fact_irrel : forall er ts f, fact_rel ts f = false -> project_fact er ts f = [].
Proof.
  intros er ts [fts fr] H. unfold project_fact. cbn [fst snd].
  assert (P : fst (split_fact_terms ts fts) = []).
  { pose proof (fact_rel_false_coef ts (fts, fr) H) as Z0. cbn [fst] in Z0. clear H.
    induction fts as [|[k b] r IH]; [reflexivity|]. cbn [split_fact_terms].
    destruct (split_fact_terms ts r) as [pr rs] eqn:Hs. cbn [fst] in IH.
    rewrite (Z0 k b (or_introl eq_refl)). cbn [Z.eqb]. cbn [fst]. apply IH. intros k' b' Hin. exact (Z0 k' b' (or_intror Hin)). }
  destruct (split_fact_terms ts fts) as [pr rs]. cbn [fst] in P. subst pr. reflexivity.
Qed.

Lemma flat_map_project_drop_nr : forall er ts0 l1 l2, drop_nr ts0 l1 l2 ->
  List.flat_map (project_fact er ts0) l1 = List.flat_map (project_fact er ts0) l2.
Proof.
  intros er ts0 l1 l2 H. induction H; cbn [flat_map]; [reflexivity | rewrite IHdrop_nr; reflexivity |].
  rewrite project_fact_irrel by assumption. exact IHdrop_nr.
Qed.

Lemma fact_quots_irrel : forall fts ts, (forall k b, In (k, b) fts -> coef_of b ts = 0) -> fact_quots fts ts = [].
Proof.
  induction fts as [|[k b] r IH]; intros ts H; [reflexivity|]. cbn [fact_quots].
  rewrite (H k b (or_introl eq_refl)). rewrite orb_true_r.
  apply IH; intros k' b' Hin; exact (H k' b' (or_intror Hin)).
Qed.

Lemma lin_test_relq_drop_nr : forall er ts0 l1 l2 c test, drop_nr ts0 l1 l2 ->
  lin_test_relq er l1 c ts0 test = lin_test_relq er l2 c ts0 test.
Proof.
  intros er ts0 l1 l2 c test H. unfold lin_test_relq. induction H; cbn [existsb]; [reflexivity | rewrite IHdrop_nr; reflexivity |].
  rewrite IHdrop_nr. rewrite (fact_quots_irrel (fst f) ts0) by exact (fact_rel_false_coef ts0 f H). reflexivity.
Qed.

Lemma relk_false_rel : forall ts f, relk (ts_keys ts) (fact_keys f) = false -> fact_rel ts f = false.
Proof.
  intros ts [fts fr] H. unfold relk, fact_keys, fact_rel in *. cbn [fst] in *.
  induction fts as [|[k b] r IH]; [reflexivity|]. cbn [existsb List.map] in H |- *. apply orb_false_iff in H as [H1 H2].
  rewrite (IH H2), orb_false_r. apply negb_false_iff. apply Z.eqb_eq. cbn [snd] in *.
  destruct b; cbn [atom_key key_in] in H1; try discriminate.
  (* [comment removed for export] *)
  clear IH H2. induction ts as [|[k' a'] rest IHt]; [reflexivity|]. cbn [coef_of].
  unfold ts_keys in H1. cbn [flat_map] in H1. rewrite existsb_app in H1. apply orb_false_iff in H1 as [H3 H4].
  destruct (expr_eqb (EVar n) a') eqn:E.
  - apply expr_eqb_eqB in E. subst a'. cbn [snd atom_key existsb] in H3. rewrite Pos.eqb_refl in H3. discriminate.
  - apply IHt. exact H4.
Qed.

Lemma drop_nr_keyed : forall ts fs,
  drop_nr ts (List.map fst (List.filter (fun p => relk (ts_keys ts) (snd p)) (List.map (fun f => (f, fact_keys f)) fs))) fs.
Proof.
  intros ts fs. induction fs as [|f r IH]; cbn [List.map List.filter]; [constructor|].
  cbn [snd]. destruct (relk (ts_keys ts) (fact_keys f)) eqn:E; cbn [List.map fst].
  - apply dn_keep. exact IH.
  - apply dn_drop; [exact (relk_false_rel ts f E) | exact IH].
Qed.

Lemma lin_test_relB_filter : forall fk c ts test, lin_test_relB (mkbc fk) c ts test = lin_test_relB0 (mkbc fk) c ts test.
Proof.
  intros fk c ts test. unfold lin_test_relB, lin_test_relB0.
  set (bc := mkbc fk).
  assert (FK : bc_fsk bc = List.map (fun f => (f, fact_keys f)) (bc_fs bc)) by reflexivity.
  rewrite FK.
  pose proof (drop_nr_keyed ts (bc_fs bc)) as D.
  rewrite (flat_map_project_drop_nr (erangeB bc) ts _ _ D).
  rewrite (lin_test_rel0_drop_nr (erangeB bc) ts _ _ c test D).
  rewrite (lin_test_rel0_drop_nr (erangeB bc) ts _ _ c test (drop_nr_app ts _ _ _ D)).
  rewrite (lin_test_relq_drop_nr (erangeB bc) ts _ _ c test (drop_nr_app ts _ _ _ D)).
  reflexivity.
Qed.

End FactFilter.

Lemma lin_test_relB_eqf : forall fk, lin_test_relB (mkbc fk) = lin_test_rel fk.
Proof. intros. bcfe. rewrite lin_test_relB_filter. unfold lin_test_relB0, lin_test_rel. autorewrite with bceq. reflexivity. Qed.
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
Proof.
  intros fk. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1.
  apply functional_extensionality; intros n1. apply functional_extensionality; intros b2.
  apply functional_extensionality; intros k2. apply functional_extensionality; intros n2.
  unfold lin_apart0B, lin_apart0. autorewrite with bceq.
  destruct (lin_nowrapR fk b1); [|reflexivity]. destruct (lin_nowrapR fk b2); reflexivity.
Qed.
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
  cbn [xt_nowrapB xt_nowrap]. rewrite IH. autorewrite with bceq. destruct (lin_nowrapR fk e); reflexivity.
Qed.
#[export] Hint Rewrite xt_nowrapB_eqf : bceq.
Lemma lin_ge0_scaledB_eqf : forall fk, lin_ge0_scaledB (mkbc fk) = lin_ge0_scaled fk.
Proof. intros. bcfe. unfold lin_ge0_scaledB, lin_ge0_scaled. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_ge0_scaledB_eqf : bceq.
Lemma lin_ge0B_eqf : forall fk, lin_ge0B (mkbc fk) = lin_ge0 fk.
Proof.
  intros fk. apply functional_extensionality; intros pos. apply functional_extensionality; intros neg.
  unfold lin_ge0B, lin_ge0. autorewrite with bceq.
  destruct (xt_nowrap fk pos); [|reflexivity]. destruct (xt_nowrap fk neg); reflexivity.
Qed.
#[export] Hint Rewrite lin_ge0B_eqf : bceq.

Lemma lin_apart2B_eqf : forall fk, lin_apart2B (mkbc fk) = lin_apart2 fk.
Proof. intros. bcfe. unfold lin_apart2B, lin_apart2. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_apart2B_eqf : bceq.
Lemma xinside_refutedB_eqf : forall fk, xinside_refutedB (mkbc fk) = xinside_refuted fk.
Proof. intros. bcfe. unfold xinside_refutedB, xinside_refuted. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite xinside_refutedB_eqf : bceq.
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
(* [comment removed for export] *)
Lemma ekeys_acc : forall e acc x, In x acc -> In x (ekeys e acc).
Proof.
  induction e as [z|v|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx kk i n];
    intros acc x H; cbn [ekeys]; auto; try (right; exact H).
Qed.
Lemma ekeys_mentions : forall e v acc, mentions_var v e = true -> In (pos_fast v) (ekeys e acc).
Proof.
  induction e as [z|w|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx kk i n];
    intros v acc H; cbn [mentions_var ekeys] in *; try discriminate.
  - apply N.eqb_eq in H. subst w. left. reflexivity.
  - destruct (mentions_var v a) eqn:Ha; [exact (IHa v _ Ha) | apply ekeys_acc; exact (IHb v acc H)].
  - destruct (mentions_var v a) eqn:Ha; [exact (IHa v _ Ha) | apply ekeys_acc; exact (IHb v acc H)].
  - destruct (mentions_var v a) eqn:Ha; [exact (IHa v _ Ha) | apply ekeys_acc; exact (IHb v acc H)].
  - destruct (mentions_var v a) eqn:Ha; [exact (IHa v _ Ha) | apply ekeys_acc; exact (IHb v acc H)].
  - exact (IHa v acc H).
Qed.
Lemma shares_var_witness : forall c b, shares_var b c = true -> exists v, mentions_var v c = true /\ mentions_var v b = true.
Proof.
  induction c as [z|w|op x IHx y IHy|op x IHx y IHy|op x IHx y IHy|op x IHx y IHy|sx lo n x IHx|sx kk i n];
    intros b H; cbn [shares_var] in H; try discriminate.
  - exists w. split; [cbn [mentions_var]; apply N.eqb_refl | exact H].
  - destruct (shares_var b x) eqn:Hx.
    + destruct (IHx b Hx) as (v & V1 & V2). exists v. split; [cbn [mentions_var]; rewrite V1; reflexivity | exact V2].
    + destruct (IHy b H) as (v & V1 & V2). exists v. split; [cbn [mentions_var]; rewrite V1; destruct (mentions_var v x); reflexivity | exact V2].
  - destruct (shares_var b x) eqn:Hx.
    + destruct (IHx b Hx) as (v & V1 & V2). exists v. split; [cbn [mentions_var]; rewrite V1; reflexivity | exact V2].
    + destruct (IHy b H) as (v & V1 & V2). exists v. split; [cbn [mentions_var]; rewrite V1; destruct (mentions_var v x); reflexivity | exact V2].
  - destruct (shares_var b x) eqn:Hx.
    + destruct (IHx b Hx) as (v & V1 & V2). exists v. split; [cbn [mentions_var]; rewrite V1; reflexivity | exact V2].
    + destruct (IHy b H) as (v & V1 & V2). exists v. split; [cbn [mentions_var]; rewrite V1; destruct (mentions_var v x); reflexivity | exact V2].
  - destruct (shares_var b x) eqn:Hx.
    + destruct (IHx b Hx) as (v & V1 & V2). exists v. split; [cbn [mentions_var]; rewrite V1; reflexivity | exact V2].
    + destruct (IHy b H) as (v & V1 & V2). exists v. split; [cbn [mentions_var]; rewrite V1; destruct (mentions_var v x); reflexivity | exact V2].
  - destruct (IHx b H) as (v & V1 & V2). exists v. split; [exact V1 | exact V2].
Qed.
Lemma shares_var_meet : forall b c, shares_var b c = true -> keys_meet (ekeys b []) (ekeys c []) = true.
Proof.
  intros b c H. destruct (shares_var_witness c b H) as (v & V1 & V2). unfold keys_meet. apply existsb_exists.
  exists (pos_fast v). split; [exact (ekeys_mentions b v [] V2)|]. apply existsb_exists.
  exists (pos_fast v). split; [exact (ekeys_mentions c v [] V1) | apply Pos.eqb_refl].
Qed.
Lemma shares_var_self_gen : forall c b, (forall v, mentions_var v c = true -> mentions_var v b = true) -> novars c = false -> shares_var b c = true.
Proof.
  induction c as [z|w|op x IHx y IHy|op x IHx y IHy|op x IHx y IHy|op x IHx y IHy|sx lo n x IHx|sx kk i n];
    intros b Hm Hn; cbn [novars shares_var] in *; try discriminate.
  - apply Hm. cbn [mentions_var]. apply N.eqb_refl.
  - destruct (novars x) eqn:Ex.
    + assert (Hy : shares_var b y = true).
      { apply IHy. intros v Hv; apply Hm; cbn [mentions_var]; rewrite Hv. destruct (mentions_var v x); reflexivity. exact Hn. }
      rewrite Hy. destruct (shares_var b x); reflexivity.
    + assert (Hx : shares_var b x = true).
      { apply IHx. intros v Hv; apply Hm; cbn [mentions_var]; rewrite Hv. reflexivity. reflexivity. }
      rewrite Hx. reflexivity.
  - destruct (novars x) eqn:Ex.
    + assert (Hy : shares_var b y = true).
      { apply IHy. intros v Hv; apply Hm; cbn [mentions_var]; rewrite Hv. destruct (mentions_var v x); reflexivity. exact Hn. }
      rewrite Hy. destruct (shares_var b x); reflexivity.
    + assert (Hx : shares_var b x = true).
      { apply IHx. intros v Hv; apply Hm; cbn [mentions_var]; rewrite Hv. reflexivity. reflexivity. }
      rewrite Hx. reflexivity.
  - destruct (novars x) eqn:Ex.
    + assert (Hy : shares_var b y = true).
      { apply IHy. intros v Hv; apply Hm; cbn [mentions_var]; rewrite Hv. destruct (mentions_var v x); reflexivity. exact Hn. }
      rewrite Hy. destruct (shares_var b x); reflexivity.
    + assert (Hx : shares_var b x = true).
      { apply IHx. intros v Hv; apply Hm; cbn [mentions_var]; rewrite Hv. reflexivity. reflexivity. }
      rewrite Hx. reflexivity.
  - destruct (novars x) eqn:Ex.
    + assert (Hy : shares_var b y = true).
      { apply IHy. intros v Hv; apply Hm; cbn [mentions_var]; rewrite Hv. destruct (mentions_var v x); reflexivity. exact Hn. }
      rewrite Hy. destruct (shares_var b x); reflexivity.
    + assert (Hx : shares_var b x = true).
      { apply IHx. intros v Hv; apply Hm; cbn [mentions_var]; rewrite Hv. reflexivity. reflexivity. }
      rewrite Hx. reflexivity.
  - apply IHx; [intros v Hv; apply Hm; exact Hv | exact Hn].
Qed.
Lemma xinsideB_cand : forall bc b1 k1 n1 b2 k2 n2, xinsideB bc b1 k1 n1 b2 k2 n2 = true -> novars b2 = true \/ shares_var b1 b2 = true.
Proof.
  intros bc b1 k1 n1 b2 k2 n2 H. unfold xinsideB in H.
  destruct (shares_var b1 b2) eqn:Hs; [right; reflexivity|]. destruct (novars b2) eqn:Hn; [left; reflexivity | discriminate].
Qed.
Lemma sub_itvB_cand : forall bc b k n c m, sub_itvB bc b k n c m = true -> novars (a_base c) = true \/ shares_var b (a_base c) = true.
Proof.
  intros bc b k n c m H. unfold sub_itvB in H.
  destruct (expr_eqb b (a_base c)) eqn:He.
  - apply p_expr_eqb_eq in He. subst b. destruct (novars (a_base c)) eqn:Hn; [left; reflexivity|]. right.
    apply shares_var_self_gen; [intros v Hv; exact Hv | exact Hn].
  - cbn [andb] in H. destruct (scale_clash b (a_base c)); [discriminate|].
    destruct (Z.leb 0 n && Z.ltb n two64)%bool; [|discriminate]. exact (xinsideB_cand _ _ _ _ _ _ _ H).
Qed.
Lemma sub_itv_xB_cand : forall bc b k n c m, sub_itv_xB bc b k n c m = true -> novars (a_base c) = true \/ shares_var b (a_base c) = true.
Proof.
  intros bc b k n c m H. unfold sub_itv_xB in H. destruct (scale_clash b (a_base c)); [discriminate|].
  exact (xinsideB_cand _ _ _ _ _ _ _ H).
Qed.
Lemma cand_false : forall b c, cand (ekeys b []) (ekeys (a_base c) []) (novars (a_base c)) = false ->
  novars (a_base c) = false /\ shares_var b (a_base c) = false.
Proof.
  intros b c H. unfold cand in H. destruct (novars (a_base c)); [discriminate|]. split; [reflexivity|].
  destruct (shares_var b (a_base c)) eqn:Hs; [|reflexivity]. rewrite (shares_var_meet _ _ Hs) in H. discriminate.
Qed.
Lemma sub_itvB_guard : forall bc b k n c m,
  (if cand (ekeys b []) (ekeys (a_base c) []) (novars (a_base c)) then sub_itvB bc b k n c m else false) = sub_itvB bc b k n c m.
Proof.
  intros bc b k n c m. destruct (cand _ _ _) eqn:Hc; [reflexivity|]. destruct (cand_false _ _ Hc) as [H1 H2].
  destruct (sub_itvB bc b k n c m) eqn:Hs; [|reflexivity]. destruct (sub_itvB_cand _ _ _ _ _ _ Hs); congruence.
Qed.
Lemma sub_itv_xB_guard : forall bc b k n c m,
  (if cand (ekeys b []) (ekeys (a_base c) []) (novars (a_base c)) then sub_itv_xB bc b k n c m else false) = sub_itv_xB bc b k n c m.
Proof.
  intros bc b k n c m. destruct (cand _ _ _) eqn:Hc; [reflexivity|]. destruct (cand_false _ _ Hc) as [H1 H2].
  destruct (sub_itv_xB bc b k n c m) eqn:Hs; [|reflexivity]. destruct (sub_itv_xB_cand _ _ _ _ _ _ Hs); congruence.
Qed.
Lemma guard2 : forall (g1 g2 x y : bool), (if g1 then x else false) = x -> (if g2 then y else false) = y ->
  (if g1 then if g2 then (if x then y else false) else false else false) = (if x then y else false).
Proof. intros [|] [|] [|] [|]; cbn; congruence. Qed.
Lemma kdisj_apartBX_eq : forall bc kn b1 k1 n1 b2 k2 n2,
  kdisj_apartBX bc (mk_kdx kn) (ekeys b1 []) (ekeys b2 []) b1 k1 n1 b2 k2 n2 = kdisj_apartB bc kn b1 k1 n1 b2 k2 n2.
Proof.
  intros bc kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; [reflexivity|].
  destruct K; cbn [mk_kdx kdisj_apartB]; try exact IH.
  cbn [kdisj_apartBX kd_c1 kd_m1 kd_c2 kd_m2 kd_k1 kd_l1 kd_k2 kd_l2].
  rewrite (guard2 _ _ _ _ (sub_itvB_guard bc b1 k1 n1 _ _) (sub_itvB_guard bc b2 k2 n2 _ _)).
  rewrite (guard2 _ _ _ _ (sub_itvB_guard bc b1 k1 n1 _ _) (sub_itvB_guard bc b2 k2 n2 _ _)).
  rewrite IH. reflexivity.
Qed.
Lemma kdisj_apart_xBX_eq : forall bc kn b1 k1 n1 b2 k2 n2,
  kdisj_apart_xBX bc (mk_kdx kn) (ekeys b1 []) (ekeys b2 []) b1 k1 n1 b2 k2 n2 = kdisj_apart_xB bc kn b1 k1 n1 b2 k2 n2.
Proof.
  intros bc kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; [reflexivity|].
  destruct K; cbn [mk_kdx kdisj_apart_xB]; try exact IH.
  cbn [kdisj_apart_xBX kd_c1 kd_m1 kd_c2 kd_m2 kd_k1 kd_l1 kd_k2 kd_l2].
  rewrite (guard2 _ _ _ _ (sub_itv_xB_guard bc b1 k1 n1 _ _) (sub_itv_xB_guard bc b2 k2 n2 _ _)).
  rewrite (guard2 _ _ _ _ (sub_itv_xB_guard bc b1 k1 n1 _ _) (sub_itv_xB_guard bc b2 k2 n2 _ _)).
  rewrite IH. reflexivity.
Qed.
Lemma disj_sidesBX_eq : forall bc kn b1 k1 n1,
  disj_sidesBX bc (mk_kdx kn) (ekeys b1 []) b1 k1 n1 = disj_sidesB bc kn b1 k1 n1.
Proof.
  intros bc kn b1 k1 n1. induction kn as [|K rest IH]; [reflexivity|].
  destruct K; cbn [mk_kdx disj_sidesB]; try exact IH.
  cbn [disj_sidesBX kd_c1 kd_m1 kd_c2 kd_m2 kd_k1 kd_l1 kd_k2 kd_l2]. rewrite !sub_itvB_guard, IH. reflexivity.
Qed.
Lemma disj_sides_xBX_eq : forall bc kn b1 k1 n1,
  disj_sides_xBX bc (mk_kdx kn) (ekeys b1 []) b1 k1 n1 = disj_sides_xB bc kn b1 k1 n1.
Proof.
  intros bc kn b1 k1 n1. induction kn as [|K rest IH]; [reflexivity|].
  destruct K; cbn [mk_kdx disj_sides_xB]; try exact IH.
  cbn [disj_sides_xBX kd_c1 kd_m1 kd_c2 kd_m2 kd_k1 kd_l1 kd_k2 kd_l2]. rewrite !sub_itv_xB_guard, IH. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma kdisj_apartBX_mkbc : forall fk b1 k1 n1 b2 k2 n2,
  kdisj_apartBX (mkbc fk) (bc_kd (mkbc fk)) (ekeys b1 []) (ekeys b2 []) b1 k1 n1 b2 k2 n2 = kdisj_apartB (mkbc fk) (bc_fk (mkbc fk)) b1 k1 n1 b2 k2 n2.
Proof. intros. rewrite bc_kd_mkbc, bc_fk_mkbc. apply kdisj_apartBX_eq. Qed.
Lemma kdisj_apart_xBX_mkbc : forall fk b1 k1 n1 b2 k2 n2,
  kdisj_apart_xBX (mkbc fk) (bc_kd (mkbc fk)) (ekeys b1 []) (ekeys b2 []) b1 k1 n1 b2 k2 n2 = kdisj_apart_xB (mkbc fk) (bc_fk (mkbc fk)) b1 k1 n1 b2 k2 n2.
Proof. intros. rewrite bc_kd_mkbc, bc_fk_mkbc. apply kdisj_apart_xBX_eq. Qed.
Lemma disj_sidesBX_mkbc : forall fk b1 k1 n1,
  disj_sidesBX (mkbc fk) (bc_kd (mkbc fk)) (ekeys b1 []) b1 k1 n1 = disj_sidesB (mkbc fk) (bc_fk (mkbc fk)) b1 k1 n1.
Proof. intros. rewrite bc_kd_mkbc, bc_fk_mkbc. apply disj_sidesBX_eq. Qed.
Lemma disj_sides_xBX_mkbc : forall fk b1 k1 n1,
  disj_sides_xBX (mkbc fk) (bc_kd (mkbc fk)) (ekeys b1 []) b1 k1 n1 = disj_sides_xB (mkbc fk) (bc_fk (mkbc fk)) b1 k1 n1.
Proof. intros. rewrite bc_kd_mkbc, bc_fk_mkbc. apply disj_sides_xBX_eq. Qed.

Lemma kdisj_apartB_eqf : forall fk, kdisj_apartB (mkbc fk) = kdisj_apart fk.
Proof.
  intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2. 
  revert b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kdisj_apartB kdisj_apart]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite kdisj_apartB_eqf : bceq.
Lemma ranges_apartB_eqf : forall fk, ranges_apartB (mkbc fk) = ranges_apart fk.
Proof. intros. bcfe. unfold ranges_apartB, ranges_apart. rewrite kdisj_apartBX_mkbc. autorewrite with bceq. reflexivity. Qed.
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
Proof. intros. bcfe. unfold ranges_apart_xB, ranges_apart_x. rewrite ?kdisj_apart_xBX_mkbc. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite ranges_apart_xB_eqf : bceq.
Definition priv_apart_xB (bc : bctx) (wb : expr) (wk : Z) (wn : expr) (rs : list (saddr * expr)) : bool :=
  forallb (fun r : saddr * expr => ranges_apart_xB bc wb wk wn (a_base (fst r)) (a_off (fst r)) (snd r)) rs.
Lemma priv_apart_xB_eqf : forall fk, priv_apart_xB (mkbc fk) = priv_apart_x fk.
Proof. intros. bcfe. unfold priv_apart_xB, priv_apart_x. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite priv_apart_xB_eqf : bceq.
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
  intros fk. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1.
  unfold mk_sprepB, mk_sprep. rewrite disj_sides_xBX_mkbc.
  destruct n1; try rewrite disj_sidesBX_mkbc; autorewrite with bceq; reflexivity.
Qed.
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

Definition mkSrl_partB (bc : bctx) (a : expr) (s : Z) : option expr :=
  let l := lin_of a in
  let m := (2 ^ s)%Z in
  match (if (negb (lin_trivial l) && lin_nowrapB bc a)%bool then lsplit_divc m (snd l) else ([], [])) with
  | ((_ :: _) as dts, (_ :: _) as rts) =>
      match (if lin_nowrap_lB bc (fst l) rts then erangeB bc (unlin (fst l, rts)) else None) with
      | Some (lo, hi) =>
          if Z.eqb (lo / m) (hi / m) then Some (unlin ((lo / m)%Z, ldiv_terms m dts)) else None
      | None => None
      end
  | _ => None
  end.

Fixpoint mkSrlNB (f : nat) (bc : bctx) (a : expr) (s : Z) : expr :=
  let l := lin_of a in
  let m := (2 ^ s)%Z in
  if (negb (lin_trivial l) && coeffs_div m (snd l) && lin_nowrapB bc a)%bool
  then unlin ((fst l / m)%Z, ldiv_terms m (snd l))     (* [comment removed for export] *)
  else
    match mkSrl_partB bc a s with
    | Some e => e
    | None =>
        match f, (if (negb (lin_trivial l) && lin_nowrapB bc a && Z.ltb s 64)%bool then srl_step_t (snd l) s (Z.to_nat (s - 1)) else None) with
        | S f', Some t => mkSrlNB f' bc (unlin ((fst l / 2 ^ t)%Z, ldiv_terms (2 ^ t) (snd l))) (s - t)
        | _, _ => mkAlu ALU_SRL a (ELit s)
        end
    end.
Definition mkSrlB (bc : bctx) (a : expr) (s : Z) : expr := mkSrlNB 1 bc a s.

Fixpoint lowbitsB (bc : bctx) (e : expr) (j : Z) {struct e} : option Z :=
  let m := (2 ^ j)%Z in
  let dflt := if Z.leb j (ealignB bc e) then Some 0%Z else lin_lowbits_knB bc e j in
  match e with
  | ELit z => Some ((zmod64 z) mod m)%Z
  | EAlu ALU_AND a (ELit c) =>
      if Z.eqb ((zmod64 c) mod m) 0 then Some 0%Z else
      match lowbitsB bc a j with Some v => Some (Z.land v ((zmod64 c) mod m)) | None => dflt end
  | EAlu ALU_OR a (ELit c) =>
      match lowbitsB bc a j with Some v => Some (Z.lor v ((zmod64 c) mod m)) | None => dflt end
  | EAlu ALU_XOR a (ELit c) =>
      match lowbitsB bc a j with Some v => Some (Z.lxor v ((zmod64 c) mod m)) | None => dflt end
  | EAlu ALU_ADD a b =>
      match lowbitsB bc a j, lowbitsB bc b j with Some x, Some y => Some ((x + y) mod m)%Z | _, _ => dflt end
  | EAlu ALU_SUB a b =>
      match lowbitsB bc a j, lowbitsB bc b j with Some x, Some y => Some ((x - y) mod m)%Z | _, _ => dflt end
  | EMd M_MUL (ELit c) a =>
      if Z.eqb ((zmod64 c) mod m) 0 then Some 0%Z else
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
      let k' := (zmod64 k) in
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
      match narrow_maskB bc a (zmod64 k) with
      | Some m => mkAnd0B bc a (ELit m)
      | None => mkAnd0B bc a b
      end
  | _ => mkAnd0B bc a b
  end.

Definition mkAndKB (bc : bctx) (a b : expr) : expr :=
  match a, b with
  | EAlu ALU_AND x (ELit m1), ELit k => mkAndB bc x (ELit (Z.land (zmod64 m1) (zmod64 k))%Z)
  | EMd M_MUL (ELit m) (EAlu ALU_SRL x (ELit i)), ELit k =>
      (* [comment removed for export] *)
      let i' := ((zmod64 i) mod 64)%Z in
      if Z.eqb (zmod64 m) (2 ^ i') then mkAndB bc x (ELit (Z.land (two64 - 2 ^ i') (zmod64 k))%Z)
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
           | ELit c => mkAlu ALU_ADD (mkAndKB bc a (ELit (Z.lnot (zmod64 c)))) (ELit c)
           | _ => match a with
                  | ELit c => mkAlu ALU_ADD (mkAndKB bc b (ELit (Z.lnot (zmod64 c)))) (ELit c)
                  | _ => EAlu ALU_OR a b
                  end
           end
  end.

(* [comment removed for export] *)
Inductive etpl : Type :=
| THole | TLit (w : Z) | TNone
| TAlu (op : aluop) (a b : etpl) | TAluw (op : aluop) (a b : etpl)
| TMd (op : mulop) (a b : etpl) | TMdw (op : mulop) (a b : etpl)
| TExt (sx : bool) (lo n : nat) (a : etpl).
Fixpoint mark (s e : expr) : etpl :=
  if expr_eqb e s then THole else
  match e with
  | ELit w => TLit (wrap64 w)
  | EVar _ => TNone
  | EAlu op a b => TAlu op (mark s a) (mark s b)
  | EAluw op a b => TAluw op (mark s a) (mark s b)
  | EMd op a b => TMd op (mark s a) (mark s b)
  | EMdw op a b => TMdw op (mark s a) (mark s b)
  | EExt sx lo n a => TExt sx lo n (mark s a)
  | EBlob _ _ _ _ => TNone
  end.
Fixpoint evalT (t : etpl) (z : Z) : option Z :=
  match t with
  | THole => Some z
  | TLit w => Some w
  | TNone => None
  | TAlu op a b => match evalT a z with Some x => match evalT b z with Some y => Some (zfast op x y) | None => None end | None => None end
  | TAluw op a b => match evalT a z with Some x => match evalT b z with Some y => Some (zfastw op x y) | None => None end | None => None end
  | TMd op a b => match evalT a z with Some x => match evalT b z with Some y => Some (zfastm op x y) | None => None end | None => None end
  | TMdw op a b => match evalT a z with Some x => match evalT b z with Some y => Some (zmdw op x y) | None => None end | None => None end
  | TExt sx lo n a => match evalT a z with Some x => Some (zext_fast sx lo n x) | None => None end
  end.
Lemma evalT_mark : forall s z e, evalT (mark s e) z = evalS s z e.
Proof.
  intros s z e. induction e; cbn [mark evalS]; destruct (expr_eqb _ s); cbn [evalT]; try reflexivity;
    try (rewrite IHe1, IHe2; reflexivity); try (rewrite IHe; reflexivity).
Qed.
Fixpoint all_evalT (t : etpl) (v lo : Z) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c => match evalT t (wrap64 lo) with
           | Some w => if Z.eqb w v then all_evalT t v (lo + 1) c else false
           | None => false
           end
  end.
Definition all_eval_toT (s e : expr) (v lo : Z) (cnt : nat) : bool := all_evalT (mark s e) v lo cnt.
Lemma all_eval_toT_eq : forall s e v lo cnt, all_eval_toT s e v lo cnt = all_eval_toS s e v lo cnt.
Proof.
  intros s e v lo cnt. unfold all_eval_toT. revert lo. induction cnt as [|c IH]; intros lo; [reflexivity|].
  cbn [all_evalT all_eval_toS]. rewrite evalT_mark.
  destruct (evalS s (wrap64 lo) e) as [w|]; [|reflexivity]. destruct (Z.eqb w v); [apply IH | reflexivity].
Qed.
Lemma all_eval_toT_eqf : all_eval_toT = all_eval_toS.
Proof. repeat (apply functional_extensionality; intros ?). apply all_eval_toT_eq. Qed.

(* [comment removed for export] *)
Inductive dgo : Type := GHole | GLit (w : Z) | GNode (i : nat).
Inductive dgr : Type := DgH | DgL (w : Z) | DgN (d : nat).
Inductive dgn : Type :=
| GAlu (op : aluop) (a b : dgr) | GAluw (op : aluop) (a b : dgr) | GMd (op : mulop) (a b : dgr) | GMdw (op : mulop) (a b : dgr)
| GExt (sx : bool) (lo n : nat) (a : dgr).
Definition aluc (op : aluop) : nat :=
  match op with ALU_ADD => 0 | ALU_SUB => 1 | ALU_SLL => 2 | ALU_SLT => 3 | ALU_SLTU => 4 | ALU_XOR => 5 | ALU_SRL => 6 | ALU_SRA => 7 | ALU_OR => 8 | ALU_AND => 9 end.
Definition mulc (op : mulop) : nat :=
  match op with M_MUL => 0 | M_MULH => 1 | M_MULHSU => 2 | M_MULHU => 3 | M_DIV => 4 | M_DIVU => 5 | M_REM => 6 | M_REMU => 7 end.
Lemma aluc_inj : forall a b, Nat.eqb (aluc a) (aluc b) = true -> a = b.
Proof. intros [] [] H; cbn in H; try discriminate H; reflexivity. Qed.
Lemma mulc_inj : forall a b, Nat.eqb (mulc a) (mulc b) = true -> a = b.
Proof. intros [] [] H; cbn in H; try discriminate H; reflexivity. Qed.
Fixpoint etpl_eqb (x y : etpl) : bool :=
  match x, y with
  | THole, THole => true
  | TLit a, TLit b => Z.eqb a b
  | TNone, TNone => true
  | TAlu o a b, TAlu o' a' b' => if Nat.eqb (aluc o) (aluc o') then if etpl_eqb a a' then etpl_eqb b b' else false else false
  | TAluw o a b, TAluw o' a' b' => if Nat.eqb (aluc o) (aluc o') then if etpl_eqb a a' then etpl_eqb b b' else false else false
  | TMd o a b, TMd o' a' b' => if Nat.eqb (mulc o) (mulc o') then if etpl_eqb a a' then etpl_eqb b b' else false else false
  | TMdw o a b, TMdw o' a' b' => if Nat.eqb (mulc o) (mulc o') then if etpl_eqb a a' then etpl_eqb b b' else false else false
  | TExt sx lo n a, TExt sx' lo' n' a' =>
      if Bool.eqb sx sx' then if Nat.eqb lo lo' then if Nat.eqb n n' then etpl_eqb a a' else false else false else false
  | _, _ => false
  end.
Lemma etpl_eqb_eq : forall x y, etpl_eqb x y = true -> x = y.
Proof.
  induction x; destruct y; cbn; intros H; try discriminate H; try reflexivity.
  - apply Z.eqb_eq in H. subst. reflexivity.
  - destruct (Nat.eqb (aluc op) (aluc op0)) eqn:E; [|discriminate H]. apply aluc_inj in E. subst.
    destruct (etpl_eqb x1 y1) eqn:E1; [|discriminate H]. rewrite (IHx1 _ E1), (IHx2 _ H). reflexivity.
  - destruct (Nat.eqb (aluc op) (aluc op0)) eqn:E; [|discriminate H]. apply aluc_inj in E. subst.
    destruct (etpl_eqb x1 y1) eqn:E1; [|discriminate H]. rewrite (IHx1 _ E1), (IHx2 _ H). reflexivity.
  - destruct (Nat.eqb (mulc op) (mulc op0)) eqn:E; [|discriminate H]. apply mulc_inj in E. subst.
    destruct (etpl_eqb x1 y1) eqn:E1; [|discriminate H]. rewrite (IHx1 _ E1), (IHx2 _ H). reflexivity.
  - destruct (Nat.eqb (mulc op) (mulc op0)) eqn:E; [|discriminate H]. apply mulc_inj in E. subst.
    destruct (etpl_eqb x1 y1) eqn:E1; [|discriminate H]. rewrite (IHx1 _ E1), (IHx2 _ H). reflexivity.
  - destruct (Bool.eqb sx sx0) eqn:E0; [|discriminate H]. apply Bool.eqb_prop in E0. subst.
    destruct (Nat.eqb lo lo0) eqn:E1; [|discriminate H]. apply Nat.eqb_eq in E1. subst.
    destruct (Nat.eqb n n0) eqn:E2; [|discriminate H]. apply Nat.eqb_eq in E2. subst.
    rewrite (IHx _ H). reflexivity.
Qed.
Record dgs := DGS { dg_cur : nat; dg_memo : list (etpl * dgo); dg_prog : list dgn }.
Fixpoint dg_find (t : etpl) (m : list (etpl * dgo)) : option dgo :=
  match m with [] => None | (t', o) :: r => if etpl_eqb t t' then Some o else dg_find t r end.
Definition dg_rel (cur : nat) (o : dgo) : dgr := match o with GHole => DgH | GLit w => DgL w | GNode i => DgN (cur - S i) end.
Definition dg_emit (st : dgs) (t : etpl) (nd : dgn) : dgo * dgs :=
  (GNode (dg_cur st), DGS (S (dg_cur st)) ((t, GNode (dg_cur st)) :: dg_memo st) (nd :: dg_prog st)).
Fixpoint dg_comp (t : etpl) (st : dgs) : option (dgo * dgs) :=
  match t with
  | THole => Some (GHole, st)
  | TLit w => Some (GLit w, st)
  | TNone => None
  | TAlu op a b =>
      match dg_find t (dg_memo st) with
      | Some o => Some (o, st)
      | None =>
          match dg_comp a st with
          | Some (oa, st1) => match dg_comp b st1 with
                              | Some (ob, st2) => Some (dg_emit st2 t (GAlu op (dg_rel (dg_cur st2) oa) (dg_rel (dg_cur st2) ob)))
                              | None => None end
          | None => None end
      end
  | TAluw op a b =>
      match dg_find t (dg_memo st) with
      | Some o => Some (o, st)
      | None =>
          match dg_comp a st with
          | Some (oa, st1) => match dg_comp b st1 with
                              | Some (ob, st2) => Some (dg_emit st2 t (GAluw op (dg_rel (dg_cur st2) oa) (dg_rel (dg_cur st2) ob)))
                              | None => None end
          | None => None end
      end
  | TMd op a b =>
      match dg_find t (dg_memo st) with
      | Some o => Some (o, st)
      | None =>
          match dg_comp a st with
          | Some (oa, st1) => match dg_comp b st1 with
                              | Some (ob, st2) => Some (dg_emit st2 t (GMd op (dg_rel (dg_cur st2) oa) (dg_rel (dg_cur st2) ob)))
                              | None => None end
          | None => None end
      end
  | TMdw op a b =>
      match dg_find t (dg_memo st) with
      | Some o => Some (o, st)
      | None =>
          match dg_comp a st with
          | Some (oa, st1) => match dg_comp b st1 with
                              | Some (ob, st2) => Some (dg_emit st2 t (GMdw op (dg_rel (dg_cur st2) oa) (dg_rel (dg_cur st2) ob)))
                              | None => None end
          | None => None end
      end
  | TExt sx lo n a =>
      match dg_find t (dg_memo st) with
      | Some o => Some (o, st)
      | None =>
          match dg_comp a st with
          | Some (oa, st1) => Some (dg_emit st1 t (GExt sx lo n (dg_rel (dg_cur st1) oa)))
          | None => None end
      end
  end.
Definition dg_val (env : list Z) (z : Z) (o : dgr) : Z := match o with DgH => z | DgL w => w | DgN d => nth d env 0%Z end.
Definition dg_step (n : dgn) (z : Z) (env : list Z) : Z :=
  match n with
  | GAlu op a b => zfast op (dg_val env z a) (dg_val env z b)
  | GAluw op a b => zfastw op (dg_val env z a) (dg_val env z b)
  | GMd op a b => zfastm op (dg_val env z a) (dg_val env z b)
  | GMdw op a b => zmdw op (dg_val env z a) (dg_val env z b)
  | GExt sx lo n a => zext_fast sx lo n (dg_val env z a)
  end.
(* [comment removed for export] *)
Fixpoint dg_run (prog : list dgn) (z : Z) (env : list Z) : list Z :=
  match prog with [] => env | n :: r => dg_run r z (dg_step n z env :: env) end.
Fixpoint all_evalD (prog : list dgn) (r : dgr) (v lo : Z) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c => let z := wrap64 lo in if Z.eqb (dg_val (dg_run prog z []) z r) v then all_evalD prog r v (lo + 1) c else false
  end.
Definition all_eval_toD (s e : expr) (v lo : Z) (cnt : nat) : bool :=
  let t := mark s e in
  if Nat.leb cnt 64 then all_evalT t v lo cnt else   (* [comment removed for export] *)
  match dg_comp t (DGS O [] []) with
  | Some (o, st) => all_evalD (rev (dg_prog st)) (dg_rel (dg_cur st) o) v lo cnt
  | None => all_evalT t v lo cnt
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dg_aval (env : list Z) (z : Z) (o : dgo) : Z :=
  match o with GHole => z | GLit w => w | GNode i => nth (length env - S i) env 0%Z end.
Definition dg_aok (n : nat) (o : dgo) : Prop := match o with GNode i => (i < n)%nat | _ => True end.
Lemma dg_aval_ext : forall env env' z o, dg_aok (length env) o -> dg_aval (env' ++ env) z o = dg_aval env z o.
Proof.
  intros env env' z [|w|i] H; cbn [dg_aval dg_aok] in *; try reflexivity.
  rewrite length_app. rewrite app_nth2 by lia. f_equal. lia.
Qed.
Lemma dg_val_rel : forall env z o, dg_aok (length env) o -> dg_val env z (dg_rel (length env) o) = dg_aval env z o.
Proof. intros env z [|w|i] H; reflexivity. Qed.
Lemma dg_run_app : forall p1 p2 z env, dg_run (p1 ++ p2) z env = dg_run p2 z (dg_run p1 z env).
Proof. induction p1 as [|n r IH]; intros p2 z env; cbn; [reflexivity|]. apply IH. Qed.
Lemma dg_run_length : forall p z env, length (dg_run p z env) = (length p + length env)%nat.
Proof. induction p as [|n r IH]; intros z env; cbn; [reflexivity|]. rewrite IH. cbn. lia. Qed.
Lemma dg_run_suffix : forall p z env, exists l, dg_run p z env = l ++ env.
Proof.
  induction p as [|n r IH]; intros z env; cbn; [exists []; reflexivity|].
  destruct (IH z (dg_step n z env :: env)) as [l E]. rewrite E. exists (l ++ [dg_step n z env]). rewrite <- app_assoc. reflexivity.
Qed.
Definition dg_env (st : dgs) (z : Z) : list Z := dg_run (rev (dg_prog st)) z [].
Definition dg_inv (st : dgs) : Prop :=
  length (dg_prog st) = dg_cur st /\
  forall t o, In (t, o) (dg_memo st) -> dg_aok (dg_cur st) o /\ forall z, evalT t z = Some (dg_aval (dg_env st z) z o).
Lemma dg_env_length : forall st z, dg_inv st -> length (dg_env st z) = dg_cur st.
Proof. intros st z [HL _]. unfold dg_env. rewrite dg_run_length, length_rev. cbn. lia. Qed.
Lemma dg_find_in : forall t m o, dg_find t m = Some o -> In (t, o) m.
Proof.
  induction m as [|[t' o'] r IH]; intros o H; cbn in H; [discriminate H|].
  destruct (etpl_eqb t t') eqn:E.
  - apply etpl_eqb_eq in E. subst. injection H as <-. left. reflexivity.
  - right. apply IH. exact H.
Qed.
(* [comment removed for export] *)
Definition dg_ext (st st' : dgs) : Prop :=
  (dg_cur st <= dg_cur st')%nat /\ exists p, dg_prog st' = p ++ dg_prog st.
Lemma dg_ext_refl : forall st, dg_ext st st.
Proof. intros st. split; [lia|]. exists []. reflexivity. Qed.
Lemma dg_ext_trans : forall a b c, dg_ext a b -> dg_ext b c -> dg_ext a c.
Proof.
  intros a b c [H1 [p1 E1]] [H2 [p2 E2]]. split; [lia|]. exists (p2 ++ p1). rewrite E2, E1. apply app_assoc.
Qed.
Lemma dg_env_ext : forall st st' z, dg_ext st st' -> exists l, dg_env st' z = l ++ dg_env st z.
Proof.
  intros st st' z [_ [p E]]. unfold dg_env. rewrite E, rev_app_distr, dg_run_app. apply dg_run_suffix.
Qed.
Lemma dg_aval_ext2 : forall st st' z o, dg_inv st -> dg_ext st st' -> dg_aok (dg_cur st) o -> dg_aval (dg_env st' z) z o = dg_aval (dg_env st z) z o.
Proof.
  intros st st' z o Hi Hx Ho. destruct (dg_env_ext _ _ z Hx) as [l E]. rewrite E. apply dg_aval_ext.
  rewrite (dg_env_length _ _ Hi). exact Ho.
Qed.
Lemma dg_aok_mono : forall n n' o, (n <= n')%nat -> dg_aok n o -> dg_aok n' o.
Proof. intros n n' [|w|i] H; cbn; auto; lia. Qed.
Lemma dg_emit_ok : forall st t nd,
  dg_inv st -> (forall z, evalT t z = Some (dg_step nd z (dg_env st z))) ->
  let '(o, st') := dg_emit st t nd in dg_inv st' /\ dg_ext st st' /\ dg_aok (dg_cur st') o /\ forall z, evalT t z = Some (dg_aval (dg_env st' z) z o).
Proof.
  intros st t nd Hi Ht. unfold dg_emit. cbn [dg_cur dg_memo dg_prog].
  assert (Hx : dg_ext st (DGS (S (dg_cur st)) ((t, GNode (dg_cur st)) :: dg_memo st) (nd :: dg_prog st))).
  { split; cbn; [lia|]. exists [nd]. reflexivity. }
  assert (Hv : forall z, dg_env (DGS (S (dg_cur st)) ((t, GNode (dg_cur st)) :: dg_memo st) (nd :: dg_prog st)) z
                         = dg_step nd z (dg_env st z) :: dg_env st z).
  { intros z. unfold dg_env. cbn [dg_prog rev]. rewrite dg_run_app. reflexivity. }
  assert (Hn : forall z, dg_aval (dg_env (DGS (S (dg_cur st)) ((t, GNode (dg_cur st)) :: dg_memo st) (nd :: dg_prog st)) z) z (GNode (dg_cur st))
                         = dg_step nd z (dg_env st z)).
  { intros z. rewrite Hv. cbn [dg_aval length]. rewrite (dg_env_length _ _ Hi). replace (S (dg_cur st) - S (dg_cur st))%nat with O by lia. reflexivity. }
  destruct Hi as [HL HM].
  split; [split|split; [exact Hx|split]].
  - cbn. rewrite HL. reflexivity.
  - intros t' o' Hin. cbn [dg_memo dg_cur] in Hin |- *. destruct Hin as [E|Hin].
    + injection E as <- <-. split; [cbn; lia|]. intros z. rewrite Hn. apply Ht.
    + destruct (HM _ _ Hin) as [Ho Hz]. split; [apply (dg_aok_mono (dg_cur st)); [lia|exact Ho]|].
      intros z. rewrite Hz. f_equal. symmetry. apply (dg_aval_ext2 st); [split; assumption|exact Hx|exact Ho].
  - cbn. lia.
  - intros z. rewrite Hn. apply Ht.
Qed.
Definition dg_res (t : etpl) (st st' : dgs) (o : dgo) : Prop :=
  dg_inv st' /\ dg_ext st st' /\ dg_aok (dg_cur st') o /\ forall z, evalT t z = Some (dg_aval (dg_env st' z) z o).
Lemma dg_comp_bin : forall (t a b : etpl) (f : Z -> Z -> Z) (mk : dgr -> dgr -> dgn) st oa st1 ob st2,
  (forall z, evalT t z = match evalT a z with Some x => match evalT b z with Some y => Some (f x y) | None => None end | None => None end) ->
  (forall env z x y, dg_step (mk x y) z env = f (dg_val env z x) (dg_val env z y)) ->
  dg_res a st st1 oa -> dg_res b st1 st2 ob ->
  forall o st', Some (dg_emit st2 t (mk (dg_rel (dg_cur st2) oa) (dg_rel (dg_cur st2) ob))) = Some (o, st') -> dg_res t st st' o.
Proof.
  intros t a b f mk st oa st1 ob st2 Ht Hmk [Hi1 [Hx1 [Ho1 Hz1]]] [Hi2 [Hx2 [Ho2 Hz2]]] o st' HS.
  pose proof (dg_emit_ok st2 t (mk (dg_rel (dg_cur st2) oa) (dg_rel (dg_cur st2) ob)) Hi2) as HE.
  destruct (dg_emit st2 t (mk (dg_rel (dg_cur st2) oa) (dg_rel (dg_cur st2) ob))) as [o0 st0] eqn:Hem. injection HS as <- <-.
  assert (Hd : forall z, evalT t z = Some (dg_step (mk (dg_rel (dg_cur st2) oa) (dg_rel (dg_cur st2) ob)) z (dg_env st2 z))).
  { intros z. rewrite Ht, Hz1, Hz2, Hmk. rewrite <- (dg_env_length st2 z Hi2).
    assert (Ho1' : dg_aok (length (dg_env st2 z)) oa).
    { rewrite (dg_env_length _ _ Hi2). apply (dg_aok_mono (dg_cur st1)); [apply Hx2|exact Ho1]. }
    assert (Ho2' : dg_aok (length (dg_env st2 z)) ob) by (rewrite (dg_env_length _ _ Hi2); exact Ho2).
    rewrite (dg_val_rel _ _ _ Ho1'), (dg_val_rel _ _ _ Ho2'). rewrite (dg_aval_ext2 st1 st2 z oa Hi1 Hx2 Ho1). reflexivity. }
  destruct (HE Hd) as [Hi' [Hx' [Ho' Hz']]]. split; [exact Hi'|split; [|split; [exact Ho'|exact Hz']]].
  apply (dg_ext_trans _ st1); [exact Hx1|]. apply (dg_ext_trans _ st2); [exact Hx2|exact Hx'].
Qed.
Lemma dg_comp_ok : forall t st o st', dg_inv st -> dg_comp t st = Some (o, st') -> dg_res t st st' o.
Proof.
  induction t as [| w | | op a IHa b IHb | op a IHa b IHb | op a IHa b IHb | op a IHa b IHb | sx lo n a IHa];
    intros st o st' Hi H; cbn [dg_comp] in H.
  1,2: injection H as <- <-; split; [exact Hi|split; [apply dg_ext_refl|split; [exact I|]]]; intros z; reflexivity.
  1: discriminate H.
  all: destruct (dg_find _ (dg_memo st)) as [o0|] eqn:Hf;
    [ injection H as <- <-; destruct (proj2 Hi _ _ (dg_find_in _ _ _ Hf)) as [Ho Hz];
      split; [exact Hi|split; [apply dg_ext_refl|split; [exact Ho|exact Hz]]] | ].
  all: destruct (dg_comp a st) as [[oa st1]|] eqn:Ha; [|discriminate H].
  all: pose proof (IHa _ _ _ Hi Ha) as Ra.
  1-4: destruct (dg_comp b st1) as [[ob st2]|] eqn:Hb; [|discriminate H];
       pose proof (IHb _ _ _ (proj1 Ra) Hb) as Rb.
  - exact (dg_comp_bin (TAlu op a b) a b (zfast op) (GAlu op) st oa st1 ob st2 (fun z => eq_refl) (fun env z x y => eq_refl) Ra Rb o st' H).
  - exact (dg_comp_bin (TAluw op a b) a b (zfastw op) (GAluw op) st oa st1 ob st2 (fun z => eq_refl) (fun env z x y => eq_refl) Ra Rb o st' H).
  - exact (dg_comp_bin (TMd op a b) a b (zfastm op) (GMd op) st oa st1 ob st2 (fun z => eq_refl) (fun env z x y => eq_refl) Ra Rb o st' H).
  - exact (dg_comp_bin (TMdw op a b) a b (zmdw op) (GMdw op) st oa st1 ob st2 (fun z => eq_refl) (fun env z x y => eq_refl) Ra Rb o st' H).
  - destruct Ra as [Hi1 [Hx1 [Ho1 Hz1]]].
    pose proof (dg_emit_ok st1 (TExt sx lo n a) (GExt sx lo n (dg_rel (dg_cur st1) oa)) Hi1) as HE.
    destruct (dg_emit st1 (TExt sx lo n a) (GExt sx lo n (dg_rel (dg_cur st1) oa))) as [o0 st0] eqn:Hem. injection H as <- <-.
    assert (Hd : forall z, evalT (TExt sx lo n a) z = Some (dg_step (GExt sx lo n (dg_rel (dg_cur st1) oa)) z (dg_env st1 z))).
    { intros z. cbn [evalT dg_step]. rewrite Hz1. rewrite <- (dg_env_length st1 z Hi1).
      assert (Ho1' : dg_aok (length (dg_env st1 z)) oa) by (rewrite (dg_env_length _ _ Hi1); exact Ho1).
      rewrite (dg_val_rel _ _ _ Ho1'). reflexivity. }
    destruct (HE Hd) as [Hi' [Hx' [Ho' Hz']]]. split; [exact Hi'|split; [|split; [exact Ho'|exact Hz']]].
    apply (dg_ext_trans _ st1); [exact Hx1|exact Hx'].
Qed.
Lemma dg_inv0 : dg_inv (DGS O [] []).
Proof. split; [reflexivity|]. intros t o H. destruct H. Qed.
Lemma all_evalD_eq : forall t st o, dg_comp t (DGS O [] []) = Some (o, st) ->
  forall v lo cnt, all_evalD (rev (dg_prog st)) (dg_rel (dg_cur st) o) v lo cnt = all_evalT t v lo cnt.
Proof.
  intros t st o H. destruct (dg_comp_ok _ _ _ _ dg_inv0 H) as [Hi [_ [Ho Hz]]].
  intros v lo cnt. revert lo. induction cnt as [|c IH]; intros lo; [reflexivity|]. cbn [all_evalD all_evalT].
  rewrite Hz.
  assert (E : dg_val (dg_run (rev (dg_prog st)) (wrap64 lo) []) (wrap64 lo) (dg_rel (dg_cur st) o) = dg_aval (dg_env st (wrap64 lo)) (wrap64 lo) o).
  { fold (dg_env st (wrap64 lo)). rewrite <- (dg_env_length st (wrap64 lo) Hi). apply dg_val_rel. rewrite (dg_env_length _ _ Hi). exact Ho. }
  rewrite E. destruct (Z.eqb _ v); [apply IH|reflexivity].
Qed.
Lemma all_eval_toD_eq : forall s e v lo cnt, all_eval_toD s e v lo cnt = all_eval_toT s e v lo cnt.
Proof.
  intros s e v lo cnt. unfold all_eval_toD, all_eval_toT. destruct (Nat.leb cnt 64); [reflexivity|].
  destruct (dg_comp (mark s e) (DGS O [] [])) as [[o st]|] eqn:H; [|reflexivity].
  apply (all_evalD_eq _ _ _ H).
Qed.
Lemma all_eval_toD_eqf : all_eval_toD = all_eval_toT.
Proof. repeat (apply functional_extensionality; intros ?). apply all_eval_toD_eq. Qed.


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
                  if all_eval_toD s e v lo (Z.to_nat (hi - lo + 1)) then Some v   (* [comment removed for export] *)
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
          if (Z.ltb ah two63z && Z.ltb bh two63z)%bool
          then match c with BC_LT => ltu | _ => option_map negb ltu end
          else None
      | _, _ => None
      end
  | BC_EQ | BC_NE =>
      (* [comment removed for export] *)
      if (if lin_ge0B bc [(b, (-1)%Z)] [(a, 0%Z)] then true else lin_ge0B bc [(a, (-1)%Z)] [(b, 0%Z)])   (* [comment removed for export] *)
      then Some (match c with BC_EQ => false | _ => true end)
      else
      (* [comment removed for export] *)
      if (if lin_ge0B bc [(a, 0%Z)] [(b, 0%Z)] then lin_ge0B bc [(b, 0%Z)] [(a, 0%Z)] else false)
      then Some (match c with BC_EQ => true | _ => false end)
      else None
  end.

Definition apart_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
  match c with
  | BC_EQ | BC_NE =>
      if ranges_apart_xB bc a 0 (ELit 1) b 0 (ELit 1) then Some (match c with BC_EQ => false | _ => true end) else None
  | _ => None
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
             | None => match lin_branchB bc c a b with      (* [comment removed for export] *)
                       | Some t => Some t
                       | None => apart_branchB bc c a b    (* [comment removed for export] *)
                       end
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
  | Some (lo, hi) => (Z.ltb (- two31z) lo && Z.ltb hi two31z)%bool
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
      if (Z.leb 0 (lo + a_off a) && Z.leb (hi + a_off a + Z.of_nat n) two64)%bool
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
              match rel_lit rb rk (Z.of_nat n) kb kk (zmod64 l0) with
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
              match rel_lit rb rk (Z.of_nat n) kb kk (zmod64 l0) with
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
      | KPriv _ _ _ _ => know_lookup segs rest rb rk n sx hints acc   (* [comment removed for export] *)
      | KBlob (SA kb kk) len k =>
          if expr_eqb rb kb then
            (* [comment removed for export] *)
            if Z.leb kk rk then
              match len with
              | ELit l0 =>
                  if Z.leb (rk + Z.of_nat n) (kk + (zmod64 l0))
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else if Z.leb (kk + (zmod64 l0)) rk then know_lookup segs rest rb rk n sx hints acc
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
  : option (expr * list sidecond * scripts * N) :=
  match log_lookupB bc (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
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
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', N.succ i)
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
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod two64)) [] scr
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
  | [], S _ => know_lookupA0B bc segs (kx_select kx rb rk) rb rk n sx [] acc
  | _, _ => know_lookupA0B bc segs (kx_kn kx) rb rk n sx hints acc
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
  induction x; cbn -[Z.eqb Nat.eqb N.eqb]; rewrite ?N.eqb_refl, ?kx_aluop_eqb_refl, ?kx_mulop_eqb_refl, ?IHx, ?IHx1, ?IHx2, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
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
  cbn [know_lookupA0B]. rewrite ?zmod64_eqf; cbv beta. unfold two64.   (* [comment removed for export] *)
  unfold kx_cand0, kx_wide0 in HC.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len|pt prs pargs pk];
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
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len|pt prs pargs pk];
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
    destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len|pt prs pargs pk]; try reflexivity.
  - rewrite know_lookupA0B_skip0 by exact HC. apply IH.
Qed.
Lemma know_lookupA0B_filterf : forall bc segs l rb rk n sx acc,
  is_lit0 rb = false ->
  know_lookupA0B bc segs (List.filter kx_candf l) rb rk n sx [] acc = know_lookupA0B bc segs l rb rk n sx [] acc.
Proof.
  intros bc segs l rb rk n sx acc Hrb. revert acc. induction l as [|K rest IH]; intros acc; [reflexivity|].
  cbn [List.filter]. destruct (kx_candf K) eqn:HC.
  - cbn [know_lookupA0B]. rewrite !IH.
    destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len|pt prs pargs pk]; try reflexivity.
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
  intros bc kn segs rb rk n sx hints acc. unfold know_lookupA0I.
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

(* [comment removed for export] *)
Definition ranges_apartBr (bc : bctx) (br1 : option (Z * Z)) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match br1, base_rangeB bc b2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
      | _, _ => false
      end) then true
  else if kdisj_apartBX bc (bc_kd bc) (ekeys b1 []) (ekeys b2 []) b1 k1 n1 b2 k2 n2 then true   (* [comment removed for export] *)
  else if lin_apartB bc b1 k1 n1 b2 k2 n2 then true
  else lin_apart2B bc b1 k1 n1 b2 k2 n2.
Lemma ranges_apartBr_eq : forall bc b1 k1 n1 b2 k2 n2,
  ranges_apartBr bc (base_rangeB bc b1) b1 k1 n1 b2 k2 n2 = ranges_apartB bc b1 k1 n1 b2 k2 n2.
Proof. reflexivity. Qed.
Fixpoint log_lookupBL (bc : bctx) (obr : option (option (Z * Z))) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupBL bc obr rest rb rk n sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          let br := match obr with Some r => r | None => base_rangeB bc rb end in
          if ranges_apartBr bc br rb rk (Z.of_nat n) kb kk (Z.of_nat w)
          then log_lookupBL bc (Some br) rest rb rk n sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupBL bc (Some br) rest rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
          end
      end
  end.
Lemma log_lookupBL_eq : forall bc log rb rk n sx hints acc obr,
  match obr with Some r => r = base_rangeB bc rb | None => True end ->
  log_lookupBL bc obr log rb rk n sx hints acc = log_lookupB bc log rb rk n sx hints acc.
Proof.
  intros bc log rb rk n sx. induction log as [|[[kb kk] w v] rest IH]; intros hints acc obr Hobr; [reflexivity|].
  cbn [log_lookupBL log_lookupB].
  destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)); try reflexivity; [apply IH; exact Hobr|].
  assert (Hbr : (match obr with Some r => r | None => base_rangeB bc rb end) = base_rangeB bc rb) by (destruct obr; [exact Hobr | reflexivity]).
  cbv zeta. rewrite Hbr, ranges_apartBr_eq.
  destruct (ranges_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w)); [apply IH; reflexivity|].
  destruct hints as [|[|] hs]; try reflexivity; apply IH; reflexivity.
Qed.

Definition sym_readBI (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * N) :=
  match log_lookupBL bc None (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with   (* [comment removed for export] *)
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
          Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', N.succ i)
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
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod two64)) [] scr
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
Proof. intros. bcfe. unfold sym_readBI, sym_readB. rewrite know_lookupABI_eq. rewrite log_lookupBL_eq by exact I. reflexivity. Qed.
Lemma sym_stepBI_eq : forall bc segs i ss scr,
  sym_stepBI bc (mk_kix (s_know ss)) segs i ss scr = sym_stepB bc segs i ss scr.
Proof. intros. unfold sym_stepBI, sym_stepB. rewrite sym_readBI_eqf. reflexivity. Qed.

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
Lemma mkSrl_partB_eqf : forall fk, mkSrl_partB (mkbc fk) = mkSrl_part fk.
Proof. intros. bcfe. unfold mkSrl_partB, mkSrl_part. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkSrl_partB_eqf : bceq.
Lemma mkSrlNB_eqf : forall f fk, mkSrlNB f (mkbc fk) = mkSrlN f fk.
Proof. induction f as [|f IH]; intros; bcfe; cbn [mkSrlNB mkSrlN]; autorewrite with bceq; rewrite ?IH; reflexivity. Qed.
#[export] Hint Rewrite mkSrlNB_eqf : bceq.
Lemma mkSrlB_eqf : forall fk, mkSrlB (mkbc fk) = mkSrl fk.
Proof. intros. bcfe. unfold mkSrlB, mkSrl. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkSrlB_eqf : bceq.
Lemma lowbitsB_eqf : forall fk, lowbitsB (mkbc fk) = lowbits fk.
Proof.
  intros fk. apply functional_extensionality; intros e.
  induction e; bcfe; cbn [lowbitsB lowbits]; rewrite ?IHe1, ?IHe2, ?IHe; autorewrite with bceq; rewrite ?zmod64_eqf; cbv beta; reflexivity.
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
Proof. intros. bcfe. unfold mkAnd0B, mkAnd0. autorewrite with bceq. rewrite ?zmod64_eqf; cbv beta. reflexivity. Qed.
#[export] Hint Rewrite mkAnd0B_eqf : bceq.
Lemma mkAndB_eqf : forall fk, mkAndB (mkbc fk) = mkAnd fk.
Proof. intros. bcfe. unfold mkAndB, mkAnd. autorewrite with bceq. rewrite ?zmod64_eqf; cbv beta. reflexivity. Qed.
#[export] Hint Rewrite mkAndB_eqf : bceq.
Lemma mkAndKB_eqf : forall fk, mkAndKB (mkbc fk) = mkAndK fk.
Proof. intros. bcfe. unfold mkAndKB, mkAndK. autorewrite with bceq. rewrite ?zmod64_eqf; cbv beta. reflexivity. Qed.
#[export] Hint Rewrite mkAndKB_eqf : bceq.
Lemma or_disjointB_eqf : forall fk, or_disjointB (mkbc fk) = or_disjoint fk.
Proof. intros. bcfe. unfold or_disjointB, or_disjoint. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite or_disjointB_eqf : bceq.
Lemma mkOrB_eqf : forall fk, mkOrB (mkbc fk) = mkOr fk.
Proof. intros. bcfe. unfold mkOrB, mkOr. autorewrite with bceq. rewrite ?zmod64_eqf; cbv beta. reflexivity. Qed.
#[export] Hint Rewrite mkOrB_eqf : bceq.
Lemma conc_tryB_eqf : forall fk, conc_tryB (mkbc fk) = conc_try fk.
Proof.
  intros fk. apply functional_extensionality; intros e. apply functional_extensionality; intros cands. 
  induction cands as [|s rest IH]; intros; bcfe; [reflexivity|].
  cbn [conc_tryB conc_try]. rewrite IH, all_eval_toD_eqf, all_eval_toT_eqf. autorewrite with bceq. reflexivity.
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
Lemma apart_branchB_eqf : forall fk, apart_branchB (mkbc fk) = apart_branch fk.
Proof. intros. bcfe. unfold apart_branchB, apart_branch. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite apart_branchB_eqf : bceq.
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
  cbn [know_lookupA0B know_lookupA0]. rewrite IH. autorewrite with bceq. rewrite ?zmod64_eqf; cbv beta. reflexivity.   (* [comment removed for export] *)
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
   | ELit l0 => match rel_lit rb rk (Z.of_nat n) kb kk (zmod64 l0) with RInside _ => true | _ => false end
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

Definition x_dischargeableB (bc : bctx) (ss ss' : sym_state) (rb : option (saddr * nat * bool)) (sc : sidecond) : bool :=
  let kn := s_know ss in
  match sc with
  | SCReadBase a n sx (EVar j) =>
      (match rb with
       | Some (a', n', sx') => saddr_eqb a' a && Nat.eqb n' n && Bool.eqb sx' sx
       | None => false
       end)
      && N.eqb j (s_next ss) && N.ltb j (s_next ss') && evars_lt (s_next ss) (a_base a)
      && Nat.leb 1 n && Nat.leb n 8 && kn_readable segs (bc_fk bc) kn (a_base a) (a_off a) n
  | SCFlat a (ELit z) =>
      Z.leb 1 z && Z.leb z 8 && kn_readable segs (bc_fk bc) kn (a_base a) (a_off a) (Z.to_nat z)
  | SCStoreOk a n => Nat.leb 1 n && Nat.leb n 8 && kn_overlay segs (bc_fk bc) kn (a_base a) (a_off a) n
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
      if N.leb (s_next ss) (s_next ss')            (* [comment removed for export] *)
      then SOk (cap_rd K i ss') (x_filterB bc ss ss' scs) scr'
      else SStop
  | SStop => SStop
  end.


Lemma zf_coversB_eqf : forall fk, zf_coversB (mkbc fk) = zf_covers fk.
Proof. intros. bcfe. unfold zf_coversB, zf_covers. autorewrite with bceq. rewrite ?zmod64_eqf; cbv beta. reflexivity. Qed.
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
  destruct (N.leb (s_next ss) (s_next ss1)); [|discriminate]. injection H as <- _ _.
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
      if N.leb (s_next ss) (s_next ss')
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
         let ha := if (if lin_ge0B bc [(hb, ho)] [(wb, wk); (wn, 0%Z)] then lin_ge0B bc [(wb, wk); (wn, 0%Z)] [(hb, ho)] else false)   (* [comment removed for export] *)
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

Definition priv_apart_pB (bc : bctx) (sp : sprep) (wb : expr) (wk : Z) (wn : expr) (rs : list (saddr * expr)) : bool :=
  forallb (fun r : saddr * expr => ranges_apart_pB bc sp wb wk wn (a_base (fst r)) (a_off (fst r)) (snd r)) rs.

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
  | KPriv _ rs _ _ => if priv_apart_pB bc sp (a_base wa) k (elen w) rs then ([K], [], hints) else ([], [], hints)   (* [comment removed for export] *)
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
            let l := (zmod64 l0) in
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
      else if lin_apartB bc b1 k1 m1 b2 k2 m2 then true
      else lin_apart2B bc b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match sp_rng sp, br2, sp_h1 sp, xhiB bc n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else  
            if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_xB bc (sp_Dx sp) b2 k2 n2 then true
    else if apart_gate b1 b2 then false   (* [comment removed for export] *)
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
  | KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ | KImg _ _ | KPriv _ _ _ _ => prune1pB bc sp wa w wv K hints
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
Lemma priv_apart_pB_eqf : forall fk, priv_apart_pB (mkbc fk) = priv_apart_p fk.
Proof. intros. bcfe. unfold priv_apart_pB, priv_apart_p. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite priv_apart_pB_eqf : bceq.
Lemma prune1pB_eqf : forall fk, prune1pB (mkbc fk) = prune1p fk.
Proof. intros. bcfe. unfold prune1pB, prune1p. autorewrite with bceq. rewrite ?zmod64_eqf; cbv beta. reflexivity. Qed.
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
  intros. unfold kword_cut.
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
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|[kb kk] n|a1 n1 a2 n2|[kb kk] len c|[kb kk] len|pt prs pargs pk]; cbn [List.filter is_factb];
    try reflexivity;
    try (apply prune_zf_nofacts; [reflexivity|reflexivity|]); nfcrush.
Qed.

Lemma prune1pc_facts : forall allkn sp wa w wv K hints br2,
  List.filter is_factb (fst (fst (prune1pc allkn sp wa w wv K hints br2))) = List.filter is_factb [K].
Proof.
  intros allkn sp wa w wv K hints br2. unfold prune1pc.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|[kb kk] n|a1 n1 a2 n2|[kb kk] len c|[kb kk] len|pt prs pargs pk];
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
  induction x; cbn -[Z.eqb Nat.eqb N.eqb]; rewrite ?N.eqb_refl, ?p_aluop_eqb_refl, ?p_mulop_eqb_refl, ?IHx, ?IHx1, ?IHx2, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
Qed.
Lemma p_prune1pc_eq : forall allkn sp wa w wv K hints br2,
  match kbase K with Some kb => br2 = base_range allkn kb | None => True end ->
  prune1pc allkn sp wa w wv K hints br2 = prune1p allkn sp wa w wv K hints.
Proof.
  intros allkn sp wa w wv K hints br2 Hb.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len|pt prs pargs pk];
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
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len|pt prs pargs pk]; pk_crush.
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
      | _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl (kcutB bc mk wb k (elen w) kb kk len)
      end
    else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk len then PKeep
    else match kcutB bc mk wb k (elen w) kb kk len with
         | [] => if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk len then PKeep else PRepl []
         | cut => PRepl cut
         end in
  match K with
  | KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ => PKeep
  | KPriv _ rs _ _ => if priv_apart_pB bc sp wb k (elen w) rs then PKeep else PRepl []   (* [comment removed for export] *)
  | KImg lo hi =>
      match wb with
      | ELit 0 =>
          let r1 := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
          let lo2 := Z.max lo (k + Z.of_nat w) in
          let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
          PRepl (r1 ++ r2)
      | _ => if Z.ltb (hi - lo) two64 then
               (if ranges_apart_pB bc sp wb k (elen w) (ELit 0) lo (ELit (hi - lo)) then PKeep else PRepl [])
             else PRepl []
      end
  | KZero (SA kb kk) len => zfK KZero kb kk len
  | KFill (SA kb kk) len c => zfK (fun a n => KFill a n c) kb kk len
  | KUnk (SA kb kk) len => zfK KUnk kb kk len
  | KWord (SA kb kk) w' v =>
      if same then (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool then PKeep else PRepl (kword_cut kb kk w' v k w))
      else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk (elen w') then PKeep
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool then PKeep
      else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk (elen w') then PKeep else PRepl []
  | KBlob (SA kb kk) len bk =>
      if same then
        match len with
        | ELit l0 => let l := (zmod64 l0) in
                     if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool then PKeep else PRepl []
        | _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl []
        end
      else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk len then PKeep else PRepl []
  end.

Lemma prune1pcK_eq : forall fk sp wa w wv K br2 same,
  (match kbase K with Some kb => same = expr_eqb kb (a_base wa) | None => True end) ->
  pk_list K (prune1pcK (mkbc fk) sp wa w wv K same br2) = fst (fst (prune1pc fk sp wa w wv K [] br2)).
Proof.
  intros fk sp wa w wv K br2 same H.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len|pt prs pargs pk];
    cbn [kbase] in H; try subst same; unfold prune1pcK, prune1pc, prune1p, prune_zf, kzero_cut, kfill_cut, kunk_cut;
    autorewrite with bceq; rewrite ?zmod64_eqf; cbv beta; cbn [a_base a_off]; try unfold two64; pk_crush.   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
Definition bkey (e : expr) : option N := first_var e.
Record binfo := BI { bi_base : expr; bi_br : option (Z * Z) }.
Record ntab := NT { nt_vars : ptree (list (expr * positive)); nt_other : list (expr * positive); nt_next : positive; nt_info : ptree binfo }.   (* [comment removed for export] *)
Definition nt_empty : ntab := NT PTLeaf [] xH PTLeaf.
Fixpoint alookupE (l : list (expr * positive)) (b : expr) : option positive :=
  match l with
  | [] => None
  | (b', id) :: rest => if expr_eqb b b' then Some id else alookupE rest b
  end.
Definition nt_bucket (t : ntab) (k : option N) : list (expr * positive) :=
  match k with Some n => lget2 (nt_vars t) n | None => nt_other t end.
Definition nt_add (t : ntab) (k : option N) (p : expr * positive) (bi : binfo) : ntab :=
  match k with
  | Some n => NT (lset2 (nt_vars t) n p) (nt_other t) (Pos.succ (nt_next t)) (pt_set (nt_next t) bi (nt_info t))
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
Proof. intros [n|]; cbn [nt_bucket nt_empty nt_vars nt_other]; [apply lget2_leaf | reflexivity]. Qed.
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
  intros t [n|] p bi [m|]; cbn [nt_add nt_bucket nt_vars nt_other okey_eqb]; try reflexivity. apply lget2_lset2.
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
      match prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
      | PKeep => chainK bc rest K same_of br2
      | PRepl l => chain_slow bc rest l
      end
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
Lemma chainK_eq : forall fk sxs K same_of br2,
  Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))) sxs ->
  match kbase K with
  | Some kb => br2 = base_rangeB (mkbc fk) kb /\ Forall (fun sx => same_of (sx_bid sx) = expr_eqb kb (a_base (sx_a sx))) sxs
  | None => br2 = None
  end ->
  chainK (mkbc fk) sxs K same_of br2 = chain_slow (mkbc fk) sxs [K].
Proof.
  intros fk sxs. induction sxs as [|sx rest IH]; intros K same_of br2 HS HK; [reflexivity|].
  apply Forall_cons_iff in HS as [H1 HS]. cbn [chainK chain_slow flat_map]. rewrite app_nil_r.
  unfold g1cB at 1.
  assert (E : pk_list K (prune1pcK (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2)
              = fst (fst (prune1pcB (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K [] (obrB (mkbc fk) K)))).
  { autorewrite with bceq. destruct (kbase K) as [kb|] eqn:HB.
    - destruct HK as [-> HK]. apply Forall_cons_iff in HK as [HK1 HK].
      unfold obrB. rewrite HB. apply prune1pcK_eq. rewrite HB. exact HK1.
    - unfold obrB. rewrite HB. subst br2. apply prune1pcK_eq. rewrite HB. exact I. }
  destruct (prune1pcK _ _ _ _ _ K _ br2) as [|l]; cbn [pk_list] in E.
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
  | KImg lo hi => Some (ELit 0%Z, lo, if Z.ltb (hi - lo) two64 then Some (zlit64 (hi - lo)) else None)
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
                             | Some m => let '(gid, gs0) := ggroup gs bid (if is_lit0 kb then (kk * 256)%Z else kk) in (gid, bnd_add gs0 gid bid (bi_br bi) kk (kk + m)%Z)   (* [comment removed for export] *)
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
(* [comment removed for export] *)
Definition side_cov (bc : bctx) (D : list (saddr * expr)) (gb : expr) (glo ghi : Z) : bool :=
  existsb (fun cm => if (expr_eqb gb (a_base (fst cm)) && Z.leb (a_off (fst cm)) glo)%bool then
                       match xloB bc (snd cm) with Some ml => Z.leb ghi (a_off (fst cm) + ml) | None => false end
                     else false) D.
(* [comment removed for export] *)
Definition side_cov_num (bc : bctx) (D : list (saddr * expr)) (obr : option (Z * Z)) (glo ghi : Z) : bool :=
  match obr with
  | Some (lo1, hi1) =>
      existsb (fun cm => if novars (a_base (fst cm)) then
                           match xloB bc (a_base (fst cm)), xhiB bc (a_base (fst cm)), xloB bc (snd cm) with
                           | Some lo2, Some hi2, Some l2 =>
                               (Z.eqb lo2 hi2 && Z.leb (lo2 + a_off (fst cm)) (lo1 + glo) && Z.leb (hi1 + ghi) (lo2 + a_off (fst cm) + l2))%bool
                           | _, _, _ => false
                           end
                         else false) D
  | None => false
  end.
Definition verdict2 (bc : bctx) (t : ntab) (sx : stx) (g : gval) : bool :=
  if verdict sx g then true else
  match g with
  | (b, obr, (glo, ghi)) =>
      if Pos.eqb b (sx_bid sx) then false else
      if side_cov_num bc (sp_D (sx_sp sx)) obr glo ghi then true else   (* [comment removed for export] *)
      match pt_get (nt_info t) b with
      | Some bi => side_cov bc (sp_D (sx_sp sx)) (bi_base bi) glo ghi
      | None => false
      end
  end.
Fixpoint mk_fl2 (bc : bctx) (t : ntab) (g : gval) (sxs : list stx) : list (stx * list stx) :=
  match sxs with
  | [] => []
  | sx :: rest => if verdict2 bc t sx g then mk_fl2 bc t g rest else (sx, rest) :: mk_fl2 bc t g rest
  end.
Definition mk_gl2 (bc : bctx) (t : ntab) (bnds : gtab) (sxs : list stx) : ptree gfl := pt_map (fun g => (g, mk_fl2 bc t g sxs)) bnds.

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

(* [comment removed for export] *)
Section LbB.
Local Open Scope Z_scope.
(* [comment removed for export] *)
Definition ochk (c : Z) (o : option Z) : bool := match o with Some L => Z.leb 0 (c + L) | None => false end.
Definition omax (a b : option Z) : option Z :=
  match a, b with Some x, Some y => Some (Z.max x y) | Some x, None => Some x | None, y => y end.
Definition omaxl (l : list (option Z)) : option Z := fold_right omax None l.
Definition oshift (d : Z) (o : option Z) : option Z := match o with Some L => Some (L + d) | None => None end.
Definition t0 : Z -> Z -> bool := fun lo _ => Z.leb 0 lo.

Definition lb_plain (er : expr -> option (Z * Z)) (ts : list (Z * expr)) : option Z :=
  match lin_range er 0 ts with Some (lo, _) => Some lo | None => None end.
Definition lb_rel0 (er : expr -> option (Z * Z)) (fs : list sfact) (ts : list (Z * expr)) : option Z :=
  match fs with
  | [] => None
  | _ => match sum_subst fs ts 0 0 false with
         | (ts', (lo0, hi0), true) => match lin_range er 0 ts' with Some (lo, _) => Some (lo + lo0) | None => None end
         | _ => None
         end
  end.
Definition lb_q1 (er : expr -> option (Z * Z)) (ts : list (Z * expr)) (f : sfact) (q : Z) : option Z :=
  match lin_range er 0 (sub_fact q (fst f) ts) with
  | Some (lo, hi) => Some (if Z.leb 0 q then lo + q * fst (snd f) else lo + q * snd (snd f))
  | None => None
  end.
Definition lb_relq (er : expr -> option (Z * Z)) (fs : list sfact) (ts : list (Z * expr)) : option Z :=
  omaxl (map (fun f => omaxl (map (lb_q1 er ts f) (nodup Z.eq_dec (fact_quots (fst f) ts)))) fs).
Definition lb_relB (bc : bctx) (ts : list (Z * expr)) : option Z :=
  let tsk := ts_keys ts in
  let fs := List.map fst (List.filter (fun p => relk tsk (snd p)) (bc_fsk bc)) in
  let fsP := List.flat_map (project_fact (erangeB bc) ts) fs in
  omax (lb_rel0 (erangeB bc) fs ts)
   (omax (lb_rel0 (erangeB bc) (fs ++ fsP) ts)
    (omax (lb_rel0 (erangeB bc) fsP ts)
     (omax (omaxl (map (fun f => lb_rel0 (erangeB bc) [f] ts) fsP))
           (lb_relq (erangeB bc) (fs ++ fsP) ts)))).
Definition lb_testB (bc : bctx) (ts : list (Z * expr)) : option Z := omax (lb_plain (erangeB bc) ts) (lb_relB bc ts).
Definition lb_scaledB (bc : bctx) (ts : list (Z * expr)) : option Z :=
  let j := srl_scale_need ts in
  if (if Z.ltb 0 j then Z.leb j 24 else false) then
    let sc := (2 ^ j)%Z in
    let ts' := List.map (fun t => ((sc * fst t)%Z, snd t)) ts in
    let '(c2, t2) := srl_expandB bc ts' in
    let '(c3, t3) := (if has_srl t2 then srl_expandB bc t2 else (0%Z, t2)) in
    match lb_testB bc t3 with Some L => Some ((c2 + c3 + L) / sc) | None => None end
  else None.
Definition lb_ge0B (bc : bctx) (T : list (Z * expr)) : option Z :=
  let '(c2, t2) := srl_expandB bc T in
  omax (lb_testB bc T)
   (omax (oshift c2 (lb_testB bc t2))
    (omax (if has_srl t2 then let '(c3, t3) := srl_expandB bc t2 in oshift (c2 + c3) (lb_testB bc t3) else None)
          (lb_scaledB bc T))).

(* [comment removed for export] *)
Lemma lb_existsb_map : forall {A B : Type} (f : B -> bool) (g : A -> B) (l : list A), existsb f (map g l) = existsb (fun x => f (g x)) l.
Proof. intros A B f g l. induction l as [|x l IH]; [reflexivity|]. cbn [map existsb]. rewrite IH. reflexivity. Qed.
Lemma lb_existsb_ext : forall {T : Type} (f g : T -> bool) (l : list T), (forall x, f x = g x) -> existsb f l = existsb g l.
Proof. intros T f g l H. induction l as [|x l IH]; [reflexivity|]. cbn [existsb]. rewrite H, IH. reflexivity. Qed.
Lemma lin_range_shift : forall er c ts,
  lin_range er c ts = match lin_range er 0 ts with Some (lo, hi) => Some (c + lo, c + hi) | None => None end.
Proof.
  intros er c ts. induction ts as [|[k a] rest IH]; cbn [lin_range].
  - f_equal. f_equal; lia.
  - rewrite IH. destruct (er a) as [[al ah]|]; [|reflexivity].
    destruct (lin_range er 0 rest) as [[lo hi]|]; [|reflexivity].
    destruct (Z.leb 0 k); f_equal; f_equal; lia.
Qed.
Lemma ochk_omax : forall c a b, ochk c (omax a b) = (ochk c a || ochk c b)%bool.
Proof.
  intros c [x|] [y|]; unfold omax, ochk; cbv beta iota; try reflexivity; [|now rewrite orb_false_r].
  destruct (Z.leb_spec 0 (c + x)), (Z.leb_spec 0 (c + y)), (Z.leb_spec 0 (c + Z.max x y)); cbn [orb]; try reflexivity; lia.
Qed.
Lemma ochk_omaxl : forall c l, ochk c (omaxl l) = existsb (ochk c) l.
Proof. intros c l. induction l as [|o l IH]; [reflexivity|]. cbn [omaxl fold_right existsb]. fold (omaxl l). rewrite ochk_omax, IH. reflexivity. Qed.
Lemma ochk_oshift : forall c d o, ochk c (oshift d o) = ochk (c + d) o.
Proof. intros c d [L|]; unfold oshift, ochk; cbv beta iota; [|reflexivity]. replace (c + (L + d)) with (c + d + L) by lia. reflexivity. Qed.
Lemma lin_test_rel0_lb : forall er fs c ts, lin_test_rel0 er fs c ts t0 = ochk c (lb_rel0 er fs ts).
Proof.
  intros er fs c ts. unfold lin_test_rel0, lb_rel0. destruct fs as [|f fs]; [reflexivity|].
  destruct (sum_subst (f :: fs) ts 0 0 false) as [[ts' [lo0 hi0]] hit]. destruct hit; [|reflexivity].
  rewrite lin_range_shift. destruct (lin_range er 0 ts') as [[lo hi]|]; [|reflexivity].
  unfold ochk, t0. cbv beta iota. rewrite Z.add_assoc. reflexivity.
Qed.
Lemma lin_test_q1_lb : forall er c ts f q, lin_test_q1 er c ts t0 f q = ochk c (lb_q1 er ts f q).
Proof.
  intros er c ts f q. unfold lin_test_q1, lb_q1. rewrite lin_range_shift.
  destruct (lin_range er 0 (sub_fact q (fst f) ts)) as [[lo hi]|]; [|reflexivity].
  unfold ochk, t0. cbv beta iota. destruct (Z.leb 0 q); rewrite Z.add_assoc; reflexivity.
Qed.
Lemma lin_test_relq_lb : forall er fs c ts, lin_test_relq er fs c ts t0 = ochk c (lb_relq er fs ts).
Proof.
  intros er fs c ts. unfold lin_test_relq, lb_relq. rewrite ochk_omaxl, lb_existsb_map.
  apply lb_existsb_ext. intros f. rewrite ochk_omaxl, lb_existsb_map. apply lb_existsb_ext. intros q. apply lin_test_q1_lb.
Qed.
Lemma if_orb : forall (b x : bool), (if b then true else x) = (b || x)%bool.
Proof. intros [] x; reflexivity. Qed.
Lemma lin_test_relB_lb : forall bc c ts, lin_test_relB bc c ts t0 = ochk c (lb_relB bc ts).
Proof.
  intros bc c ts. unfold lin_test_relB, lb_relB. cbv zeta.
  rewrite !lin_test_rel0_lb, lin_test_relq_lb.
  rewrite (lb_existsb_ext (fun f => lin_test_rel0 (erangeB bc) [f] c ts t0) (fun f => ochk c (lb_rel0 (erangeB bc) [f] ts)))
    by (intros f; apply lin_test_rel0_lb).
  rewrite !ochk_omax, ochk_omaxl, lb_existsb_map, !if_orb. reflexivity.
Qed.
Lemma lin_testB_lb : forall bc c ts, lin_testB bc c ts t0 = ochk c (lb_testB bc ts).
Proof.
  intros bc c ts. unfold lin_testB, lb_testB. rewrite ochk_omax, lin_test_relB_lb. unfold lb_plain.
  rewrite lin_range_shift. destruct (lin_range (erangeB bc) 0 ts) as [[lo hi]|]; [|reflexivity].
  unfold t0, ochk. cbv beta iota. rewrite if_orb. reflexivity.
Qed.
Lemma ochk_div : forall c K sc, 0 < sc -> Z.leb 0 (sc * c + K) = ochk c (Some (K / sc)).
Proof.
  intros c K sc Hsc. unfold ochk. destruct (Z.leb_spec 0 (sc * c + K)), (Z.leb_spec 0 (c + K / sc)); try reflexivity.
  - exfalso. assert (H1 : - c <= K / sc) by (apply Z.div_le_lower_bound; lia). lia.
  - exfalso. pose proof (Z.mul_div_le K sc Hsc). nia.
Qed.
Lemma lin_ge0_scaledB_lb : forall bc c ts, lin_ge0_scaledB bc c ts = ochk c (lb_scaledB bc ts).
Proof.
  intros bc c ts. unfold lin_ge0_scaledB, lb_scaledB. cbv zeta.
  destruct (if Z.ltb 0 (srl_scale_need ts) then Z.leb (srl_scale_need ts) 24 else false) eqn:Hj; [|reflexivity].
  assert (Hsc : 0 < 2 ^ srl_scale_need ts).
  { apply Z.pow_pos_nonneg; [lia|]. destruct (Z.ltb_spec 0 (srl_scale_need ts)); [lia|discriminate]. }
  destruct (srl_expandB bc (map (fun t => (2 ^ srl_scale_need ts * fst t, snd t)) ts)) as [c2 t2].
  destruct (if has_srl t2 then srl_expandB bc t2 else (0, t2)) as [c3 t3].
  change (lin_testB bc (2 ^ srl_scale_need ts * c + c2 + c3) t3 (fun lo _ => 0 <=? lo)) with (lin_testB bc (2 ^ srl_scale_need ts * c + c2 + c3) t3 t0).
  rewrite lin_testB_lb. destruct (lb_testB bc t3) as [L|]; [|reflexivity].
  unfold ochk at 1. rewrite <- (ochk_div c (c2 + c3 + L) _ Hsc). f_equal. lia.
Qed.
Lemma lin_ge0B_lb : forall bc pos neg,
  lin_ge0B bc pos neg = (xt_nowrapB bc pos && xt_nowrapB bc neg
                         && ochk (xt_const pos - xt_const neg) (lb_ge0B bc (lsub_e (xt_lin pos) (xt_lin neg))))%bool.
Proof.
  intros bc pos neg. unfold lin_ge0B, lb_ge0B.
  destruct (xt_nowrapB bc pos); [|reflexivity]. destruct (xt_nowrapB bc neg); [|reflexivity]. cbn [andb].
  set (C := xt_const pos - xt_const neg). set (T := lsub_e (xt_lin pos) (xt_lin neg)).
  change (lin_testB bc C T (fun lo _ => 0 <=? lo)) with (lin_testB bc C T t0). rewrite lin_testB_lb.
  destruct (srl_expandB bc T) as [c2 t2].
  change (lin_testB bc (C + c2) t2 (fun lo _ => 0 <=? lo)) with (lin_testB bc (C + c2) t2 t0). rewrite lin_testB_lb.
  rewrite lin_ge0_scaledB_lb.
  rewrite !ochk_omax, ochk_oshift, !if_orb. f_equal. f_equal.
  destruct (has_srl t2); [|reflexivity].
  destruct (srl_expandB bc t2) as [c3 t3].
  change (lin_testB bc (C + c2 + c3) t3 (fun lo _ => 0 <=? lo)) with (lin_testB bc (C + c2 + c3) t3 t0). rewrite lin_testB_lb.
  rewrite ochk_oshift. rewrite Z.add_assoc. reflexivity.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Record xpre := XP { xp_r1 : option (Z * Z); xp_r2 : option (Z * Z); xp_h2 : option Z;
                    xp_lo2 : option Z; xp_hi2 : option Z; xp_l2 : option Z;
                    xp_nw1 : bool; xp_L1 : option Z; xp_nwn2 : bool; xp_L2 : option Z }.
Definition compute_pre (bc : bctx) (b1 b2 n2 : expr) : xpre :=
  if shares_var b1 b2 then
    XP (base_rangeB bc b1) (base_rangeB bc b2) (xhiB bc n2) None None None
       (lin_nowrapRB bc b1 && lin_nowrapRB bc b2)%bool
       (lb_ge0B bc (lsub_e (xt_lin [(b1, 0)]) (xt_lin [(b2, 0)])))
       (lin_nowrapRB bc n2)
       (lb_ge0B bc (lsub_e (xt_lin [(b2, 0); (n2, 0)]) (xt_lin [(b1, 0)])))
  else XP None None None None None None false None false None.   (* [comment removed for export] *)
Definition xinside_refutedB_pre (b1 : expr) (k1 : Z) (b2 : expr) (k2 : Z) (p : xpre) : bool :=
  match xp_r1 p, xp_r2 p with
  | Some (lo1, hi1), Some (lo2, hi2) =>
      if Z.ltb (hi1 + k1) (lo2 + k2) then true
      else match xp_h2 p with Some h2 => Z.ltb (hi2 + k2 + h2) (lo1 + k1) | None => false end
  | _, _ => false
  end.
Definition xinside0B_pre (bc : bctx) (b1 : expr) (k1 z1 : Z) (b2 : expr) (k2 : Z) (n2 : expr) (p : xpre) : bool :=
  if xinside_refutedB_pre b1 k1 b2 k2 p then false
  else if (xp_nw1 p && ochk (fst (lin_of b1) + k1 - (fst (lin_of b2) + k2)) (xp_L1 p))%bool
  then (xp_nw1 p && xp_nwn2 p && lin_nowrapRB bc (ELit z1)
        && ochk (fst (lin_of b2) + k2 + fst (lin_of n2) - (fst (lin_of b1) + k1 + snorm z1)) (xp_L2 p))%bool
  else false.
Lemma ochk_ext : forall c1 c2 o, c1 = c2 -> ochk c1 o = ochk c2 o.
Proof. intros; subst; reflexivity. Qed.
Lemma xinside0B_pre_eq : forall bc b1 k1 z1 b2 k2 n2, shares_var b1 b2 = true ->
  xinside0B_pre bc b1 k1 z1 b2 k2 n2 (compute_pre bc b1 b2 n2) = xinside0B bc b1 k1 (ELit z1) b2 k2 n2.
Proof.
  intros bc b1 k1 z1 b2 k2 n2 Hs. unfold xinside0B_pre, xinside0B, compute_pre. rewrite Hs.
  change (xinside_refutedB_pre b1 k1 b2 k2 (XP (base_rangeB bc b1) (base_rangeB bc b2) (xhiB bc n2) None None None
            (lin_nowrapRB bc b1 && lin_nowrapRB bc b2)%bool (lb_ge0B bc (lsub_e (xt_lin [(b1, 0)]) (xt_lin [(b2, 0)])))
            (lin_nowrapRB bc n2) (lb_ge0B bc (lsub_e (xt_lin [(b2, 0); (n2, 0)]) (xt_lin [(b1, 0)])))))
    with (xinside_refutedB bc b1 k1 b2 k2 n2).
  cbn [xp_nw1 xp_L1 xp_nwn2 xp_L2].
  destruct (xinside_refutedB bc b1 k1 b2 k2 n2); [reflexivity|].
  rewrite !lin_ge0B_lb. cbn [xt_nowrapB xt_const xt_lin lin_of fold_right].
  rewrite (ochk_ext (fst (lin_of b1) + k1 + 0 - (fst (lin_of b2) + k2 + 0)) (fst (lin_of b1) + k1 - (fst (lin_of b2) + k2))) by lia.
  rewrite (ochk_ext (fst (lin_of b2) + k2 + (fst (lin_of n2) + 0 + 0) - (fst (lin_of b1) + k1 + (snorm z1 + 0 + 0)))
                    (fst (lin_of b2) + k2 + fst (lin_of n2) - (fst (lin_of b1) + k1 + snorm z1))) by lia.
  destruct (lin_nowrapRB bc b1), (lin_nowrapRB bc b2), (lin_nowrapRB bc n2), (lin_nowrapRB bc (ELit z1)); reflexivity.
Qed.


Definition xkey : Type := (expr * expr * expr)%type.
Fixpoint tlookup (tab : list (xkey * xpre)) (b1 b2 n2 : expr) : option xpre :=
  match tab with
  | [] => None
  | ((x, y, z), p) :: r => if (expr_eqb x b1 && expr_eqb y b2 && expr_eqb z n2)%bool then Some p else tlookup r b1 b2 n2
  end.
Definition table_ok (bc : bctx) (tab : list (xkey * xpre)) : Prop :=
  Forall (fun e : xkey * xpre => let '((x, y, z), p) := e in p = compute_pre bc x y z) tab.
Lemma tlookup_ok : forall bc tab b1 b2 n2 p, table_ok bc tab -> tlookup tab b1 b2 n2 = Some p -> p = compute_pre bc b1 b2 n2.
Proof.
  intros bc tab b1 b2 n2 p Hok. induction Hok as [|e tab Hq Hok IH]; intros H; [discriminate|].
  destruct e as [[[x y] z] q]. cbn [tlookup] in H.
  destruct (expr_eqb x b1 && expr_eqb y b2 && expr_eqb z n2)%bool eqn:He.
  - injection H as <-. apply andb_prop in He as [He H3]. apply andb_prop in He as [H1 H2].
    apply expr_eqb_eqB in H1. apply expr_eqb_eqB in H2. apply expr_eqb_eqB in H3. subst x y z. exact Hq.
  - exact (IH H).
Qed.
Definition xinsideB_t (bc : bctx) (tab : list (xkey * xpre)) (b1 : expr) (k1 z1 : Z) (b2 : expr) (k2 : Z) (n2 : expr)
  : bool * list (xkey * xpre) :=
  if shares_var b1 b2 then
    match tlookup tab b1 b2 n2 with
    | Some p => (xinside0B_pre bc b1 k1 z1 b2 k2 n2 p, tab)
    | None => let p := compute_pre bc b1 b2 n2 in (xinside0B_pre bc b1 k1 z1 b2 k2 n2 p, ((b1, b2, n2), p) :: tab)
    end
  else (xinsideB bc b1 k1 (ELit z1) b2 k2 n2, tab).   (* [comment removed for export] *)
Lemma xinsideB_t_eq : forall bc tab b1 k1 z1 b2 k2 n2, table_ok bc tab ->
  fst (xinsideB_t bc tab b1 k1 z1 b2 k2 n2) = xinsideB bc b1 k1 (ELit z1) b2 k2 n2
  /\ table_ok bc (snd (xinsideB_t bc tab b1 k1 z1 b2 k2 n2)).
Proof.
  intros bc tab b1 k1 z1 b2 k2 n2 Hok. unfold xinsideB_t. destruct (shares_var b1 b2) eqn:Hs; [|split; [reflexivity | exact Hok]].
  assert (X : xinsideB bc b1 k1 (ELit z1) b2 k2 n2 = xinside0B bc b1 k1 (ELit z1) b2 k2 n2) by (unfold xinsideB; rewrite Hs; reflexivity).
  destruct (tlookup tab b1 b2 n2) as [p|] eqn:Hl.
  - rewrite (tlookup_ok bc tab b1 b2 n2 p Hok Hl). cbn [fst snd]. rewrite xinside0B_pre_eq, X by exact Hs. split; [reflexivity | exact Hok].
  - cbv zeta. cbn [fst snd]. rewrite xinside0B_pre_eq, X by exact Hs. split; [reflexivity|]. constructor; [reflexivity | exact Hok].
Qed.
Definition sub_itvB_t (bc : bctx) (tab : list (xkey * xpre)) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool * list (xkey * xpre) :=
  if (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
        match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
      else false)
  then (true, tab)
  else if scale_clash b (a_base c) then (false, tab)
  else if (Z.leb 0 n && Z.ltb n two64)%bool then xinsideB_t bc tab b k n (a_base c) (a_off c) m else (false, tab).
Lemma sub_itvB_t_eq : forall bc tab b k n c m, table_ok bc tab ->
  fst (sub_itvB_t bc tab b k n c m) = sub_itvB bc b k n c m /\ table_ok bc (snd (sub_itvB_t bc tab b k n c m)).
Proof.
  intros bc tab b k n c m Hok. unfold sub_itvB_t, sub_itvB.
  destruct (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
              match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end else false);
    [split; [reflexivity | exact Hok]|].
  destruct (scale_clash b (a_base c)); [split; [reflexivity | exact Hok]|].
  destruct (Z.leb 0 n && Z.ltb n two64)%bool; [|split; [reflexivity | exact Hok]].
  exact (xinsideB_t_eq bc tab b k n (a_base c) (a_off c) m Hok).
Qed.
Fixpoint in_sidesB_t (bc : bctx) (tab : list (xkey * xpre)) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool * list (xkey * xpre) :=
  match D with
  | [] => (false, tab)
  | (c, m) :: r => let '(x, tab') := sub_itvB_t bc tab b2 k2 n2 c m in if x then (true, tab') else in_sidesB_t bc tab' r b2 k2 n2
  end.
Lemma in_sidesB_t_eq : forall bc D tab b2 k2 n2, table_ok bc tab ->
  fst (in_sidesB_t bc tab D b2 k2 n2) = in_sidesB bc D b2 k2 n2 /\ table_ok bc (snd (in_sidesB_t bc tab D b2 k2 n2)).
Proof.
  intros bc D. induction D as [|[c m] r IH]; intros tab b2 k2 n2 Hok; [split; [reflexivity | exact Hok]|].
  cbn [in_sidesB_t in_sidesB]. destruct (sub_itvB_t_eq bc tab b2 k2 n2 c m Hok) as [E1 O1].
  destruct (sub_itvB_t bc tab b2 k2 n2 c m) as [x tab'] eqn:Hx. cbn [fst snd] in E1, O1. rewrite <- E1.
  destruct x; [split; [reflexivity | exact O1]|]. exact (IH tab' b2 k2 n2 O1).
Qed.

(* [comment removed for export] *)
Definition sub_itv_xB_t (bc : bctx) (tab : list (xkey * xpre)) (b : expr) (k : Z) (n : expr) (c : saddr) (m : expr) : bool * list (xkey * xpre) :=
  if scale_clash b (a_base c) then (false, tab) else
  match n with
  | ELit z => xinsideB_t bc tab b k z (a_base c) (a_off c) m
  | _ => (xinsideB bc b k n (a_base c) (a_off c) m, tab)
  end.
Lemma sub_itv_xB_t_eq : forall bc tab b k n c m, table_ok bc tab ->
  fst (sub_itv_xB_t bc tab b k n c m) = sub_itv_xB bc b k n c m /\ table_ok bc (snd (sub_itv_xB_t bc tab b k n c m)).
Proof.
  intros bc tab b k n c m Hok. unfold sub_itv_xB_t, sub_itv_xB.
  destruct (scale_clash b (a_base c)); [split; [reflexivity | exact Hok]|].
  destruct n as [z| | | | | | |]; try (split; [reflexivity | exact Hok]).
  exact (xinsideB_t_eq bc tab b k z (a_base c) (a_off c) m Hok).
Qed.
(* [comment removed for export] *)
Fixpoint in_sides_xB_t (bc : bctx) (tab : list (xkey * xpre)) (D : list (saddr * expr)) (b2 : expr) (k2 : Z) (n2 : expr) : bool * list (xkey * xpre) :=
  match D with
  | [] => (false, tab)
  | (c, m) :: r => let '(x, tab') := sub_itv_xB_t bc tab b2 k2 n2 c m in if x then (true, tab') else in_sides_xB_t bc tab' r b2 k2 n2
  end.
Lemma in_sides_xB_t_eq : forall bc D tab b2 k2 n2, table_ok bc tab ->
  fst (in_sides_xB_t bc tab D b2 k2 n2) = in_sides_xB bc D b2 k2 n2 /\ table_ok bc (snd (in_sides_xB_t bc tab D b2 k2 n2)).
Proof.
  intros bc D. induction D as [|[c m] r IH]; intros tab b2 k2 n2 Hok; [split; [reflexivity | exact Hok]|].
  cbn [in_sides_xB_t in_sides_xB]. destruct (sub_itv_xB_t_eq bc tab b2 k2 n2 c m Hok) as [E1 O1].
  destruct (sub_itv_xB_t bc tab b2 k2 n2 c m) as [x tab'] eqn:Hx. cbn [fst snd] in E1, O1. rewrite <- E1.
  destruct x; [split; [reflexivity | exact O1]|]. exact (IH tab' b2 k2 n2 O1).
Qed.
Definition ranges_apart_pBt (bc : bctx) (sp : sprep) (tab : list (xkey * xpre)) (b1 : expr) (k1 : Z) (n1 : expr)
           (b2 : expr) (k2 : Z) (n2 : expr) : bool * list (xkey * xpre) :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, base_rangeB bc b2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then (true, tab)
      else let '(x, tab') := in_sidesB_t bc tab (sp_D sp) b2 k2 m2 in
           if x then (true, tab')
           else ((if lin_apartB bc b1 k1 m1 b2 k2 m2 then true else lin_apart2B bc b1 k1 m1 b2 k2 m2), tab')
  | _, _ =>
    if (match sp_rng sp, base_rangeB bc b2, sp_h1 sp, xhiB bc n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else
            if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then (true, tab)
    else let '(x, tab') := in_sides_xB_t bc tab (sp_Dx sp) b2 k2 n2 in
         if x then (true, tab')
         else ((if apart_gate b1 b2 then false
                else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
                else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]), tab')
  end.
Lemma ranges_apart_pBt_eq : forall bc sp tab b1 k1 n1 b2 k2 n2, table_ok bc tab ->
  fst (ranges_apart_pBt bc sp tab b1 k1 n1 b2 k2 n2) = ranges_apart_pB bc sp b1 k1 n1 b2 k2 n2
  /\ table_ok bc (snd (ranges_apart_pBt bc sp tab b1 k1 n1 b2 k2 n2)).
Proof.
  intros bc sp tab b1 k1 n1 b2 k2 n2 Hok. unfold ranges_apart_pBt, ranges_apart_pB.
  destruct n1 as [z1| | | | | | |], n2 as [z2| | | | | | |];
    try (lazymatch goal with
         | |- fst (if ?c then _ else _) = _ /\ _ => destruct c; [split; [reflexivity | exact Hok]|]
         end;
         lazymatch goal with
         | |- context [in_sides_xB_t bc tab ?D ?b ?k ?n] =>
             destruct (in_sides_xB_t_eq bc D tab b k n Hok) as [E O];
             destruct (in_sides_xB_t bc tab D b k n) as [x tab']; cbn [fst snd] in E, O; rewrite <- E;
             destruct x; (split; [reflexivity | exact O])
         end).
  cbv zeta.
  lazymatch goal with
  | |- fst (if ?c then _ else _) = _ /\ _ => destruct c; [split; [reflexivity | exact Hok]|]
  end.
  destruct (in_sidesB_t_eq bc (sp_D sp) tab b2 k2 (zlit64 z2) Hok) as [E O].
  destruct (in_sidesB_t bc tab (sp_D sp) b2 k2 (zlit64 z2)) as [x tab']. cbn [fst snd] in E, O. rewrite <- E.
  destruct x; (split; [reflexivity | exact O]).
Qed.
Fixpoint disj_sidesBXt (bc : bctx) (tab : list (xkey * xpre)) (ds : list kdx) (kb1 : list positive) (b1 : expr) (k1 n1 : Z)
  : list (saddr * expr) * list (xkey * xpre) :=
  match ds with
  | [] => ([], tab)
  | d :: rest =>
      let '(r, tab1) := disj_sidesBXt bc tab rest kb1 b1 k1 n1 in
      let '(x2, tab2) := if cand kb1 (kd_k2 d) (kd_l2 d) then sub_itvB_t bc tab1 b1 k1 n1 (kd_c2 d) (kd_m2 d) else (false, tab1) in
      let r1 := if x2 then (kd_c1 d, kd_m1 d) :: r else r in
      let '(x1, tab3) := if cand kb1 (kd_k1 d) (kd_l1 d) then sub_itvB_t bc tab2 b1 k1 n1 (kd_c1 d) (kd_m1 d) else (false, tab2) in
      (if x1 then (kd_c2 d, kd_m2 d) :: r1 else r1, tab3)
  end.
Lemma disj_sidesBXt_eq : forall bc ds tab kb1 b1 k1 n1, table_ok bc tab ->
  fst (disj_sidesBXt bc tab ds kb1 b1 k1 n1) = disj_sidesBX bc ds kb1 b1 k1 n1 /\ table_ok bc (snd (disj_sidesBXt bc tab ds kb1 b1 k1 n1)).
Proof.
  intros bc ds. induction ds as [|d rest IH]; intros tab kb1 b1 k1 n1 Hok; [split; [reflexivity | exact Hok]|].
  cbn [disj_sidesBXt disj_sidesBX].
  destruct (IH tab kb1 b1 k1 n1 Hok) as [E0 O0]. destruct (disj_sidesBXt bc tab rest kb1 b1 k1 n1) as [r tab1]. cbn [fst snd] in E0, O0.
  assert (S2 : exists tab2, table_ok bc tab2 /\
     (if cand kb1 (kd_k2 d) (kd_l2 d) then sub_itvB_t bc tab1 b1 k1 n1 (kd_c2 d) (kd_m2 d) else (false, tab1))
     = ((if cand kb1 (kd_k2 d) (kd_l2 d) then sub_itvB bc b1 k1 n1 (kd_c2 d) (kd_m2 d) else false), tab2)).
  { destruct (cand kb1 (kd_k2 d) (kd_l2 d)); [|exists tab1; split; [exact O0 | reflexivity]].
    destruct (sub_itvB_t_eq bc tab1 b1 k1 n1 (kd_c2 d) (kd_m2 d) O0) as [E O].
    destruct (sub_itvB_t bc tab1 b1 k1 n1 (kd_c2 d) (kd_m2 d)) as [x tab2]. cbn [fst snd] in E, O.
    exists tab2. split; [exact O | rewrite E; reflexivity]. }
  destruct S2 as (tab2 & O2 & E2). rewrite E2.
  assert (S1 : exists tab3, table_ok bc tab3 /\
     (if cand kb1 (kd_k1 d) (kd_l1 d) then sub_itvB_t bc tab2 b1 k1 n1 (kd_c1 d) (kd_m1 d) else (false, tab2))
     = ((if cand kb1 (kd_k1 d) (kd_l1 d) then sub_itvB bc b1 k1 n1 (kd_c1 d) (kd_m1 d) else false), tab3)).
  { destruct (cand kb1 (kd_k1 d) (kd_l1 d)); [|exists tab2; split; [exact O2 | reflexivity]].
    destruct (sub_itvB_t_eq bc tab2 b1 k1 n1 (kd_c1 d) (kd_m1 d) O2) as [E O].
    destruct (sub_itvB_t bc tab2 b1 k1 n1 (kd_c1 d) (kd_m1 d)) as [x tab3]. cbn [fst snd] in E, O.
    exists tab3. split; [exact O | rewrite E; reflexivity]. }
  destruct S1 as (tab3 & O3 & E3). rewrite E3. rewrite E0. split; [reflexivity | exact O3].
Qed.
Fixpoint disj_sides_xBXt (bc : bctx) (tab : list (xkey * xpre)) (ds : list kdx) (kb1 : list positive) (b1 : expr) (k1 : Z) (n1 : expr)
  : list (saddr * expr) * list (xkey * xpre) :=
  match ds with
  | [] => ([], tab)
  | d :: rest =>
      let '(r, tab1) := disj_sides_xBXt bc tab rest kb1 b1 k1 n1 in
      let '(x2, tab2) := if cand kb1 (kd_k2 d) (kd_l2 d) then sub_itv_xB_t bc tab1 b1 k1 n1 (kd_c2 d) (kd_m2 d) else (false, tab1) in
      let r1 := if x2 then (kd_c1 d, kd_m1 d) :: r else r in
      let '(x1, tab3) := if cand kb1 (kd_k1 d) (kd_l1 d) then sub_itv_xB_t bc tab2 b1 k1 n1 (kd_c1 d) (kd_m1 d) else (false, tab2) in
      (if x1 then (kd_c2 d, kd_m2 d) :: r1 else r1, tab3)
  end.
Lemma disj_sides_xBXt_eq : forall bc ds tab kb1 b1 k1 n1, table_ok bc tab ->
  fst (disj_sides_xBXt bc tab ds kb1 b1 k1 n1) = disj_sides_xBX bc ds kb1 b1 k1 n1 /\ table_ok bc (snd (disj_sides_xBXt bc tab ds kb1 b1 k1 n1)).
Proof.
  intros bc ds. induction ds as [|d rest IH]; intros tab kb1 b1 k1 n1 Hok; [split; [reflexivity | exact Hok]|].
  cbn [disj_sides_xBXt disj_sides_xBX].
  destruct (IH tab kb1 b1 k1 n1 Hok) as [E0 O0]. destruct (disj_sides_xBXt bc tab rest kb1 b1 k1 n1) as [r tab1]. cbn [fst snd] in E0, O0.
  assert (S2 : exists tab2, table_ok bc tab2 /\
     (if cand kb1 (kd_k2 d) (kd_l2 d) then sub_itv_xB_t bc tab1 b1 k1 n1 (kd_c2 d) (kd_m2 d) else (false, tab1))
     = ((if cand kb1 (kd_k2 d) (kd_l2 d) then sub_itv_xB bc b1 k1 n1 (kd_c2 d) (kd_m2 d) else false), tab2)).
  { destruct (cand kb1 (kd_k2 d) (kd_l2 d)); [|exists tab1; split; [exact O0 | reflexivity]].
    destruct (sub_itv_xB_t_eq bc tab1 b1 k1 n1 (kd_c2 d) (kd_m2 d) O0) as [E O].
    destruct (sub_itv_xB_t bc tab1 b1 k1 n1 (kd_c2 d) (kd_m2 d)) as [x tab2]. cbn [fst snd] in E, O.
    exists tab2. split; [exact O | rewrite E; reflexivity]. }
  destruct S2 as (tab2 & O2 & E2). rewrite E2.
  assert (S1 : exists tab3, table_ok bc tab3 /\
     (if cand kb1 (kd_k1 d) (kd_l1 d) then sub_itv_xB_t bc tab2 b1 k1 n1 (kd_c1 d) (kd_m1 d) else (false, tab2))
     = ((if cand kb1 (kd_k1 d) (kd_l1 d) then sub_itv_xB bc b1 k1 n1 (kd_c1 d) (kd_m1 d) else false), tab3)).
  { destruct (cand kb1 (kd_k1 d) (kd_l1 d)); [|exists tab2; split; [exact O2 | reflexivity]].
    destruct (sub_itv_xB_t_eq bc tab2 b1 k1 n1 (kd_c1 d) (kd_m1 d) O2) as [E O].
    destruct (sub_itv_xB_t bc tab2 b1 k1 n1 (kd_c1 d) (kd_m1 d)) as [x tab3]. cbn [fst snd] in E, O.
    exists tab3. split; [exact O | rewrite E; reflexivity]. }
  destruct S1 as (tab3 & O3 & E3). rewrite E3. rewrite E0. split; [reflexivity | exact O3].
Qed.
Definition mk_sprepBt (bc : bctx) (tab : list (xkey * xpre)) (b1 : expr) (k1 : Z) (n1 : expr) : sprep * list (xkey * xpre) :=
  let '(D, tab1) := match n1 with ELit z1 => disj_sidesBXt bc tab (bc_kd bc) (ekeys b1 []) b1 k1 (zlit64 z1) | _ => ([], tab) end in
  let '(Dx, tab2) := disj_sides_xBXt bc tab1 (bc_kd bc) (ekeys b1 []) b1 k1 n1 in
  (SPrep (base_rangeB bc b1) (xhiB bc n1) D Dx, tab2).
Lemma mk_sprepBt_eq : forall bc tab b1 k1 n1, table_ok bc tab ->
  fst (mk_sprepBt bc tab b1 k1 n1) = mk_sprepB bc b1 k1 n1 /\ table_ok bc (snd (mk_sprepBt bc tab b1 k1 n1)).
Proof.
  intros bc tab b1 k1 n1 Hok. unfold mk_sprepBt, mk_sprepB.
  assert (S1 : exists tab1, table_ok bc tab1 /\
     (match n1 with ELit z1 => disj_sidesBXt bc tab (bc_kd bc) (ekeys b1 []) b1 k1 (zlit64 z1) | _ => ([], tab) end)
     = ((match n1 with ELit z1 => disj_sidesBX bc (bc_kd bc) (ekeys b1 []) b1 k1 (zlit64 z1) | _ => [] end), tab1)).
  { destruct n1 as [z1| | | | | | |]; try (exists tab; split; [exact Hok | reflexivity]).
    destruct (disj_sidesBXt_eq bc (bc_kd bc) tab (ekeys b1 []) b1 k1 (zlit64 z1) Hok) as [E O].
    destruct (disj_sidesBXt bc tab (bc_kd bc) (ekeys b1 []) b1 k1 (zlit64 z1)) as [D tab1]. cbn [fst snd] in E, O.
    exists tab1. split; [exact O | rewrite E; reflexivity]. }
  destruct S1 as (tab1 & O1 & E1). rewrite E1.
  destruct (disj_sides_xBXt_eq bc (bc_kd bc) tab1 (ekeys b1 []) b1 k1 n1 O1) as [E O].
  destruct (disj_sides_xBXt bc tab1 (bc_kd bc) (ekeys b1 []) b1 k1 n1) as [Dx tab2]. cbn [fst snd] in E, O.
  rewrite E. split; [reflexivity | exact O].
Qed.
(* [comment removed for export] *)
Definition sub_itv_2t (bc : bctx) (tab : list (xkey * xpre)) (b : expr) (k z : Z) (c : saddr) (m : expr) : bool * bool * list (xkey * xpre) :=
  if scale_clash b (a_base c) then
    ((if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
        match xloB bc m with Some ml => Z.leb (k + z) (a_off c + ml) | None => false end
      else false), false, tab)
  else
    let '(x, tab') := xinsideB_t bc tab b k z (a_base c) (a_off c) m in
    ((if x then true else
      if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
        match xloB bc m with Some ml => Z.leb (k + z) (a_off c + ml) | None => false end
      else false), x, tab').
Lemma sub_itv_2t_eq : forall bc tab b k z c m, table_ok bc tab -> 0 <= z < two64 ->
  fst (fst (sub_itv_2t bc tab b k z c m)) = sub_itvB bc b k z c m
  /\ snd (fst (sub_itv_2t bc tab b k z c m)) = sub_itv_xB bc b k (ELit z) c m
  /\ table_ok bc (snd (sub_itv_2t bc tab b k z c m)).
Proof.
  intros bc tab b k z c m Hok Hz. unfold sub_itv_2t, sub_itvB, sub_itv_xB.
  set (F := if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
              match xloB bc m with Some ml => Z.leb (k + z) (a_off c + ml) | None => false end else false).
  destruct (scale_clash b (a_base c)) eqn:Hc.
  - cbn [fst snd]. split; [|split; [reflexivity | exact Hok]]. destruct F; reflexivity.
  - destruct (xinsideB_t_eq bc tab b k z (a_base c) (a_off c) m Hok) as [E O].
    destruct (xinsideB_t bc tab b k z (a_base c) (a_off c) m) as [x tab'] eqn:Hx. cbn [fst snd] in E, O |- *.
    replace (Z.leb 0 z && Z.ltb z two64)%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite <- E. split; [|split; [reflexivity | exact O]].
    destruct x, F; reflexivity.
Qed.
Fixpoint disj_sides_2t (bc : bctx) (tab : list (xkey * xpre)) (ds : list kdx) (kb1 : list positive) (b1 : expr) (k1 z1 : Z)
  : list (saddr * expr) * list (saddr * expr) * list (xkey * xpre) :=
  match ds with
  | [] => ([], [], tab)
  | d :: rest =>
      let '(r, rx, tab1) := disj_sides_2t bc tab rest kb1 b1 k1 z1 in
      let '(x2, x2x, tab2) := if cand kb1 (kd_k2 d) (kd_l2 d) then sub_itv_2t bc tab1 b1 k1 z1 (kd_c2 d) (kd_m2 d) else (false, false, tab1) in
      let r1 := if x2 then (kd_c1 d, kd_m1 d) :: r else r in
      let rx1 := if x2x then (kd_c1 d, kd_m1 d) :: rx else rx in
      let '(x1, x1x, tab3) := if cand kb1 (kd_k1 d) (kd_l1 d) then sub_itv_2t bc tab2 b1 k1 z1 (kd_c1 d) (kd_m1 d) else (false, false, tab2) in
      (if x1 then (kd_c2 d, kd_m2 d) :: r1 else r1, if x1x then (kd_c2 d, kd_m2 d) :: rx1 else rx1, tab3)
  end.
Lemma disj_sides_2t_eq : forall bc ds tab kb1 b1 k1 z1, table_ok bc tab -> 0 <= z1 < two64 ->
  fst (fst (disj_sides_2t bc tab ds kb1 b1 k1 z1)) = disj_sidesBX bc ds kb1 b1 k1 z1
  /\ snd (fst (disj_sides_2t bc tab ds kb1 b1 k1 z1)) = disj_sides_xBX bc ds kb1 b1 k1 (ELit z1)
  /\ table_ok bc (snd (disj_sides_2t bc tab ds kb1 b1 k1 z1)).
Proof.
  intros bc ds. induction ds as [|d rest IH]; intros tab kb1 b1 k1 z1 Hok Hz; [split; [reflexivity | split; [reflexivity | exact Hok]]|].
  cbn [disj_sides_2t disj_sidesBX disj_sides_xBX].
  destruct (IH tab kb1 b1 k1 z1 Hok Hz) as (E0 & Ex0 & O0).
  destruct (disj_sides_2t bc tab rest kb1 b1 k1 z1) as [[r rx] tab1]. cbn [fst snd] in E0, Ex0, O0.
  assert (S2 : exists tab2, table_ok bc tab2 /\
     (if cand kb1 (kd_k2 d) (kd_l2 d) then sub_itv_2t bc tab1 b1 k1 z1 (kd_c2 d) (kd_m2 d) else (false, false, tab1))
     = ((if cand kb1 (kd_k2 d) (kd_l2 d) then sub_itvB bc b1 k1 z1 (kd_c2 d) (kd_m2 d) else false),
        (if cand kb1 (kd_k2 d) (kd_l2 d) then sub_itv_xB bc b1 k1 (ELit z1) (kd_c2 d) (kd_m2 d) else false), tab2)).
  { destruct (cand kb1 (kd_k2 d) (kd_l2 d)); [|exists tab1; split; [exact O0 | reflexivity]].
    destruct (sub_itv_2t_eq bc tab1 b1 k1 z1 (kd_c2 d) (kd_m2 d) O0 Hz) as (E & Ex & O).
    destruct (sub_itv_2t bc tab1 b1 k1 z1 (kd_c2 d) (kd_m2 d)) as [[x xx] tab2]. cbn [fst snd] in E, Ex, O.
    exists tab2. split; [exact O | rewrite E, Ex; reflexivity]. }
  destruct S2 as (tab2 & O2 & E2). rewrite E2.
  assert (S1 : exists tab3, table_ok bc tab3 /\
     (if cand kb1 (kd_k1 d) (kd_l1 d) then sub_itv_2t bc tab2 b1 k1 z1 (kd_c1 d) (kd_m1 d) else (false, false, tab2))
     = ((if cand kb1 (kd_k1 d) (kd_l1 d) then sub_itvB bc b1 k1 z1 (kd_c1 d) (kd_m1 d) else false),
        (if cand kb1 (kd_k1 d) (kd_l1 d) then sub_itv_xB bc b1 k1 (ELit z1) (kd_c1 d) (kd_m1 d) else false), tab3)).
  { destruct (cand kb1 (kd_k1 d) (kd_l1 d)); [|exists tab2; split; [exact O2 | reflexivity]].
    destruct (sub_itv_2t_eq bc tab2 b1 k1 z1 (kd_c1 d) (kd_m1 d) O2 Hz) as (E & Ex & O).
    destruct (sub_itv_2t bc tab2 b1 k1 z1 (kd_c1 d) (kd_m1 d)) as [[x xx] tab3]. cbn [fst snd] in E, Ex, O.
    exists tab3. split; [exact O | rewrite E, Ex; reflexivity]. }
  destruct S1 as (tab3 & O3 & E3). rewrite E3. cbn [fst snd]. rewrite E0, Ex0. split; [reflexivity | split; [reflexivity | exact O3]].
Qed.
Definition mk_sprepBt2o (bc : bctx) (tab : list (xkey * xpre)) (b1 : expr) (k1 : Z) (n1 : expr) : sprep * list (xkey * xpre) :=
  match n1 with
  | ELit z1 =>
      if (Z.leb 0 z1 && Z.ltb z1 two64)%bool then
        let '(D, Dx, tab2) := disj_sides_2t bc tab (bc_kd bc) (ekeys b1 []) b1 k1 z1 in
        (SPrep (base_rangeB bc b1) (xhiB bc n1) D Dx, tab2)
      else mk_sprepBt bc tab b1 k1 n1
  | _ => mk_sprepBt bc tab b1 k1 n1
  end.
Lemma mk_sprepBt2o_eq : forall bc tab b1 k1 n1, table_ok bc tab ->
  fst (mk_sprepBt2o bc tab b1 k1 n1) = mk_sprepB bc b1 k1 n1 /\ table_ok bc (snd (mk_sprepBt2o bc tab b1 k1 n1)).
Proof.
  intros bc tab b1 k1 n1 Hok. unfold mk_sprepBt2o.
  destruct n1 as [z1| | | | | | |]; try exact (mk_sprepBt_eq bc tab _ k1 _ Hok).
  destruct (Z.leb 0 z1 && Z.ltb z1 two64)%bool eqn:Hz; [|exact (mk_sprepBt_eq bc tab b1 k1 (ELit z1) Hok)].
  apply andb_prop in Hz as [Hz1 Hz2]. apply Z.leb_le in Hz1. apply Z.ltb_lt in Hz2.
  destruct (disj_sides_2t_eq bc (bc_kd bc) tab (ekeys b1 []) b1 k1 z1 Hok (conj Hz1 Hz2)) as (E & Ex & O).
  destruct (disj_sides_2t bc tab (bc_kd bc) (ekeys b1 []) b1 k1 z1) as [[D Dx] tab2]. cbn [fst snd] in E, Ex, O |- *.
  split; [|exact O]. unfold mk_sprepB. rewrite E, Ex.
  replace (zlit64 z1) with z1; [reflexivity|].
  unfold zlit64. replace (Z.leb 0 z1 && Z.ltb z1 two64)%bool with true; [reflexivity|].
  symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
(* [comment removed for export] *)
Definition xinside_numBr (bc : bctx) (br1 : option (Z * Z)) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match xloB bc b2, xhiB bc b2 with
  | Some lo2, Some hi2 =>
      if Z.eqb lo2 hi2 then
        match br1, xhiB bc n1, xloB bc n2 with
        | Some (lo1, hi1), Some h1, Some l2 => Z.leb (lo2 + k2) (lo1 + k1) && Z.leb (hi1 + k1 + h1) (lo2 + k2 + l2)
        | _, _, _ => false
        end
      else false
  | _, _ => false
  end.
Definition xinsideB_lr (bc : bctx) (br1 : option (Z * Z)) (b1 : expr) (k1 z1 : Z) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if shares_var b1 b2 then xinside0B bc b1 k1 (ELit z1) b2 k2 n2
  else if novars b2 then (if xinside_numBr bc br1 k1 (ELit z1) b2 k2 n2 then true else false) else false.
Lemma xinsideB_lr_eq : forall bc b1 k1 z1 b2 k2 n2,
  xinsideB_lr bc (base_rangeB bc b1) b1 k1 z1 b2 k2 n2 = xinsideB bc b1 k1 (ELit z1) b2 k2 n2.
Proof. intros. reflexivity. Qed.
Definition xinsideB_tr (bc : bctx) (br1 : option (Z * Z)) (tab : list (xkey * xpre)) (b1 : expr) (k1 z1 : Z) (b2 : expr) (k2 : Z) (n2 : expr)
  : bool * list (xkey * xpre) :=
  if shares_var b1 b2 then
    match tlookup tab b1 b2 n2 with
    | Some p => (xinside0B_pre bc b1 k1 z1 b2 k2 n2 p, tab)
    | None => let p := compute_pre bc b1 b2 n2 in (xinside0B_pre bc b1 k1 z1 b2 k2 n2 p, ((b1, b2, n2), p) :: tab)
    end
  else (xinsideB_lr bc br1 b1 k1 z1 b2 k2 n2, tab).
Lemma xinsideB_tr_eq : forall bc tab b1 k1 z1 b2 k2 n2,
  xinsideB_tr bc (base_rangeB bc b1) tab b1 k1 z1 b2 k2 n2 = xinsideB_t bc tab b1 k1 z1 b2 k2 n2.
Proof. intros. unfold xinsideB_tr, xinsideB_t. rewrite xinsideB_lr_eq. reflexivity. Qed.
Definition sub_itv_2tr (bc : bctx) (br1 : option (Z * Z)) (tab : list (xkey * xpre)) (b : expr) (k z : Z) (c : saddr) (m : expr)
  : bool * bool * list (xkey * xpre) :=
  if scale_clash b (a_base c) then
    ((if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
        match xloB bc m with Some ml => Z.leb (k + z) (a_off c + ml) | None => false end
      else false), false, tab)
  else
    let '(x, tab') := xinsideB_tr bc br1 tab b k z (a_base c) (a_off c) m in
    ((if x then true else
      if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
        match xloB bc m with Some ml => Z.leb (k + z) (a_off c + ml) | None => false end
      else false), x, tab').
Lemma sub_itv_2tr_eq : forall bc tab b k z c m, sub_itv_2tr bc (base_rangeB bc b) tab b k z c m = sub_itv_2t bc tab b k z c m.
Proof. intros. unfold sub_itv_2tr, sub_itv_2t. rewrite xinsideB_tr_eq. reflexivity. Qed.
Fixpoint disj_sides_2tr (bc : bctx) (br1 : option (Z * Z)) (tab : list (xkey * xpre)) (ds : list kdx) (kb1 : list positive) (b1 : expr) (k1 z1 : Z)
  : list (saddr * expr) * list (saddr * expr) * list (xkey * xpre) :=
  match ds with
  | [] => ([], [], tab)
  | d :: rest =>
      let '(r, rx, tab1) := disj_sides_2tr bc br1 tab rest kb1 b1 k1 z1 in
      let '(x2, x2x, tab2) := if cand kb1 (kd_k2 d) (kd_l2 d) then sub_itv_2tr bc br1 tab1 b1 k1 z1 (kd_c2 d) (kd_m2 d) else (false, false, tab1) in
      let r1 := if x2 then (kd_c1 d, kd_m1 d) :: r else r in
      let rx1 := if x2x then (kd_c1 d, kd_m1 d) :: rx else rx in
      let '(x1, x1x, tab3) := if cand kb1 (kd_k1 d) (kd_l1 d) then sub_itv_2tr bc br1 tab2 b1 k1 z1 (kd_c1 d) (kd_m1 d) else (false, false, tab2) in
      (if x1 then (kd_c2 d, kd_m2 d) :: r1 else r1, if x1x then (kd_c2 d, kd_m2 d) :: rx1 else rx1, tab3)
  end.
Lemma disj_sides_2tr_eq : forall bc ds tab kb1 b1 k1 z1,
  disj_sides_2tr bc (base_rangeB bc b1) tab ds kb1 b1 k1 z1 = disj_sides_2t bc tab ds kb1 b1 k1 z1.
Proof.
  intros bc ds. induction ds as [|d rest IH]; intros tab kb1 b1 k1 z1; [reflexivity|].
  cbn [disj_sides_2tr disj_sides_2t]. rewrite IH.
  destruct (disj_sides_2t bc tab rest kb1 b1 k1 z1) as [[r rx] tab1].
  rewrite sub_itv_2tr_eq.
  destruct (if cand kb1 (kd_k2 d) (kd_l2 d) then sub_itv_2t bc tab1 b1 k1 z1 (kd_c2 d) (kd_m2 d) else (false, false, tab1)) as [[x2 x2x] tab2].
  rewrite sub_itv_2tr_eq. reflexivity.
Qed.
Definition mk_sprepBt2 (bc : bctx) (tab : list (xkey * xpre)) (b1 : expr) (k1 : Z) (n1 : expr) : sprep * list (xkey * xpre) :=
  match n1 with
  | ELit z1 =>
      if (Z.leb 0 z1 && Z.ltb z1 two64)%bool then
        let br1 := base_rangeB bc b1 in
        let '(D, Dx, tab2) := disj_sides_2tr bc br1 tab (bc_kd bc) (ekeys b1 []) b1 k1 z1 in
        (SPrep br1 (xhiB bc n1) D Dx, tab2)
      else mk_sprepBt bc tab b1 k1 n1
  | _ => mk_sprepBt bc tab b1 k1 n1
  end.
Lemma mk_sprepBt2_r : forall bc tab b1 k1 n1, mk_sprepBt2 bc tab b1 k1 n1 = mk_sprepBt2o bc tab b1 k1 n1.
Proof.
  intros. unfold mk_sprepBt2, mk_sprepBt2o. destruct n1 as [z1| | | | | | |]; try reflexivity.
  destruct (Z.leb 0 z1 && Z.ltb z1 two64)%bool; [|reflexivity]. cbv zeta. rewrite disj_sides_2tr_eq. reflexivity.
Qed.
Lemma mk_sprepBt2_eq : forall bc tab b1 k1 n1, table_ok bc tab ->
  fst (mk_sprepBt2 bc tab b1 k1 n1) = mk_sprepB bc b1 k1 n1 /\ table_ok bc (snd (mk_sprepBt2 bc tab b1 k1 n1)).
Proof. intros. rewrite mk_sprepBt2_r. apply mk_sprepBt2o_eq. assumption. Qed.

(* [comment removed for export] *)
Definition sub_itvB_tr (bc : bctx) (br : option (Z * Z)) (tab : list (xkey * xpre)) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool * list (xkey * xpre) :=
  if (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
        match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
      else false)
  then (true, tab)
  else if scale_clash b (a_base c) then (false, tab)
  else if (Z.leb 0 n && Z.ltb n two64)%bool then xinsideB_tr bc br tab b k n (a_base c) (a_off c) m else (false, tab).
Lemma sub_itvB_tr_eq : forall bc tab b k n c m, sub_itvB_tr bc (base_rangeB bc b) tab b k n c m = sub_itvB_t bc tab b k n c m.
Proof. intros. unfold sub_itvB_tr, sub_itvB_t. rewrite xinsideB_tr_eq. reflexivity. Qed.
Fixpoint in_sidesB_tr (bc : bctx) (br : option (Z * Z)) (tab : list (xkey * xpre)) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool * list (xkey * xpre) :=
  match D with
  | [] => (false, tab)
  | (c, m) :: r => let '(x, tab') := sub_itvB_tr bc br tab b2 k2 n2 c m in if x then (true, tab') else in_sidesB_tr bc br tab' r b2 k2 n2
  end.
Lemma in_sidesB_tr_eq : forall bc D tab b2 k2 n2, in_sidesB_tr bc (base_rangeB bc b2) tab D b2 k2 n2 = in_sidesB_t bc tab D b2 k2 n2.
Proof.
  intros bc D. induction D as [|[c m] r IH]; intros tab b2 k2 n2; [reflexivity|].
  cbn [in_sidesB_tr in_sidesB_t]. rewrite sub_itvB_tr_eq. destruct (sub_itvB_t bc tab b2 k2 n2 c m) as [x tab']. destruct x; [reflexivity | apply IH].
Qed.
Definition sub_itv_xB_tr (bc : bctx) (br : option (Z * Z)) (tab : list (xkey * xpre)) (b : expr) (k : Z) (n : expr) (c : saddr) (m : expr) : bool * list (xkey * xpre) :=
  if scale_clash b (a_base c) then (false, tab) else
  match n with
  | ELit z => xinsideB_tr bc br tab b k z (a_base c) (a_off c) m
  | _ => (xinsideB bc b k n (a_base c) (a_off c) m, tab)
  end.
Lemma sub_itv_xB_tr_eq : forall bc tab b k n c m, sub_itv_xB_tr bc (base_rangeB bc b) tab b k n c m = sub_itv_xB_t bc tab b k n c m.
Proof. intros. unfold sub_itv_xB_tr, sub_itv_xB_t. destruct (scale_clash b (a_base c)); [reflexivity|]. destruct n; reflexivity. Qed.
Fixpoint in_sides_xB_tr (bc : bctx) (br : option (Z * Z)) (tab : list (xkey * xpre)) (D : list (saddr * expr)) (b2 : expr) (k2 : Z) (n2 : expr) : bool * list (xkey * xpre) :=
  match D with
  | [] => (false, tab)
  | (c, m) :: r => let '(x, tab') := sub_itv_xB_tr bc br tab b2 k2 n2 c m in if x then (true, tab') else in_sides_xB_tr bc br tab' r b2 k2 n2
  end.
Lemma in_sides_xB_tr_eq : forall bc D tab b2 k2 n2, in_sides_xB_tr bc (base_rangeB bc b2) tab D b2 k2 n2 = in_sides_xB_t bc tab D b2 k2 n2.
Proof.
  intros bc D. induction D as [|[c m] r IH]; intros tab b2 k2 n2; [reflexivity|].
  cbn [in_sides_xB_tr in_sides_xB_t]. rewrite sub_itv_xB_tr_eq. destruct (sub_itv_xB_t bc tab b2 k2 n2 c m) as [x tab']. destruct x; [reflexivity | apply IH].
Qed.
Definition ranges_apart_pBtr (bc : bctx) (sp : sprep) (br2 : option (Z * Z)) (tab : list (xkey * xpre)) (b1 : expr) (k1 : Z) (n1 : expr)
           (b2 : expr) (k2 : Z) (n2 : expr) : bool * list (xkey * xpre) :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, br2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then (true, tab)
      else let '(x, tab') := in_sidesB_tr bc br2 tab (sp_D sp) b2 k2 m2 in
           if x then (true, tab')
           else ((if lin_apartB bc b1 k1 m1 b2 k2 m2 then true else lin_apart2B bc b1 k1 m1 b2 k2 m2), tab')
  | _, _ =>
    if (match sp_rng sp, br2, sp_h1 sp, xhiB bc n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else
            if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then (true, tab)
    else let '(x, tab') := in_sides_xB_tr bc br2 tab (sp_Dx sp) b2 k2 n2 in
         if x then (true, tab')
         else ((if apart_gate b1 b2 then false
                else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
                else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]), tab')
  end.
Lemma ranges_apart_pBtr_eq : forall bc sp tab b1 k1 n1 b2 k2 n2,
  ranges_apart_pBtr bc sp (base_rangeB bc b2) tab b1 k1 n1 b2 k2 n2 = ranges_apart_pBt bc sp tab b1 k1 n1 b2 k2 n2.
Proof.
  intros. unfold ranges_apart_pBtr, ranges_apart_pBt.
  destruct n1, n2; cbv zeta; rewrite ?in_sides_xB_tr_eq, ?in_sidesB_tr_eq; reflexivity.
Qed.
End LbB.

(* [comment removed for export] *)
Fixpoint dlist_eqb (D1 D2 : list (saddr * expr)) : bool :=
  match D1, D2 with
  | [], [] => true
  | (c1, m1) :: r1, (c2, m2) :: r2 => if saddr_eqb c1 c2 then (if expr_eqb m1 m2 then dlist_eqb r1 r2 else false) else false   (* [comment removed for export] *)
  | _, _ => false
  end.
Definition ranges_apart_pcBo (bc : bctx) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
           (br2 : option (Z * Z)) (b2 : expr) (k2 : Z) (n2 : expr) (io : option bool) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, br2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then true
      else if (match io with Some r => r | None => in_sidesB bc (sp_D sp) b2 k2 m2 end) then true
      else if lin_apartB bc b1 k1 m1 b2 k2 m2 then true
      else lin_apart2B bc b1 k1 m1 b2 k2 m2
  | _, _ => ranges_apart_pcB bc sp b1 k1 n1 br2 b2 k2 n2
  end.
Definition prune1pcKo (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
  (br2 : option (Z * Z)) (io : option bool) : pk_res :=
  let k := a_off wa in
  let wb := a_base wa in
  let zfK (mk : saddr -> expr -> kentry) (kb : expr) (kk : Z) (len : expr) :=
    if same then
      match len with
      | ELit l0 => PRepl (ktrim mk kb kk l0 k w)
      | _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl (kcutB bc mk wb k (elen w) kb kk len)
      end
    else if ranges_apart_pcBo bc sp wb k (elen w) br2 kb kk len io then PKeep
    else match kcutB bc mk wb k (elen w) kb kk len with
         | [] => PRepl []       (* [comment removed for export] *)
         | cut => PRepl cut
         end in
  match K with
  | KZero (SA kb kk) len => zfK KZero kb kk len
  | KFill (SA kb kk) len c => zfK (fun a n => KFill a n c) kb kk len
  | KUnk (SA kb kk) len => zfK KUnk kb kk len
  | KWord (SA kb kk) w' v =>
      if same then (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool then PKeep else PRepl (kword_cut kb kk w' v k w))
      else if ranges_apart_pcBo bc sp wb k (elen w) br2 kb kk (elen w') io then PKeep
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool then PKeep
      else PRepl []             (* [comment removed for export] *)
  | _ => prune1pcK bc sp wa w wv K same br2
  end.
Definition memo_get (memo : list (list (saddr * expr) * bool)) (D : list (saddr * expr)) : option bool :=
  match List.find (fun p => dlist_eqb (fst p) D) memo with Some (_, r) => Some r | None => None end.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition needs_sides (sx : stx) (K : kentry) (br2 : option (Z * Z)) : option (expr * Z * Z) :=
  match kdescr K with
  | Some (kb, kk, Some m) =>
      match sp_rng (sx_sp sx), br2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          if (Z.leb (hi1 + a_off (sx_a sx) + sx_m1 sx) (lo2 + kk) || Z.leb (hi2 + kk + m) (lo1 + a_off (sx_a sx)))%bool then None
          else Some (kb, kk, m)
      | _, _ => Some (kb, kk, m)
      end
  | _ => None
  end.
Fixpoint chainKFo (bc : bctx) (fl : list (stx * list stx)) (K : kentry) (okb : option expr) (same_of : positive -> bool)
         (br2 : option (Z * Z)) (memo : list (list (saddr * expr) * bool)) : list kentry :=
  match fl with
  | [] => [K]
  | (sx, rest) :: fl' =>
      let D := sp_D (sx_sp sx) in
      let io := if same_of (sx_bid sx) then None else
                match memo_get memo D with
                | Some r => Some r
                | None => match needs_sides sx K br2 with
                          | Some (kb, kk, m) => Some (in_sidesB bc D kb kk m)
                          | None => None
                          end
                end in
      match prune1pcKo bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 io with
      | PKeep => chainKFo bc fl' K okb same_of br2 (match io with Some r => (D, r) :: firstn 3 memo | None => memo end)
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

(* [comment removed for export] *)
Definition symK (K : kentry) : option (expr * Z * expr) :=
  match K with
  | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KUnk (SA kb kk) len => match len with ELit _ => None | _ => Some (kb, kk, len) end
  | _ => None
  end.
Definition ranges_apart_pcBx (bc : bctx) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
           (br2 : option (Z * Z)) (b2 : expr) (k2 : Z) (n2 : expr) (iox : option bool) : bool :=
  match n1, n2 with
  | ELit _, ELit _ => ranges_apart_pcB bc sp b1 k1 n1 br2 b2 k2 n2
  | _, _ =>
    if (match sp_rng sp, br2, sp_h1 sp, xhiB bc n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else  
            if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if (match iox with Some r => r | None => in_sides_xB bc (sp_Dx sp) b2 k2 n2 end) then true
    else if apart_gate b1 b2 then false
    else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.
Definition prune1pcKx (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
  (br2 : option (Z * Z)) (iox : option bool) : pk_res :=
  let k := a_off wa in
  let wb := a_base wa in
  let zfKx (mk : saddr -> expr -> kentry) (kb : expr) (kk : Z) (len : expr) :=
    if same then
      match len with
      | ELit l0 => PRepl (ktrim mk kb kk l0 k w)
      | _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl (kcutB bc mk wb k (elen w) kb kk len)
      end
    else if ranges_apart_pcBx bc sp wb k (elen w) br2 kb kk len iox then PKeep
    else match kcutB bc mk wb k (elen w) kb kk len with
         | [] => PRepl []       (* [comment removed for export] *)
         | cut => PRepl cut
         end in
  match K with
  | KZero (SA kb kk) len => zfKx KZero kb kk len
  | KFill (SA kb kk) len c => zfKx (fun a n => KFill a n c) kb kk len
  | KUnk (SA kb kk) len => zfKx KUnk kb kk len
  | _ => prune1pcK bc sp wa w wv K same br2
  end.
(* [comment removed for export] *)
Definition num_decides_x (bc : bctx) (sx : stx) (br2 : option (Z * Z)) (kb : expr) (kk : Z) (len : expr) : bool :=
  match sp_rng (sx_sp sx), br2, sp_h1 (sx_sp sx), xhiB bc len with
  | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
      if (Z.leb (hi1 + a_off (sx_a sx) + h1) (lo2 + kk) || Z.leb (hi2 + kk + h2) (lo1 + a_off (sx_a sx)))%bool then true
      else match end_hiB bc kb kk len lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + a_off (sx_a sx)) | None => false end
  | _, _, _, _ => false
  end.
(* [comment removed for export] *)
Definition num_decides_xh (bc : bctx) (sx : stx) (br2 : option (Z * Z)) (kb : expr) (kk : Z) (len : expr) (h2o : option Z) : bool :=
  match sp_rng (sx_sp sx), br2, sp_h1 (sx_sp sx), h2o with
  | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
      if (Z.leb (hi1 + a_off (sx_a sx) + h1) (lo2 + kk) || Z.leb (hi2 + kk + h2) (lo1 + a_off (sx_a sx)))%bool then true
      else match end_hiB bc kb kk len lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + a_off (sx_a sx)) | None => false end
  | _, _, _, _ => false
  end.
Lemma num_decides_xh_eq : forall bc sx br2 kb kk len, num_decides_xh bc sx br2 kb kk len (xhiB bc len) = num_decides_x bc sx br2 kb kk len.
Proof. reflexivity. Qed.
Definition symh (bc : bctx) (K : kentry) : option Z := match symK K with Some (_, _, len) => xhiB bc len | None => None end.
Fixpoint chainK2x (bc : bctx) (sxs : list stx) (K : kentry) (okb : option expr) (same_of : positive -> bool) (br2 : option (Z * Z))
         (memo : list (list (saddr * expr) * bool)) (h2o : option Z) : list kentry :=
  match sxs with
  | [] => [K]
  | sx :: rest =>
      let iox := if same_of (sx_bid sx) then None else
                 match symK K with
                 | Some (kb, kk, len) =>
                     if num_decides_xh bc sx br2 kb kk len h2o then None   (* [comment removed for export] *)
                     else match memo_get memo (sp_Dx (sx_sp sx)) with
                          | Some r => Some r
                          | None => Some (in_sides_xB bc (sp_Dx (sx_sp sx)) kb kk len)
                          end
                 | None => None
                 end in
      match prune1pcKx bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 iox with
      | PKeep => chainK2x bc rest K okb same_of br2 (match iox with Some r => (sp_Dx (sx_sp sx), r) :: firstn 3 memo | None => memo end) h2o
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
           | Some (g, fl) => if inb g ei then chainKFo bc fl K okb same_of br2 [] else chainK2 bc sxs K okb same_of br2   (* [comment removed for export] *)
           | None => chainK2 bc sxs K okb same_of br2
           end
       | None => chainK2 bc sxs K None (fun _ => false) None
       end) ++ entriesG bc sxs gl rest irest
  | _, _ => []
  end.

(* [comment removed for export] *)
Definition kpure (K : kentry) : bool := match K with KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ => true | _ => false end.
Lemma chainK2_pure : forall bc sxs K okb same_of br2, kpure K = true -> chainK2 bc sxs K okb same_of br2 = [K].
Proof.
  intros bc sxs K okb same_of br2 Hp. induction sxs as [|sx rest IH]; [reflexivity|].
  cbn [chainK2]. destruct K; try discriminate Hp; cbn [prune1pcK]; exact IH.
Qed.

Section LbBChainD.
Local Open Scope Z_scope.
Fixpoint chainKFt (bc : bctx) (fl : list (stx * list stx)) (K : kentry) (okb : option expr) (same_of : positive -> bool)
         (br2 : option (Z * Z)) (memo : list (list (saddr * expr) * bool)) (tab : list (xkey * xpre)) : list kentry * list (xkey * xpre) :=
  match fl with
  | [] => ([K], tab)
  | (sx, rest) :: fl' =>
      let D := sp_D (sx_sp sx) in
      let '(io, tab1) := if same_of (sx_bid sx) then (None, tab) else
                         match memo_get memo D with
                         | Some r => (Some r, tab)
                         | None => match needs_sides sx K br2 with
                                   | Some (kb, kk, m) => let '(r, tab') := in_sidesB_t bc tab D kb kk m in (Some r, tab')
                                   | None => (None, tab)
                                   end
                         end in
      match prune1pcKo bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 io with
      | PKeep => chainKFt bc fl' K okb same_of br2 (match io with Some r => (D, r) :: firstn 3 memo | None => memo end) tab1
      | PRepl l =>
          (match okb with
           | Some kb =>
               flat_map (fun K' => match kbase K' with
                                   | Some kb' => if expr_eqb kb' kb then chainK2 bc rest K' okb same_of br2 else chain_slow bc rest [K']
                                   | None => chain_slow bc rest [K']
                                   end) l
           | None => chain_slow bc rest l
           end, tab1)
      end
  end.
Fixpoint entriesGt (bc : bctx) (sxs : list stx) (gl : ptree gfl) (kn : list kentry) (infos : list (option einfo))
         (tab : list (xkey * xpre)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      let '(res, tab') :=
        (match oi with
         | Some ei =>
             let okb := kbase K in
             let same_of := match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end in
             let br2 := match okb with Some _ => ei_br ei | None => None end in
             match pt_get gl (ei_gid ei) with
             | Some (g, fl) => if inb g ei then chainKFt bc fl K okb same_of br2 [] tab else (chainK2x bc sxs K okb same_of br2 [] (symh bc K), tab)   (* [comment removed for export] *)
             | None => (chainK2x bc sxs K okb same_of br2 [] (symh bc K), tab)
             end
         | None => (if kpure K then [K] else chainK2 bc sxs K None (fun _ => false) None, tab)   (* [comment removed for export] *)
         end) in
      res ++ entriesGt bc sxs gl rest irest tab'
  | _, _ => []
  end.
(* [comment removed for export] *)
Definition same_disj (g : gval) (sx : stx) : bool :=
  match g with
  | (b, _, (glo, ghi)) =>
      if Pos.eqb b (sx_bid sx) then (if Z.leb (a_off (sx_a sx) + Z.of_nat (sx_w sx)) glo then true else Z.leb ghi (a_off (sx_a sx)))
      else false
  end.
Definition mk_gl3 (gl : ptree gfl) : ptree (list (stx * list stx)) :=
  pt_map (fun p => List.filter (fun q => negb (same_disj (fst p) (fst q))) (snd p)) gl.
Definition kword_small (K : kentry) : bool := match K with KWord _ w _ => Nat.leb w 8 | _ => false end.
Fixpoint entriesGt3 (bc : bctx) (sxs : list stx) (gl : ptree gfl) (gl3 : ptree (list (stx * list stx))) (kn : list kentry)
         (infos : list (option einfo)) (tab : list (xkey * xpre)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      let '(res, tab') :=
        (match oi with
         | Some ei =>
             let okb := kbase K in
             let same_of := match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end in
             let br2 := match okb with Some _ => ei_br ei | None => None end in
             match pt_get gl (ei_gid ei) with
             | Some (g, fl) =>
                 if inb g ei then
                   chainKFt bc (if kword_small K then match pt_get gl3 (ei_gid ei) with Some fl3 => fl3 | None => fl end else fl)
                            K okb same_of br2 [] tab
                 else (chainK2x bc sxs K okb same_of br2 [] (symh bc K), tab)
             | None => (chainK2x bc sxs K okb same_of br2 [] (symh bc K), tab)
             end
         | None => (if kpure K then [K] else chainK2 bc sxs K None (fun _ => false) None, tab)
         end) in
      res ++ entriesGt3 bc sxs gl gl3 rest irest tab'
  | _, _ => []
  end.
Lemma chainKFt_filter : forall bc (P : stx -> bool) fl K okb same_of br2 memo tab,
  (forall sx rest, In (sx, rest) fl -> P sx = true ->
     same_of (sx_bid sx) = true /\ prune1pcKo bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K true br2 None = PKeep) ->
  chainKFt bc (List.filter (fun q => negb (P (fst q))) fl) K okb same_of br2 memo tab = chainKFt bc fl K okb same_of br2 memo tab.
Proof.
  intros bc P fl. induction fl as [|[sx rest] fl' IH]; intros K okb same_of br2 memo tab H; [reflexivity|].
  assert (H' : forall sx0 rest0, In (sx0, rest0) fl' -> P sx0 = true ->
                 same_of (sx_bid sx0) = true /\ prune1pcKo bc (sx_sp sx0) (sx_a sx0) (sx_w sx0) (sx_v sx0) K true br2 None = PKeep)
    by (intros sx0 rest0 Hin HP0; apply (H sx0 rest0); [right; exact Hin | exact HP0]).
  cbn [List.filter fst]. destruct (P sx) eqn:HP; cbn [negb].
  - destruct (H sx rest (or_introl eq_refl) HP) as [Hs Hp].
    rewrite (IH K okb same_of br2 memo tab H'). cbn [chainKFt]. rewrite Hs, Hp. reflexivity.
  - cbn [chainKFt]. destruct (if same_of (sx_bid sx) then _ else _) as [io tab1].
    destruct (prune1pcKo bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 io); [|reflexivity].
    apply IH. exact H'.
Qed.
Lemma same_disj_keep : forall bc g ei sx kb kk w' v br2,
  inb g ei = true -> kdescr (KWord (SA kb kk) w' v) = Some (ei_kb ei, ei_k ei, ei_m ei) -> Nat.leb w' 8 = true ->
  same_disj g sx = true ->
  Pos.eqb (ei_bid ei) (sx_bid sx) = true /\ prune1pcKo bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) (KWord (SA kb kk) w' v) true br2 None = PKeep.
Proof.
  intros bc [[b obr] [glo ghi]] ei sx kb kk w' v br2 Hin HD Hw Hs.
  unfold inb in Hin. cbn [kdescr] in HD. injection HD as Hkb Hk Hm.
  destruct (ei_m ei) as [m|]; [|discriminate Hin]. injection Hm as Hm.
  apply Nat.leb_le in Hw.
  assert (Hm' : m = Z.of_nat w') by (rewrite <- Hm; unfold zlit64; destruct (Z.leb 0 (Z.of_nat w') && Z.ltb (Z.of_nat w') two64)%bool eqn:E; [reflexivity|];
                                     exfalso; apply Bool.andb_false_iff in E; destruct E as [E|E]; [apply Z.leb_gt in E | apply Z.ltb_ge in E]; unfold two64 in E; lia).
  repeat (apply andb_prop in Hin as [Hin ?H]).
  unfold same_disj in Hs. destruct (Pos.eqb b (sx_bid sx)) eqn:Hb; [|discriminate Hs].
  split.
  - apply Pos.eqb_eq in Hb. apply Pos.eqb_eq in Hin. rewrite <- Hin, Hb. apply Pos.eqb_refl.
  - unfold prune1pcKo. cbn [a_off a_base].
    replace ((kk + Z.of_nat w' <=? a_off (sx_a sx)) || (a_off (sx_a sx) + Z.of_nat (sx_w sx) <=? kk))%Z%bool with true; [reflexivity|].
    symmetry. apply Bool.orb_true_iff.
    repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
    rewrite Hk in *. rewrite Hm' in *.
    destruct (Z.leb (a_off (sx_a sx) + Z.of_nat (sx_w sx)) glo) eqn:E1.
    + right. apply Z.leb_le in E1. apply Z.leb_le. lia.
    + apply Z.leb_le in Hs. left. apply Z.leb_le. lia.
Qed.
Definition KDI (K : kentry) (oi : option einfo) : Prop :=
  match oi with Some ei => kdescr K = Some (ei_kb ei, ei_k ei, ei_m ei) | None => True end.
Lemma scan_entries_kdi : forall bc kn t gs infos t' gs', scan_entries bc kn t gs = (infos, t', gs') -> Forall2 KDI kn infos.
Proof.
  intros bc kn. induction kn as [|K rest IH]; intros t gs infos t' gs' H; cbn [scan_entries] in H.
  - injection H as <- _ _. constructor.
  - destruct (kdescr K) as [[[kb kk] om]|] eqn:HD.
    + destruct (intern bc t kb) as [[bid bi] t1].
      lazymatch type of H with (let '(_, _) := ?X in _) = _ => destruct X as [gid gs1] end.
      destruct (scan_entries bc rest t1 _) as [[infos2 t2] gs2] eqn:ES. injection H as <- _ _.
      constructor; [exact HD | exact (IH _ _ _ _ _ ES)].
    + destruct (scan_entries bc rest t gs) as [[infos2 t2] gs2] eqn:ES. injection H as <- _ _.
      constructor; [exact I | exact (IH _ _ _ _ _ ES)].
Qed.
Lemma entriesGt3_eq : forall bc sxs gl kn infos tab, Forall2 KDI kn infos ->
  entriesGt3 bc sxs gl (mk_gl3 gl) kn infos tab = entriesGt bc sxs gl kn infos tab.
Proof.
  intros bc sxs gl kn. induction kn as [|K rest IH]; intros infos tab HF; [destruct infos; reflexivity|].
  destruct infos as [|oi irest]; [reflexivity|]. inversion HF as [|? ? ? ? HK HF']; subst.
  cbn [entriesGt3 entriesGt]. cbv zeta.
  Ltac same_pair IH irest HF' :=
    first [ rewrite (IH irest _ HF'); reflexivity
          | lazymatch goal with |- match ?X with pair _ _ => _ end = match ?X with pair _ _ => _ end =>
              let res := fresh "res" in let tb := fresh "tb" in destruct X as [res tb]; rewrite (IH irest tb HF'); reflexivity end ].
  destruct oi as [ei|]; [|same_pair IH irest HF'].
  destruct (pt_get gl (ei_gid ei)) as [[g fl]|] eqn:Hg; [|same_pair IH irest HF'].
  destruct (inb g ei) eqn:Hin; [|same_pair IH irest HF'].
  destruct (kword_small K) eqn:Hk; [|same_pair IH irest HF'].
  unfold mk_gl3. rewrite pt_get_map. replace (@pt_get (gval * list (stx * list stx)) gl (ei_gid ei)) with (Some (g, fl)) by (symmetry; exact Hg). cbn [fst snd].
  destruct K as [[kb kk] w' v| | | | | | | | | | ]; try discriminate Hk. cbn [KDI] in HK. cbn [kbase]. fold (mk_gl3 gl).
  rewrite (chainKFt_filter bc (same_disj g) fl (KWord (SA kb kk) w' v) (Some kb) (Pos.eqb (ei_bid ei)) (ei_br ei) [] tab).
  - same_pair IH irest HF'.
  - intros sx rest0 _ Hs. exact (same_disj_keep bc g ei sx kb kk w' v (ei_br ei) Hin HK Hk Hs).
Qed.
Fixpoint mk_stxst (bc : bctx) (log : list sentry) (t : ntab) (tab : list (xkey * xpre)) : list stx * ntab * list (xkey * xpre) :=
  match log with
  | [] => ([], t, tab)
  | SE a w v :: older =>
      let '(sxs, t1, tab1) := mk_stxst bc older t tab in
      let '(r, t2) := intern bc t1 (a_base a) in
      let '(bid, bi) := r in
      let '(sp, tab2) := mk_sprepBt2 bc tab1 (a_base a) (a_off a) (elen w) in   (* [comment removed for export] *)
      (sxs ++ [STX a w v sp bid (bi_br bi)], t2, tab2)
  end.
End LbBChainD.

Definition carryG (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0, tab0) := mk_stxst bc log nt_empty [] in   (* [comment removed for export] *)
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, t1) := r in
  stores_part bc sxs ++ entriesGt bc sxs (mk_gl2 bc t1 (gs_bnds gs) sxs) kn infos tab0.   (* [comment removed for export] *)

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
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len|pt prs pargs pk];
    cbn [kdescr kbase] in *; try discriminate; try (injection H as <- <- Hm); try (left; reflexivity).
  right. exists lo, hi. repeat split; congruence.
Qed.
Lemma kdescr_None_kbase : forall K, kdescr K = None -> kbase K = None.
Proof.
  intros K H. destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len|pt prs pargs pk];
    cbn [kdescr kbase] in *; try discriminate; reflexivity.
Qed.

Lemma prune1pcK_keep_based : forall bc sp wa w wv K kb kk m lo1 hi1 lo2 hi2,
  kbase K = Some kb -> kdescr K = Some (kb, kk, Some m) ->
  sp_rng sp = Some (lo1, hi1) -> base_rangeB bc kb = Some (lo2, hi2) ->
  (hi1 + a_off wa + zlit64 (Z.of_nat w) <= lo2 + kk \/ hi2 + kk + m <= lo1 + a_off wa)%Z ->
  prune1pcK bc sp wa w wv K false (base_rangeB bc kb) = PKeep.
Proof.
  intros bc sp wa w wv K kb kk m lo1 hi1 lo2 hi2 HB HD Hsp Hbr Hnum.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len|pt prs pargs pk];
    cbn [kbase kdescr] in HB, HD; try discriminate; injection HB as ->;
    try (injection HD as <- <-); try (destruct len as [z| | | | | | |]; try discriminate; injection HD as <- <-);
    unfold prune1pcK; cbn [a_base a_off]; unfold ranges_apart_pcB; cbn [elen]; rewrite Hsp, Hbr;
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
  cbn [kdescr] in HD. destruct (Z.ltb (hi - lo) two64) eqn:Hlt; [|discriminate]. injection HD as <-.
  unfold prune1pcK. destruct wa as [wb k]. cbn [a_base a_off] in *.
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

Lemma chainKF_eq2 : forall bc t g sxs K okb same_of br2,
  (forall sx, In sx sxs -> verdict2 bc t sx g = true ->
     prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 = PKeep) ->
  chainKF bc (mk_fl2 bc t g sxs) K okb same_of br2 = chainK2 bc sxs K okb same_of br2.
Proof.
  intros bc t g sxs. induction sxs as [|sx rest IH]; intros K okb same_of br2 Hf; [reflexivity|].
  cbn [mk_fl2 chainK2].
  assert (IH' : chainKF bc (mk_fl2 bc t g rest) K okb same_of br2 = chainK2 bc rest K okb same_of br2)
    by (apply IH; intros; apply Hf; [right|]; assumption).
  destruct (verdict2 bc t sx g) eqn:Hv.
  - rewrite (Hf sx (or_introl eq_refl) Hv). exact IH'.
  - cbn [chainKF]. destruct (prune1pcK _ _ _ _ _ K _ br2); [exact IH'|reflexivity].
Qed.

(* [comment removed for export] *)
Lemma in_sidesB_In : forall bc D b k n c mm,
  In (c, mm) D -> sub_itvB bc b k n c mm = true -> in_sidesB bc D b k n = true.
Proof.
  intros bc D b k n c mm. induction D as [|[c' m'] rest IH]; intros Hin Hs; [destruct Hin|].
  cbn [in_sidesB]. destruct Hin as [E|Hin].
  - injection E as -> ->. rewrite Hs. reflexivity.
  - destruct (sub_itvB bc b k n c' m'); [reflexivity|]. exact (IH Hin Hs).
Qed.
Lemma side_cov_in_sides : forall bc D gb glo ghi kk m,
  side_cov bc D gb glo ghi = true -> (glo <= kk)%Z -> (kk + m <= ghi)%Z ->
  in_sidesB bc D gb kk m = true.
Proof.
  intros bc D gb glo ghi kk m Hc Hlo Hhi. unfold side_cov in Hc. apply existsb_exists in Hc as ([c mm] & Hin & Hx).
  cbn [fst snd] in Hx. apply (in_sidesB_In bc D gb kk m c mm Hin).
  destruct (expr_eqb gb (a_base c) && Z.leb (a_off c) glo)%bool eqn:E1; [|discriminate].
  apply andb_prop in E1 as [E1 E2]. apply Z.leb_le in E2.
  destruct (xloB bc mm) as [ml|] eqn:Exl; [|discriminate]. apply Z.leb_le in Hx.
  unfold sub_itvB. rewrite E1. rewrite (proj2 (Z.leb_le (a_off c) kk) ltac:(lia)). rewrite Exl. cbv beta iota.
  rewrite (proj2 (Z.leb_le (kk + m) (a_off c + ml)) ltac:(lia)). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma lead_term_novars : forall e, novars e = true -> lead_term e = None.
Proof.
  induction e as [z|v|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx kk i n]; cbn [novars lead_term]; intros H;
    try reflexivity; try discriminate.
  - destruct op; try reflexivity. destruct (novars a) eqn:Ea; [|discriminate]. exact (IHa eq_refl).
  - destruct op; try reflexivity. destruct a as [c| | | | | | |]; try reflexivity. destruct b as [|w| | | | | |]; try reflexivity.
    destruct (novars (ELit c)); discriminate.
Qed.
Lemma scale_clash_novars_r : forall b1 b2, novars b2 = true -> scale_clash b1 b2 = false.
Proof. intros b1 b2 H. unfold scale_clash. rewrite (lead_term_novars b2 H). destruct (lead_term b1) as [[? ?]|]; reflexivity. Qed.
Lemma shares_var_novars_r : forall b1 b2, novars b2 = true -> shares_var b1 b2 = false.
Proof.
  intros b1 b2. induction b2 as [z|v|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx kk i n];
    cbn [novars shares_var]; intros H; try reflexivity; try discriminate;
    try (destruct (novars a) eqn:Ea; [|discriminate]; rewrite (IHa eq_refl); exact (IHb H));
    exact (IHa H).
Qed.
Lemma zlit64_range : forall z, (0 <= zlit64 z < two64)%Z.
Proof.
  intros z. unfold zlit64. destruct (Z.leb 0 z && Z.ltb z two64)%bool eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
  - apply Z.mod_pos_bound. unfold two64. lia.
Qed.
Lemma obr_eqb_eq : forall a b, obr_eqb a b = true -> a = b.
Proof.
  intros [[x1 y1]|] [[x2 y2]|] H; cbn [obr_eqb] in H; try discriminate; [|reflexivity].
  apply andb_prop in H as [X Y]. apply Z.eqb_eq in X. apply Z.eqb_eq in Y. subst x2 y2. reflexivity.
Qed.
Lemma side_cov_num_in_sides : forall bc D gb obr glo ghi kk m,
  side_cov_num bc D obr glo ghi = true -> obr = base_rangeB bc gb ->
  (glo <= kk)%Z -> (kk + m <= ghi)%Z -> (0 <= m < two64)%Z ->
  in_sidesB bc D gb kk m = true.
Proof.
  intros bc D gb obr glo ghi kk m Hc Hobr Hlo Hhi Hm. unfold side_cov_num in Hc.
  destruct obr as [[lo1 hi1]|]; [|discriminate].
  apply existsb_exists in Hc as ([c mm] & Hin & Hx). cbn [fst snd] in Hx.
  apply (in_sidesB_In bc D gb kk m c mm Hin).
  destruct (novars (a_base c)) eqn:Hnv; [|discriminate].
  destruct (xloB bc (a_base c)) as [lo2|] eqn:El; [|discriminate].
  destruct (xhiB bc (a_base c)) as [hi2|] eqn:Eh; [|discriminate].
  destruct (xloB bc mm) as [l2|] eqn:Em; [|discriminate].
  apply andb_prop in Hx as [Hx H3]. apply andb_prop in Hx as [H1 H2].
  apply Z.leb_le in H2. apply Z.leb_le in H3.
  unfold sub_itvB.
  lazymatch goal with |- (if ?c then true else _) = true => destruct c; [reflexivity|] end.
  rewrite (scale_clash_novars_r gb (a_base c) Hnv).
  replace (Z.leb 0 m && Z.ltb m two64)%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  unfold xinsideB. rewrite (shares_var_novars_r gb (a_base c) Hnv), Hnv.
  unfold xinside_numB. rewrite El, Eh, H1. rewrite <- Hobr. cbn [xhiB]. rewrite Em.
  replace (zlit64 m) with m by (unfold zlit64; replace (Z.leb 0 m && Z.ltb m two64)%bool with true; [reflexivity|];
                                 symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  replace (Z.leb (lo2 + a_off c) (lo1 + kk) && Z.leb (hi1 + kk + m) (lo2 + a_off c + l2))%bool with true; [reflexivity|].
  symmetry. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Lemma ranges_apart_pcB_side : forall bc sp b1 k1 z1 br2 b2 k2 z2,
  in_sidesB bc (sp_D sp) b2 k2 (zlit64 z2) = true ->
  ranges_apart_pcB bc sp b1 k1 (ELit z1) br2 b2 k2 (ELit z2) = true.
Proof.
  intros bc sp b1 k1 z1 br2 b2 k2 z2 H. unfold ranges_apart_pcB. cbv beta iota zeta.
  lazymatch goal with |- (if ?c then _ else _) = _ => destruct c; [reflexivity|] end.
  rewrite H. reflexivity.
Qed.
Lemma ranges_apart_pB_side : forall bc sp b1 k1 z1 b2 k2 z2,
  in_sidesB bc (sp_D sp) b2 k2 (zlit64 z2) = true ->
  ranges_apart_pB bc sp b1 k1 (ELit z1) b2 k2 (ELit z2) = true.
Proof.
  intros bc sp b1 k1 z1 b2 k2 z2 H. unfold ranges_apart_pB. cbv beta iota zeta.
  lazymatch goal with |- (if ?c then _ else _) = _ => destruct c; [reflexivity|] end.
  rewrite H. reflexivity.
Qed.
Lemma prune1pcK_keep_side : forall bc sp wa w wv K kb kk m br2,
  kbase K = Some kb -> kdescr K = Some (kb, kk, Some m) ->
  in_sidesB bc (sp_D sp) kb kk m = true ->
  prune1pcK bc sp wa w wv K false br2 = PKeep.
Proof.
  intros bc sp wa w wv K kb kk m br2 HB HD Hin.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len|pt prs pargs pk];
    cbn [kbase kdescr] in HB, HD; try discriminate; injection HB as ->.
  - injection HD as <- <-. unfold prune1pcK. cbn [a_base a_off].
    unfold elen. rewrite (ranges_apart_pcB_side _ _ _ _ _ _ _ _ _ Hin). reflexivity.
  - destruct len as [z| | | | | | |]; try discriminate. injection HD as <- <-.
    unfold prune1pcK. cbn [a_base a_off]. unfold elen. rewrite (ranges_apart_pcB_side _ _ _ _ _ _ _ _ _ Hin). reflexivity.
  - destruct len as [z| | | | | | |]; try discriminate. injection HD as <- <-.
    unfold prune1pcK. cbn [a_base a_off]. unfold elen. rewrite (ranges_apart_pcB_side _ _ _ _ _ _ _ _ _ Hin). reflexivity.
  - destruct len as [z| | | | | | |]; try discriminate. injection HD as <- <-.
    unfold prune1pcK. cbn [a_base a_off]. unfold elen. rewrite (ranges_apart_pcB_side _ _ _ _ _ _ _ _ _ Hin). reflexivity.
  - destruct len as [z| | | | | | |]; try discriminate. injection HD as <- <-.
    unfold prune1pcK. cbn [a_base a_off]. unfold elen. rewrite (ranges_apart_pcB_side _ _ _ _ _ _ _ _ _ Hin). reflexivity.
Qed.
Lemma prune1pcK_keep_side_img : forall bc sp wa w wv lo hi m same br2,
  kdescr (KImg lo hi) = Some (ELit 0%Z, lo, Some m) ->
  expr_eqb (ELit 0%Z) (a_base wa) = false ->
  in_sidesB bc (sp_D sp) (ELit 0%Z) lo m = true ->
  prune1pcK bc sp wa w wv (KImg lo hi) same br2 = PKeep.
Proof.
  intros bc sp wa w wv lo hi m same br2 HD Hne Hin.
  cbn [kdescr] in HD. destruct (Z.ltb (hi - lo) two64) eqn:Hlt; [|discriminate]. injection HD as <-.
  unfold prune1pcK. destruct wa as [wb k]. cbn [a_base a_off] in *.
  assert (STEP : (if ranges_apart_pB bc sp wb k (elen w) (ELit 0%Z) lo (ELit (hi - lo)) then PKeep else PRepl []) = PKeep).
  { unfold elen. rewrite (ranges_apart_pB_side _ _ _ _ _ _ _ _ Hin). reflexivity. }
  rewrite Hlt. destruct wb as [z| | | | | | |]; try exact STEP.
  destruct z; try exact STEP. cbn in Hne. discriminate.
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

(* [comment removed for export] *)
Lemma dlist_eqb_eq : forall D1 D2, dlist_eqb D1 D2 = true -> D1 = D2.
Proof.
  induction D1 as [|[c1 m1] r1 IH]; destruct D2 as [|[c2 m2] r2]; cbn [dlist_eqb]; intros H; try discriminate; [reflexivity|].
  destruct (saddr_eqb c1 c2) eqn:H1; [|discriminate H]. destruct (expr_eqb m1 m2) eqn:H2; [|discriminate H]. rename H into H3.
  destruct c1 as [b1 o1]. destruct c2 as [b2 o2]. unfold saddr_eqb in H1. cbn [a_base a_off] in H1.
  destruct (Z.eqb o1 o2) eqn:H1'; [|discriminate H1]. apply expr_eqb_eqB in H1. apply Z.eqb_eq in H1'. apply expr_eqb_eqB in H2.
  subst. rewrite (IH _ H3). reflexivity.
Qed.
Lemma ranges_apart_pcBo_eq : forall bc sp b1 k1 n1 br2 b2 k2 n2 io,
  (forall z2, n2 = ELit z2 -> io = None \/ io = Some (in_sidesB bc (sp_D sp) b2 k2 (zlit64 z2))) ->
  ranges_apart_pcBo bc sp b1 k1 n1 br2 b2 k2 n2 io = ranges_apart_pcB bc sp b1 k1 n1 br2 b2 k2 n2.
Proof.
  intros bc sp b1 k1 n1 br2 b2 k2 n2 io Hio. unfold ranges_apart_pcBo.
  destruct n1 as [z1| | | | | | |]; try reflexivity. destruct n2 as [z2| | | | | | |]; try reflexivity.
  unfold ranges_apart_pcB. destruct (Hio z2 eq_refl) as [->| ->]; reflexivity.
Qed.
Definition io_ok (bc : bctx) (sp : sprep) (K : kentry) (io : option bool) : Prop :=
  forall kb kk m, kdescr K = Some (kb, kk, Some m) -> io = None \/ io = Some (in_sidesB bc (sp_D sp) kb kk m).
Lemma prune1pcKo_eq : forall bc sp wa w wv K same br2 io,
  io_ok bc sp K io ->
  prune1pcKo bc sp wa w wv K same br2 io = prune1pcK bc sp wa w wv K same br2.
Proof.
  intros bc sp wa w wv K same br2 io Hio. unfold io_ok in Hio.
  assert (ZF : forall kb kk len, (forall z, len = ELit z -> io = None \/ io = Some (in_sidesB bc (sp_D sp) kb kk (zlit64 z))) ->
             ranges_apart_pcBo bc sp (a_base wa) (a_off wa) (elen w) br2 kb kk len io
             = ranges_apart_pcB bc sp (a_base wa) (a_off wa) (elen w) br2 kb kk len).
  { intros kb kk len H. apply ranges_apart_pcBo_eq. exact H. }
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len|pt prs pargs pk];
    try reflexivity; unfold prune1pcKo, prune1pcK; cbv zeta.
  - (* [comment removed for export] *)
    rewrite (ZF kb kk (elen w')) by (intros z Hz; unfold elen in Hz; injection Hz as <-; exact (Hio kb kk _ eq_refl)).
    destruct same; [reflexivity|].
    destruct (ranges_apart_pcB bc sp (a_base wa) (a_off wa) (elen w) br2 kb kk (elen w')); [reflexivity|].
    destruct (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool; reflexivity.
  - (* [comment removed for export] *)
    rewrite (ZF kb kk len) by (intros z Hz; subst len; exact (Hio kb kk _ eq_refl)).
    destruct same; [reflexivity|].
    destruct (ranges_apart_pcB bc sp (a_base wa) (a_off wa) (elen w) br2 kb kk len); [reflexivity|].
    destruct (kcutB bc KZero (a_base wa) (a_off wa) (elen w) kb kk len); reflexivity.
  - (* [comment removed for export] *)
    rewrite (ZF kb kk len) by (intros z Hz; subst len; exact (Hio kb kk _ eq_refl)).
    destruct same; [reflexivity|].
    destruct (ranges_apart_pcB bc sp (a_base wa) (a_off wa) (elen w) br2 kb kk len); [reflexivity|].
    destruct (kcutB bc (fun a n => KFill a n fc) (a_base wa) (a_off wa) (elen w) kb kk len); reflexivity.
  - (* [comment removed for export] *)
    rewrite (ZF kb kk len) by (intros z Hz; subst len; exact (Hio kb kk _ eq_refl)).
    destruct same; [reflexivity|].
    destruct (ranges_apart_pcB bc sp (a_base wa) (a_off wa) (elen w) br2 kb kk len); [reflexivity|].
    destruct (kcutB bc KUnk (a_base wa) (a_off wa) (elen w) kb kk len); reflexivity.
Qed.
Definition memo_ok (bc : bctx) (K : kentry) (memo : list (list (saddr * expr) * bool)) : Prop :=
  Forall (fun p : list (saddr * expr) * bool => forall kb kk m, kdescr K = Some (kb, kk, Some m) -> snd p = in_sidesB bc (fst p) kb kk m) memo.
Lemma chainKFo_eq : forall bc fl K okb same_of br2 memo,
  memo_ok bc K memo -> chainKFo bc fl K okb same_of br2 memo = chainKF bc fl K okb same_of br2.
Proof.
  intros bc fl. induction fl as [|[sx rest] fl IH]; intros K okb same_of br2 memo Hm; [reflexivity|].
  cbn [chainKFo chainKF]. cbv zeta.
  match goal with |- match prune1pcKo _ _ _ _ _ _ _ _ ?IO with _ => _ end = _ => remember IO as io eqn:Hiodef end.
  assert (Hio : forall kb kk m, kdescr K = Some (kb, kk, Some m) -> io = None \/ io = Some (in_sidesB bc (sp_D (sx_sp sx)) kb kk m)).
  { intros kb kk m HD. rewrite Hiodef. destruct (same_of (sx_bid sx)); [left; reflexivity|].
    destruct (memo_get memo (sp_D (sx_sp sx))) as [r|] eqn:Hg.
    - right. unfold memo_get in Hg. destruct (List.find (fun p => dlist_eqb (fst p) (sp_D (sx_sp sx))) memo) as [[D0 r0]|] eqn:Hf; [|discriminate].
      injection Hg as <-. apply find_some in Hf as [Hin He]. cbn [fst] in He. apply dlist_eqb_eq in He. subst D0.
      pose proof (proj1 (Forall_forall _ _) Hm _ Hin kb kk m HD) as X. cbn [fst snd] in X. rewrite X. reflexivity.
    - unfold needs_sides. rewrite HD.
      destruct (sp_rng (sx_sp sx)) as [[lo1 hi1]|]; [|right; reflexivity].
      destruct br2 as [[lo2 hi2]|]; [|right; reflexivity].
      destruct (Z.leb (hi1 + a_off (sx_a sx) + sx_m1 sx) (lo2 + kk) || Z.leb (hi2 + kk + m) (lo1 + a_off (sx_a sx)))%bool;
        [left; reflexivity | right; reflexivity]. }
  rewrite (prune1pcKo_eq bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 io Hio).
  destruct (prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2); [|reflexivity].
  apply IH. destruct io as [r0|].
  - constructor.
    + intros kb kk m HD. destruct (Hio kb kk m HD) as [X|X]; [discriminate X|]. injection X as X. exact X.
    + unfold memo_ok in Hm |- *. rewrite <- (firstn_skipn 3 memo) in Hm. apply Forall_app in Hm as [Hm _]. exact Hm.
  - exact Hm.
Qed.

(* [comment removed for export] *)
Lemma ranges_apart_pcBx_eq : forall bc sp b1 k1 n1 br2 b2 k2 n2 iox,
  (iox = None \/ iox = Some (in_sides_xB bc (sp_Dx sp) b2 k2 n2)) ->
  ranges_apart_pcBx bc sp b1 k1 n1 br2 b2 k2 n2 iox = ranges_apart_pcB bc sp b1 k1 n1 br2 b2 k2 n2.
Proof.
  intros bc sp b1 k1 n1 br2 b2 k2 n2 iox H. unfold ranges_apart_pcBx.
  destruct n1 as [z1| | | | | | |]; destruct n2 as [z2| | | | | | |]; try reflexivity;
    unfold ranges_apart_pcB; destruct H as [->| ->]; reflexivity.
Qed.
Definition iox_ok (bc : bctx) (sp : sprep) (K : kentry) (iox : option bool) : Prop :=
  forall kb kk len, symK K = Some (kb, kk, len) -> iox = None \/ iox = Some (in_sides_xB bc (sp_Dx sp) kb kk len).
Lemma prune1pcKx_eq : forall bc sp wa w wv K same br2 iox,
  iox_ok bc sp K iox -> prune1pcKx bc sp wa w wv K same br2 iox = prune1pcK bc sp wa w wv K same br2.
Proof.
  intros bc sp wa w wv K same br2 iox Hio. unfold iox_ok in Hio.
  assert (RA : forall kb kk len, (forall z, len <> ELit z) -> (iox = None \/ iox = Some (in_sides_xB bc (sp_Dx sp) kb kk len)) ->
             ranges_apart_pcBx bc sp (a_base wa) (a_off wa) (elen w) br2 kb kk len iox
             = ranges_apart_pcB bc sp (a_base wa) (a_off wa) (elen w) br2 kb kk len).
  { intros kb kk len _ H. apply ranges_apart_pcBx_eq. exact H. }
  assert (RL : forall kb kk z, ranges_apart_pcBx bc sp (a_base wa) (a_off wa) (elen w) br2 kb kk (ELit z) iox
                               = ranges_apart_pcB bc sp (a_base wa) (a_off wa) (elen w) br2 kb kk (ELit z)).
  { intros kb kk z. unfold ranges_apart_pcBx, elen. reflexivity. }
  assert (ZF : forall kb kk len,
             (match len with ELit _ => True | _ => iox = None \/ iox = Some (in_sides_xB bc (sp_Dx sp) kb kk len) end) ->
             ranges_apart_pcBx bc sp (a_base wa) (a_off wa) (elen w) br2 kb kk len iox
             = ranges_apart_pcB bc sp (a_base wa) (a_off wa) (elen w) br2 kb kk len).
  { intros kb kk len H. destruct len as [z| | | | | | |]; [apply RL|..]; apply ranges_apart_pcBx_eq; exact H. }
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len|pt prs pargs pk];
    try reflexivity; unfold prune1pcKx, prune1pcK; cbv beta zeta.
  - (* [comment removed for export] *)
    rewrite (ZF kb kk len) by (destruct len; [exact I | apply (Hio kb kk _ eq_refl) ..]).
    destruct same; [reflexivity|].
    destruct (ranges_apart_pcB bc sp (a_base wa) (a_off wa) (elen w) br2 kb kk len) eqn:E0; [reflexivity|].
    destruct (kcutB bc KZero (a_base wa) (a_off wa) (elen w) kb kk len); reflexivity.
  - (* [comment removed for export] *)
    rewrite (ZF kb kk len) by (destruct len; [exact I | apply (Hio kb kk _ eq_refl) ..]).
    destruct same; [reflexivity|].
    destruct (ranges_apart_pcB bc sp (a_base wa) (a_off wa) (elen w) br2 kb kk len) eqn:E0; [reflexivity|].
    destruct (kcutB bc (fun a n => KFill a n fc) (a_base wa) (a_off wa) (elen w) kb kk len); reflexivity.
  - (* [comment removed for export] *)
    rewrite (ZF kb kk len) by (destruct len; [exact I | apply (Hio kb kk _ eq_refl) ..]).
    destruct same; [reflexivity|].
    destruct (ranges_apart_pcB bc sp (a_base wa) (a_off wa) (elen w) br2 kb kk len) eqn:E0; [reflexivity|].
    destruct (kcutB bc KUnk (a_base wa) (a_off wa) (elen w) kb kk len); reflexivity.
Qed.
Definition memo_okx (bc : bctx) (K : kentry) (memo : list (list (saddr * expr) * bool)) : Prop :=
  Forall (fun p : list (saddr * expr) * bool => forall kb kk len, symK K = Some (kb, kk, len) -> snd p = in_sides_xB bc (fst p) kb kk len) memo.
Lemma chainK2x_eq : forall bc sxs K okb same_of br2 memo,
  memo_okx bc K memo -> chainK2x bc sxs K okb same_of br2 memo (symh bc K) = chainK2 bc sxs K okb same_of br2.
Proof.
  intros bc sxs. induction sxs as [|sx rest IH]; intros K okb same_of br2 memo Hm; [reflexivity|].
  cbn [chainK2x chainK2]. cbv zeta.
  match goal with |- match prune1pcKx _ _ _ _ _ _ _ _ ?IO with _ => _ end = _ => remember IO as iox eqn:Hiodef end.
  assert (Hio : iox_ok bc (sx_sp sx) K iox).
  { intros kb kk len HD. rewrite Hiodef. destruct (same_of (sx_bid sx)); [left; reflexivity|]. rewrite HD.
    assert (Hh : symh bc K = xhiB bc len) by (unfold symh; rewrite HD; reflexivity). rewrite Hh, num_decides_xh_eq.   (* [comment removed for export] *)
    destruct (num_decides_x bc sx br2 kb kk len); [left; reflexivity|].
    destruct (memo_get memo (sp_Dx (sx_sp sx))) as [r|] eqn:Hg; [|right; reflexivity].
    right. unfold memo_get in Hg. destruct (List.find (fun p => dlist_eqb (fst p) (sp_Dx (sx_sp sx))) memo) as [[D0 r0]|] eqn:Hf; [|discriminate].
    injection Hg as <-. apply find_some in Hf as [Hin He]. cbn [fst] in He. apply dlist_eqb_eq in He. subst D0.
    pose proof (proj1 (Forall_forall _ _) Hm _ Hin kb kk len HD) as X. cbn [fst snd] in X. rewrite X. reflexivity. }
  rewrite (prune1pcKx_eq bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 iox Hio).
  destruct (prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2); [|reflexivity].
  apply IH. destruct iox as [r0|].
  - constructor.
    + intros kb kk len HD. destruct (Hio kb kk len HD) as [X|X]; [discriminate X|]. injection X as X. exact X.
    + unfold memo_okx in Hm |- *. rewrite <- (firstn_skipn 3 memo) in Hm. apply Forall_app in Hm as [Hm _]. exact Hm.
  - exact Hm.
Qed.

Section LbBChainL.
Local Open Scope Z_scope.
Lemma chainKFt_eq : forall bc fl K okb same_of br2 memo tab, table_ok bc tab ->
  fst (chainKFt bc fl K okb same_of br2 memo tab) = chainKFo bc fl K okb same_of br2 memo
  /\ table_ok bc (snd (chainKFt bc fl K okb same_of br2 memo tab)).
Proof.
  intros bc fl. induction fl as [|[sx rest] fl IH]; intros K okb same_of br2 memo tab Hok; [split; [reflexivity | exact Hok]|].
  cbn [chainKFt chainKFo]. cbv zeta.
  assert (HIO : exists tab1, table_ok bc tab1 /\
            (if same_of (sx_bid sx) then (None, tab) else
             match memo_get memo (sp_D (sx_sp sx)) with
             | Some r => (Some r, tab)
             | None => match needs_sides sx K br2 with
                       | Some (kb, kk, m) => let '(r, tab') := in_sidesB_t bc tab (sp_D (sx_sp sx)) kb kk m in (Some r, tab')
                       | None => (None, tab)
                       end
             end)
            = ((if same_of (sx_bid sx) then None else
                match memo_get memo (sp_D (sx_sp sx)) with
                | Some r => Some r
                | None => match needs_sides sx K br2 with
                          | Some (kb, kk, m) => Some (in_sidesB bc (sp_D (sx_sp sx)) kb kk m)
                          | None => None
                          end
                end), tab1)).
  { destruct (same_of (sx_bid sx)); [exists tab; split; [exact Hok | reflexivity]|].
    destruct (memo_get memo (sp_D (sx_sp sx))) as [r|]; [exists tab; split; [exact Hok | reflexivity]|].
    destruct (needs_sides sx K br2) as [[[kb kk] m]|]; [|exists tab; split; [exact Hok | reflexivity]].
    destruct (in_sidesB_t_eq bc (sp_D (sx_sp sx)) tab kb kk m Hok) as [E O].
    destruct (in_sidesB_t bc tab (sp_D (sx_sp sx)) kb kk m) as [r tab'] eqn:Ht. cbn [fst snd] in E, O.
    exists tab'. split; [exact O|]. rewrite E. reflexivity. }
  destruct HIO as (tab1 & Hok1 & HE). rewrite HE.
  destruct (prune1pcKo bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 _); [|split; [reflexivity | exact Hok1]].
  apply IH. exact Hok1.
Qed.
Lemma entriesGt_eq : forall bc sxs gl kn infos tab, table_ok bc tab -> entriesGt bc sxs gl kn infos tab = entriesG bc sxs gl kn infos.
Proof.
  intros bc sxs gl kn. induction kn as [|K rest IH]; intros infos tab Hok; [destruct infos; reflexivity|].
  destruct infos as [|oi irest]; [reflexivity|]. cbn [entriesGt entriesG]. cbv zeta.
  destruct oi as [ei|].
  - destruct (pt_get gl (ei_gid ei)) as [[g fl]|].
    + destruct (inb g ei).
      * destruct (chainKFt_eq bc fl K (kbase K) (match kbase K with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end)
                    (match kbase K with Some _ => ei_br ei | None => None end) [] tab Hok) as [E O].
        destruct (chainKFt bc fl K _ _ _ [] tab) as [res tab'] eqn:Hc. cbn [fst snd] in E, O. rewrite E, (IH irest tab' O). reflexivity.
      * rewrite chainK2x_eq by constructor. rewrite (IH irest tab Hok). reflexivity.
    + rewrite chainK2x_eq by constructor. rewrite (IH irest tab Hok). reflexivity.
  - destruct (kpure K) eqn:Hp; [rewrite (chainK2_pure bc sxs K None (fun _ => false) None Hp)|]; rewrite (IH irest tab Hok); reflexivity.
Qed.

Lemma mk_stxst_eq : forall bc log t tab, table_ok bc tab ->
  (fst (fst (mk_stxst bc log t tab)), snd (fst (mk_stxst bc log t tab))) = mk_stxs bc log t /\ table_ok bc (snd (mk_stxst bc log t tab)).
Proof.
  intros bc log. induction log as [|[a w v] older IH]; intros t tab Hok; [split; [reflexivity | exact Hok]|].
  cbn [mk_stxst mk_stxs].
  destruct (IH t tab Hok) as [E0 O0]. destruct (mk_stxst bc older t tab) as [[sxs t1] tab1]. cbn [fst snd] in E0, O0. rewrite <- E0.
  destruct (intern bc t1 (a_base a)) as [[bid bi] t2].
  destruct (mk_sprepBt2_eq bc tab1 (a_base a) (a_off a) (elen w) O0) as [E O].
  destruct (mk_sprepBt2 bc tab1 (a_base a) (a_off a) (elen w)) as [sp tab2]. cbn [fst snd] in E, O. rewrite E.
  split; [reflexivity | exact O].
Qed.
End LbBChainL.


Lemma entriesG_eq : forall fk sxs bnds kn infos t1,
  NTI (mkbc fk) t1 -> Forall (SX_OK (mkbc fk) t1) sxs -> Forall2 (EINF (mkbc fk) t1) kn infos ->
  entriesG (mkbc fk) sxs (mk_gl2 (mkbc fk) t1 bnds sxs) kn infos = chainRo fk (map strip sxs) kn.
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
      unfold mk_gl2. rewrite pt_get_map.
      destruct (pt_get bnds (ei_gid ei)) as [g|]; [|apply FULL; reflexivity].
      destruct (inb g ei) eqn:Hinb; [|apply FULL; reflexivity].
      rewrite <- (FULL (kbase K) eq_refl).
      rewrite chainKFo_eq by (constructor).   (* [comment removed for export] *)
      apply chainKF_eq2.
      intros sx Hsx Hv2.
      assert (Hm : exists m, ei_m ei = Some m).
      { unfold inb in Hinb. destruct (ei_m ei) as [m|]; [exists m; reflexivity|discriminate]. }
      destruct Hm as [m Hm].
      unfold verdict2 in Hv2. destruct (verdict sx g) eqn:Hv.
      2: { (* [comment removed for export] *)
        destruct g as [[b obr] [glo ghi]]. cbv beta iota in Hv2.
        unfold inb in Hinb. rewrite Hm in Hinb.
        apply andb_prop in Hinb as [Hinb H4]. apply andb_prop in Hinb as [Hinb H3]. apply andb_prop in Hinb as [H1 H2].
        apply Pos.eqb_eq in H1. subst b. apply Z.leb_le in H3. apply Z.leb_le in H4.
        destruct (Pos.eqb (ei_bid ei) (sx_bid sx)) eqn:Hne; [cbv beta iota in Hv2; discriminate Hv2|]. cbv beta iota in Hv2.
        assert (Hm64 : (0 <= m < two64)%Z).
        { rewrite Hm in HD. destruct (kdescr_kbase _ _ _ _ HD) as [HB0|(lo & hi & -> & _ & _)].
          - destruct K as [[b0 k0] w' v|[b0 k0] len|[b0 k0] len bk|lo hi|e' m'|e' lo' hi'|[b0 k0] n|a1 n1 a2 n2|[b0 k0] len fc|[b0 k0] len|pt prs pargs pk];
              cbn [kdescr] in HD; try discriminate;
              try (destruct len as [z| | | | | | |]; try discriminate);
              injection HD as _ _ <-; apply zlit64_range.
          - cbn [kdescr] in HD. destruct (Z.ltb (hi - lo) two64); [|discriminate]. injection HD as _ _ <-. apply zlit64_range. }
        assert (Hsides : in_sidesB (mkbc fk) (sp_D (sx_sp sx)) (ei_kb ei) (ei_k ei) m = true).
        { destruct (side_cov_num (mkbc fk) (sp_D (sx_sp sx)) obr glo ghi) eqn:Hnum.
          - (* [comment removed for export] *)
            eapply side_cov_num_in_sides; [exact Hnum | | exact H3 | exact H4 | exact Hm64].
            rewrite <- Hbr. apply obr_eqb_eq. exact H2.
          - cbv beta iota in Hv2.
            destruct (proj1 HT _ _ _ HIn) as (_ & Hinfo & _). rewrite Hinfo in Hv2. cbv beta iota in Hv2. cbn [bi_base] in Hv2.
            exact (side_cov_in_sides _ _ _ _ _ _ _ Hv2 H3 H4). }
        pose proof (proj1 (Forall_forall _ _) HS sx Hsx) as (SXin & SXbr & SXsp).
        rewrite Hm in HD.
        destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
        - rewrite HB. rewrite Hne. eapply prune1pcK_keep_side; [exact HB | exact HD | exact Hsides].
        - cbn [kbase]. rewrite Hkb, Hk in *.
          eapply prune1pcK_keep_side_img; [exact HD| | exact Hsides].
          rewrite <- (nt_same_eq _ _ _ _ _ _ HT HIn SXin). exact Hne. }
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
  intros log kn. unfold carryG.
  destruct (mk_stxst_eq (mkbc (facts_of kn)) log nt_empty [] (Forall_nil _)) as [E0 O0].
  destruct (mk_stxst (mkbc (facts_of kn)) log nt_empty []) as [[sxs t0] tab0]. cbn [fst snd] in E0, O0.
  assert (E : mk_stxs (mkbc (facts_of kn)) log nt_empty = (sxs, t0)) by (symmetry; exact E0).
  destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT0 & HS0 & Hmap & _).
  destruct (scan_entries (mkbc (facts_of kn)) kn t0 gst_empty) as [[infos t1] gs] eqn:ES.
  destruct (scan_entries_ok _ _ _ _ _ _ _ HT0 ES) as (HT1 & Hm & HF).
  assert (HS1 : Forall (SX_OK (mkbc (facts_of kn)) t1) sxs).
  { apply Forall_impl with (P := SX_OK (mkbc (facts_of kn)) t0); [|exact HS0]. intros sx. apply SX_OK_mono. exact Hm. }
  rewrite (entriesGt_eq _ _ _ _ _ tab0 O0).   (* [comment removed for export] *)
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

(* [comment removed for export] *)
Local Open Scope Z_scope.
Definition is_st (i : instr) : bool := match i with Store _ _ _ _ | Sc _ _ _ _ _ _ | Amo _ _ _ _ _ _ _ => true | _ => false end.
Definition sp_of (bc : bctx) (s : sentry) : sprep := match s with SE a w v => mk_sprepB bc (a_base a) (a_off a) (elen w) end.

Definition ranges_apartBrS (bc : bctx) (br1 : option (Z * Z)) (b1 : expr) (k1 n1 : Z) (sp : sprep) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match br1, sp_rng sp with
      | Some (lo1, hi1), Some (lo2, hi2) => (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
      | _, _ => false
      end) then true
  else if (if (Z.leb 0 n2 && Z.ltb n2 two64)%bool then in_sidesB bc (sp_D sp) b1 k1 n1
           else kdisj_apartBX bc (bc_kd bc) (ekeys b1 []) (ekeys b2 []) b1 k1 n1 b2 k2 n2) then true
  else if lin_apartB bc b1 k1 n1 b2 k2 n2 then true
  else lin_apart2B bc b1 k1 n1 b2 k2 n2.

Fixpoint log_lookupBLS (bc : bctx) (obr : option (option (Z * Z))) (log : list sentry) (sps : list sprep) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match log, sps with
  | [], _ => LMiss acc hints
  | SE (SA kb kk) w v :: rest, sp :: sps' =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupBLS bc obr rest sps' rb rk n sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          let br := match obr with Some r => r | None => base_rangeB bc rb end in
          if ranges_apartBrS bc br rb rk (Z.of_nat n) sp kb kk (Z.of_nat w)
          then log_lookupBLS bc (Some br) rest sps' rb rk n sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupBLS bc (Some br) rest sps' rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
          end
      end
  | _ :: _, [] => log_lookupBL bc obr log rb rk n sx hints acc
  end.

Lemma kdisj_apartBX_sym : forall bc ds kb1 kb2 b1 k1 n1 b2 k2 n2,
  kdisj_apartBX bc ds kb1 kb2 b1 k1 n1 b2 k2 n2 = kdisj_apartBX bc ds kb2 kb1 b2 k2 n2 b1 k1 n1.
Proof.
  intros bc ds kb1 kb2 b1 k1 n1 b2 k2 n2. induction ds as [|d rest IH]; [reflexivity|].
  cbn [kdisj_apartBX]. rewrite IH.
  destruct (cand kb1 (kd_k1 d) (kd_l1 d)), (cand kb2 (kd_k2 d) (kd_l2 d)), (cand kb1 (kd_k2 d) (kd_l2 d)), (cand kb2 (kd_k1 d) (kd_l1 d));
  destruct (sub_itvB bc b1 k1 n1 (kd_c1 d) (kd_m1 d)), (sub_itvB bc b2 k2 n2 (kd_c2 d) (kd_m2 d)),
           (sub_itvB bc b1 k1 n1 (kd_c2 d) (kd_m2 d)), (sub_itvB bc b2 k2 n2 (kd_c1 d) (kd_m1 d)); reflexivity.
Qed.

Lemma in_sides_disjBX : forall bc kn b1 k1 n1 b2 k2 n2,
  in_sidesB bc (disj_sidesBX bc (mk_kdx kn) (ekeys b1 []) b1 k1 n1) b2 k2 n2
  = kdisj_apartBX bc (mk_kdx kn) (ekeys b1 []) (ekeys b2 []) b1 k1 n1 b2 k2 n2.
Proof.
  intros bc kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; [reflexivity|].
  destruct K; cbn [mk_kdx]; try exact IH.
  cbn [disj_sidesBX kdisj_apartBX kd_c1 kd_m1 kd_c2 kd_m2 kd_k1 kd_l1 kd_k2 kd_l2].
  rewrite !sub_itvB_guard.
  rewrite (guard2 _ _ _ _ (sub_itvB_guard bc b1 k1 n1 _ _) (sub_itvB_guard bc b2 k2 n2 _ _)).
  rewrite (guard2 _ _ _ _ (sub_itvB_guard bc b1 k1 n1 _ _) (sub_itvB_guard bc b2 k2 n2 _ _)).
  rewrite <- IH.
  destruct (sub_itvB bc b1 k1 n1 a1 n0) eqn:X1, (sub_itvB bc b1 k1 n1 a2 n3) eqn:X2; cbn [in_sidesB];
    destruct (sub_itvB bc b2 k2 n2 a2 n3), (sub_itvB bc b2 k2 n2 a1 n0); reflexivity.
Qed.

Lemma ranges_apartBrS_eq : forall fk br1 b1 k1 n1 b2 k2 (w : nat) (v : expr),
  ranges_apartBrS (mkbc fk) br1 b1 k1 n1 (mk_sprepB (mkbc fk) b2 k2 (elen w)) b2 k2 (Z.of_nat w)
  = ranges_apartBr (mkbc fk) br1 b1 k1 n1 b2 k2 (Z.of_nat w).
Proof.
  intros fk br1 b1 k1 n1 b2 k2 w v. unfold ranges_apartBrS, ranges_apartBr, mk_sprepB. cbn [a_base a_off sp_rng sp_D elen].
  destruct (match br1, base_rangeB (mkbc fk) b2 with
            | Some (lo1, hi1), Some (lo2, hi2) => (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + Z.of_nat w) (lo1 + k1))%bool
            | _, _ => false end); [reflexivity|].
  destruct (Z.leb 0 (Z.of_nat w) && Z.ltb (Z.of_nat w) two64)%bool eqn:Hw; [|reflexivity].
  apply andb_prop in Hw as [Hw1 Hw2]. apply Z.leb_le in Hw1. apply Z.ltb_lt in Hw2.
  replace (zlit64 (Z.of_nat w)) with (Z.of_nat w)
    by (unfold zlit64; replace (Z.leb 0 (Z.of_nat w) && Z.ltb (Z.of_nat w) two64)%bool with true; [reflexivity|];
        symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  change (bc_kd (mkbc fk)) with (mk_kdx fk).
  rewrite in_sides_disjBX, kdisj_apartBX_sym. reflexivity.
Qed.

Lemma log_lookupBLS_eq : forall fk log sps rb rk n sx hints acc obr,
  sps = map (sp_of (mkbc fk)) log ->
  log_lookupBLS (mkbc fk) obr log sps rb rk n sx hints acc = log_lookupBL (mkbc fk) obr log rb rk n sx hints acc.
Proof.
  intros fk log. induction log as [|[[kb kk] w v] rest IH]; intros sps rb rk n sx hints acc obr Hs; [destruct sps; reflexivity|].
  destruct sps as [|sp sps']; [discriminate|]. cbn [map] in Hs. injection Hs as Hsp Hs'.
  cbn [log_lookupBLS log_lookupBL].
  destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)); try reflexivity; [apply IH; exact Hs'|].
  cbv zeta. subst sp. rewrite (ranges_apartBrS_eq fk _ rb rk (Z.of_nat n) kb kk w v).
  destruct (ranges_apartBr (mkbc fk) _ rb rk (Z.of_nat n) kb kk (Z.of_nat w)); [apply IH; exact Hs'|].
  destruct hints as [|[|] hs]; try reflexivity; apply IH; exact Hs'.
Qed.

Section WithSegsS.
Variable segs : list Segment.

Definition sym_readBIS (ss : sym_state) (bc : bctx) (kx : kix) (sps : list sprep) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool) : option (expr * list sidecond * scripts * N) :=
  match log_lookupBLS bc None (s_log ss) sps (a_base a) (a_off a) n sx' (sc_hints scr) [] with
  | LStuck => None
  | LHit v scs hints =>
      Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookupABI bc kx segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extKB bc v, flat_scB bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
      | LMiss scs' hints' =>
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', N.succ i)
      end
  end.
Lemma sym_readBIS_eq : forall fk ss kx sps scr a n sx', sps = map (sp_of (mkbc fk)) (s_log ss) ->
  sym_readBIS ss (mkbc fk) kx sps scr a n sx' = sym_readBI segs ss (mkbc fk) kx scr a n sx'.
Proof. intros. unfold sym_readBIS, sym_readBI. rewrite log_lookupBLS_eq by exact H. reflexivity. Qed.

Definition sym_stepBIS (bc : bctx) (kx : kix) (sps : list sprep) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match i with
  | Load sz sx rd rs imm =>
      let g r := sr_get (s_regs ss) r in
      let p := s_pc ss in
      let n := msize_bytes sz in
      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrKB bc (g rs) (bv_signed imm) in
      match sym_readBIS ss bc kx sps scr a n sx' with
      | None => SStop
      | Some (v, scs, scr', nx') =>
          SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                   (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | _ => sym_stepBI bc kx segs i ss scr
  end.
Lemma sym_stepBIS_eq : forall fk kx sps i ss scr, sps = map (sp_of (mkbc fk)) (s_log ss) ->
  sym_stepBIS (mkbc fk) kx sps i ss scr = sym_stepBI (mkbc fk) kx segs i ss scr.
Proof.
  intros fk kx sps i ss scr Hs. destruct i; try reflexivity.
  unfold sym_stepBIS, sym_stepBI. rewrite sym_readBIS_eq by exact Hs. reflexivity.
Qed.

Definition sym_stepXBIS (bc : bctx) (kx : kix) (sps : list sprep) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match sym_stepBIS bc kx sps i ss scr with
  | SOk ss' scs scr' =>
      if N.leb (s_next ss) (s_next ss')
      then SOk (cap_rd K i ss') (x_filterB segs bc ss ss' scs) scr'
      else SStop
  | SStop => SStop
  end.
Lemma sym_stepXBIS_eq : forall fk kx sps K i ss scr, sps = map (sp_of (mkbc fk)) (s_log ss) ->
  sym_stepXBIS (mkbc fk) kx sps K i ss scr = sym_stepXBI segs (mkbc fk) kx K i ss scr.
Proof. intros. unfold sym_stepXBIS, sym_stepXBI. rewrite sym_stepBIS_eq by exact H. reflexivity. Qed.

Lemma sym_stepBI_log : forall bc kx i ss scr ss' scs scr', is_st i = false ->
  sym_stepBI bc kx segs i ss scr = SOk ss' scs scr' -> s_log ss' = s_log ss.
Proof.
  intros bc kx i ss scr ss' scs scr' Hst H. destruct i; try discriminate Hst; cbn [sym_stepBI] in H; unfold sset, sjump in H;
  repeat match type of H with context [match ?x with _ => _ end] => destruct x end;
  try discriminate H; injection H as <- _ _; reflexivity.
Qed.
Lemma sym_stepBI_log_st : forall bc kx i ss scr ss' scs scr', is_st i = true ->
  sym_stepBI bc kx segs i ss scr = SOk ss' scs scr' -> exists e, s_log ss' = e :: s_log ss.
Proof.
  intros bc kx i ss scr ss' scs scr' Hst H. destruct i; try discriminate Hst; cbn [sym_stepBI] in H; unfold sset, sjump in H;
  repeat match type of H with context [match ?x with _ => _ end] => destruct x end;
  try discriminate H; injection H as <- _ _; eexists; reflexivity.
Qed.
Lemma cap_rd_log : forall K i ss, s_log (cap_rd K i ss) = s_log ss.
Proof. intros K i ss. unfold cap_rd. repeat match goal with |- context [match ?x with _ => _ end] => destruct x end; reflexivity. Qed.

(* [comment removed for export] *)
Definition push_sp (bc : bctx) (tab : list (xkey * xpre)) (i : instr) (log' : list sentry) (sps : list sprep)
  : list sprep * list (xkey * xpre) :=
  if is_st i then
    match log' with
    | SE a w v :: _ => let '(sp, tab1) := mk_sprepBt2 bc tab (a_base a) (a_off a) (elen w) in (sp :: sps, tab1)
    | [] => (sps, tab)
    end
  else (sps, tab).

Fixpoint sym_execTXS_go (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z)
  (ss : sym_state) (sps : list sprep) (tab : list (xkey * xpre)) (ck : sym_state) (cks : list sprep)
  : sym_state * list sprep * list (xkey * xpre) :=
  match fuel with
  | O => if s_clean ss then (ss, sps, tab) else (ck, cks, tab)
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then (ss, sps, tab) else (ck, cks, tab)) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then (ss, sps, tab) else (ck, cks, tab)
      | Some i =>
          match sym_stepXBIS bc kx sps K i ss scr_nil with
          | SOk ss' [] _ =>
              let '(sps', tab') := push_sp bc tab i (s_log ss') sps in
              sym_execTXS_go bc kx t K f false stops ss' sps' tab' (if s_clean ss' then ss' else ck) (if s_clean ss' then sps' else cks)
          | _ => if s_clean ss then (ss, sps, tab) else (ck, cks, tab)
          end
      end
  end.

Lemma push_sp_ok : forall fk kx K i ss scr ss' scs scr' sps tab,
  sps = map (sp_of (mkbc fk)) (s_log ss) -> table_ok (mkbc fk) tab ->
  sym_stepXBI segs (mkbc fk) kx K i ss scr = SOk ss' scs scr' ->
  fst (push_sp (mkbc fk) tab i (s_log ss') sps) = map (sp_of (mkbc fk)) (s_log ss') /\ table_ok (mkbc fk) (snd (push_sp (mkbc fk) tab i (s_log ss') sps)).
Proof.
  intros fk kx K i ss scr ss' scs scr' sps tab Hs Hok H. unfold sym_stepXBI in H.
  destruct (sym_stepBI (mkbc fk) kx segs i ss scr) as [ss1 scs1 scr1|] eqn:E1; [|discriminate].
  destruct (N.leb (s_next ss) (s_next ss1)); [|discriminate]. injection H as <- _ _. rewrite cap_rd_log.
  unfold push_sp. destruct (is_st i) eqn:Hst.
  - destruct (sym_stepBI_log_st _ _ _ _ _ _ _ _ Hst E1) as [e He]. rewrite He. destruct e as [a w v].
    destruct (mk_sprepBt2_eq (mkbc fk) tab (a_base a) (a_off a) (elen w) Hok) as [E O].
    destruct (mk_sprepBt2 (mkbc fk) tab (a_base a) (a_off a) (elen w)) as [sp tab1]. cbn [fst snd] in E, O |- *.
    split; [|exact O]. cbn [map sp_of]. rewrite E, Hs. reflexivity.
  - rewrite (sym_stepBI_log _ _ _ _ _ _ _ _ Hst E1). split; [exact Hs | exact Hok].
Qed.

Lemma sym_execTXS_go_eq : forall t K fuel first stops ss sps tab ck cks,
  sps = map (sp_of (mkbc (facts_of (s_know ss)))) (s_log ss) -> cks = map (sp_of (mkbc (facts_of (s_know ss)))) (s_log ck) ->
  table_ok (mkbc (facts_of (s_know ss))) tab ->
  fst (fst (sym_execTXS_go (mkbc (facts_of (s_know ss))) (mk_kix (s_know ss)) t K fuel first stops ss sps tab ck cks))
    = sym_execTX_go segs t K fuel first stops ss ck
  /\ snd (fst (sym_execTXS_go (mkbc (facts_of (s_know ss))) (mk_kix (s_know ss)) t K fuel first stops ss sps tab ck cks))
    = map (sp_of (mkbc (facts_of (s_know ss)))) (s_log (sym_execTX_go segs t K fuel first stops ss ck))
  /\ table_ok (mkbc (facts_of (s_know ss))) (snd (sym_execTXS_go (mkbc (facts_of (s_know ss))) (mk_kix (s_know ss)) t K fuel first stops ss sps tab ck cks)).
Proof.
  intros t K fuel. induction fuel as [|f IH]; intros first stops ss sps tab ck cks Hs Hcks Hok.
  - cbn [sym_execTXS_go sym_execTX_go]. destruct (s_clean ss); cbn [fst snd]; auto.
  - cbn [sym_execTXS_go sym_execTX_go].
    destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [destruct (s_clean ss); cbn [fst snd]; auto|].
    destruct (itab_lookup t (s_pc ss)) as [i|]; [|destruct (s_clean ss); cbn [fst snd]; auto].
    rewrite (sym_stepXBIS_eq (facts_of (s_know ss))) by exact Hs.
    rewrite <- (sym_stepXBI_eq segs K i ss scr_nil).
    destruct (sym_stepXBI segs (mkbc (facts_of (s_know ss))) (mk_kix (s_know ss)) K i ss scr_nil) as [ss' scs scr'|] eqn:HstB;
      [|destruct (s_clean ss); cbn [fst snd]; auto].
    destruct scs as [|sc scs']; [|destruct (s_clean ss); cbn [fst snd]; auto].
    destruct (push_sp_ok (facts_of (s_know ss)) (mk_kix (s_know ss)) K i ss scr_nil ss' [] scr' sps tab Hs Hok HstB) as [Ep Op].
    destruct (push_sp (mkbc (facts_of (s_know ss))) tab i (s_log ss') sps) as [sps' tab'] eqn:Hp. cbn [fst snd] in Ep, Op.
    assert (Hk' : s_know ss' = s_know ss).
    { pose proof HstB as E. rewrite sym_stepXBI_eq in E. eapply sym_stepX_know. exact E. }
    rewrite <- Hk' in *.
    apply IH; [exact Ep | destruct (s_clean ss'); [exact Ep | exact Hcks] | exact Op].
Qed.
End WithSegsS.

(* [comment removed for export] *)
Fixpoint mk_stxsS (bc : bctx) (log : list sentry) (sps : list sprep) (t : ntab) : list stx * ntab :=
  match log, sps with
  | SE a w v :: older, sp :: sps' =>
      let '(sxs, t1) := mk_stxsS bc older sps' t in
      let '(r, t2) := intern bc t1 (a_base a) in
      let '(bid, bi) := r in
      (sxs ++ [STX a w v sp bid (bi_br bi)], t2)
  | _, _ => mk_stxs bc log t
  end.
Lemma mk_stxsS_eq : forall bc log t, mk_stxsS bc log (map (sp_of bc) log) t = mk_stxs bc log t.
Proof.
  intros bc log t. induction log as [|[a w v] older IH]; [reflexivity|].
  cbn [mk_stxsS mk_stxs map sp_of]. rewrite IH. reflexivity.
Qed.
(* [comment removed for export] *)
Fixpoint tails_fl (sxs : list stx) : list (stx * list stx) :=
  match sxs with [] => [] | sx :: rest => (sx, rest) :: tails_fl rest end.
Fixpoint stores_partM (bc : bctx) (sxs : list stx) : list kentry :=
  match sxs with
  | [] => []
  | sx :: newer => stores_partM bc newer ++ chainKFo bc (tails_fl newer) (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx)))
                                                     (Pos.eqb (sx_bid sx)) (sx_br sx) []
  end.
Lemma chainKF_tails : forall bc l K okb same_of br2, chainKF bc (tails_fl l) K okb same_of br2 = chainK2 bc l K okb same_of br2.
Proof.
  intros bc l. induction l as [|sx rest IH]; intros K okb same_of br2; [reflexivity|].
  cbn [tails_fl chainKF chainK2].
  destruct (prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2); [apply IH | reflexivity].
Qed.
Lemma stores_partM_eq : forall bc sxs, stores_partM bc sxs = stores_part bc sxs.
Proof.
  intros bc sxs. induction sxs as [|sx newer IH]; [reflexivity|].
  cbn [stores_partM stores_part]. rewrite IH, chainKFo_eq by constructor. rewrite chainKF_tails. reflexivity.
Qed.
Lemma stores_partM_eqf : stores_partM = stores_part.
Proof. bcfe. apply stores_partM_eq. Qed.
Definition carryGS (bc : bctx) (log : list sentry) (sps : list sprep) (tab : list (xkey * xpre)) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxsS bc log sps nt_empty in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, t1) := r in
  let gl := mk_gl2 bc t1 (gs_bnds gs) sxs in
  stores_partM bc sxs ++ entriesGt3 bc sxs gl (mk_gl3 gl) kn infos tab.   (* [comment removed for export] *)
Definition carryKS (bc : bctx) (log : list sentry) (sps : list sprep) (tab : list (xkey * xpre)) (kn : list kentry)
  : list kentry * list sidecond * list bool :=
  match log with
  | [] => (kn, [], [])
  | _ => (carryGS bc log sps tab kn, [], [])
  end.
Lemma carryGS_eq : forall kn log tab, table_ok (mkbc (facts_of kn)) tab ->
  carryGS (mkbc (facts_of kn)) log (map (sp_of (mkbc (facts_of kn))) log) tab kn = carryG (mkbc (facts_of kn)) log kn.
Proof.
  intros kn log tab Hok. unfold carryGS, carryG. rewrite mk_stxsS_eq, stores_partM_eqf.   (* [comment removed for export] *)
  destruct (mk_stxst_eq (mkbc (facts_of kn)) log nt_empty [] (Forall_nil _)) as [E0 O0].
  destruct (mk_stxst (mkbc (facts_of kn)) log nt_empty []) as [[sxs t0] tab0]. cbn [fst snd] in E0, O0.
  rewrite <- E0.
  destruct (scan_entries (mkbc (facts_of kn)) kn t0 gst_empty) as [[infos t1] gs] eqn:HSE. cbv zeta.
  rewrite (entriesGt3_eq _ _ _ _ _ tab (scan_entries_kdi _ _ _ _ _ _ _ HSE)).   (* [comment removed for export] *)
  rewrite (entriesGt_eq _ _ _ _ _ tab Hok), (entriesGt_eq _ _ _ _ _ tab0 O0). reflexivity.
Qed.
Lemma carryKS_eq : forall kn log tab, table_ok (mkbc (facts_of kn)) tab ->
  carryKS (mkbc (facts_of kn)) log (map (sp_of (mkbc (facts_of kn))) log) tab kn = carryK (mkbc (facts_of kn)) log kn [].
Proof.
  intros kn log tab Hok. unfold carryKS, carryK. destruct log as [|s older]; [reflexivity|].
  rewrite carryGS_eq by exact Hok. reflexivity.
Qed.

End AX2B.
