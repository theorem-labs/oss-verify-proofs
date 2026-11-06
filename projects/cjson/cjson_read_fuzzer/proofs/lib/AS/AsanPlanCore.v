(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require SymStepR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require CatSim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require MemSplit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require SymExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AxSymExec3.
Module AxSymExec3B.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.SymStepR.CatExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.CatSim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.SymStepR.SeqExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.MemSplit.StoreOk OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.SymExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Unset Lia Cache.
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
  cbn [erange_fB erange_f]. rewrite IH. rewrite ?find_rangeI_mkbc0. reflexivity.
Qed.
#[export] Hint Rewrite erange_fB_eqf0 : bceq.

Lemma erange0B_eqf0 : forall fk fs, erange0B (mkbc0 fk fs) = erange0 fk.
Proof. intros. bcfe. unfold erange0B, erange0. rewrite ?erange_fB_eqf0. reflexivity. Qed.
#[export] Hint Rewrite erange0B_eqf0 : bceq.
Lemma erangeB_eqf0 : forall fk fs, erangeB (mkbc0 fk fs) = erange fk.
Proof. intros. bcfe. unfold erangeB, erange. rewrite ?erange0B_eqf0. reflexivity. Qed.
#[export] Hint Rewrite erangeB_eqf0 : bceq.
Lemma base_rangeB_eqf0 : forall fk fs, base_rangeB (mkbc0 fk fs) = base_range fk.
Proof. intros. bcfe. unfold base_rangeB, base_range. rewrite ?erangeB_eqf0. reflexivity. Qed.
#[export] Hint Rewrite base_rangeB_eqf0 : bceq.
Lemma ealignB_eqf0 : forall fk fs, ealignB (mkbc0 fk fs) = ealign fk.
Proof. intros. bcfe. unfold ealignB, ealign. rewrite ?bc_ffk_mkbc0. reflexivity. Qed.
#[export] Hint Rewrite ealignB_eqf0 : bceq.
Lemma lin_nowrapB_eqf0 : forall fk fs, lin_nowrapB (mkbc0 fk fs) = lin_nowrap fk.
Proof. intros. bcfe. unfold lin_nowrapB, lin_nowrap. rewrite ?erangeB_eqf0. reflexivity. Qed.
#[export] Hint Rewrite lin_nowrapB_eqf0 : bceq.
Lemma srl_expandB_eqf0 : forall fk fs, srl_expandB (mkbc0 fk fs) = srl_expand fk.
Proof.
  intros fk fs. apply functional_extensionality; intros ts. 
  induction ts as [|[k a] rest IH]; intros; bcfe; [reflexivity|].
  cbn [srl_expandB srl_expand]. rewrite IH. rewrite ?ealignB_eqf0, ?lin_nowrapB_eqf0. reflexivity.
Qed.
#[export] Hint Rewrite srl_expandB_eqf0 : bceq.
Lemma fact_nowrapB_eqf0 : forall fk fs, fact_nowrapB (mkbc0 fk fs) = fact_nowrap fk.
Proof. intros. bcfe. unfold fact_nowrapB, fact_nowrap. rewrite ?erangeB_eqf0. reflexivity. Qed.
#[export] Hint Rewrite fact_nowrapB_eqf0 : bceq.
Lemma sum_fact_xB_eqf0 : forall fk fs, sum_fact_xB (mkbc0 fk fs) = sum_fact_x fk.
Proof. intros. bcfe. unfold sum_fact_xB, sum_fact_x. rewrite ?srl_expandB_eqf0. reflexivity. Qed.
#[export] Hint Rewrite sum_fact_xB_eqf0 : bceq.
Lemma sum_factsB_eqf0 : forall fk fs, sum_factsB (mkbc0 fk fs) = sum_facts fk.
Proof.
  intros fk fs. apply functional_extensionality; intros kn. 
  induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [sum_factsB sum_facts]. rewrite IH. rewrite ?fact_nowrapB_eqf0, ?sum_fact_xB_eqf0. reflexivity.
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

Definition lin_ge0B (bc : bctx) (pos neg : xterms) : bool :=
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
  else if novars b2 then (if xinside_numB bc b1 k1 n1 b2 k2 n2 then true
                          else if (lenlit n1 && lenlit n2)%bool then false else xinside0B bc b1 k1 n1 b2 k2 n2)
  else if (novars b1 && negb (lenlit n2))%bool then xinside0B bc b1 k1 n1 b2 k2 n2 else false.   (* [comment removed for export] *)

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
  else if kdisj_apartB bc (bc_fk bc) b1 k1 n1 b2 k2 n2 then true
  else lin_apartB bc b1 k1 n1 b2 k2 n2.

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
    else if kdisj_apart_xB bc (bc_fk bc) b1 k1 n1 b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
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
Proof. intros. bcfe. unfold lin_test_relB, lin_test_rel. rewrite ?bc_fs_mkbc, ?erangeB_eqf. reflexivity. Qed.
#[export] Hint Rewrite lin_test_relB_eqf : bceq.
Lemma lin_testB_eqf : forall fk, lin_testB (mkbc fk) = lin_test fk.
Proof. intros. bcfe. unfold lin_testB, lin_test. rewrite ?erangeB_eqf, ?lin_test_relB_eqf. reflexivity. Qed.
#[export] Hint Rewrite lin_testB_eqf : bceq.
Lemma lin_srangeB_eqf : forall fk, lin_srangeB (mkbc fk) = lin_srange fk.
Proof. intros. bcfe. unfold lin_srangeB, lin_srange. rewrite ?erangeB_eqf, ?srl_expandB_eqf. reflexivity. Qed.
#[export] Hint Rewrite lin_srangeB_eqf : bceq.
Lemma lin_nowrapRB_eqf : forall fk, lin_nowrapRB (mkbc fk) = lin_nowrapR fk.
Proof. intros. bcfe. unfold lin_nowrapRB, lin_nowrapR. rewrite ?srl_expandB_eqf, ?lin_testB_eqf, ?lin_srangeB_eqf. reflexivity. Qed.
#[export] Hint Rewrite lin_nowrapRB_eqf : bceq.
Lemma lin_apart0B_eqf : forall fk, lin_apart0B (mkbc fk) = lin_apart0 fk.
Proof. intros. bcfe. unfold lin_apart0B, lin_apart0. rewrite ?lin_testB_eqf, ?lin_nowrapRB_eqf. reflexivity. Qed.
#[export] Hint Rewrite lin_apart0B_eqf : bceq.
Lemma lin_apartB_eqf : forall fk, lin_apartB (mkbc fk) = lin_apart fk.
Proof. intros. bcfe. unfold lin_apartB, lin_apart. rewrite ?lin_apart0B_eqf. reflexivity. Qed.
#[export] Hint Rewrite lin_apartB_eqf : bceq.
Lemma lin_brangeB_eqf : forall fk, lin_brangeB (mkbc fk) = lin_brange fk.
Proof. intros. bcfe. unfold lin_brangeB, lin_brange. rewrite ?bc_fs_mkbc, ?erangeB_eqf. reflexivity. Qed.
#[export] Hint Rewrite lin_brangeB_eqf : bceq.
Lemma xloB_eqf : forall fk, xloB (mkbc fk) = xlo fk.
Proof. intros. bcfe. unfold xloB, xlo. rewrite ?erangeB_eqf, ?lin_srangeB_eqf, ?lin_brangeB_eqf. reflexivity. Qed.
#[export] Hint Rewrite xloB_eqf : bceq.
Lemma xhiB_eqf : forall fk, xhiB (mkbc fk) = xhi fk.
Proof. intros. bcfe. unfold xhiB, xhi. rewrite ?erangeB_eqf, ?lin_srangeB_eqf, ?lin_brangeB_eqf. reflexivity. Qed.
#[export] Hint Rewrite xhiB_eqf : bceq.
Lemma xt_nowrapB_eqf : forall fk, xt_nowrapB (mkbc fk) = xt_nowrap fk.
Proof.
  intros fk. apply functional_extensionality; intros ts. 
  induction ts as [|[e k] rest IH]; intros; bcfe; [reflexivity|].
  cbn [xt_nowrapB xt_nowrap]. rewrite IH. rewrite ?lin_nowrapRB_eqf. reflexivity.
Qed.
#[export] Hint Rewrite xt_nowrapB_eqf : bceq.
Lemma lin_ge0_scaledB_eqf : forall fk, lin_ge0_scaledB (mkbc fk) = lin_ge0_scaled fk.
Proof. intros. bcfe. unfold lin_ge0_scaledB, lin_ge0_scaled. rewrite ?srl_expandB_eqf, ?lin_testB_eqf. reflexivity. Qed.
#[export] Hint Rewrite lin_ge0_scaledB_eqf : bceq.
Lemma lin_ge0B_eqf : forall fk, lin_ge0B (mkbc fk) = lin_ge0 fk.
Proof. intros. bcfe. unfold lin_ge0B, lin_ge0. rewrite ?srl_expandB_eqf, ?lin_testB_eqf, ?xt_nowrapB_eqf, ?lin_ge0_scaledB_eqf. reflexivity. Qed.
#[export] Hint Rewrite lin_ge0B_eqf : bceq.
Lemma xinside0B_eqf : forall fk, xinside0B (mkbc fk) = xinside0 fk.
Proof. intros. bcfe. unfold xinside0B, xinside0. rewrite ?lin_ge0B_eqf. reflexivity. Qed.
#[export] Hint Rewrite xinside0B_eqf : bceq.
Lemma xinside_numB_eqf : forall fk, xinside_numB (mkbc fk) = xinside_num fk.
Proof. intros. bcfe. unfold xinside_numB, xinside_num. rewrite ?base_rangeB_eqf, ?xloB_eqf, ?xhiB_eqf. reflexivity. Qed.
#[export] Hint Rewrite xinside_numB_eqf : bceq.
Lemma xinsideB_eqf : forall fk, xinsideB (mkbc fk) = xinside fk.
Proof. intros. bcfe. unfold xinsideB, xinside. rewrite ?xinside0B_eqf, ?xinside_numB_eqf. reflexivity. Qed.
#[export] Hint Rewrite xinsideB_eqf : bceq.
Lemma sub_itvB_eqf : forall fk, sub_itvB (mkbc fk) = sub_itv fk.
Proof. intros. bcfe. unfold sub_itvB, sub_itv. rewrite ?xloB_eqf, ?xinsideB_eqf. reflexivity. Qed.
#[export] Hint Rewrite sub_itvB_eqf : bceq.
Lemma kdisj_apartB_eqf : forall fk, kdisj_apartB (mkbc fk) = kdisj_apart fk.
Proof.
  intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2. 
  revert b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kdisj_apartB kdisj_apart]. rewrite IH. rewrite ?sub_itvB_eqf. reflexivity.
Qed.
#[export] Hint Rewrite kdisj_apartB_eqf : bceq.
Lemma ranges_apartB_eqf : forall fk, ranges_apartB (mkbc fk) = ranges_apart fk.
Proof. intros. bcfe. unfold ranges_apartB, ranges_apart. rewrite ?bc_fk_mkbc, ?base_rangeB_eqf, ?lin_apartB_eqf, ?kdisj_apartB_eqf. reflexivity. Qed.
#[export] Hint Rewrite ranges_apartB_eqf : bceq.
Lemma sub_itv_xB_eqf : forall fk, sub_itv_xB (mkbc fk) = sub_itv_x fk.
Proof. intros. bcfe. unfold sub_itv_xB, sub_itv_x. rewrite ?xinsideB_eqf. reflexivity. Qed.
#[export] Hint Rewrite sub_itv_xB_eqf : bceq.
Lemma kdisj_apart_xB_eqf : forall fk, kdisj_apart_xB (mkbc fk) = kdisj_apart_x fk.
Proof.
  intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2. 
  revert b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kdisj_apart_xB kdisj_apart_x]. rewrite IH. rewrite ?sub_itv_xB_eqf. reflexivity.
Qed.
#[export] Hint Rewrite kdisj_apart_xB_eqf : bceq.
Lemma end_hiB_eqf : forall fk, end_hiB (mkbc fk) = end_hi fk.
Proof. intros. bcfe. unfold end_hiB, end_hi. rewrite ?find_rangeI_mkbc. reflexivity. Qed.
#[export] Hint Rewrite end_hiB_eqf : bceq.
Lemma ranges_apart_xB_eqf : forall fk, ranges_apart_xB (mkbc fk) = ranges_apart_x fk.
Proof. intros. bcfe. unfold ranges_apart_xB, ranges_apart_x. rewrite ?bc_fk_mkbc, ?base_rangeB_eqf, ?xhiB_eqf, ?lin_ge0B_eqf, ?ranges_apartB_eqf, ?kdisj_apart_xB_eqf, ?end_hiB_eqf. reflexivity. Qed.
#[export] Hint Rewrite ranges_apart_xB_eqf : bceq.
Lemma disj_sidesB_eqf : forall fk, disj_sidesB (mkbc fk) = disj_sides fk.
Proof.
  intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1. 
  revert b1 k1 n1. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [disj_sidesB disj_sides]. rewrite IH. rewrite ?sub_itvB_eqf. reflexivity.
Qed.
#[export] Hint Rewrite disj_sidesB_eqf : bceq.
Lemma disj_sides_xB_eqf : forall fk, disj_sides_xB (mkbc fk) = disj_sides_x fk.
Proof.
  intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1. 
  revert b1 k1 n1. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [disj_sides_xB disj_sides_x]. rewrite IH. rewrite ?sub_itv_xB_eqf. reflexivity.
Qed.
#[export] Hint Rewrite disj_sides_xB_eqf : bceq.
Lemma in_sidesB_eqf : forall fk, in_sidesB (mkbc fk) = in_sides fk.
Proof.
  intros fk. apply functional_extensionality; intros D. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2. 
  revert b2 k2 n2. induction D as [|[c m] rest IH]; intros; bcfe; [reflexivity|].
  cbn [in_sidesB in_sides]. rewrite IH. rewrite ?sub_itvB_eqf. reflexivity.
Qed.
#[export] Hint Rewrite in_sidesB_eqf : bceq.
Lemma in_sides_xB_eqf : forall fk, in_sides_xB (mkbc fk) = in_sides_x fk.
Proof.
  intros fk. apply functional_extensionality; intros D. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2. 
  revert b2 k2 n2. induction D as [|[c m] rest IH]; intros; bcfe; [reflexivity|].
  cbn [in_sides_xB in_sides_x]. rewrite IH. rewrite ?sub_itv_xB_eqf. reflexivity.
Qed.
#[export] Hint Rewrite in_sides_xB_eqf : bceq.
Lemma mk_sprepB_eqf : forall fk, mk_sprepB (mkbc fk) = mk_sprep fk.
Proof. intros. bcfe. unfold mk_sprepB, mk_sprep. rewrite ?bc_fk_mkbc, ?base_rangeB_eqf, ?xhiB_eqf, ?disj_sidesB_eqf, ?disj_sides_xB_eqf. reflexivity. Qed.
#[export] Hint Rewrite mk_sprepB_eqf : bceq.
Lemma ranges_apart_pB_eqf : forall fk, ranges_apart_pB (mkbc fk) = ranges_apart_p fk.
Proof. intros. bcfe. unfold ranges_apart_pB, ranges_apart_p. rewrite ?base_rangeB_eqf, ?lin_apartB_eqf, ?xhiB_eqf, ?lin_ge0B_eqf, ?end_hiB_eqf, ?in_sidesB_eqf, ?in_sides_xB_eqf. reflexivity. Qed.
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
      match know_lookupAB bc segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
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
          SOk (SSR (p + 4) (s_regs ss) (log_push a n (g rs2) (s_log ss)) (s_know ss) (s_next ss) r')
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
                       (log_push a n (g rs2) (s_log ss)) (s_know ss) (s_next ss) None)
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
                             (log_push a n (amo_newvalB bc wd aop vold (g rs2)) (s_log ss)) (s_know ss) nx' r')
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

Definition sym_readBI (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match log_lookupB bc (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
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
          SOk (SSR (p + 4) (s_regs ss) (log_push a n (g rs2) (s_log ss)) (s_know ss) (s_next ss) r')
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
                       (log_push a n (g rs2) (s_log ss)) (s_know ss) (s_next ss) None)
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
                             (log_push a n (amo_newvalB bc wd aop vold (g rs2)) (s_log ss)) (s_know ss) nx' r')
                        (scs ++ storeok_scB bc a n) scr'
                end
            end
          else SStop
      end
  | _ => SStop
  end.


Lemma sym_readBI_eqf : forall segs ss bc, sym_readBI segs ss bc (mk_kix (s_know ss)) = sym_readB segs ss bc.
Proof. intros. bcfe. unfold sym_readBI, sym_readB. rewrite know_lookupABI_eq. reflexivity. Qed.
Lemma sym_stepBI_eq : forall bc segs i ss scr,
  sym_stepBI bc (mk_kix (s_know ss)) segs i ss scr = sym_stepB bc segs i ss scr.
Proof. intros. unfold sym_stepBI, sym_stepB. rewrite sym_readBI_eqf. reflexivity. Qed.

Lemma coeffs_divkB_eqf : forall fk, coeffs_divkB (mkbc fk) = coeffs_divk fk.
Proof.
  intros fk. apply functional_extensionality; intros m. apply functional_extensionality; intros ts. 
  induction ts as [|[k a] rest IH]; intros; bcfe; [reflexivity|].
  cbn [coeffs_divkB coeffs_divk]. rewrite IH. rewrite ?ealignB_eqf. reflexivity.
Qed.
#[export] Hint Rewrite coeffs_divkB_eqf : bceq.
Lemma lin_lowbits_knB_eqf : forall fk, lin_lowbits_knB (mkbc fk) = lin_lowbits_kn fk.
Proof. intros. bcfe. unfold lin_lowbits_knB, lin_lowbits_kn. rewrite ?coeffs_divkB_eqf. reflexivity. Qed.
#[export] Hint Rewrite lin_lowbits_knB_eqf : bceq.
Lemma lin_nowrap_lB_eqf : forall fk, lin_nowrap_lB (mkbc fk) = lin_nowrap_l fk.
Proof. intros. bcfe. unfold lin_nowrap_lB, lin_nowrap_l. rewrite ?erangeB_eqf. reflexivity. Qed.
#[export] Hint Rewrite lin_nowrap_lB_eqf : bceq.
Lemma mkSrlB_eqf : forall fk, mkSrlB (mkbc fk) = mkSrl fk.
Proof. intros. bcfe. unfold mkSrlB, mkSrl. rewrite ?erangeB_eqf, ?lin_nowrapB_eqf, ?lin_nowrap_lB_eqf. reflexivity. Qed.
#[export] Hint Rewrite mkSrlB_eqf : bceq.
Lemma lowbitsB_eqf : forall fk, lowbitsB (mkbc fk) = lowbits fk.
Proof.
  intros fk. apply functional_extensionality; intros e.
  induction e; bcfe; cbn [lowbitsB lowbits]; rewrite ?IHe1, ?IHe2, ?IHe; rewrite ?ealignB_eqf, ?lin_lowbits_knB_eqf; reflexivity.
Qed.
#[export] Hint Rewrite lowbitsB_eqf : bceq.
Lemma lsplit_divB_eqf : forall fk, lsplit_divB (mkbc fk) = lsplit_div fk.
Proof.
  intros fk. apply functional_extensionality; intros m. apply functional_extensionality; intros ts. 
  induction ts as [|[k a] rest IH]; intros; bcfe; [reflexivity|].
  cbn [lsplit_divB lsplit_div]. rewrite IH. rewrite ?ealignB_eqf. reflexivity.
Qed.
#[export] Hint Rewrite lsplit_divB_eqf : bceq.
Lemma and_high_splitB_eqf : forall fk, and_high_splitB (mkbc fk) = and_high_split fk.
Proof. intros. bcfe. unfold and_high_splitB, and_high_split. rewrite ?erangeB_eqf. reflexivity. Qed.
#[export] Hint Rewrite and_high_splitB_eqf : bceq.
Lemma and_low_splitB_eqf : forall fk, and_low_splitB (mkbc fk) = and_low_split fk.
Proof. intros. bcfe. unfold and_low_splitB, and_low_split. rewrite ?erangeB_eqf. reflexivity. Qed.
#[export] Hint Rewrite and_low_splitB_eqf : bceq.
Lemma narrow_maskB_eqf : forall fk, narrow_maskB (mkbc fk) = narrow_mask fk.
Proof. intros. bcfe. unfold narrow_maskB, narrow_mask. rewrite ?xhiB_eqf. reflexivity. Qed.
#[export] Hint Rewrite narrow_maskB_eqf : bceq.
Lemma mkAnd0B_eqf : forall fk, mkAnd0B (mkbc fk) = mkAnd0 fk.
Proof. intros. bcfe. unfold mkAnd0B, mkAnd0. rewrite ?ealignB_eqf, ?coeffs_divkB_eqf, ?lin_lowbits_knB_eqf, ?mkSrlB_eqf, ?lowbitsB_eqf, ?lsplit_divB_eqf, ?and_high_splitB_eqf, ?and_low_splitB_eqf. reflexivity. Qed.
#[export] Hint Rewrite mkAnd0B_eqf : bceq.
Lemma mkAndB_eqf : forall fk, mkAndB (mkbc fk) = mkAnd fk.
Proof. intros. bcfe. unfold mkAndB, mkAnd. rewrite ?narrow_maskB_eqf, ?mkAnd0B_eqf. reflexivity. Qed.
#[export] Hint Rewrite mkAndB_eqf : bceq.
Lemma mkAndKB_eqf : forall fk, mkAndKB (mkbc fk) = mkAndK fk.
Proof. intros. bcfe. unfold mkAndKB, mkAndK. rewrite ?mkAndB_eqf. reflexivity. Qed.
#[export] Hint Rewrite mkAndKB_eqf : bceq.
Lemma or_disjointB_eqf : forall fk, or_disjointB (mkbc fk) = or_disjoint fk.
Proof. intros. bcfe. unfold or_disjointB, or_disjoint. rewrite ?erangeB_eqf, ?ealignB_eqf. reflexivity. Qed.
#[export] Hint Rewrite or_disjointB_eqf : bceq.
Lemma mkOrB_eqf : forall fk, mkOrB (mkbc fk) = mkOr fk.
Proof. intros. bcfe. unfold mkOrB, mkOr. rewrite ?mkAndKB_eqf, ?or_disjointB_eqf. reflexivity. Qed.
#[export] Hint Rewrite mkOrB_eqf : bceq.
Lemma conc_tryB_eqf : forall fk, conc_tryB (mkbc fk) = conc_try fk.
Proof.
  intros fk. apply functional_extensionality; intros e. apply functional_extensionality; intros cands. 
  induction cands as [|s rest IH]; intros; bcfe; [reflexivity|].
  cbn [conc_tryB conc_try]. rewrite IH. rewrite ?erangeB_eqf. reflexivity.
Qed.
#[export] Hint Rewrite conc_tryB_eqf : bceq.
Lemma concretizeB_eqf : forall fk, concretizeB (mkbc fk) = concretize fk.
Proof. intros. bcfe. unfold concretizeB, concretize. rewrite ?conc_tryB_eqf. reflexivity. Qed.
#[export] Hint Rewrite concretizeB_eqf : bceq.
Lemma foldKB_eqf : forall fk, foldKB (mkbc fk) = foldK fk.
Proof. intros. bcfe. unfold foldKB, foldK. rewrite ?erangeB_eqf, ?concretizeB_eqf. reflexivity. Qed.
#[export] Hint Rewrite foldKB_eqf : bceq.
Lemma lin_branchB_eqf : forall fk, lin_branchB (mkbc fk) = lin_branch fk.
Proof. intros. bcfe. unfold lin_branchB, lin_branch. rewrite ?erangeB_eqf, ?lin_ge0B_eqf. reflexivity. Qed.
#[export] Hint Rewrite lin_branchB_eqf : bceq.
Lemma decide_branchB_eqf : forall fk, decide_branchB (mkbc fk) = decide_branch fk.
Proof. intros. bcfe. unfold decide_branchB, decide_branch. rewrite ?erangeB_eqf, ?lin_branchB_eqf. reflexivity. Qed.
#[export] Hint Rewrite decide_branchB_eqf : bceq.
Lemma mkSltB_eqf : forall fk, mkSltB (mkbc fk) = mkSlt fk.
Proof. intros. bcfe. unfold mkSltB, mkSlt. rewrite ?decide_branchB_eqf. reflexivity. Qed.
#[export] Hint Rewrite mkSltB_eqf : bceq.
Lemma mkAluK0B_eqf : forall fk, mkAluK0B (mkbc fk) = mkAluK0 fk.
Proof. intros. bcfe. unfold mkAluK0B, mkAluK0. rewrite ?mkSrlB_eqf, ?mkAndB_eqf, ?mkAndKB_eqf, ?mkOrB_eqf, ?mkSltB_eqf. reflexivity. Qed.
#[export] Hint Rewrite mkAluK0B_eqf : bceq.
Lemma mkAluKB_eqf : forall fk, mkAluKB (mkbc fk) = mkAluK fk.
Proof. intros. bcfe. unfold mkAluKB, mkAluK. rewrite ?foldKB_eqf, ?mkAluK0B_eqf. reflexivity. Qed.
#[export] Hint Rewrite mkAluKB_eqf : bceq.
Lemma mkMdKB_eqf : forall fk, mkMdKB (mkbc fk) = mkMdK fk.
Proof. intros. bcfe. unfold mkMdKB, mkMdK. rewrite ?mkAluKB_eqf. reflexivity. Qed.
#[export] Hint Rewrite mkMdKB_eqf : bceq.
Lemma zband32B_eqf : forall fk, zband32B (mkbc fk) = zband32 fk.
Proof. intros. bcfe. unfold zband32B, zband32. rewrite ?erangeB_eqf. reflexivity. Qed.
#[export] Hint Rewrite zband32B_eqf : bceq.
Lemma mkAluwK0B_eqf : forall fk, mkAluwK0B (mkbc fk) = mkAluwK0 fk.
Proof. intros. bcfe. unfold mkAluwK0B, mkAluwK0. rewrite ?erangeB_eqf, ?zband32B_eqf. reflexivity. Qed.
#[export] Hint Rewrite mkAluwK0B_eqf : bceq.
Lemma mkAluwKB_eqf : forall fk, mkAluwKB (mkbc fk) = mkAluwK fk.
Proof. intros. bcfe. unfold mkAluwKB, mkAluwK. rewrite ?foldKB_eqf, ?mkAluwK0B_eqf. reflexivity. Qed.
#[export] Hint Rewrite mkAluwKB_eqf : bceq.
Lemma extK0B_eqf : forall fk, extK0B (mkbc fk) = extK0 fk.
Proof. intros. bcfe. unfold extK0B, extK0. rewrite ?erangeB_eqf. reflexivity. Qed.
#[export] Hint Rewrite extK0B_eqf : bceq.
Lemma extKB_eqf : forall fk, extKB (mkbc fk) = extK fk.
Proof. intros. bcfe. unfold extKB, extK. rewrite ?foldKB_eqf, ?extK0B_eqf. reflexivity. Qed.
#[export] Hint Rewrite extKB_eqf : bceq.
Lemma flat_scB_eqf : forall fk, flat_scB (mkbc fk) = flat_sc fk.
Proof. intros. bcfe. unfold flat_scB, flat_sc. rewrite ?base_rangeB_eqf. reflexivity. Qed.
#[export] Hint Rewrite flat_scB_eqf : bceq.
Lemma wr_coveredB_eqf : forall fk, wr_coveredB (mkbc fk) = wr_covered fk.
Proof.
  intros fk. apply functional_extensionality; intros kn. 
  induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [wr_coveredB wr_covered]. rewrite IH. rewrite ?xloB_eqf, ?xinsideB_eqf. reflexivity.
Qed.
#[export] Hint Rewrite wr_coveredB_eqf : bceq.
Lemma storeok_scB_eqf : forall fk, storeok_scB (mkbc fk) = storeok_sc fk.
Proof. intros. bcfe. unfold storeok_scB, storeok_sc. rewrite ?bc_fk_mkbc, ?wr_coveredB_eqf. reflexivity. Qed.
#[export] Hint Rewrite storeok_scB_eqf : bceq.
Lemma conc_exprB_eqf : forall fk, conc_exprB (mkbc fk) = conc_expr fk.
Proof. intros. bcfe. unfold conc_exprB, conc_expr. rewrite ?concretizeB_eqf. reflexivity. Qed.
#[export] Hint Rewrite conc_exprB_eqf : bceq.
Lemma enum_branchB_eqf : forall fk, enum_branchB (mkbc fk) = enum_branch fk.
Proof. intros. bcfe. unfold enum_branchB, enum_branch. rewrite ?concretizeB_eqf. reflexivity. Qed.
#[export] Hint Rewrite enum_branchB_eqf : bceq.
Lemma to_saddrKB_eqf : forall fk, to_saddrKB (mkbc fk) = to_saddrK fk.
Proof. intros. bcfe. unfold to_saddrKB, to_saddrK. rewrite ?concretizeB_eqf. reflexivity. Qed.
#[export] Hint Rewrite to_saddrKB_eqf : bceq.
Lemma amo_alignedbB_eqf : forall fk, amo_alignedbB (mkbc fk) = amo_alignedb fk.
Proof. intros. bcfe. unfold amo_alignedbB, amo_alignedb. rewrite ?lin_lowbits_knB_eqf. reflexivity. Qed.
#[export] Hint Rewrite amo_alignedbB_eqf : bceq.
Lemma amo_newvalB_eqf : forall fk, amo_newvalB (mkbc fk) = amo_newval fk.
Proof. intros. bcfe. unfold amo_newvalB, amo_newval. rewrite ?mkAluKB_eqf, ?mkAluwKB_eqf. reflexivity. Qed.
#[export] Hint Rewrite amo_newvalB_eqf : bceq.
Lemma log_lookupB_eqf : forall fk, log_lookupB (mkbc fk) = log_lookup fk.
Proof.
  intros fk. apply functional_extensionality; intros log. 
  induction log as [|[[kb kk] w v] rest IH]; intros; bcfe; [reflexivity|].
  cbn [log_lookupB log_lookup]. rewrite IH. rewrite ?ranges_apartB_eqf. reflexivity.
Qed.
#[export] Hint Rewrite log_lookupB_eqf : bceq.
Lemma know_lookupA0B_eqf : forall fk, know_lookupA0B (mkbc fk) = know_lookupA0 fk.
Proof.
  intros fk. apply functional_extensionality; intros segs. apply functional_extensionality; intros kn. 
  induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [know_lookupA0B know_lookupA0]. rewrite IH. rewrite ?erangeB_eqf, ?xinsideB_eqf. reflexivity.
Qed.
#[export] Hint Rewrite know_lookupA0B_eqf : bceq.
Lemma know_lookupAB_eqf : forall fk, know_lookupAB (mkbc fk) = know_lookupA fk.
Proof. intros. bcfe. unfold know_lookupAB, know_lookupA. rewrite ?know_lookupA0B_eqf. reflexivity. Qed.
#[export] Hint Rewrite know_lookupAB_eqf : bceq.
Lemma sym_readB_eqf : forall fk segs ss, sym_readB segs ss (mkbc fk) = sym_read segs ss fk.
Proof. intros. bcfe. unfold sym_readB, sym_read. rewrite ?extKB_eqf, ?flat_scB_eqf, ?log_lookupB_eqf, ?know_lookupAB_eqf. reflexivity. Qed.
#[export] Hint Rewrite sym_readB_eqf : bceq.
Lemma know_lookupB_eqf : forall fk segs, know_lookupB segs (mkbc fk) = know_lookup segs fk.
Proof. intros. bcfe. unfold know_lookupB, know_lookup. rewrite ?bc_fk_mkbc, ?know_lookupAB_eqf. reflexivity. Qed.
#[export] Hint Rewrite know_lookupB_eqf : bceq.

Lemma sym_stepB_eq : forall segs i ss scr,
  sym_stepB (mkbc (facts_of (s_know ss))) segs i ss scr = sym_step segs i ss scr.
Proof. intros. unfold sym_stepB, sym_step. rewrite ?decide_branchB_eqf, ?mkAluKB_eqf, ?mkMdKB_eqf, ?mkAluwKB_eqf, ?flat_scB_eqf, ?storeok_scB_eqf, ?conc_exprB_eqf, ?enum_branchB_eqf, ?to_saddrKB_eqf, ?amo_alignedbB_eqf, ?amo_newvalB_eqf, ?sym_readB_eqf. reflexivity. Qed.
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
  (match len with
   | ELit l0 => match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2 ^ 64)%Z with RInside _ => true | _ => false end
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
      && Nat.eqb j (s_next ss) && Nat.ltb j (s_next ss') && evars_lt (s_next ss) (a_base a)
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
      if Nat.leb (s_next ss) (s_next ss')            (* [comment removed for export] *)
      then SOk (cap_rd K i ss') (x_filterB bc ss ss' scs) scr'
      else SStop
  | SStop => SStop
  end.


Lemma zf_coversB_eqf : forall fk, zf_coversB (mkbc fk) = zf_covers fk.
Proof. intros. bcfe. unfold zf_coversB, zf_covers. rewrite ?xinsideB_eqf. reflexivity. Qed.
#[local] Hint Rewrite zf_coversB_eqf : bceq.
Lemma kentry_overlayB_eqf : forall fk, kentry_overlayB (mkbc fk) = kentry_overlay fk.
Proof. intros. bcfe. unfold kentry_overlayB, kentry_overlay. rewrite ?zf_coversB_eqf. reflexivity. Qed.
#[local] Hint Rewrite kentry_overlayB_eqf : bceq.
Lemma kentry_readableB_eqf : forall fk, kentry_readableB (mkbc fk) = kentry_readable fk.
Proof. intros. bcfe. unfold kentry_readableB, kentry_readable. rewrite ?kentry_overlayB_eqf. reflexivity. Qed.
#[local] Hint Rewrite kentry_readableB_eqf : bceq.
Lemma kn_readableB_eqf : forall fk, kn_readableB (mkbc fk) = kn_readable segs fk.
Proof. intros. bcfe. unfold kn_readableB, kn_readable. rewrite ?kentry_readableB_eqf. reflexivity. Qed.
#[local] Hint Rewrite kn_readableB_eqf : bceq.
Lemma kn_overlayB_eqf : forall fk, kn_overlayB (mkbc fk) = kn_overlay segs fk.
Proof. intros. bcfe. unfold kn_overlayB, kn_overlay. rewrite ?kentry_overlayB_eqf. reflexivity. Qed.
#[local] Hint Rewrite kn_overlayB_eqf : bceq.

Lemma x_dischargeableB_eq : forall ss ss' rb sc,
  x_dischargeableB (mkbc (facts_of (s_know ss))) ss ss' rb sc = x_dischargeable segs ss ss' rb sc.
Proof. intros. unfold x_dischargeableB, x_dischargeable. rewrite ?bc_fk_mkbc. reflexivity. Qed.
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
Proof. intros. bcfe. unfold kcutB, kcut. rewrite ?lin_ge0B_eqf. reflexivity. Qed.
#[export] Hint Rewrite kcutB_eqf : bceq.
Lemma kzero_cutB_eqf : forall fk, kzero_cutB (mkbc fk) = kzero_cut fk.
Proof. intros. bcfe. unfold kzero_cutB, kzero_cut. rewrite ?kcutB_eqf. reflexivity. Qed.
#[export] Hint Rewrite kzero_cutB_eqf : bceq.
Lemma kfill_cutB_eqf : forall fk, kfill_cutB (mkbc fk) = (fun c => kfill_cut c fk).
Proof. intros. bcfe. unfold kfill_cutB, kfill_cut. rewrite ?kcutB_eqf. reflexivity. Qed.
#[export] Hint Rewrite kfill_cutB_eqf : bceq.
Lemma kunk_cutB_eqf : forall fk, kunk_cutB (mkbc fk) = kunk_cut fk.
Proof. intros. bcfe. unfold kunk_cutB, kunk_cut. rewrite ?kcutB_eqf. reflexivity. Qed.
#[export] Hint Rewrite kunk_cutB_eqf : bceq.
Lemma prune_zfB_eqf : forall fk, prune_zfB (mkbc fk) = (fun mk => prune_zf mk fk).
Proof. intros. bcfe. unfold prune_zfB, prune_zf. rewrite ?kcutB_eqf. reflexivity. Qed.
#[export] Hint Rewrite prune_zfB_eqf : bceq.
Lemma prune1pB_eqf : forall fk, prune1pB (mkbc fk) = prune1p fk.
Proof. intros. bcfe. unfold prune1pB, prune1p. rewrite ?ranges_apart_pB_eqf, ?prune_zfB_eqf. reflexivity. Qed.
#[export] Hint Rewrite prune1pB_eqf : bceq.
Lemma ranges_apart_pcB_eqf : forall fk, ranges_apart_pcB (mkbc fk) = ranges_apart_pc fk.
Proof. intros. bcfe. unfold ranges_apart_pcB, ranges_apart_pc. rewrite ?lin_apartB_eqf, ?xhiB_eqf, ?lin_ge0B_eqf, ?end_hiB_eqf, ?in_sidesB_eqf, ?in_sides_xB_eqf. reflexivity. Qed.
#[export] Hint Rewrite ranges_apart_pcB_eqf : bceq.
Lemma prune1pcB_eqf : forall fk, prune1pcB (mkbc fk) = prune1pc fk.
Proof. intros. bcfe. unfold prune1pcB, prune1pc. rewrite ?kzero_cutB_eqf, ?kfill_cutB_eqf, ?kunk_cutB_eqf, ?prune1pB_eqf, ?ranges_apart_pcB_eqf. reflexivity. Qed.
#[export] Hint Rewrite prune1pcB_eqf : bceq.
Lemma prunepcB_eqf : forall fk, prunepcB (mkbc fk) = prunepc fk.
Proof.
  intros fk. apply functional_extensionality; intros sp. apply functional_extensionality; intros wa. apply functional_extensionality; intros w. apply functional_extensionality; intros wv. apply functional_extensionality; intros kn. 
  induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [prunepcB prunepc]. rewrite IH. rewrite ?base_rangeB_eqf, ?prune1pcB_eqf. reflexivity.
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
  rewrite ?mk_sprepB_eqf, ?prunepcB_eqf. reflexivity.
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
      | _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl (kcutB bc mk wb k (elen w) kb kk len)
      end
    else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk len then PKeep
    else match kcutB bc mk wb k (elen w) kb kk len with
         | [] => if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk len then PKeep else PRepl []
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
        | ELit l0 => let l := (l0 mod 2 ^ 64)%Z in
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
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    cbn [kbase] in H; try subst same; unfold prune1pcK, prune1pc, prune1p, prune_zf, kzero_cut, kfill_cut, kunk_cut;
    rewrite ?ranges_apart_pB_eqf, ?kcutB_eqf, ?ranges_apart_pcB_eqf; cbn [a_base a_off]; pk_crush.
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
  apply functional_extensionality; intros K. unfold g1cB, obrB. rewrite Hsp. rewrite ?base_rangeB_eqf, ?mk_sprepB_eqf, ?prune1pcB_eqf.
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
  { rewrite ?prune1pcB_eqf. destruct (kbase K) as [kb|] eqn:HB.
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
  { rewrite ?prune1pcB_eqf. unfold obrB. rewrite <- Hokb. destruct okb as [kb|].
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
  let g := Z.shiftr kk 8 in Z.to_pos (if Z.leb 0 g then 2 * g + 1 else - (2 * g))%Z.   (* [comment removed for export] *)
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
Fixpoint hull_in_sides (bc : bctx) (D : list (saddr * expr)) (kb : expr) (glo ghi : Z) : bool :=
  match D with
  | [] => false
  | (c, m) :: r =>
      if (if expr_eqb kb (a_base c) then
            (if Z.leb (a_off c) glo then match xloB bc m with Some ml => Z.leb ghi (a_off c + ml) | None => false end else false)
          else false)
      then true else hull_in_sides bc r kb glo ghi
  end.
Definition dverdict (bc : bctx) (t : ntab) (sx : stx) (g : gval) : bool :=
  match g with
  | (b, _, (glo, ghi)) =>
      if Pos.eqb b (sx_bid sx) then false else
      match pt_get (nt_info t) b with
      | Some bi => match bi_base bi with
                   | ELit _ => false
                   | kb => hull_in_sides bc (sp_D (sx_sp sx)) kb glo ghi
                   end
      | None => false
      end
  end.
Definition verdict2 (bc : bctx) (t : ntab) (sx : stx) (g : gval) : bool :=
  if verdict sx g then true else dverdict bc t sx g.
(* [comment removed for export] *)
Fixpoint mk_flv (vf : stx -> bool) (sxs : list stx) : list (stx * list stx) :=
  match sxs with
  | [] => []
  | sx :: rest => if vf sx then mk_flv vf rest else (sx, rest) :: mk_flv vf rest
  end.
Definition mk_fl (bc : bctx) (t : ntab) (g : gval) (sxs : list stx) : list (stx * list stx) :=
  mk_flv (fun sx => verdict2 bc t sx g) sxs.
(* [comment removed for export] *)
Definition sverdict (sx : stx) (g : gval) : bool :=
  match g with
  | (b, _, (glo, ghi)) =>
      if Pos.eqb b (sx_bid sx) then
        (if Nat.leb (sx_w sx) 8 then
           (if Z.leb ghi (a_off (sx_a sx)) then true else Z.leb (a_off (sx_a sx) + Z.of_nat (sx_w sx)) glo)
         else false)
      else false
  end.
Definition verdictW (bc : bctx) (t : ntab) (sx : stx) (g : gval) : bool :=
  if verdict2 bc t sx g then true else sverdict sx g.
Definition kword_small (K : kentry) : bool := match K with KWord _ w' _ => Nat.leb w' 8 | _ => false end.
Definition gfl : Type := (gval * list (stx * list stx) * list (stx * list stx))%type.
Definition mk_gl (bc : bctx) (t : ntab) (bnds : gtab) (sxs : list stx) : ptree gfl :=
  pt_map (fun g => let fl := mk_fl bc t g sxs in
                   (g, fl, List.filter (fun p => negb (sverdict (fst p) g)) fl)) bnds.

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
           | Some (g, fl, flw) => if inb g ei then chainKF bc (if kword_small K then flw else fl) K okb same_of br2
                                  else chainK2 bc sxs K okb same_of br2
           | None => chainK2 bc sxs K okb same_of br2
           end
       | None => chainK2 bc sxs K None (fun _ => false) None
       end) ++ entriesG bc sxs gl rest irest
  | _, _ => []
  end.

Definition carryG (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxs bc log nt_empty in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, t1) := r in
  stores_part bc sxs ++ entriesG bc sxs (mk_gl bc t1 (gs_bnds gs) sxs) kn infos.

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
  cbn [kdescr] in HD. destruct (Z.ltb (hi - lo) (2 ^ 64)) eqn:Hlt; [|discriminate]. injection HD as <-.
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
Lemma hull_in_sides_member : forall bc D kb glo ghi kk m,
  hull_in_sides bc D kb glo ghi = true -> (glo <= kk)%Z -> (kk + m <= ghi)%Z ->
  in_sidesB bc D kb kk m = true.
Proof.
  intros bc D kb glo ghi kk m. induction D as [|[c ml] r IH]; intros H Hlo Hhi; cbn [hull_in_sides in_sidesB] in *; [discriminate|].
  destruct (expr_eqb kb (a_base c)) eqn:Eb; [|destruct (sub_itvB bc kb kk m c ml); [reflexivity|exact (IH H Hlo Hhi)]].
  destruct (Z.leb (a_off c) glo) eqn:El; [|destruct (sub_itvB bc kb kk m c ml); [reflexivity|exact (IH H Hlo Hhi)]].
  destruct (xloB bc ml) as [l|] eqn:Ex; [|destruct (sub_itvB bc kb kk m c ml); [reflexivity|exact (IH H Hlo Hhi)]].
  destruct (Z.leb ghi (a_off c + l)) eqn:Eh; [|destruct (sub_itvB bc kb kk m c ml); [reflexivity|exact (IH H Hlo Hhi)]].
  apply Z.leb_le in El. apply Z.leb_le in Eh.
  unfold sub_itvB. rewrite Eb, Ex.
  replace (Z.leb (a_off c) kk) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
  replace (Z.leb (kk + m) (a_off c + l)) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ranges_apart_pcB_sides : forall bc sp b1 k1 z1 br2 b2 k2 z2,
  in_sidesB bc (sp_D sp) b2 k2 (zlit64 z2) = true ->
  ranges_apart_pcB bc sp b1 k1 (ELit z1) br2 b2 k2 (ELit z2) = true.
Proof.
  intros bc sp b1 k1 z1 br2 b2 k2 z2 H. unfold ranges_apart_pcB. rewrite H.
  repeat match goal with |- (if ?c then true else _) = true => destruct c; [reflexivity|] end. reflexivity.
Qed.
Lemma prune1pcK_keep_sides : forall bc sp wa w wv K kb kk m br2,
  kbase K = Some kb -> kdescr K = Some (kb, kk, Some m) ->
  in_sidesB bc (sp_D sp) kb kk m = true ->
  prune1pcK bc sp wa w wv K false br2 = PKeep.
Proof.
  intros bc sp wa w wv K kb kk m br2 HB HD Hs.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [kbase kdescr] in HB, HD; try discriminate; injection HB as ->;
    try (injection HD as <- <-); try (destruct len as [z| | | | | | |]; try discriminate; injection HD as <- <-);
    unfold prune1pcK, elen; cbn [a_base a_off];
    rewrite !(ranges_apart_pcB_sides _ _ _ _ _ _ _ _ _ Hs); reflexivity.
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

Lemma chainKF_eqv : forall bc vf sxs K okb same_of br2,
  (forall sx, In sx sxs -> vf sx = true ->
     prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 = PKeep) ->
  chainKF bc (mk_flv vf sxs) K okb same_of br2 = chainK2 bc sxs K okb same_of br2.
Proof.
  intros bc vf sxs. induction sxs as [|sx rest IH]; intros K okb same_of br2 Hf; [reflexivity|].
  cbn [mk_flv chainK2].
  assert (IH' : chainKF bc (mk_flv vf rest) K okb same_of br2 = chainK2 bc rest K okb same_of br2)
    by (apply IH; intros; apply Hf; [right|]; assumption).
  destruct (vf sx) eqn:Hv.
  - rewrite (Hf sx (or_introl eq_refl) Hv). exact IH'.
  - cbn [chainKF]. destruct (prune1pcK _ _ _ _ _ K _ br2); [exact IH'|reflexivity].
Qed.
Lemma mk_flv_filter : forall v1 v2 sxs,
  List.filter (fun p => negb (v2 (fst p))) (mk_flv v1 sxs) = mk_flv (fun sx => if v1 sx then true else v2 sx) sxs.
Proof.
  intros v1 v2 sxs. induction sxs as [|sx rest IH]; [reflexivity|]. cbn [mk_flv].
  destruct (v1 sx); [exact IH|]. cbn [List.filter fst]. destruct (v2 sx); cbn [negb]; [exact IH | rewrite IH; reflexivity].
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
  entriesG (mkbc fk) sxs (mk_gl (mkbc fk) t1 bnds sxs) kn infos = chainRo fk (map strip sxs) kn.
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
      cbv beta zeta iota.
      destruct (inb g ei) eqn:Hinb; [|apply FULL; reflexivity].
      assert (Hm : exists m, ei_m ei = Some m).
      { unfold inb in Hinb. destruct (ei_m ei) as [m|]; [exists m; reflexivity|discriminate]. }
      destruct Hm as [m Hm].
      (* [comment removed for export] *)
      assert (V2 : forall sx, In sx sxs -> verdict2 (mkbc fk) t1 sx g = true ->
                 prune1pcK (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K
                   ((match kbase K with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end) (sx_bid sx))
                   (match kbase K with Some _ => ei_br ei | None => None end) = PKeep).
      { intros sx Hsx Hv.
        unfold verdict2 in Hv. destruct (verdict sx g) eqn:Hv1.
        { (* [comment removed for export] *)
        destruct (verdict_inb_num _ _ _ _ Hv1 Hinb Hm) as (Hne & lo1 & hi1 & lo2 & hi2 & Hsp & Hbr2 & Hnum).
        pose proof (proj1 (Forall_forall _ _) HS sx Hsx) as (SXin & SXbr & SXsp).
        rewrite Hm in HD.
        destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
        * rewrite HB. rewrite Hne. rewrite Hbr. eapply prune1pcK_keep_based; [exact HB|exact HD|exact Hsp| | exact Hnum].
          rewrite <- Hbr. exact Hbr2.
        * cbn [kbase]. rewrite Hkb, Hk in *.
          eapply prune1pcK_keep_img; [exact HD| |exact Hsp| rewrite <- Hbr; exact Hbr2 | exact Hnum].
          rewrite <- (nt_same_eq _ _ _ _ _ _ HT HIn SXin). exact Hne. }
        (* [comment removed for export] *)
        destruct g as [[b obr] [glo ghi]]. unfold dverdict in Hv. unfold inb in Hinb. rewrite Hm in Hinb.
        apply andb_prop in Hinb as [Hinb H4]. apply andb_prop in Hinb as [Hinb H3]. apply andb_prop in Hinb as [H1 _].
        apply Pos.eqb_eq in H1. subst b. apply Z.leb_le in H3. apply Z.leb_le in H4.
        destruct (Pos.eqb (ei_bid ei) (sx_bid sx)) eqn:Hne; [discriminate|].
        destruct (proj1 HT _ _ _ HIn) as (_ & Hinfo & _). rewrite Hinfo in Hv. cbn [bi_base] in Hv.
        rewrite Hm in HD.
        destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
        * rewrite HB. rewrite Hne.
          assert (HH : hull_in_sides (mkbc fk) (sp_D (sx_sp sx)) (ei_kb ei) glo ghi = true)
            by (destruct (ei_kb ei); first [discriminate | exact Hv]).
          eapply prune1pcK_keep_sides; [exact HB | exact HD |].
          exact (hull_in_sides_member _ _ _ _ _ _ _ HH H3 H4).
        * rewrite Hkb in Hv. discriminate. }
      rewrite <- (FULL (kbase K) eq_refl).
      destruct (kword_small K) eqn:HW.
      * (* [comment removed for export] *)
        unfold mk_fl. rewrite (mk_flv_filter (fun sx => verdict2 (mkbc fk) t1 sx g) (fun sx => sverdict sx g)).
        apply chainKF_eqv. intros sx Hsx Hv.
        destruct (verdict2 (mkbc fk) t1 sx g) eqn:Hv2; [exact (V2 sx Hsx Hv2)|].
        destruct K as [[kb kk] w' v|? ?|? ? ?|? ?|? ?|? ? ?|? ?|? ? ? ?|? ? ?|? ?]; cbn [kword_small] in HW; try discriminate.
        apply Nat.leb_le in HW. cbn [kdescr] in HD. rewrite Hm in HD. injection HD as Ekb Ekk Em.
        destruct g as [[b obr] [glo ghi]]. unfold sverdict in Hv. unfold inb in Hinb. rewrite Hm in Hinb.
        apply andb_prop in Hinb as [Hinb H4]. apply andb_prop in Hinb as [Hinb H3]. apply andb_prop in Hinb as [H1 _].
        apply Pos.eqb_eq in H1. subst b. apply Z.leb_le in H3. apply Z.leb_le in H4.
        destruct (Pos.eqb (ei_bid ei) (sx_bid sx)) eqn:Hsame; [|discriminate].
        destruct (Nat.leb (sx_w sx) 8) eqn:Hw8; [|discriminate]. apply Nat.leb_le in Hw8.
        assert (Zm : m = Z.of_nat w').
        { rewrite <- Em. unfold zlit64. replace (Z.leb 0 (Z.of_nat w') && Z.ltb (Z.of_nat w') two64)%bool with true; [reflexivity|].
          symmetry. apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; unfold two64; change (2 ^ 64)%Z with 18446744073709551616%Z; lia]. }
        cbn [kbase]. rewrite Hsame. unfold prune1pcK.
        replace (Z.leb (kk + Z.of_nat w') (a_off (sx_a sx)) || Z.leb (a_off (sx_a sx) + Z.of_nat (sx_w sx)) kk)%bool with true; [reflexivity|].
        symmetry. apply Bool.orb_true_iff.
        destruct (Z.leb ghi (a_off (sx_a sx))) eqn:Hg; [left; apply Z.leb_le in Hg | right; apply Z.leb_le in Hv]; apply Z.leb_le; lia.
      * unfold mk_fl. apply chainKF_eqv. exact V2.
    + apply chainK2_eq; [exact HSP| symmetry; apply kdescr_None_kbase; exact HK | reflexivity].
Qed.

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
End AxSymExec3B.

(* [comment removed for export] *)
Module AxSymExec3L.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.SymStepR.CatExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.CatSim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.SymStepR.SeqExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.MemSplit.StoreOk OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.SymExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 AxSymExec3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Module AX2L.
Import AX2. Import AX2B.
Local Open Scope Z_scope.

Record lrec : Type := LR { lr_base : expr; lr_rng : option (Z * Z); lr_lo : Z; lr_hi : Z; lr_sub : list sentry; lr_keys : ptree (list nat) }.
(* [comment removed for export] *)
Definition zkey (z : Z) : positive := match z with Z0 => xH | Zpos p => xO p | Zneg p => xI p end.
Definition key_has (ks : ptree (list nat)) (off : Z) (n : nat) : bool :=
  match pt_get ks (zkey off) with Some ws => existsb (Nat.eqb n) ws | None => false end.
Definition key_add (ks : ptree (list nat)) (off : Z) (n : nat) : ptree (list nat) :=
  pt_set (zkey off) (n :: match pt_get ks (zkey off) with Some ws => ws | None => [] end) ks.
Definition lix : Type := list lrec.

Definition same_base (b : expr) (e : sentry) : bool := expr_eqb b (a_base (e_addr e)).

(* [comment removed for export] *)
Fixpoint lix_ins (bc : bctx) (rm : bool) (a : saddr) (n : nat) (v : expr) (lx : lix) : lix :=
  match lx with
  | [] => [LR (a_base a) (base_rangeB bc (a_base a)) (a_off a) (a_off a + Z.of_nat n) [SE a n v] (key_add PTLeaf (a_off a) n)]
  | r :: rest =>
      if expr_eqb (lr_base r) (a_base a)
      then LR (lr_base r) (lr_rng r) (Z.min (lr_lo r) (a_off a)) (Z.max (lr_hi r) (a_off a + Z.of_nat n))
              (SE a n v :: (if rm then (if key_has (lr_keys r) (a_off a) n then log_rm a n (lr_sub r) else lr_sub r) else lr_sub r))
              (key_add (lr_keys r) (a_off a) n) :: rest
      else r :: lix_ins bc rm a n v rest
  end.
Fixpoint lix_has (lx : lix) (a : saddr) (n : nat) : bool :=
  match lx with
  | [] => false
  | r :: rest => if expr_eqb (lr_base r) (a_base a) then key_has (lr_keys r) (a_off a) n else lix_has rest a n
  end.
Definition log_pushL (lx : lix) (a : saddr) (n : nat) (v : expr) (log : list sentry) : list sentry :=
  if lix_has lx a n then log_push a n v log else SE a n v :: log.
Definition mk_lix (bc : bctx) (log : list sentry) : lix :=
  fold_right (fun e lx => lix_ins bc false (e_addr e) (e_width e) (e_val e) lx) [] log.

(* [comment removed for export] *)
Definition hull_in_side (bc : bctx) (kb : expr) (K N : Z) (c : saddr) (m : expr) : bool :=
  if (expr_eqb kb (a_base c) && Z.leb (a_off c) K)%bool then
    match xloB bc m with Some ml => Z.leb (K + N) (a_off c + ml) | None => false end
  else false.
Fixpoint kdisj_hullB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) (kb : expr) (K N : Z) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if hull_in_side bc kb K N c2 m2 then sub_itvB bc b1 k1 n1 c1 m1 else false) then true
      else if (if hull_in_side bc kb K N c1 m1 then sub_itvB bc b1 k1 n1 c2 m2 else false) then true
      else kdisj_hullB bc rest b1 k1 n1 kb K N
  | _ :: rest => kdisj_hullB bc rest b1 k1 n1 kb K N
  end.
Definition hull_apart (bc : bctx) (r1 : option (Z * Z)) (rb : expr) (rk n : Z) (r : lrec) : bool :=
  if (match r1, lr_rng r with
      | Some (lo1, hi1), Some (lo2, hi2) => (Z.leb (hi1 + rk + n) (lo2 + lr_lo r) || Z.leb (hi2 + lr_hi r) (lo1 + rk))%bool
      | _, _ => false
      end) then true
  else kdisj_hullB bc (bc_fk bc) rb rk n (lr_base r) (lr_lo r) (lr_hi r - lr_lo r).
(* [comment removed for export] *)
Fixpoint lix_others_apart (bc : bctx) (r1 : option (Z * Z)) (rb : expr) (rk n : Z) (lx : lix) : bool :=
  match lx with
  | [] => true
  | r :: rest =>
      if expr_eqb rb (lr_base r) then lix_others_apart bc r1 rb rk n rest
      else if hull_apart bc r1 rb rk n r then lix_others_apart bc r1 rb rk n rest else false
  end.
Fixpoint lix_sub (rb : expr) (lx : lix) : list sentry :=
  match lx with
  | [] => []
  | r :: rest => if expr_eqb rb (lr_base r) then lr_sub r else lix_sub rb rest
  end.
(* [comment removed for export] *)
Fixpoint log_lookup_same (sub : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool) : option (option expr) :=
  match sub with
  | [] => Some None
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => Some (Some (mkExt sx (Z.to_nat d) n v))
      | RDisjoint => log_lookup_same rest rb rk n sx
      | _ => None
      end
  end.
Definition log_lookupL (bc : bctx) (lx : lix) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
           (hints : list bool) (acc : list sidecond) : lres :=
  if lix_others_apart bc (base_rangeB bc rb) rb rk (Z.of_nat n) lx then
    match log_lookup_same (lix_sub rb lx) rb rk n sx with
    | Some (Some v) => LHit v acc hints
    | Some None => LMiss acc hints
    | None => log_lookupB bc log rb rk n sx hints acc
    end
  else log_lookupB bc log rb rk n sx hints acc.

(* [comment removed for export] *)
Definition in_hull (r : lrec) (e : sentry) : Prop :=
  lr_lo r <= a_off (e_addr e) /\ a_off (e_addr e) + Z.of_nat (e_width e) <= lr_hi r.
Definition lrec_ok (bc : bctx) (log : list sentry) (r : lrec) : Prop :=
  lr_rng r = base_rangeB bc (lr_base r) /\
  lr_sub r = List.filter (same_base (lr_base r)) log /\
  Forall (in_hull r) (lr_sub r) /\
  Forall (fun e => key_has (lr_keys r) (a_off (e_addr e)) (e_width e) = true) (lr_sub r).
Definition has_rec (lx : lix) (e : sentry) : Prop := existsb (fun r => expr_eqb (lr_base r) (a_base (e_addr e))) lx = true.
Definition lix_ok (bc : bctx) (lx : lix) (log : list sentry) : Prop :=
  Forall (lrec_ok bc log) lx /\ Forall (has_rec lx) log /\ List.NoDup (map lr_base lx).

Lemma eqb_true : forall x y, expr_eqb x y = true -> x = y. Proof. exact p_expr_eqb_eq. Qed.
Lemma eqb_refl : forall x, expr_eqb x x = true. Proof. exact kx_expr_eqb_refl. Qed.
Lemma eqb_false : forall x y, expr_eqb x y = false -> x <> y.
Proof. intros x y H ->. rewrite eqb_refl in H. discriminate. Qed.
Lemma eqb_sym : forall x y, expr_eqb x y = expr_eqb y x.
Proof.
  intros x y. destruct (expr_eqb x y) eqn:E.
  - apply eqb_true in E. subst. symmetry. apply eqb_refl.
  - destruct (expr_eqb y x) eqn:E2; [|reflexivity]. apply eqb_true in E2. subst. rewrite eqb_refl in E. discriminate.
Qed.

Lemma filter_cons_if : forall (A : Type) (f : A -> bool) x l, List.filter f (x :: l) = if f x then x :: List.filter f l else List.filter f l.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma filter_log_rm_same : forall b a n log, expr_eqb b (a_base a) = true ->
  List.filter (same_base b) (log_rm a n log) = log_rm a n (List.filter (same_base b) log).
Proof.
  intros b a n log Hb. apply eqb_true in Hb. subst b.
  induction log as [|[a' n' v'] rest IH]; [reflexivity|].
  cbn [log_rm]. destruct (Z.eqb (a_off a) (a_off a') && Nat.eqb n n' && expr_eqb (a_base a) (a_base a'))%bool eqn:T.
  - rewrite filter_cons_if. change (same_base (a_base a) (SE a' n' v')) with (expr_eqb (a_base a) (a_base a')).
    destruct (andb_prop _ _ T) as [_ T3]. rewrite T3. cbn [log_rm]. rewrite T. reflexivity.
  - rewrite !filter_cons_if. change (same_base (a_base a) (SE a' n' v')) with (expr_eqb (a_base a) (a_base a')). destruct (expr_eqb (a_base a) (a_base a')) eqn:E.
    + cbn [log_rm]. rewrite E, T. rewrite IH. reflexivity.
    + exact IH.
Qed.
Lemma filter_log_rm_other : forall b a n log, expr_eqb b (a_base a) = false ->
  List.filter (same_base b) (log_rm a n log) = List.filter (same_base b) log.
Proof.
  intros b a n log Hb. induction log as [|[a' n' v'] rest IH]; [reflexivity|].
  cbn [log_rm]. destruct (Z.eqb (a_off a) (a_off a') && Nat.eqb n n' && expr_eqb (a_base a) (a_base a'))%bool eqn:T.
  - rewrite filter_cons_if. change (same_base b (SE a' n' v')) with (expr_eqb b (a_base a')).
    apply andb_prop in T. destruct T as [_ T3]. apply eqb_true in T3. rewrite <- T3, Hb. reflexivity.
  - rewrite !filter_cons_if. rewrite IH. reflexivity.
Qed.
Lemma Forall_log_rm : forall (P : sentry -> Prop) a n log, Forall P log -> Forall P (log_rm a n log).
Proof.
  intros P a n log H. induction H as [|[a' n' v'] rest Hx Hr IH]; [constructor|].
  cbn [log_rm]. destruct (Z.eqb (a_off a) (a_off a') && Nat.eqb n n' && expr_eqb (a_base a) (a_base a'))%bool; [exact Hr| constructor; assumption].
Qed.

(* [comment removed for export] *)
Lemma has_rec_ins : forall bc rm a n v lx e, has_rec lx e -> has_rec (lix_ins bc rm a n v lx) e.
Proof.
  intros bc rm a n v lx e. unfold has_rec. induction lx as [|r rest IH]; [discriminate|].
  cbn [lix_ins existsb]. intros H. destruct (expr_eqb (lr_base r) (a_base a)).
  - cbn [existsb lr_base]. exact H.
  - cbn [existsb]. apply orb_true_iff in H. apply orb_true_iff. destruct H as [H|H]; [left; exact H| right; exact (IH H)].
Qed.
Lemma has_rec_ins_new : forall bc rm a n v lx, has_rec (lix_ins bc rm a n v lx) (SE a n v).
Proof.
  intros bc rm a n v lx. unfold has_rec. cbn [e_addr]. induction lx as [|r rest IH].
  - cbn [lix_ins existsb lr_base]. rewrite eqb_refl. reflexivity.
  - cbn [lix_ins]. destruct (expr_eqb (lr_base r) (a_base a)) eqn:E.
    + cbn [existsb lr_base]. rewrite E. reflexivity.
    + cbn [existsb]. rewrite E. exact IH.
Qed.
Lemma bases_ins : forall bc rm a n v lx,
  map lr_base (lix_ins bc rm a n v lx) = if existsb (fun r => expr_eqb (lr_base r) (a_base a)) lx then map lr_base lx else map lr_base lx ++ [a_base a].
Proof.
  intros bc rm a n v lx. induction lx as [|r rest IH]; [reflexivity|].
  cbn [lix_ins existsb]. destruct (expr_eqb (lr_base r) (a_base a)) eqn:E; [reflexivity|].
  cbn [map orb]. rewrite IH. destruct (existsb _ rest); reflexivity.
Qed.
Lemma existsb_base_false : forall b lx, existsb (fun r => expr_eqb (lr_base r) b) lx = false -> ~ In b (map lr_base lx).
Proof.
  intros b lx. induction lx as [|r rest IH]; [intros _ []|].
  cbn [existsb map]. intros H [H1|H1].
  - rewrite H1, eqb_refl in H. discriminate.
  - apply orb_false_iff in H. exact (IH (proj2 H) H1).
Qed.
Lemma nodup_snoc : forall (l : list expr) x, List.NoDup l -> ~ In x l -> List.NoDup (l ++ [x]).
Proof.
  intros l x H. induction H as [|y l Hy Hl IH]; intros Hx; [constructor; [intros []| constructor]|].
  cbn [app]. constructor.
  - intros Hin. apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]]; [exact (Hy Hin)| apply Hx; left; reflexivity].
  - apply IH. intros Hin. apply Hx. right. exact Hin.
Qed.
Lemma nodup_ins : forall bc rm a n v lx, List.NoDup (map lr_base lx) -> List.NoDup (map lr_base (lix_ins bc rm a n v lx)).
Proof.
  intros bc rm a n v lx H. rewrite bases_ins. destruct (existsb _ lx) eqn:E; [exact H|].
  apply nodup_snoc; [exact H| exact (existsb_base_false _ _ E)].
Qed.

(* [comment removed for export] *)
Definition ins_log (rm : bool) (a : saddr) (n : nat) (v : expr) (log : list sentry) : list sentry :=
  SE a n v :: (if rm then log_rm a n log else log).
Lemma ins_log_push : forall a n v log, ins_log true a n v log = log_push a n v log.
Proof. reflexivity. Qed.

Lemma filter_ins_other : forall rm b a n v log, expr_eqb b (a_base a) = false ->
  List.filter (same_base b) (ins_log rm a n v log) = List.filter (same_base b) log.
Proof.
  intros rm b a n v log Hb. unfold ins_log. rewrite filter_cons_if. change (same_base b (SE a n v)) with (expr_eqb b (a_base a)). rewrite Hb.
  destruct rm; [apply filter_log_rm_other; exact Hb| reflexivity].
Qed.
Lemma filter_ins_same : forall rm b a n v log, expr_eqb b (a_base a) = true ->
  List.filter (same_base b) (ins_log rm a n v log) = SE a n v :: (if rm then log_rm a n (List.filter (same_base b) log) else List.filter (same_base b) log).
Proof.
  intros rm b a n v log Hb. unfold ins_log. rewrite filter_cons_if. change (same_base b (SE a n v)) with (expr_eqb b (a_base a)). rewrite Hb.
  destruct rm; [rewrite filter_log_rm_same by exact Hb; reflexivity| reflexivity].
Qed.

Lemma lrec_ok_ins_other : forall bc rm a n v log r, expr_eqb (lr_base r) (a_base a) = false ->
  lrec_ok bc log r -> lrec_ok bc (ins_log rm a n v log) r.
Proof.
  intros bc rm a n v log r Hb (H1 & H2 & H3). split; [exact H1|]. split; [|exact H3].
  rewrite filter_ins_other by exact Hb. exact H2.
Qed.

Lemma existsb_false_neq : forall (f : lrec -> expr -> bool) b lx,
  (forall r, f r b = true -> lr_base r = b) -> (forall r, lr_base r = b -> f r b = true) ->
  existsb (fun r => f r b) lx = false -> forall r, In r lx -> lr_base r <> b.
Proof.
  intros f b lx F1 F2 H r Hin Heq. assert (X : existsb (fun r => f r b) lx = true) by (apply existsb_exists; exists r; split; [exact Hin| exact (F2 r Heq)]).
  rewrite X in H. discriminate.
Qed.
Lemma norec_filter_nil : forall lx log b, Forall (has_rec lx) log -> (forall r, In r lx -> lr_base r <> b) ->
  List.filter (same_base b) log = [].
Proof.
  intros lx log b H Hn. induction H as [|e rest He Hrest IH]; [reflexivity|].
  rewrite filter_cons_if. destruct (same_base b e) eqn:E; [|exact IH]. exfalso.
  unfold same_base in E. apply eqb_true in E. unfold has_rec in He. apply existsb_exists in He. destruct He as (r & Hin & Hr).
  apply eqb_true in Hr. apply (Hn r Hin). rewrite Hr. symmetry. exact E.
Qed.

Lemma key_has_add_same : forall ks off n, key_has (key_add ks off n) off n = true.
Proof. intros. unfold key_has, key_add. rewrite pt_gss. cbn [existsb]. rewrite Nat.eqb_refl. reflexivity. Qed.
Lemma key_has_add_mono : forall ks off n o w, key_has ks o w = true -> key_has (key_add ks off n) o w = true.
Proof.
  intros ks off n o w H. unfold key_has, key_add in *. destruct (Pos.eq_dec (zkey o) (zkey off)) as [E|E].
  - rewrite E in *. rewrite pt_gss. cbn [existsb]. destruct (pt_get ks (zkey off)); [|discriminate]. rewrite H. apply orb_true_r.
  - rewrite pt_gso by exact E. exact H.
Qed.
Lemma log_rm_absent : forall a n log,
  (forall e, In e log -> (Z.eqb (a_off a) (a_off (e_addr e)) && Nat.eqb n (e_width e) && expr_eqb (a_base a) (a_base (e_addr e)))%bool = false) ->
  log_rm a n log = log.
Proof.
  intros a n log H. induction log as [|[a' n' v'] rest IH]; [reflexivity|].
  cbn [log_rm]. pose proof (H (SE a' n' v') (or_introl eq_refl)) as T. cbn [e_addr e_width] in T. rewrite T.
  rewrite IH; [reflexivity|]. intros e Hin. apply H. right. exact Hin.
Qed.
Lemma keys_absent_rm : forall ks a n sub,
  Forall (fun e => key_has ks (a_off (e_addr e)) (e_width e) = true) sub -> key_has ks (a_off a) n = false -> log_rm a n sub = sub.
Proof.
  intros ks a n sub HK Hno. apply log_rm_absent. intros e Hin. rewrite Forall_forall in HK. pose proof (HK e Hin) as He.
  destruct (Z.eqb (a_off a) (a_off (e_addr e))) eqn:E1; [|reflexivity]. destruct (Nat.eqb n (e_width e)) eqn:E2; [|reflexivity].
  apply Z.eqb_eq in E1. apply Nat.eqb_eq in E2. rewrite <- E1, <- E2, Hno in He. discriminate.
Qed.

Lemma in_hull_widen : forall r r' e, lr_lo r' <= lr_lo r -> lr_hi r <= lr_hi r' -> in_hull r e -> in_hull r' e.
Proof. unfold in_hull. intros r r' e H1 H2 [H3 H4]. split; lia. Qed.

Lemma Forall_in_hull_widen : forall r r' sub, lr_lo r' <= lr_lo r -> lr_hi r <= lr_hi r' -> Forall (in_hull r) sub -> Forall (in_hull r') sub.
Proof. intros r r' sub H1 H2 H. eapply Forall_impl; [|exact H]. intros e He. exact (in_hull_widen r r' e H1 H2 He). Qed.
Lemma recs_ok_ins : forall bc rm a n v log lx,
  Forall (lrec_ok bc log) lx -> List.NoDup (map lr_base lx) ->
  ((forall r, In r lx -> lr_base r <> a_base a) -> List.filter (same_base (a_base a)) log = []) ->
  Forall (lrec_ok bc (ins_log rm a n v log)) (lix_ins bc rm a n v lx).
Proof.
  intros bc rm a n v log lx H. induction H as [|r rest Hr Hrest IH]; intros ND Hnil.
  - cbn [lix_ins]. constructor; [|constructor]. split; [reflexivity|]. cbn [lr_base lr_sub lr_lo lr_hi lr_keys].
    split; [|split].
    + rewrite filter_ins_same by apply eqb_refl. rewrite Hnil by (intros r []). destruct rm; reflexivity.
    + constructor; [|constructor]. unfold in_hull. cbn [lr_lo lr_hi e_addr e_width]. lia.
    + constructor; [|constructor]. cbn [e_addr e_width]. apply key_has_add_same.
  - cbn [lix_ins]. destruct (expr_eqb (lr_base r) (a_base a)) eqn:E.
    + constructor.
      * destruct Hr as (H1 & H2 & H3 & H4). split; [exact H1|]. cbn [lr_base lr_sub lr_keys].
        assert (S : (if rm then (if key_has (lr_keys r) (a_off a) n then log_rm a n (lr_sub r) else lr_sub r) else lr_sub r)
                    = (if rm then log_rm a n (lr_sub r) else lr_sub r)).
        { destruct rm; [|reflexivity]. destruct (key_has (lr_keys r) (a_off a) n) eqn:KH; [reflexivity|]. symmetry. exact (keys_absent_rm _ _ _ _ H4 KH). }
        rewrite S. split; [|split].
        -- rewrite filter_ins_same by exact E. rewrite <- H2. reflexivity.
        -- constructor.
           ++ unfold in_hull. cbn [lr_lo lr_hi e_addr e_width]. lia.
           ++ assert (W : Forall (in_hull (LR (lr_base r) (lr_rng r) (Z.min (lr_lo r) (a_off a)) (Z.max (lr_hi r) (a_off a + Z.of_nat n))
                                               (SE a n v :: (if rm then log_rm a n (lr_sub r) else lr_sub r)) (key_add (lr_keys r) (a_off a) n))) (lr_sub r)).
              { eapply Forall_in_hull_widen; [| |exact H3]; cbn [lr_lo lr_hi]; lia. }
              destruct rm; [apply Forall_log_rm; exact W| exact W].
        -- constructor; [cbn [e_addr e_width]; apply key_has_add_same|].
           assert (W : Forall (fun e => key_has (key_add (lr_keys r) (a_off a) n) (a_off (e_addr e)) (e_width e) = true) (lr_sub r)).
           { eapply Forall_impl; [|exact H4]. intros e He. apply key_has_add_mono. exact He. }
           destruct rm; [apply Forall_log_rm; exact W| exact W].
      * apply eqb_true in E. cbn [map] in ND. inversion ND as [|x l Hnotin ND']; subst.
        rewrite Forall_forall in Hrest |- *. intros r' Hin. apply lrec_ok_ins_other; [|exact (Hrest r' Hin)].
        destruct (expr_eqb (lr_base r') (a_base a)) eqn:E'; [|reflexivity]. exfalso. apply eqb_true in E'. apply Hnotin. rewrite E, <- E'. apply in_map. exact Hin.
    + constructor; [apply lrec_ok_ins_other; [exact E| exact Hr]|].
      apply IH; [cbn [map] in ND; inversion ND; assumption|].
      intros Hn. apply Hnil. intros r' [<-|Hin]; [apply eqb_false; exact E| exact (Hn r' Hin)].
Qed.

Lemma lix_ins_ok : forall bc rm a n v lx log, lix_ok bc lx log -> lix_ok bc (lix_ins bc rm a n v lx) (ins_log rm a n v log).
Proof.
  intros bc rm a n v lx log (H1 & H2 & H3). split; [|split].
  - apply recs_ok_ins; [exact H1| exact H3|]. intros Hn. exact (norec_filter_nil lx log (a_base a) H2 Hn).
  - unfold ins_log. constructor; [apply has_rec_ins_new|].
    assert (W : Forall (has_rec (lix_ins bc rm a n v lx)) log) by (eapply Forall_impl; [|exact H2]; intros e He; apply has_rec_ins; exact He).
    destruct rm; [apply Forall_log_rm; exact W| exact W].
  - apply nodup_ins. exact H3.
Qed.
Lemma lix_push_ok : forall bc a n v lx log, lix_ok bc lx log -> lix_ok bc (lix_ins bc true a n v lx) (log_push a n v log).
Proof. intros. rewrite <- ins_log_push. apply lix_ins_ok. assumption. Qed.
Lemma lix_nil_ok : forall bc, lix_ok bc [] [].
Proof. intros bc. split; [constructor| split; [constructor| constructor]]. Qed.
Lemma mk_lix_ok : forall bc log, lix_ok bc (mk_lix bc log) log.
Proof.
  intros bc log. induction log as [|[a n v] rest IH]; [apply lix_nil_ok|].
  change (mk_lix bc (SE a n v :: rest)) with (lix_ins bc false a n v (mk_lix bc rest)).
  change (SE a n v :: rest) with (ins_log false a n v rest). apply lix_ins_ok. exact IH.
Qed.

(* [comment removed for export] *)
Lemma lix_has_false_rm : forall bc lx log a n, lix_ok bc lx log -> lix_has lx a n = false -> log_rm a n log = log.
Proof.
  intros bc lx log a n (H1 & H2 & _) Hno. apply log_rm_absent. intros e Hin.
  destruct (Z.eqb (a_off a) (a_off (e_addr e))) eqn:E1; [|reflexivity]. destruct (Nat.eqb n (e_width e)) eqn:E2; [|reflexivity].
  destruct (expr_eqb (a_base a) (a_base (e_addr e))) eqn:E3; [|reflexivity]. exfalso.
  apply Z.eqb_eq in E1. apply Nat.eqb_eq in E2. apply eqb_true in E3.
  rewrite Forall_forall in H2. pose proof (H2 e Hin) as Hr. unfold has_rec in Hr. apply existsb_exists in Hr. destruct Hr as (r & Hrin & Hre). apply eqb_true in Hre.
  assert (G : forall l, (forall r0, In r0 l -> lrec_ok bc log r0) -> In r l -> lix_has l a n = false -> False).
  { clear Hrin. intros l. induction l as [|r0 rest IHl]; [intros _ []|]. intros Hall [<-|Hin'] Hf; cbn [lix_has] in Hf.
    - rewrite Hre, <- E3, eqb_refl in Hf. destruct (Hall r0 (or_introl eq_refl)) as (_ & R2 & _ & R4).
      assert (HE : In e (lr_sub r0)). { rewrite R2. apply filter_In. split; [exact Hin|]. unfold same_base. rewrite Hre. apply eqb_refl. }
      rewrite Forall_forall in R4. pose proof (R4 e HE) as K. rewrite <- E1, <- E2, Hf in K. discriminate.
    - destruct (expr_eqb (lr_base r0) (a_base a)) eqn:E0.
      + apply eqb_true in E0. destruct (Hall r0 (or_introl eq_refl)) as (_ & R2 & _ & R4).
        assert (HE : In e (lr_sub r0)). { rewrite R2. apply filter_In. split; [exact Hin|]. unfold same_base. rewrite E0, E3. apply eqb_refl. }
        rewrite Forall_forall in R4. pose proof (R4 e HE) as K. rewrite <- E1, <- E2, Hf in K. discriminate.
      + apply IHl; [intros r1 Hr1; apply Hall; right; exact Hr1| exact Hin'| exact Hf]. }
  rewrite Forall_forall in H1. exact (G lx H1 Hrin Hno).
Qed.
Lemma log_pushL_eq : forall bc lx log a n v, lix_ok bc lx log -> log_pushL lx a n v log = log_push a n v log.
Proof.
  intros bc lx log a n v Hok. unfold log_pushL, log_push. destruct (lix_has lx a n) eqn:E; [reflexivity|].
  rewrite (lix_has_false_rm bc lx log a n Hok E). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hull_in_side_mono : forall bc kb K N c m kk w, hull_in_side bc kb K N c m = true -> K <= kk -> kk + w <= K + N ->
  sub_itvB bc kb kk w c m = true.
Proof.
  intros bc kb K N c m kk w H H1 H2. unfold hull_in_side in H. unfold sub_itvB.
  destruct (expr_eqb kb (a_base c)) eqn:E; [|discriminate]. cbn [andb] in H |- *.
  destruct (Z.leb (a_off c) K) eqn:L; [|discriminate]. apply Z.leb_le in L.
  assert (L' : Z.leb (a_off c) kk = true) by (apply Z.leb_le; lia). rewrite L'.
  destruct (xloB bc m) as [ml|]; [|discriminate]. apply Z.leb_le in H.
  assert (L2 : Z.leb (kk + w) (a_off c + ml) = true) by (apply Z.leb_le; lia). rewrite L2. reflexivity.
Qed.
Lemma kdisj_hull_sound : forall bc kn b1 k1 n1 kb K N kk w, kdisj_hullB bc kn b1 k1 n1 kb K N = true -> K <= kk -> kk + w <= K + N ->
  kdisj_apartB bc kn b1 k1 n1 kb kk w = true.
Proof.
  intros bc kn b1 k1 n1 kb K N kk w H H1 H2. induction kn as [|Kf rest IH]; [discriminate|].
  destruct Kf; cbn [kdisj_hullB kdisj_apartB] in H |- *; try (exact (IH H)).
  destruct (hull_in_side bc kb K N a2 n2) eqn:S2.
  - destruct (sub_itvB bc b1 k1 n1 a1 n0) eqn:R1.
    + rewrite (hull_in_side_mono _ _ _ _ _ _ kk w S2 H1 H2). reflexivity.
    + destruct (hull_in_side bc kb K N a1 n0) eqn:S1.
      * destruct (sub_itvB bc b1 k1 n1 a2 n2) eqn:R2.
        -- rewrite (hull_in_side_mono _ _ _ _ _ _ kk w S1 H1 H2). reflexivity.
        -- rewrite (IH H). reflexivity.
      * rewrite (IH H). destruct (sub_itvB bc b1 k1 n1 a2 n2); [destruct (sub_itvB bc kb kk w a1 n0)|]; reflexivity.
  - destruct (hull_in_side bc kb K N a1 n0) eqn:S1.
    + destruct (sub_itvB bc b1 k1 n1 a2 n2) eqn:R2.
      * rewrite (hull_in_side_mono _ _ _ _ _ _ kk w S1 H1 H2). destruct (sub_itvB bc b1 k1 n1 a1 n0); [destruct (sub_itvB bc kb kk w a2 n2)|]; reflexivity.
      * rewrite (IH H). destruct (sub_itvB bc b1 k1 n1 a1 n0); [destruct (sub_itvB bc kb kk w a2 n2)|]; reflexivity.
    + rewrite (IH H). destruct (sub_itvB bc b1 k1 n1 a1 n0); [destruct (sub_itvB bc kb kk w a2 n2)|]; destruct (sub_itvB bc b1 k1 n1 a2 n2); try destruct (sub_itvB bc kb kk w a1 n0); reflexivity.
Qed.
Lemma hull_apart_sound : forall bc rb rk n r kk w, hull_apart bc (base_rangeB bc rb) rb rk n r = true ->
  lr_rng r = base_rangeB bc (lr_base r) -> lr_lo r <= kk -> kk + w <= lr_hi r ->
  ranges_apartB bc rb rk n (lr_base r) kk w = true.
Proof.
  intros bc rb rk n r kk w H R1 U1 U2. unfold hull_apart in H.
  assert (KD : kdisj_hullB bc (bc_fk bc) rb rk n (lr_base r) (lr_lo r) (lr_hi r - lr_lo r) = true ->
               ranges_apartB bc rb rk n (lr_base r) kk w = true).
  { intros HK. unfold ranges_apartB. rewrite (kdisj_hull_sound _ _ _ _ _ _ _ _ kk w HK) by lia.
    match goal with |- (if ?c then true else _) = true => destruct c; reflexivity end. }
  destruct (base_rangeB bc rb) as [[lo1 hi1]|] eqn:B1; [|exact (KD H)].
  destruct (lr_rng r) as [[lo2 hi2]|] eqn:B2; [|exact (KD H)].
  destruct (Z.leb (hi1 + rk + n) (lo2 + lr_lo r) || Z.leb (hi2 + lr_hi r) (lo1 + rk))%bool eqn:T; [|exact (KD H)].
  unfold ranges_apartB. rewrite B1, <- R1.
  assert (T' : (Z.leb (hi1 + rk + n) (lo2 + kk) || Z.leb (hi2 + kk + w) (lo1 + rk))%bool = true).
  { apply orb_true_iff in T. apply orb_true_iff. destruct T as [T|T]; [left| right]; apply Z.leb_le in T; apply Z.leb_le; lia. }
  rewrite T'. reflexivity.
Qed.
Lemma others_apart_in : forall bc r1 rb rk n lx r,
  lix_others_apart bc r1 rb rk n lx = true -> In r lx -> expr_eqb rb (lr_base r) = false -> hull_apart bc r1 rb rk n r = true.
Proof.
  intros bc r1 rb rk n lx r. induction lx as [|r0 rest IH]; [intros _ []|].
  cbn [lix_others_apart]. intros H [<-|Hin] Hb.
  - rewrite Hb in H. destruct (hull_apart bc r1 rb rk n r0); [reflexivity| discriminate].
  - apply IH; [|exact Hin| exact Hb]. destruct (expr_eqb rb (lr_base r0)); [exact H|].
    destruct (hull_apart bc r1 rb rk n r0); [exact H| discriminate].
Qed.
Lemma others_apart_sound : forall bc lx log rb rk n,
  lix_ok bc lx log -> lix_others_apart bc (base_rangeB bc rb) rb rk n lx = true ->
  forall e, In e log -> expr_eqb rb (a_base (e_addr e)) = false ->
  ranges_apartB bc rb rk n (a_base (e_addr e)) (a_off (e_addr e)) (Z.of_nat (e_width e)) = true.
Proof.
  intros bc lx log rb rk n (H1 & H2 & _) HA e Hin Hb.
  rewrite Forall_forall in H2. pose proof (H2 e Hin) as Hr. unfold has_rec in Hr. apply existsb_exists in Hr. destruct Hr as (r & Hrin & Hre).
  apply eqb_true in Hre. rewrite Forall_forall in H1. destruct (H1 r Hrin) as (R1 & R2 & R3 & _).
  assert (Hb' : expr_eqb rb (lr_base r) = false) by (rewrite Hre; exact Hb).
  pose proof (others_apart_in _ _ _ _ _ _ _ HA Hrin Hb') as HH.
  assert (HE : In e (lr_sub r)). { rewrite R2. apply filter_In. split; [exact Hin|]. unfold same_base. rewrite Hre. apply eqb_refl. }
  rewrite Forall_forall in R3. destruct (R3 e HE) as [U1 U2].
  rewrite <- Hre. apply hull_apart_sound; [exact HH| exact R1| exact U1| exact U2].
Qed.
Lemma same_spec : forall bc log rb rk n sx hints acc,
  (forall e, In e log -> expr_eqb rb (a_base (e_addr e)) = false ->
     ranges_apartB bc rb rk (Z.of_nat n) (a_base (e_addr e)) (a_off (e_addr e)) (Z.of_nat (e_width e)) = true) ->
  forall res, log_lookup_same (List.filter (same_base rb) log) rb rk n sx = Some res ->
  log_lookupB bc log rb rk n sx hints acc = match res with Some v => LHit v acc hints | None => LMiss acc hints end.
Proof.
  intros bc log rb rk n sx hints acc. induction log as [|[[kb kk] w v] rest IH]; intros HA res Hres.
  - cbn in Hres. injection Hres as <-. reflexivity.
  - rewrite filter_cons_if in Hres. change (same_base rb (SE (SA kb kk) w v)) with (expr_eqb rb kb) in Hres.
    cbn [log_lookupB]. destruct (expr_eqb rb kb) eqn:E.
    + cbn [log_lookup_same] in Hres. destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)) eqn:R; try discriminate.
      * injection Hres as <-. reflexivity.
      * apply IH; [|exact Hres]. intros e Hin. apply HA. right. exact Hin.
    + assert (R : rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) = RUnknown) by (unfold rel_lit; rewrite E; reflexivity).
      rewrite R. pose proof (HA (SE (SA kb kk) w v) (or_introl eq_refl) E) as Hap. cbn [e_addr a_base a_off e_width] in Hap. rewrite Hap.
      apply IH; [|exact Hres]. intros e Hin. apply HA. right. exact Hin.
Qed.
Lemma lix_sub_spec : forall bc lx log rb, lix_ok bc lx log -> lix_sub rb lx = List.filter (same_base rb) log.
Proof.
  intros bc lx log rb (H1 & H2 & _).
  assert (G : forall l, Forall (lrec_ok bc log) l -> (forall r, In r l -> lr_base r <> rb) \/ lix_sub rb l = List.filter (same_base rb) log ->
              (forall r, In r l -> lr_base r <> rb) /\ lix_sub rb l = [] \/ lix_sub rb l = List.filter (same_base rb) log).
  { intros l _ [Hn|Hs]; [left; split; [exact Hn|]| right; exact Hs].
    induction l as [|r rest IHl]; [reflexivity|]. cbn [lix_sub]. destruct (expr_eqb rb (lr_base r)) eqn:E.
    - exfalso. apply eqb_true in E. apply (Hn r (or_introl eq_refl)). symmetry. exact E.
    - apply IHl. intros r' Hin. apply Hn. right. exact Hin. }
  assert (D : (forall r, In r lx -> lr_base r <> rb) \/ lix_sub rb lx = List.filter (same_base rb) log).
  { clear G H2. induction H1 as [|r rest Hr Hrest IH]; [left; intros r []|]. cbn [lix_sub]. destruct (expr_eqb rb (lr_base r)) eqn:E.
    - right. apply eqb_true in E. destruct Hr as (_ & R2 & _). rewrite R2, E. reflexivity.
    - destruct IH as [Hn|Hs]; [left| right; exact Hs]. intros r' [<-|Hin]; [intros Heq; rewrite Heq, eqb_refl in E; discriminate| exact (Hn r' Hin)]. }
  destruct (G lx H1 D) as [[Hn Hs]|Hs]; [|exact Hs]. rewrite Hs. symmetry. exact (norec_filter_nil lx log rb H2 Hn).
Qed.
Lemma log_lookupL_eq : forall bc lx log rb rk n sx hints acc,
  lix_ok bc lx log -> log_lookupL bc lx log rb rk n sx hints acc = log_lookupB bc log rb rk n sx hints acc.
Proof.
  intros bc lx log rb rk n sx hints acc Hok. unfold log_lookupL.
  destruct (lix_others_apart bc (base_rangeB bc rb) rb rk (Z.of_nat n) lx) eqn:HA; [|reflexivity].
  destruct (log_lookup_same (lix_sub rb lx) rb rk n sx) as [res|] eqn:HS; [|reflexivity].
  rewrite (lix_sub_spec bc lx log rb Hok) in HS.
  rewrite (same_spec bc log rb rk n sx hints acc (others_apart_sound bc lx log rb rk (Z.of_nat n) Hok HA) res HS).
  destruct res; reflexivity.
Qed.

(* [comment removed for export] *)
Local Close Scope Z_scope.
Definition sym_readBIL (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (lx : lix) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match log_lookupL bc lx (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
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


Definition sym_stepBIP (lpush : saddr -> nat -> expr -> list sentry) (bc : bctx) (kx : kix) (lx : lix) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
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
      match sym_readBIL segs ss bc kx lx scr a n sx' with
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
          SOk (SSR (p + 4) (s_regs ss) (lpush a n (g rs2)) (s_know ss) (s_next ss) r')
              (flat_scB bc a n ++ storeok_scB bc a n) scr
      end
  (* [comment removed for export] *)
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match sym_readBIL segs ss bc kx lx scr a n (amo_sx wd) with
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
                       (lpush a n (g rs2)) (s_know ss) (s_next ss) None)
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
                match sym_readBIL segs ss bc kx lx scr a n (amo_sx wd) with
                | None => SStop
                | Some (vold, scs, scr', nx') =>
                    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
                             (lpush a n (amo_newvalB bc wd aop vold (g rs2))) (s_know ss) nx' r')
                        (scs ++ storeok_scB bc a n) scr'
                end
            end
          else SStop
      end
  | _ => SStop
  end.



Local Open Scope Z_scope.

Lemma sym_readBIL_eqf : forall segs ss bc kx lx, lix_ok bc lx (s_log ss) -> sym_readBIL segs ss bc kx lx = sym_readBI segs ss bc kx.
Proof. intros segs ss bc kx lx Hok. bcfe. unfold sym_readBIL, sym_readBI. rewrite log_lookupL_eq by exact Hok. reflexivity. Qed.
Definition sym_stepBIL (bc : bctx) (kx : kix) (lx : lix) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  sym_stepBIP (fun a n v => log_pushL lx a n v (s_log ss)) bc kx lx segs i ss scr.
Lemma sym_stepBIL_eq : forall bc kx lx segs i ss scr, lix_ok bc lx (s_log ss) ->
  sym_stepBIL bc kx lx segs i ss scr = sym_stepBI bc kx segs i ss scr.
Proof.
  intros bc kx lx segs i ss scr Hok. unfold sym_stepBIL.
  assert (E : (fun a n v => log_pushL lx a n v (s_log ss)) = (fun a n v => log_push a n v (s_log ss))).
  { apply functional_extensionality; intros a. apply functional_extensionality; intros n. apply functional_extensionality; intros v.
    exact (log_pushL_eq bc lx (s_log ss) a n v Hok). }
  rewrite E. unfold sym_stepBIP, sym_stepBI. rewrite (sym_readBIL_eqf segs ss bc kx lx Hok). reflexivity.
Qed.

(* [comment removed for export] *)
Definition lix_next (bc : bctx) (i : instr) (ss' : sym_state) (lx : lix) : lix :=
  match i with
  | Store _ _ _ _ => match s_log ss' with SE a n v :: _ => lix_ins bc true a n v lx | [] => lx end
  | Sc _ _ _ _ _ _ | Amo _ _ _ _ _ _ _ => mk_lix bc (s_log ss')
  | _ => lx
  end.
Lemma lix_next_ok : forall bc kx segs i ss scr ss' scs scr' lx,
  sym_stepBI bc kx segs i ss scr = SOk ss' scs scr' -> lix_ok bc lx (s_log ss) -> lix_ok bc (lix_next bc i ss' lx) (s_log ss').
Proof.
  intros bc kx segs i ss scr ss' scs scr' lx H Hok. unfold sym_stepBI, sym_readBI in H.
  destruct i; try discriminate; try (cbn [lix_next]; apply mk_lix_ok);
  repeat (lazymatch type of H with
          | SOk _ _ _ = SOk _ _ _ => injection H as <- _ _
          | (match ?x with _ => _ end) = _ => destruct x
          | (let (_, _) := ?x in _) = _ => destruct x
          | (if ?x then _ else _) = _ => destruct x
          end); try discriminate; try exact Hok.
  all: cbn [lix_next s_log log_push]; apply lix_push_ok; exact Hok.
Qed.
Lemma cap_rd_log : forall K i ss, s_log (cap_rd K i ss) = s_log ss.
Proof. intros K i ss. unfold cap_rd. destruct K; [reflexivity|]. destruct (rd_of i); [|reflexivity]. destruct (bv_eqb _ _); [reflexivity|]. destruct (esize_le _ _); reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.

Definition sym_stepXBIL (bc : bctx) (kx : kix) (lx : lix) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match sym_stepBIL bc kx lx segs i ss scr with
  | SOk ss' scs scr' =>
      if Nat.leb (s_next ss) (s_next ss')
      then SOk (cap_rd K i ss') (x_filterB segs bc ss ss' scs) scr'
      else SStop
  | SStop => SStop
  end.
Lemma sym_stepXBIL_eq : forall bc kx lx K i ss scr, lix_ok bc lx (s_log ss) ->
  sym_stepXBIL bc kx lx K i ss scr = sym_stepXBI segs bc kx K i ss scr.
Proof. intros. unfold sym_stepXBIL, sym_stepXBI. rewrite sym_stepBIL_eq by assumption. reflexivity. Qed.
Lemma lix_next_okX : forall bc kx K i ss scr ss' scs scr' lx,
  sym_stepXBI segs bc kx K i ss scr = SOk ss' scs scr' -> lix_ok bc lx (s_log ss) -> lix_ok bc (lix_next bc i ss' lx) (s_log ss').
Proof.
  intros bc kx K i ss scr ss' scs scr' lx H Hok. unfold sym_stepXBI in H.
  destruct (sym_stepBI bc kx segs i ss scr) as [ss1 scs1 scr1|] eqn:E; [|discriminate].
  destruct (Nat.leb (s_next ss) (s_next ss1)); [|discriminate]. injection H as <- _ _.
  pose proof (lix_next_ok _ _ _ _ _ _ _ _ _ lx E Hok) as G.
  unfold lix_next in *. rewrite cap_rd_log. exact G.
Qed.

Fixpoint sym_execTXBIL_go (bc : bctx) (kx : kix) (lx : lix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z)
         (ss : sym_state) (ck : sym_state) : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_stepXBIL bc kx lx K i ss scr_nil with
          | SOk ss' [] _ => sym_execTXBIL_go bc kx (lix_next bc i ss' lx) t K f false stops ss' (if s_clean ss' then ss' else ck)
          | _ => if s_clean ss then ss else ck
          end
      end
  end.
Definition sym_execTXBIL (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  sym_execTXBIL_go bc kx (mk_lix bc (s_log (clr ss))) t K fuel first stops (clr ss) (clr ss).
Lemma sym_execTXBIL_go_eq : forall bc kx t K fuel lx first stops ss ck, lix_ok bc lx (s_log ss) ->
  sym_execTXBIL_go bc kx lx t K fuel first stops ss ck = sym_execTXBI_go segs bc kx t K fuel first stops ss ck.
Proof.
  intros bc kx t K fuel. induction fuel as [|f IH]; intros lx first stops ss ck Hok; [reflexivity|].
  cbn [sym_execTXBIL_go sym_execTXBI_go].
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
  rewrite sym_stepXBIL_eq by exact Hok. destruct (sym_stepXBI segs bc kx K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|reflexivity].
  destruct scs; [|reflexivity].
  apply IH. exact (lix_next_okX _ _ _ _ _ _ _ _ _ lx E Hok).
Qed.
Lemma sym_execTXBIL_eq : forall bc kx t K fuel first stops ss,
  sym_execTXBIL bc kx t K fuel first stops ss = sym_execTXBI segs bc kx t K fuel first stops ss.
Proof. intros. unfold sym_execTXBIL, sym_execTXBI. apply sym_execTXBIL_go_eq. apply mk_lix_ok. Qed.

End WithSegs.
End AX2L.
End AxSymExec3L.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import AxSymExec3.
Import AxSymExec3B.
Import AxSymExec3L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Module APC.
Import AX2. Import AX2B.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition CEIL : Z := 0x7fff7f800000.
(* [comment removed for export] *)
Definition TOPMAX : Z := 0x7fffff800000.
(* [comment removed for export] *)
Definition KHI : Z := 0x10007fff8000.
Definition MID_LO : Z := 0x7fff7000.
(* [comment removed for export] *)
Definition FLOOR : Z := KHI.
(* [comment removed for export] *)
Definition MBASE_MIN : Z := 0x154555557000.
(* [comment removed for export] *)
Definition STK_OFF : Z := - 0x800000.
Definition STK_LEN : Z := 0xC00000.
(* [comment removed for export] *)
Definition STK_VLEN : Z := 0x800000.
(* [comment removed for export] *)
Definition STK_WTOP : Z := 0x800000000000 - STK_OFF.
Definition STK_WMAX : Z := 0x800000000000 - STK_OFF - 0x7fff80000000.

(* [comment removed for export] *)
Definition V_S1 : nat := 0.     (* [comment removed for export] *)
Definition V_ARGC : nat := 1.
Definition V_ENVC : nat := 2.
Definition V_L0 : nat := 3.     (* [comment removed for export] *)
Definition V_W : nat := 4.      (* [comment removed for export] *)
Definition V_BRK : nat := 5.    (* [comment removed for export] *)
Definition V_S2 : nat := 6.     (* [comment removed for export] *)
Definition V_L1 : nat := 7.     (* [comment removed for export] *)
Definition V_UID : nat := 8.    (* [comment removed for export] *)
Definition V_HW : nat := 9.     (* [comment removed for export] *)
Definition V_SP : nat := 10.    (* [comment removed for export] *)
Definition NX0 : nat := 11.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition e_sp0 : expr := mkAlu ALU_ADD (mkMd M_MUL (ELit 32768) (EVar V_S1)) (mkAlu ALU_ADD (mkMd M_MUL (ELit 16) (EVar V_S2)) (mkMd M_MUL (ELit 4096) (EVar V_SP))).
(* [comment removed for export] *)
Definition e_pd : expr := mkAlu ALU_ADD (mkMd M_MUL (ELit 32768) (EVar V_S1)) (mkMd M_MUL (ELit 4096) (EVar V_SP)).

(* [comment removed for export] *)
Definition PID_MAX : Z := 4194304.

Record atable : Type := AT {
  img_lo : Z; img_hi : Z;          (* [comment removed for export] *)
  n_res : nat;                     (* [comment removed for export] *)
  shadow_off : Z;                  (* [comment removed for export] *)
  a_entry : Z;                     (* [comment removed for export] *)
  rw_lo : Z; rw_len : Z;           (* [comment removed for export] *)
  ph_addr_z : Z; ph_ent_z : Z; ph_num_z : Z;   (* [comment removed for export] *)
  (* [comment removed for export] *)
  x_imemset : Z; x_imemcpy : Z; x_memset : Z; x_memcpy : Z; x_memiszero : Z;
  (* [comment removed for export] *)
  x_istrncpy : Z; x_sealed : Z; x_popfree : Z;
  (* [comment removed for export] *)
  x_maxva : Z;
  (* [comment removed for export] *)
  x_envscan : Z; x_envscan_k : Z; x_pnscan : Z; x_pnscan_k : Z;
  stops_more : list Z              (* [comment removed for export] *)
}.

Section WithSegs.
Variable segs : list Segment.
Variable IT : itab.
Variable A : atable.
Variable nx0 : nat.     (* [comment removed for export] *)
Variable LIMIT : Z.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive spiece : Type := SPLit (bs : list Z) | SPBlob (k : nat).

Inductive shape : Type :=
| SNil
| SExit (code : Z)
| SEmitP (fd : Z) (ps : list spiece) (s : shape)   (* [comment removed for export] *)
| SAlt2 (a b : shape)
| SCase (e : expr) (mid : Z) (s1 s2 : shape)
| SHole (h : nat)                            (* [comment removed for export] *)
| SNext.                                     (* [comment removed for export] *)

Definition salt2 (a b : shape) : shape :=
  match a, b with SNil, _ => b | _, SNil => a | _, _ => SAlt2 a b end.

Fixpoint listZ_eqb (x y : list Z) : bool :=
  match x, y with [], [] => true | a :: x', b :: y' => Z.eqb a b && listZ_eqb x' y' | _, _ => false end.
Definition spiece_eqb (x y : spiece) : bool :=
  match x, y with SPLit a, SPLit b => listZ_eqb a b | SPBlob k, SPBlob k' => Nat.eqb k k' | _, _ => false end.
Fixpoint spieces_eqb (x y : list spiece) : bool :=
  match x, y with [], [] => true | a :: x', b :: y' => spiece_eqb a b && spieces_eqb x' y' | _, _ => false end.
Fixpoint shape_eqb (x y : shape) : bool :=
  match x, y with
  | SNil, SNil => true
  | SExit c, SExit c' => Z.eqb c c'
  | SEmitP fd ps s, SEmitP fd' ps' s' => Z.eqb fd fd' && spieces_eqb ps ps' && shape_eqb s s'
  | SAlt2 a b, SAlt2 a' b' => shape_eqb a a' && shape_eqb b b'
  | SCase e m a b, SCase e' m' a' b' => expr_eqb e e' && Z.eqb m m' && shape_eqb a a' && shape_eqb b b'
  | SHole h, SHole h' => Nat.eqb h h'
  | SNext, SNext => true
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive mkind : Type := KRW | KRWLAZY | KNONE | KNONELAZY | KFOG | KHOLE.   (* [comment removed for export] *)

Definition mkind_eqb (a b : mkind) : bool :=
  match a, b with
  | KRW, KRW | KRWLAZY, KRWLAZY | KNONE, KNONE | KNONELAZY, KNONELAZY | KFOG, KFOG | KHOLE, KHOLE => true
  | _, _ => false
  end.

(* [comment removed for export] *)
Record amap : Type := AM {
  am_base : expr;       (* [comment removed for export] *)
  am_len  : expr;       (* [comment removed for export] *)
  am_kind : mkind
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_tok_kind (k : mkind) : bool := match k with KFOG | KHOLE => true | _ => false end.
Definition is_hole (m : amap) : bool := mkind_eqb (am_kind m) KHOLE.
Definition is_fog (m : amap) : bool := is_tok_kind (am_kind m).
Definition no_fog (ms : list amap) : bool := forallb (fun m => negb (is_fog m)) ms.
Definition no_holes (ms : list amap) : bool := forallb (fun m => negb (is_hole m)) ms.


(* [comment removed for export] *)
Inductive afd : Type :=
| FdStd                                   (* [comment removed for export] *)
| FdFile (k : nat) (len off : expr)       (* [comment removed for export] *)
| FdDir.                                  (* [comment removed for export] *)

Record acs : Type := ACS {
  a_ss    : sym_state;          (* [comment removed for export] *)
  a_maps  : list amap;          (* [comment removed for export] *)
  a_totsz : Z;                  (* [comment removed for export] *)
  a_ylo   : Z;                  (* [comment removed for export] *)
  a_eager : Z;                  (* [comment removed for export] *)
  a_vis   : list (expr * expr); (* [comment removed for export] *)
  a_ghost : list (expr * expr); (* [comment removed for export] *)
  a_abytes : Z;                 (* [comment removed for export] *)
  a_brk   : expr;               (* [comment removed for export] *)
  a_fd    : afd;
  a_tidset : bool               (* [comment removed for export] *)
}.

Definition reg (cs : acs) (n : nat) : expr := nth n (s_regs (a_ss cs)) (ELit 0).
Definition kn (cs : acs) : list kentry := s_know (a_ss cs).
Definition pc (cs : acs) : Z := s_pc (a_ss cs).
Definition nxt (cs : acs) : nat := s_next (a_ss cs).

Definition with_ss (cs : acs) (ss : sym_state) : acs :=
  ACS ss (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).
Definition mk_ss (p : Z) (sr : list expr) (k : list kentry) (nx : nat) : sym_state := SS p sr [] k nx.
Definition set_reg (cs : acs) (n : nat) (e : expr) : acs :=
  let ss := a_ss cs in with_ss cs (mk_ss (s_pc ss) (sr_upd (s_regs ss) n e) (s_know ss) (s_next ss)).
Definition set_pc (cs : acs) (p : Z) : acs :=
  let ss := a_ss cs in with_ss cs (mk_ss p (s_regs ss) (s_know ss) (s_next ss)).
Definition set_kn (cs : acs) (k : list kentry) : acs :=
  let ss := a_ss cs in with_ss cs (mk_ss (s_pc ss) (s_regs ss) k (s_next ss)).
Definition add_kn (cs : acs) (k : list kentry) : acs := set_kn cs (k ++ kn cs).
Definition bump (cs : acs) (d : nat) : acs :=
  let ss := a_ss cs in with_ss cs (mk_ss (s_pc ss) (s_regs ss) (s_know ss) (s_next ss + d)).
Definition set_regs (cs : acs) (sr : list expr) : acs :=
  let ss := a_ss cs in with_ss cs (mk_ss (s_pc ss) sr (s_know ss) (s_next ss)).

Definition lit_of (e : expr) : option Z := match e with ELit z => Some (z mod two64) | _ => None end.
Definition reg_lit (cs : acs) (n : nat) : option Z := lit_of (reg cs n).

(* [comment removed for export] *)
Definition eadd (a b : expr) : expr := mkAlu ALU_ADD a b.
Definition esub (a b : expr) : expr := mkAlu ALU_SUB a b.
Definition escale (c : Z) (e : expr) : expr := mkMd M_MUL (ELit c) e.
Definition eaddz (a : expr) (z : Z) : expr := mkAlu ALU_ADD a (ELit z).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint expr_vars (e : expr) (acc : list nat) : list nat :=
  match e with
  | ELit _ => acc
  | EVar n => if existsb (Nat.eqb n) acc then acc else n :: acc
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars x (expr_vars y acc)
  | EExt _ _ _ x => expr_vars x acc
  | EBlob _ _ _ _ => acc
  end.

Definition live_vars (cs : acs) : list nat :=
  let acc := fold_right expr_vars [] (s_regs (a_ss cs)) in
  let acc := fold_right (fun K acc => match K with
                                      | KWord a _ v => expr_vars (a_base a) (expr_vars v acc)
                                      | KZero a n => expr_vars (a_base a) (expr_vars n acc)
                                      | KBlob a n _ => expr_vars (a_base a) (expr_vars n acc)
                                      | KWr a n => expr_vars (a_base a) (expr_vars n acc)
                                      | KFill a n _ => expr_vars (a_base a) (expr_vars n acc)
                                      | KUnk a n => expr_vars (a_base a) (expr_vars n acc)
                                      | _ => acc end) acc (kn cs) in
  let acc := fold_right (fun m acc => expr_vars (am_base m) (expr_vars (am_len m) acc)) acc (a_maps cs) in
  let acc := fold_right (fun p acc => expr_vars (fst p) (expr_vars (snd p) acc)) acc (a_vis cs) in
  let acc := fold_right (fun p acc => expr_vars (fst p) (expr_vars (snd p) acc)) acc (a_ghost cs) in
  let acc := match a_fd cs with FdFile _ l o => expr_vars l (expr_vars o acc) | _ => acc end in
  expr_vars (a_brk cs) acc.

Definition all_live (live : list nat) (e : expr) : bool :=
  forallb (fun v => Nat.ltb v nx0 || existsb (Nat.eqb v) live) (expr_vars e []).

Definition kn_gc_entry (spb : expr) (spk : Z) (live : list nat) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => negb (expr_eqb b spb && Z.leb (k + Z.of_nat w) spk)
  | KZero (SA b k) (ELit n) => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KBlob (SA b k) (ELit n) _ => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KFill (SA b k) (ELit n) _ => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KUnk (SA b k) (ELit n) => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KRange e _ _ => all_live live e
  | KAlign e _ => all_live live e
  | KDisj a1 n1 a2 n2 => all_live live (a_base a1) && all_live live n1 && all_live live (a_base a2) && all_live live n2
  | _ => true
  end%bool.

Definition cs_gc_ref (cs : acs) : acs :=
  let '(spb, spk) := split_lit (reg cs 2) in
  let live := live_vars cs in
  set_kn cs (List.filter (kn_gc_entry spb spk live) (kn cs)).

(* [comment removed for export] *)
Definition vkey (n : nat) : positive := Pos.of_succ_nat n.
Fixpoint expr_vars_t (e : expr) (acc : ptree unit) : ptree unit :=
  match e with
  | ELit _ => acc
  | EVar n => pt_set (vkey n) tt acc
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_t x (expr_vars_t y acc)
  | EExt _ _ _ x => expr_vars_t x acc
  | EBlob _ _ _ _ => acc
  end.
Definition live_vars_t (cs : acs) : ptree unit :=
  let acc := fold_right expr_vars_t PTLeaf (s_regs (a_ss cs)) in
  let acc := fold_right (fun K acc => match K with
                                      | KWord a _ v => expr_vars_t (a_base a) (expr_vars_t v acc)
                                      | KZero a n => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KBlob a n _ => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KWr a n => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KFill a n _ => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KUnk a n => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | _ => acc end) acc (kn cs) in
  let acc := fold_right (fun m acc => expr_vars_t (am_base m) (expr_vars_t (am_len m) acc)) acc (a_maps cs) in
  let acc := fold_right (fun p acc => expr_vars_t (fst p) (expr_vars_t (snd p) acc)) acc (a_vis cs) in
  let acc := fold_right (fun p acc => expr_vars_t (fst p) (expr_vars_t (snd p) acc)) acc (a_ghost cs) in
  let acc := match a_fd cs with FdFile _ l o => expr_vars_t l (expr_vars_t o acc) | _ => acc end in
  expr_vars_t (a_brk cs) acc.
Definition in_live_t (t : ptree unit) (v : nat) : bool :=
  match pt_get t (vkey v) with Some _ => true | None => false end.
Fixpoint expr_all_live_t (t : ptree unit) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => if Nat.ltb n nx0 then true else in_live_t t n
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => if expr_all_live_t t x then expr_all_live_t t y else false
  | EExt _ _ _ x => expr_all_live_t t x
  | EBlob _ _ _ _ => true
  end.
Definition kn_gc_entry_t (spb : expr) (spk : Z) (t : ptree unit) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => negb (expr_eqb b spb && Z.leb (k + Z.of_nat w) spk)
  | KZero (SA b k) (ELit n) => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KBlob (SA b k) (ELit n) _ => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KFill (SA b k) (ELit n) _ => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KUnk (SA b k) (ELit n) => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KRange e _ _ => expr_all_live_t t e
  | KAlign e _ => expr_all_live_t t e
  | KDisj a1 n1 a2 n2 => expr_all_live_t t (a_base a1) && expr_all_live_t t n1 && expr_all_live_t t (a_base a2) && expr_all_live_t t n2
  | _ => true
  end%bool.
Definition cs_gc (cs : acs) : acs :=
  let '(spb, spk) := split_lit (reg cs 2) in
  let live := live_vars_t cs in
  set_kn cs (List.filter (kn_gc_entry_t spb spk live) (kn cs)).

(* [comment removed for export] *)
Definition live_agree (acc : list nat) (t : ptree unit) : Prop :=
  forall v, existsb (Nat.eqb v) acc = in_live_t t v.
Lemma vkey_inj : forall a b, vkey a = vkey b -> a = b.
Proof. intros a b H. unfold vkey in H. apply (f_equal Pos.to_nat) in H. rewrite !Pnat.SuccNat2Pos.id_succ in H. congruence. Qed.
Lemma live_agree_var : forall acc t n,
  live_agree acc t -> live_agree (if existsb (Nat.eqb n) acc then acc else n :: acc) (pt_set (vkey n) tt t).
Proof.
  intros acc t n H v. unfold in_live_t.
  destruct (Nat.eq_dec v n) as [->|NE].
  - rewrite pt_gss. destruct (existsb (Nat.eqb n) acc) eqn:E; [exact E|]. cbn [existsb]. rewrite Nat.eqb_refl. reflexivity.
  - rewrite pt_gso by (intros HK; apply NE; apply vkey_inj; exact HK).
    fold (in_live_t t v). rewrite <- (H v).
    destruct (existsb (Nat.eqb n) acc); [reflexivity|]. cbn [existsb].
    destruct (Nat.eqb_spec v n); [contradiction|]. reflexivity.
Qed.
Lemma live_agree_expr : forall e acc t, live_agree acc t -> live_agree (expr_vars e acc) (expr_vars_t e t).
Proof.
  induction e; intros acc t H; cbn [expr_vars expr_vars_t]; try exact H; try (apply live_agree_var; exact H); auto.
Qed.
Lemma live_agree_fold : forall (X : Type) (f : X -> list nat -> list nat) (g : X -> ptree unit -> ptree unit) (l : list X) acc t,
  (forall a acc t, live_agree acc t -> live_agree (f a acc) (g a t)) ->
  live_agree acc t -> live_agree (fold_right f acc l) (fold_right g t l).
Proof. intros X f g l acc t Hfg H. induction l as [|a r IH]; [exact H|]. cbn [fold_right]. apply Hfg. exact IH. Qed.
Lemma live_vars_agree : forall cs, live_agree (live_vars cs) (live_vars_t cs).
Proof.
  intros cs. unfold live_vars, live_vars_t.
  apply live_agree_expr.
  assert (A0 : live_agree [] PTLeaf) by (intros v; unfold in_live_t; rewrite pt_get_leaf; reflexivity).
  match goal with |- live_agree (match a_fd cs with _ => _ end) _ =>
    assert (A5 : forall acc t, live_agree acc t ->
      live_agree (match a_fd cs with FdFile _ l o => expr_vars l (expr_vars o acc) | _ => acc end)
                 (match a_fd cs with FdFile _ l o => expr_vars_t l (expr_vars_t o t) | _ => t end))
      by (intros acc t H; destruct (a_fd cs); repeat apply live_agree_expr; exact H);
    apply A5 end.
  apply live_agree_fold; [intros; repeat apply live_agree_expr; assumption|].
  apply live_agree_fold; [intros; repeat apply live_agree_expr; assumption|].
  apply live_agree_fold; [intros; repeat apply live_agree_expr; assumption|].
  apply live_agree_fold; [intros a acc t H; destruct a as [[] ? ?|[] ?|[] ? ?| | | |[] ?| |[] ? ?|[] ?]; repeat apply live_agree_expr; assumption|].
  apply live_agree_fold; [intros; repeat apply live_agree_expr; assumption|].
  exact A0.
Qed.
Lemma forallb_expr_vars : forall P e acc,
  forallb P (expr_vars e acc) = (forallb P (expr_vars e []) && forallb P acc)%bool.
Proof.
  intros P e. induction e; intros acc; cbn [expr_vars]; try reflexivity.
  - destruct (existsb (Nat.eqb n) acc) eqn:E; cbn [existsb forallb].
    + rewrite Bool.andb_true_r. destruct (P n) eqn:Pn; [reflexivity|]. cbn [andb].
      destruct (forallb P acc) eqn:F; [|reflexivity]. exfalso.
      apply existsb_exists in E as [x [Hx Ex]]. apply Nat.eqb_eq in Ex. subst x.
      pose proof (proj1 (forallb_forall P acc) F n Hx) as C. rewrite Pn in C. discriminate.
    + rewrite Bool.andb_true_r. reflexivity.
  - rewrite IHe1, IHe2, (IHe1 (expr_vars e2 [])). rewrite Bool.andb_assoc. reflexivity.
  - rewrite IHe1, IHe2, (IHe1 (expr_vars e2 [])). rewrite Bool.andb_assoc. reflexivity.
  - rewrite IHe1, IHe2, (IHe1 (expr_vars e2 [])). rewrite Bool.andb_assoc. reflexivity.
  - rewrite IHe1, IHe2, (IHe1 (expr_vars e2 [])). rewrite Bool.andb_assoc. reflexivity.
  - apply IHe.
Qed.
Lemma expr_all_live_t_eq : forall acc t e, live_agree acc t -> expr_all_live_t t e = all_live acc e.
Proof.
  intros acc t e H. unfold all_live. induction e; cbn [expr_all_live_t expr_vars existsb forallb]; try reflexivity.
  - rewrite <- (H n). cbn. rewrite Bool.andb_true_r. destruct (Nat.ltb n nx0); reflexivity.
  - rewrite forallb_expr_vars, IHe1, IHe2. destruct (forallb _ (expr_vars e1 [])); reflexivity.
  - rewrite forallb_expr_vars, IHe1, IHe2. destruct (forallb _ (expr_vars e1 [])); reflexivity.
  - rewrite forallb_expr_vars, IHe1, IHe2. destruct (forallb _ (expr_vars e1 [])); reflexivity.
  - rewrite forallb_expr_vars, IHe1, IHe2. destruct (forallb _ (expr_vars e1 [])); reflexivity.
  - exact IHe.
Qed.
Lemma cs_gc_eq : forall cs, cs_gc cs = cs_gc_ref cs.
Proof.
  intros cs. unfold cs_gc, cs_gc_ref. destruct (split_lit (reg cs 2)) as [spb spk].
  f_equal. apply filter_ext. intros K.
  pose proof (live_vars_agree cs) as H.
  destruct K as [[b kk] w v|[b kk] l|[b kk] l bk|lo hi|e m|e lo hi|[b kk] n|a1 n1 a2 n2|[b kk] l c|[b kk] l]; cbn [kn_gc_entry kn_gc_entry_t];
    rewrite ?(expr_all_live_t_eq _ _ _ H); reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint expr_vars_lt (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => Nat.ltb n b
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_lt b x && expr_vars_lt b y
  | EExt _ _ _ x => expr_vars_lt b x
  | EBlob _ _ _ _ => true
  end.
Definition saddr_vars_lt (b : nat) (a : saddr) : bool := expr_vars_lt b (a_base a).

(* [comment removed for export] *)
Fixpoint shape_vars_lt (b : nat) (s : shape) : bool :=
  match s with
  | SNil | SExit _ | SHole _ | SNext => true
  | SEmitP _ _ s' => shape_vars_lt b s'
  | SAlt2 x y => shape_vars_lt b x && shape_vars_lt b y
  | SCase e _ x y => expr_vars_lt b e && shape_vars_lt b x && shape_vars_lt b y
  end.
Definition kentry_vars_lt (b : nat) (K : kentry) : bool :=
  match K with
  | KWord a _ v => saddr_vars_lt b a && expr_vars_lt b v
  | KZero a n => saddr_vars_lt b a && expr_vars_lt b n
  | KBlob a n _ => saddr_vars_lt b a && expr_vars_lt b n
  | KImg _ _ => true
  | KAlign e _ => expr_vars_lt b e
  | KRange e _ _ => expr_vars_lt b e
  | KWr a n => saddr_vars_lt b a && expr_vars_lt b n
  | KDisj a1 n1 a2 n2 => saddr_vars_lt b a1 && expr_vars_lt b n1 && saddr_vars_lt b a2 && expr_vars_lt b n2
  | KFill a n _ => saddr_vars_lt b a && expr_vars_lt b n
  | KUnk a n => saddr_vars_lt b a && expr_vars_lt b n
  end.
Fixpoint sr_vars_lt (b : nat) (sr : list expr) : bool :=
  match sr with [] => true | e :: r => expr_vars_lt b e && sr_vars_lt b r end.
Fixpoint kn_vars_lt (b : nat) (k : list kentry) : bool :=
  match k with [] => true | K :: r => kentry_vars_lt b K && kn_vars_lt b r end.
Definition pairs_vars_lt (b : nat) (l : list (expr * expr)) : bool :=
  forallb (fun p => expr_vars_lt b (fst p) && expr_vars_lt b (snd p)) l.
Definition maps_vars_lt (b : nat) (ms : list amap) : bool :=
  forallb (fun m => expr_vars_lt b (am_base m) && expr_vars_lt b (am_len m)) ms.
Definition fd_vars_lt (b : nat) (f : afd) : bool :=
  match f with FdStd => true | FdFile _ l o => expr_vars_lt b l && expr_vars_lt b o | FdDir => true end.
(* [comment removed for export] *)
Definition fresh_ok (cs : acs) : bool :=
  let v := nxt cs in
  sr_vars_lt v (s_regs (a_ss cs)) && kn_vars_lt v (kn cs)
  && maps_vars_lt v (a_maps cs) && pairs_vars_lt v (a_vis cs) && pairs_vars_lt v (a_ghost cs)
  && expr_vars_lt v (a_brk cs) && fd_vars_lt v (a_fd cs) && Nat.leb nx0 v && Nat.leb NX0 v.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dd_key (a : saddr) : option positive :=
  match a with SA (ELit Z0) (Zpos p) => Some p | _ => None end.
Record ddseen : Type := DDS { dd_lit : ptree (list nat); dd_oth : list (saddr * nat) }.
Definition dd_has (s : ddseen) (a : saddr) (w : nat) : bool :=
  match dd_key a with
  | Some p => match pt_get (dd_lit s) p with Some ws => existsb (Nat.eqb w) ws | None => false end
  | None => existsb (fun aw => saddr_eqb a (fst aw) && Nat.eqb w (snd aw))%bool (dd_oth s)
  end.
Definition dd_add (s : ddseen) (a : saddr) (w : nat) : ddseen :=
  match dd_key a with
  | Some p => DDS (pt_set p (w :: match pt_get (dd_lit s) p with Some ws => ws | None => [] end) (dd_lit s)) (dd_oth s)
  | None => DDS (dd_lit s) ((a, w) :: dd_oth s)
  end.
Fixpoint log_dd_go (s : ddseen) (log : list sentry) : list sentry :=
  match log with
  | [] => []
  | SE a w v :: older => if dd_has s a w then log_dd_go s older else SE a w v :: log_dd_go (dd_add s a w) older
  end.
Definition log_dd (log : list sentry) : list sentry := log_dd_go (DDS PTLeaf []) log.

Definition run_block_ref (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  if fresh_ok cs then
    let ss := a_ss cs in
    let ss' := sym_execTX segs IT K fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    match carry (log_dd (s_log ss')) (s_know ss') [] with
    | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
    | _ => None
    end
  else None.
(* [comment removed for export] *)
Definition run_block (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  if fresh_ok cs then
    let ss := a_ss cs in
    let bc := mkbc (facts_of (s_know ss)) in
    let kx := mk_kix (s_know ss) in                 (* [comment removed for export] *)
    (* [comment removed for export] *)
    let ss' := AX2L.sym_execTXBIL segs bc kx IT K fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    match carryK bc (log_dd (s_log ss')) (s_know ss') [] with
    | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
    | _ => None
    end
  else None.
Lemma run_block_eq : forall K fuel stops cs, run_block K fuel stops cs = run_block_ref K fuel stops cs.
Proof.
  intros. unfold run_block, run_block_ref. destruct (fresh_ok cs); [|reflexivity]. cbv zeta.
  rewrite AX2L.sym_execTXBIL_eq.
  rewrite (sym_execTXBI_eq segs (s_know (a_ss cs))) by reflexivity.
  rewrite <- (sym_execTX_know segs IT K fuel true stops (SS (s_pc (a_ss cs)) (s_regs (a_ss cs)) [] (s_know (a_ss cs)) (s_next (a_ss cs)))) at 1.
  rewrite carryK_eq. reflexivity.
Qed.

Definition run_block_gc (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  match run_block K fuel stops cs with Some cs' => Some (cs_gc cs') | None => None end.

Definition kentry_eqb (x y : kentry) : bool :=
  match x, y with
  | KWord a w v, KWord a' w' v' => saddr_eqb a a' && Nat.eqb w w' && expr_eqb v v'
  | KZero a n, KZero a' n' => saddr_eqb a a' && expr_eqb n n'
  | KBlob a n k, KBlob a' n' k' => saddr_eqb a a' && expr_eqb n n' && Nat.eqb k k'
  | KImg lo hi, KImg lo' hi' => Z.eqb lo lo' && Z.eqb hi hi'
  | KAlign e m, KAlign e' m' => expr_eqb e e' && Z.eqb m m'
  | KRange e lo hi, KRange e' lo' hi' => expr_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
  | KWr a n, KWr a' n' => saddr_eqb a a' && expr_eqb n n'
  | KDisj a1 n1 a2 n2, KDisj a1' n1' a2' n2' => saddr_eqb a1 a1' && expr_eqb n1 n1' && saddr_eqb a2 a2' && expr_eqb n2 n2'
  | KFill a n c, KFill a' n' c' => saddr_eqb a a' && expr_eqb n n' && Z.eqb c c'
  | KUnk a n, KUnk a' n' => saddr_eqb a a' && expr_eqb n n'
  | _, _ => false
  end.

Definition amap_eqb (x y : amap) : bool :=
  expr_eqb (am_base x) (am_base y) && expr_eqb (am_len x) (am_len y) && mkind_eqb (am_kind x) (am_kind y).

Fixpoint list_eqb {T : Type} (eqb : T -> T -> bool) (x y : list T) : bool :=
  match x, y with
  | [], [] => true
  | a :: x', b :: y' => eqb a b && list_eqb eqb x' y'
  | _, _ => false
  end.

Definition pair_eqb (x y : expr * expr) : bool := expr_eqb (fst x) (fst y) && expr_eqb (snd x) (snd y).

Definition afd_eqb (x y : afd) : bool :=
  match x, y with
  | FdStd, FdStd => true
  | FdDir, FdDir => true
  | FdFile k l o, FdFile k' l' o' => Nat.eqb k k' && expr_eqb l l' && expr_eqb o o'
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kentry_apart_b (allkn : list kentry) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => Nat.leb w 8 && ranges_apart_x allkn ub uk un b k (ELit (Z.of_nat w))
  | KZero (SA b k) l => ranges_apart_x allkn ub uk un b k l
  | KBlob (SA b k) l _ => ranges_apart_x allkn ub uk un b k l
  | KImg lo hi => Z.leb 0 lo && Z.leb lo hi && Z.ltb (hi - lo) two64 && ranges_apart_x allkn ub uk un (ELit 0) lo (ELit (hi - lo))
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b k) n => ranges_apart_x allkn ub uk un b k n
  | KFill (SA b k) l _ => ranges_apart_x allkn ub uk un b k l
  | KUnk (SA b k) l => ranges_apart_x allkn ub uk un b k l
  end.

Definition kentry_apart_bB (bc : bctx) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => Nat.leb w 8 && ranges_apart_xB bc ub uk un b k (ELit (Z.of_nat w))
  | KZero (SA b k) l => ranges_apart_xB bc ub uk un b k l
  | KBlob (SA b k) l _ => ranges_apart_xB bc ub uk un b k l
  | KImg lo hi => Z.leb 0 lo && Z.leb lo hi && Z.ltb (hi - lo) two64 && ranges_apart_xB bc ub uk un (ELit 0) lo (ELit (hi - lo))
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b k) n => ranges_apart_xB bc ub uk un b k n
  | KFill (SA b k) l _ => ranges_apart_xB bc ub uk un b k l
  | KUnk (SA b k) l => ranges_apart_xB bc ub uk un b k l
  end.

Lemma kentry_apart_bB_eqf : forall fk, kentry_apart_bB (mkbc fk) = kentry_apart_b fk.
Proof. intros. bcfe. unfold kentry_apart_bB, kentry_apart_b. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kentry_apart_bB_eqf : bceq.


(* [comment removed for export] *)
Definition kentry_apart_bp (allkn : list kentry) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => Nat.leb w 8 && ranges_apart_p allkn sp ub uk un b k (ELit (Z.of_nat w))
  | KZero (SA b k) l => ranges_apart_p allkn sp ub uk un b k l
  | KBlob (SA b k) l _ => ranges_apart_p allkn sp ub uk un b k l
  | KImg lo hi => Z.leb 0 lo && Z.leb lo hi && Z.ltb (hi - lo) two64 && ranges_apart_p allkn sp ub uk un (ELit 0) lo (ELit (hi - lo))
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b k) n => ranges_apart_p allkn sp ub uk un b k n
  | KFill (SA b k) l _ => ranges_apart_p allkn sp ub uk un b k l
  | KUnk (SA b k) l => ranges_apart_p allkn sp ub uk un b k l
  end.

Definition kentry_apart_bpB (bc : bctx) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => Nat.leb w 8 && ranges_apart_pB bc sp ub uk un b k (ELit (Z.of_nat w))
  | KZero (SA b k) l => ranges_apart_pB bc sp ub uk un b k l
  | KBlob (SA b k) l _ => ranges_apart_pB bc sp ub uk un b k l
  | KImg lo hi => Z.leb 0 lo && Z.leb lo hi && Z.ltb (hi - lo) two64 && ranges_apart_pB bc sp ub uk un (ELit 0) lo (ELit (hi - lo))
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b k) n => ranges_apart_pB bc sp ub uk un b k n
  | KFill (SA b k) l _ => ranges_apart_pB bc sp ub uk un b k l
  | KUnk (SA b k) l => ranges_apart_pB bc sp ub uk un b k l
  end.

Lemma kentry_apart_bpB_eqf : forall fk, kentry_apart_bpB (mkbc fk) = kentry_apart_bp fk.
Proof. intros. bcfe. unfold kentry_apart_bpB, kentry_apart_bp. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kentry_apart_bpB_eqf : bceq.



Definition kimg_b (K : kentry) : bool := match K with KImg _ _ => true | _ => false end.

(* [comment removed for export] *)
Definition kn_unfill (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.filter (fun K => kimg_b K || kentry_apart_bp k sp ub uk un K) k.

Definition kn_unfillB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.filter (fun K => kimg_b K || kentry_apart_bpB bc sp ub uk un K) (bc_fk bc).

Lemma kn_unfillB_eqf : forall fk, kn_unfillB (mkbc fk) = kn_unfill fk.
Proof. intros. bcfe. unfold kn_unfillB, kn_unfill. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_unfillB_eqf : bceq.

Definition kn_unfillM (k : list kentry) := kn_unfillB (mkbc k).
Lemma kn_unfillM_eq : kn_unfillM = kn_unfill. Proof. apply functional_extensionality; intros k. unfold kn_unfillM. apply kn_unfillB_eqf. Qed.



(* [comment removed for export] *)
Definition kwr_b (K : kentry) : bool := match K with KWr _ _ => true | _ => false end.
Definition havoc1 (k : list kentry) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if (kwr_b K || kentry_apart_b k ub uk un K)%bool then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cut k ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cut c k ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cut k ub uk un kb kk len
       | _ => []
       end.

Definition havoc1B (bc : bctx) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if (kwr_b K || kentry_apart_bB bc ub uk un K)%bool then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
       | _ => []
       end.

Lemma havoc1B_eqf : forall fk, havoc1B (mkbc fk) = havoc1 fk.
Proof. intros. bcfe. unfold havoc1B, havoc1. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite havoc1B_eqf : bceq.


Definition havoc1p (k : list kentry) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if (kwr_b K || kentry_apart_bp k sp ub uk un K)%bool then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cut k ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cut c k ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cut k ub uk un kb kk len
       | _ => []
       end.

Definition havoc1pB (bc : bctx) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if (kwr_b K || kentry_apart_bpB bc sp ub uk un K)%bool then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
       | _ => []
       end.

Lemma havoc1pB_eqf : forall fk, havoc1pB (mkbc fk) = havoc1p fk.
Proof. intros. bcfe. unfold havoc1pB, havoc1p. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite havoc1pB_eqf : bceq.


Definition kn_havoc (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.flat_map (havoc1p k sp ub uk un) k.

Definition kn_havocB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.flat_map (havoc1pB bc sp ub uk un) (bc_fk bc).

Lemma kn_havocB_eqf : forall fk, kn_havocB (mkbc fk) = kn_havoc fk.
Proof. intros. bcfe. unfold kn_havocB, kn_havoc. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_havocB_eqf : bceq.

Definition kn_havocM (k : list kentry) := kn_havocB (mkbc k).
Lemma kn_havocM_eq : kn_havocM = kn_havoc. Proof. apply functional_extensionality; intros k. unfold kn_havocM. apply kn_havocB_eqf. Qed.



(* [comment removed for export] *)
Definition kwr_cut (k : list kentry) (ub : expr) (uk : Z) (un : expr) (kb : expr) (kk : Z) (len : expr) : list kentry :=
  kcut KWr k ub uk un kb kk len.

Definition kwr_cutB (bc : bctx) (ub : expr) (uk : Z) (un : expr) (kb : expr) (kk : Z) (len : expr) : list kentry :=
  kcutB bc KWr ub uk un kb kk len.

Lemma kwr_cutB_eqf : forall fk, kwr_cutB (mkbc fk) = kwr_cut fk.
Proof. intros. bcfe. unfold kwr_cutB, kwr_cut. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kwr_cutB_eqf : bceq.


Definition cutout1 (k : list kentry) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if kentry_apart_b k ub uk un K then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cut k ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cut c k ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cut k ub uk un kb kk len
       | KWr (SA kb kk) len => kwr_cut k ub uk un kb kk len
       | _ => []
       end.

Definition cutout1B (bc : bctx) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if kentry_apart_bB bc ub uk un K then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
       | KWr (SA kb kk) len => kwr_cutB bc ub uk un kb kk len
       | _ => []
       end.

Lemma cutout1B_eqf : forall fk, cutout1B (mkbc fk) = cutout1 fk.
Proof. intros. bcfe. unfold cutout1B, cutout1. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite cutout1B_eqf : bceq.


Definition cutout1p (k : list kentry) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if kentry_apart_bp k sp ub uk un K then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cut k ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cut c k ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cut k ub uk un kb kk len
       | KWr (SA kb kk) len => kwr_cut k ub uk un kb kk len
       | _ => []
       end.

Definition cutout1pB (bc : bctx) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if kentry_apart_bpB bc sp ub uk un K then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
       | KWr (SA kb kk) len => kwr_cutB bc ub uk un kb kk len
       | _ => []
       end.

Lemma cutout1pB_eqf : forall fk, cutout1pB (mkbc fk) = cutout1p fk.
Proof. intros. bcfe. unfold cutout1pB, cutout1p. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite cutout1pB_eqf : bceq.


Definition kn_cutout (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.flat_map (cutout1p k sp ub uk un) k.

Definition kn_cutoutB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.flat_map (cutout1pB bc sp ub uk un) (bc_fk bc).

Lemma kn_cutoutB_eqf : forall fk, kn_cutoutB (mkbc fk) = kn_cutout fk.
Proof. intros. bcfe. unfold kn_cutoutB, kn_cutout. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_cutoutB_eqf : bceq.

Definition kn_cutoutM (k : list kentry) := kn_cutoutB (mkbc k).
Lemma kn_cutoutM_eq : kn_cutoutM = kn_cutout. Proof. apply functional_extensionality; intros k. unfold kn_cutoutM. apply kn_cutoutB_eqf. Qed.



(* [comment removed for export] *)
Definition kn_keep (k : list kentry) (ws : list (expr * expr)) : list kentry :=
  let wss := map (fun w => (split_lit (fst w), xlo k (snd w))) ws in
  let test (b : expr) (o : Z) (n : option Z) : bool :=
    let mine := List.filter (fun w => expr_eqb (fst (fst w)) b) wss in
    match mine with
    | [] => true
    | _ => existsb (fun w => let wk := snd (fst w) in
                             match snd w with
                             | Some wl => Z.ltb 0 wl && Z.ltb wk (match n with Some n => o + n | None => wk + 1 end) && Z.ltb o (wk + wl)
                             | None => true
                             end) mine
    end in
  List.filter (fun K => match K with
                        | KWord (SA b o) w _ => test b o (Some (Z.of_nat w))
                        | KZero (SA b o) n => test b o (xhi k n)
                        | KBlob (SA b o) n _ => test b o (xhi k n)
                        | KFill (SA b o) n _ => test b o (xhi k n)
                        | KUnk (SA b o) n => test b o (xhi k n)
                        | _ => true
                        end) k.

(* [comment removed for export] *)
Definition kimg_cut1 (a n : Z) (K : kentry) : list kentry :=
  match K with
  | KImg lo hi =>
      if (Z.leb hi a || Z.leb (a + n) lo)%bool then [K]
      else (if Z.ltb lo a then [KImg lo a] else []) ++ (if Z.ltb (a + n) hi then [KImg (a + n) hi] else [])
  | _ => [K]
  end.
Definition kimg_cut (k : list kentry) (a n : Z) : list kentry := List.flat_map (kimg_cut1 a n) k.

(* [comment removed for export] *)
Definition kimg_clip (k : list kentry) : list kentry :=
  List.filter (fun K => match K with KImg lo hi => Z.leb (img_lo A) lo && Z.leb lo hi && Z.leb hi (img_hi A) | _ => true end) k.

(* [comment removed for export] *)
Definition kreadZ (k : list kentry) (b : expr) (off : Z) (n : nat) : option Z :=
  match know_lookup segs k b off n false [] [] with
  | LHit (ELit z) [] _ => Some (z mod two64)
  | _ => None
  end.

Definition kreadZB (bc : bctx) (b : expr) (off : Z) (n : nat) : option Z :=
  match know_lookupB segs bc b off n false [] [] with
  | LHit (ELit z) [] _ => Some (z mod two64)
  | _ => None
  end.

Lemma kreadZB_eqf : forall fk, kreadZB (mkbc fk) = kreadZ fk.
Proof. intros. bcfe. unfold kreadZB, kreadZ. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kreadZB_eqf : bceq.


(* [comment removed for export] *)
Definition kread8e (k : list kentry) (b : expr) (off : Z) : option expr :=
  match know_lookup segs k b off 8 false [] [] with
  | LHit v [] _ => Some v
  | _ => None
  end.

Definition kread8eB (bc : bctx) (b : expr) (off : Z) : option expr :=
  match know_lookupB segs bc b off 8 false [] [] with
  | LHit v [] _ => Some v
  | _ => None
  end.

Lemma kread8eB_eqf : forall fk, kread8eB (mkbc fk) = kread8e fk.
Proof. intros. bcfe. unfold kread8eB, kread8e. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kread8eB_eqf : bceq.



(* [comment removed for export] *)
Fixpoint kwritable (allkn k : list kentry) (b : expr) (off n : Z) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xlo allkn wn with Some wl => Z.leb (off + n) (wk + wl) | None => false end
          else false)
      then true
      else if (Z.leb 0 n && Z.ltb n two64 && xinside allkn b off (ELit n) wb wk wn)%bool then true
      else kwritable allkn rest b off n
  | _ :: rest => kwritable allkn rest b off n
  end.

Fixpoint kwritableB (bc : bctx) (k : list kentry) (b : expr) (off n : Z) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xloB bc wn with Some wl => Z.leb (off + n) (wk + wl) | None => false end
          else false)
      then true
      else if (Z.leb 0 n && Z.ltb n two64 && xinsideB bc b off (ELit n) wb wk wn)%bool then true
      else kwritableB bc rest b off n
  | _ :: rest => kwritableB bc rest b off n
  end.

Lemma kwritableB_eqf : forall fk, kwritableB (mkbc fk) = kwritable fk.
Proof.
  intros fk. apply functional_extensionality; intros k. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros n. 
  revert b off n. induction k as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kwritableB kwritable]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[local] Hint Rewrite kwritableB_eqf : bceq.


Fixpoint kwritable_x (allkn k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xhi allkn n, xlo allkn wn with
               | Some nh, Some wl => Z.leb (off + nh) (wk + wl)
               | _, _ => false
               end
          else false)
      then true
      else if xinside allkn b off n wb wk wn then true
      else kwritable_x allkn rest b off n
  | _ :: rest => kwritable_x allkn rest b off n
  end.

Fixpoint kwritable_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xhiB bc n, xloB bc wn with
               | Some nh, Some wl => Z.leb (off + nh) (wk + wl)
               | _, _ => false
               end
          else false)
      then true
      else if xinsideB bc b off n wb wk wn then true
      else kwritable_xB bc rest b off n
  | _ :: rest => kwritable_xB bc rest b off n
  end.

Lemma kwritable_xB_eqf : forall fk, kwritable_xB (mkbc fk) = kwritable_x fk.
Proof.
  intros fk. apply functional_extensionality; intros k. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros n. 
  revert b off n. induction k as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kwritable_xB kwritable_x]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[local] Hint Rewrite kwritable_xB_eqf : bceq.



(* [comment removed for export] *)
Fixpoint kzero_x (allkn k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KZero (SA zb zk) zn :: rest =>
      if (if (expr_eqb b zb && Z.leb zk off)%bool
          then match xhi allkn n, xlo allkn zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if xinside allkn b off n zb zk zn then true
      else kzero_x allkn rest b off n
  | _ :: rest => kzero_x allkn rest b off n
  end.

Fixpoint kzero_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KZero (SA zb zk) zn :: rest =>
      if (if (expr_eqb b zb && Z.leb zk off)%bool
          then match xhiB bc n, xloB bc zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if xinsideB bc b off n zb zk zn then true
      else kzero_xB bc rest b off n
  | _ :: rest => kzero_xB bc rest b off n
  end.

Lemma kzero_xB_eqf : forall fk, kzero_xB (mkbc fk) = kzero_x fk.
Proof.
  intros fk. apply functional_extensionality; intros k. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros n. 
  revert b off n. induction k as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kzero_xB kzero_x]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[local] Hint Rewrite kzero_xB_eqf : bceq.



(* [comment removed for export] *)
Fixpoint kfill_x (allkn k : list kentry) (b : expr) (off : Z) (n : expr) (c : Z) : bool :=
  match k with
  | [] => false
  | KFill (SA zb zk) zn c' :: rest =>
      if (if (Z.eqb (c' mod 256) (c mod 256) && expr_eqb b zb && Z.leb zk off)%bool
          then match xhi allkn n, xlo allkn zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if (Z.eqb (c' mod 256) (c mod 256) && xinside allkn b off n zb zk zn)%bool then true
      else kfill_x allkn rest b off n c
  | _ :: rest => kfill_x allkn rest b off n c
  end.

Fixpoint kfill_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) (c : Z) : bool :=
  match k with
  | [] => false
  | KFill (SA zb zk) zn c' :: rest =>
      if (if (Z.eqb (c' mod 256) (c mod 256) && expr_eqb b zb && Z.leb zk off)%bool
          then match xhiB bc n, xloB bc zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if (Z.eqb (c' mod 256) (c mod 256) && xinsideB bc b off n zb zk zn)%bool then true
      else kfill_xB bc rest b off n c
  | _ :: rest => kfill_xB bc rest b off n c
  end.

Lemma kfill_xB_eqf : forall fk, kfill_xB (mkbc fk) = kfill_x fk.
Proof.
  intros fk. apply functional_extensionality; intros k. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros n. apply functional_extensionality; intros c. 
  revert b off n c. induction k as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kfill_xB kfill_x]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[local] Hint Rewrite kfill_xB_eqf : bceq.



(* [comment removed for export] *)
Definition off_image_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  ranges_apart_x k b off n (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)).

Definition off_image_xB (bc : bctx) (b : expr) (off : Z) (n : expr) : bool :=
  ranges_apart_xB bc b off n (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)).

Lemma off_image_xB_eqf : forall fk, off_image_xB (mkbc fk) = off_image_x fk.
Proof. intros. bcfe. unfold off_image_xB, off_image_x. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite off_image_xB_eqf : bceq.



(* [comment removed for export] *)

(* [comment removed for export] *)
Definition flat_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match base_range k b, xlo k n, xhi k n with
  | Some (lo, hi), Some nl, Some nh => (Z.leb 0 (lo + off) && Z.leb (hi + off + nh) two64 && Z.ltb 0 nl)%bool
  | _, _, _ => false
  end.

Definition flat_xB (bc : bctx) (b : expr) (off : Z) (n : expr) : bool :=
  match base_rangeB bc b, xloB bc n, xhiB bc n with
  | Some (lo, hi), Some nl, Some nh => (Z.leb 0 (lo + off) && Z.leb (hi + off + nh) two64 && Z.ltb 0 nl)%bool
  | _, _, _ => false
  end.

Lemma flat_xB_eqf : forall fk, flat_xB (mkbc fk) = flat_x fk.
Proof. intros. bcfe. unfold flat_xB, flat_x. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite flat_xB_eqf : bceq.



(* [comment removed for export] *)
Definition ehi (k : list kentry) (e : expr) : option Z := xhi k e.
Definition elo (k : list kentry) (e : expr) : option Z := xlo k e.

(* [comment removed for export] *)
Definition len_eqb (k : list kentry) (n m : expr) : bool :=
  expr_eqb n m || (lin_ge0 k [(n, 0%Z)] [(m, 0%Z)] && lin_ge0 k [(m, 0%Z)] [(n, 0%Z)]).

Definition len_eqbB (bc : bctx) (n m : expr) : bool :=
  expr_eqb n m || (lin_ge0B bc [(n, 0%Z)] [(m, 0%Z)] && lin_ge0B bc [(m, 0%Z)] [(n, 0%Z)]).

Lemma len_eqbB_eqf : forall fk, len_eqbB (mkbc fk) = len_eqb fk.
Proof. intros. bcfe. unfold len_eqbB, len_eqb. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite len_eqbB_eqf : bceq.



(* [comment removed for export] *)
Definition lit_diff (e f : expr) : option Z :=
  match esub e f with ELit z => Some (z mod two64) | _ => None end.

(* [comment removed for export] *)
Definition page_aligned (k : list kentry) (e : expr) : bool :=
  match e with
  | ELit z => Z.eqb (z mod 4096) 0
  | _ => Z.leb 12 (ealign k e)
  end.

Definition page_alignedB (bc : bctx) (e : expr) : bool :=
  match e with
  | ELit z => Z.eqb (z mod 4096) 0
  | _ => Z.leb 12 (ealignB bc e)
  end.

Lemma page_alignedB_eqf : forall fk, page_alignedB (mkbc fk) = page_aligned fk.
Proof. intros. bcfe. unfold page_alignedB, page_aligned. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite page_alignedB_eqf : bceq.



(* [comment removed for export] *)
Definition kn_contra (k : list kentry) : bool :=
  existsb (fun K => match K with
                    | KRange e lo hi =>
                        if Z.ltb hi lo then true else
                        match e with
                        | EVar _ => false
                        | _ => let l := lin_of e in
                               match snd l with
                               | _ :: _ :: _ =>
                                   match lin_range (erange k) (fst l) (snd l) with
                                   | Some (a, b) => (Z.leb 0 a && Z.ltb b two64 && (Z.ltb b lo || Z.ltb hi a))%bool
                                   | None => false
                                   end
                               | _ => false
                               end
                        end
                    | _ => false
                    end) k.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition caller_saved : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.

Fixpoint sr_fresh (sr : list expr) (ixs : list nat) (nx : nat) : list expr :=
  match ixs with
  | [] => sr
  | i :: t => sr_fresh (sr_upd sr i (EVar nx)) t (S nx)
  end.

Definition NCS : nat := 16.

Definition ret_lit (cs : acs) : option Z :=
  match reg cs 1 with
  | ELit r => if (Z.eqb (r mod 2) 0 && Z.ltb r two64 && Z.leb 0 r)%bool then Some r else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition after_call (cs : acs) (ret : Z) (rv : option expr) (k' : list kentry) : option acs :=
  let ss := a_ss cs in
  let nx := s_next ss in
  let sr1 := sr_fresh (s_regs ss) caller_saved nx in
  let sr2 := match rv with Some e => sr_upd sr1 10 e | None => sr1 end in
  if (fresh_ok cs && kn_vars_lt nx k' && match rv with Some e => expr_vars_lt nx e | None => true end)%bool
  then Some (with_ss cs (mk_ss ret sr2 k' (nx + NCS)))
  else None.
(* [comment removed for export] *)
Definition after_call2 (cs : acs) (ret : Z) (rv : option expr) (k' : list kentry) (extra : nat) : option acs :=
  let ss := a_ss cs in
  let nx := s_next ss in
  let sr1 := sr_fresh (s_regs ss) caller_saved nx in
  let sr2 := match rv with Some e => sr_upd sr1 10 e | None => sr1 end in
  if (fresh_ok cs && kn_vars_lt (nx + NCS + extra) k' && match rv with Some e => expr_vars_lt nx e | None => true end)%bool
  then Some (with_ss cs (mk_ss ret sr2 k' (nx + NCS + extra)))
  else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition page_up (len : Z) : Z := ((len + 4095) / 4096) * 4096.

Definition is_ecall_at (cs : acs) : bool :=
  (Z.leb 0 (pc cs) && Z.ltb (pc cs + 4) two64 &&
  match fetch_word segs (Z_to_bv 64 (pc cs)) with
  | Some w => is_ecall w
  | None => false
  end)%bool.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition xlo1 (k : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erange k e, lin_brange k e with
         | Some (lo, _), Some (lo', _) => Some (Z.max lo lo')
         | Some (lo, _), None => Some lo
         | None, Some (lo', _) => Some lo'
         | None, None => match lin_srange k e with Some (lo, _) => Some lo | None => None end   (* [comment removed for export] *)
         end
  end.

Definition xlo1B (bc : bctx) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erangeB bc e, lin_brangeB bc e with
         | Some (lo, _), Some (lo', _) => Some (Z.max lo lo')
         | Some (lo, _), None => Some lo
         | None, Some (lo', _) => Some lo'
         | None, None => match lin_srangeB bc e with Some (lo, _) => Some lo | None => None end   (* [comment removed for export] *)
         end
  end.

Lemma xlo1B_eqf : forall fk, xlo1B (mkbc fk) = xlo1 fk.
Proof. intros. bcfe. unfold xlo1B, xlo1. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite xlo1B_eqf : bceq.


Definition xhi1 (k : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erange k e, lin_brange k e with
         | Some (_, hi), Some (_, hi') => Some (Z.min hi hi')
         | Some (_, hi), None => Some hi
         | None, Some (_, hi') => Some hi'
         | None, None => match lin_srange k e with Some (_, hi) => Some hi | None => None end   (* [comment removed for export] *)
         end
  end.

Definition xhi1B (bc : bctx) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erangeB bc e, lin_brangeB bc e with
         | Some (_, hi), Some (_, hi') => Some (Z.min hi hi')
         | Some (_, hi), None => Some hi
         | None, Some (_, hi') => Some hi'
         | None, None => match lin_srangeB bc e with Some (_, hi) => Some hi | None => None end   (* [comment removed for export] *)
         end
  end.

Lemma xhi1B_eqf : forall fk, xhi1B (mkbc fk) = xhi1 fk.
Proof. intros. bcfe. unfold xhi1B, xhi1. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite xhi1B_eqf : bceq.



(* [comment removed for export] *)
Fixpoint deand (e : expr) : expr * Z :=
  match e with
  | EAlu ALU_AND x (ELit m) =>
      let m' := m mod two64 in
      let j := Z.log2 (two64 - m') in
      if (Z.eqb (two64 - m') (2 ^ j) && Z.leb j 48)%bool
      then let '(x', s) := deand x in (x', s + (2 ^ j - 1))
      else (e, 0)
  | EAlu ALU_ADD a b => let '(a', s1) := deand a in let '(b', s2) := deand b in (EAlu ALU_ADD a' b', s1 + s2)
  | _ => (e, 0)
  end.

Definition xb2 (k : list kentry) (e : expr) : option (Z * Z) :=
  let plain := match xlo1 k e, xhi1 k e with Some lo, Some hi => Some (lo, hi) | _, _ => None end in
  let '(e', s) := deand e in
  if Z.eqb s 0 then plain else
  match xlo1 k e', xhi1 k e' with
  | Some lo', Some hi' =>
      if Z.leb s lo' then
        match plain with
        | Some (lo, hi) => Some (Z.max lo (lo' - s), Z.min hi hi')
        | None => Some (lo' - s, hi')
        end
      else plain
  | _, _ => plain
  end.

Definition xb2B (bc : bctx) (e : expr) : option (Z * Z) :=
  let plain := match xlo1B bc e, xhi1B bc e with Some lo, Some hi => Some (lo, hi) | _, _ => None end in
  let '(e', s) := deand e in
  if Z.eqb s 0 then plain else
  match xlo1B bc e', xhi1B bc e' with
  | Some lo', Some hi' =>
      if Z.leb s lo' then
        match plain with
        | Some (lo, hi) => Some (Z.max lo (lo' - s), Z.min hi hi')
        | None => Some (lo' - s, hi')
        end
      else plain
  | _, _ => plain
  end.

Lemma xb2B_eqf : forall fk, xb2B (mkbc fk) = xb2 fk.
Proof. intros. bcfe. unfold xb2B, xb2. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite xb2B_eqf : bceq.


Definition xlo2 (k : list kentry) (e : expr) : option Z := match xb2 k e with Some (lo, _) => Some lo | None => None end.

Definition xlo2B (bc : bctx) (e : expr) : option Z := match xb2B bc e with Some (lo, _) => Some lo | None => None end.

Lemma xlo2B_eqf : forall fk, xlo2B (mkbc fk) = xlo2 fk.
Proof. intros. bcfe. unfold xlo2B, xlo2. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite xlo2B_eqf : bceq.


Definition xhi2 (k : list kentry) (e : expr) : option Z := match xb2 k e with Some (_, hi) => Some hi | None => None end.

Definition xhi2B (bc : bctx) (e : expr) : option Z := match xb2B bc e with Some (_, hi) => Some hi | None => None end.

Lemma xhi2B_eqf : forall fk, xhi2B (mkbc fk) = xhi2 fk.
Proof. intros. bcfe. unfold xhi2B, xhi2. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite xhi2B_eqf : bceq.



(* [comment removed for export] *)
Definition fact_ok (k : list kentry) (K : kentry) : bool :=
  match K with
  | KRange e lo hi =>
      match xlo2 k e, xhi2 k e with
      | Some l, Some h => Z.leb lo l && Z.leb h hi
      | _, _ => false
      end
  | KAlign e m => Z.ltb 0 m && Z.eqb m (2 ^ (Z.log2 m)) && Z.leb (Z.log2 m) (ealign k e)
  | KDisj (SA b1 k1) n1 (SA b2 k2) n2 => ranges_apart_x k b1 k1 n1 b2 k2 n2
  | _ => false
  end.

(* [comment removed for export] *)
Fixpoint kread_bytes (fuel : nat) (k : list kentry) (b : expr) (off : Z) : option (list Z) :=
  match fuel with
  | O => Some []
  | S f => match kreadZ k b off 1, kread_bytes f k b (off + 1) with
           | Some z, Some rest => Some (z :: rest)
           | _, _ => None
           end
  end.

Fixpoint kread_bytesB (bc : bctx) (fuel : nat) (b : expr) (off : Z) : option (list Z) :=
  match fuel with
  | O => Some []
  | S f => match kreadZB bc b off 1, kread_bytesB bc f b (off + 1) with
           | Some z, Some rest => Some (z :: rest)
           | _, _ => None
           end
  end.

Lemma kread_bytesB_eqf' : forall fk fuel, kread_bytesB (mkbc fk) fuel = kread_bytes fuel fk.
Proof.
  intros fk fuel. induction fuel as [|f IH]; bcfe; [reflexivity|].
  cbn [kread_bytesB kread_bytes]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
Lemma kread_bytesB_eqf : forall fk, kread_bytesB (mkbc fk) = (fun fuel => kread_bytes fuel fk).
Proof. intros fk. apply functional_extensionality; intros fuel. apply kread_bytesB_eqf'. Qed.
#[local] Hint Rewrite kread_bytesB_eqf' kread_bytesB_eqf : bceq.


Definition node_join (cs : acs) (b : expr) (off : Z) (n : nat) : option acs :=
  if (Nat.leb 1 n && Nat.leb n 8 && flat_x (kn cs) b off (ELit (Z.of_nat n)))%bool then
    match kread_bytes n (kn cs) b off with
    | Some bs => Some (add_kn cs [KWord (SA b off) n (ELit (zbytes_le_to_Z bs))])
    | None => None
    end
  else None.

Fixpoint drop_ixs (ixs : list nat) (i : nat) (k : list kentry) : list kentry :=
  match k with
  | [] => []
  | K :: r => if existsb (Nat.eqb i) ixs then drop_ixs ixs (S i) r else K :: drop_ixs ixs (S i) r
  end.

(* [comment removed for export] *)
Definition residue_fact (k : list kentry) (e ne : expr) : list kentry :=
  let '(e', s) := deand e in
  if Z.ltb 0 s then
    match xlo1 k e', xhi1 k e' with
    | Some lo', Some _ => if Z.leb s lo' then [KRange (esub e' ne) 0 s] else []
    | _, _ => []
    end
  else [].

Definition node_fresh (cs : acs) (r : nat) (logc : Z) (base : option expr) : option acs :=
  let k := kn cs in let c := 2 ^ logc in
  let b := match base with Some b => b | None => ELit 0 end in
  let e := esub (reg cs r) b in
  if (Nat.ltb 0 r && Nat.ltb r 32 && Z.leb 0 logc && Z.leb logc 40 && Z.leb logc (ealign k e)
      && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) e && fresh_ok cs)%bool then
    match xlo2 k e, xhi2 k e with
    | Some lo, Some hi =>
        let v := nxt cs in
        let ne := escale c (EVar v) in
        let kres := residue_fact k e ne in
        let kf := KRange (EVar v) ((lo + c - 1) / c) (hi / c) :: KRange (esub e ne) 0 0 :: kres in
        Some (bump (set_reg (add_kn cs kf) r (eadd b ne)) 1)
    | _, _ => None
    end
  else None.

(* [comment removed for export] *)
Definition node_droprange (cs : acs) (b n : expr) : acs :=
  let '(bb, bk) := split_lit b in set_kn cs (kn_havoc (kn cs) bb bk n).

(* [comment removed for export] *)
Definition node_bump (cs : acs) (m : nat) : option acs :=
  if Nat.leb (nxt cs) m then Some (bump cs (m - nxt cs)) else None.

(* [comment removed for export] *)
Definition node_havoc (cs : acs) (rs : list nat) : option acs :=
  if (fresh_ok cs && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) rs)%bool then
    let ss := a_ss cs in
    Some (with_ss cs (mk_ss (s_pc ss) (sr_fresh (s_regs ss) rs (s_next ss)) (s_know ss) (s_next ss + length rs)))
  else None.

(* [comment removed for export] *)
Fixpoint esize (e : expr) : nat :=
  match e with
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => S (esize a + esize b)
  | EExt _ _ _ a => S (esize a)
  | _ => 1%nat
  end.
Definition bigb (K : nat) (e : expr) : bool := Nat.ltb K (esize e).
Fixpoint kn_bigsubst (K : nat) (k : list kentry) (nx : nat) : list kentry * nat :=
  match k with
  | [] => ([], 0%nat)
  | KWord a w v :: r =>
      if bigb K v then let '(r', c) := kn_bigsubst K r (S nx) in (KWord a w (EVar nx) :: r', S c)
      else let '(r', c) := kn_bigsubst K r nx in (KWord a w v :: r', c)
  | x :: r => let '(r', c) := kn_bigsubst K r nx in (x :: r', c)
  end.
Definition node_havocbig (cs : acs) (K : nat) : option acs :=
  let rs := List.filter (fun r => bigb K (reg cs r)) (seq 1 31) in
  match node_havoc cs rs with
  | Some cs1 =>
      if fresh_ok cs1 then
        let nx1 := nxt cs1 in
        let '(k', c) := kn_bigsubst K (kn cs1) nx1 in
        Some (with_ss cs1 (mk_ss (pc cs1) (s_regs (a_ss cs1)) k' (nx1 + c)))
      else None
  | None => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition find_containing (k : list kentry) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
  List.find (fun m => negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && xinside k b off n (am_base m) 0 (am_len m)) ms.

Definition find_containingB (bc : bctx) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
  List.find (fun m => negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && xinsideB bc b off n (am_base m) 0 (am_len m)) ms.

Lemma find_containingB_eqf : forall fk, find_containingB (mkbc fk) = find_containing fk.
Proof. intros. bcfe. unfold find_containingB, find_containing. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite find_containingB_eqf : bceq.



(* [comment removed for export] *)
Definition shadow_of (k : list kentry) (b n : expr) : expr * Z * expr :=
  let '(sb, sk) := split_lit (eadd (mkSrl k b 3) (ELit (shadow_off A))) in (sb, sk, mkSrl k n 3).

Definition shadow_ofB (bc : bctx) (b n : expr) : expr * Z * expr :=
  let '(sb, sk) := split_lit (eadd (mkSrlB bc b 3) (ELit (shadow_off A))) in (sb, sk, mkSrlB bc n 3).

Lemma shadow_ofB_eqf : forall fk, shadow_ofB (mkbc fk) = shadow_of fk.
Proof. intros. bcfe. unfold shadow_ofB, shadow_of. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite shadow_ofB_eqf : bceq.



(* [comment removed for export] *)
Definition lit_entry (ms : list amap) (kd : mkind) (b l : Z) : bool :=
  existsb (fun m => negb (is_fog m) && mkind_eqb (am_kind m) kd
                    && expr_eqb (am_base m) (ELit b) && expr_eqb (am_len m) (ELit l)) ms.
(* [comment removed for export] *)
Definition LS_LO : Z := MID_LO.
Definition LS_LEN : Z := 0x10000000.
Definition HS_LO : Z := 0x2008fff7000.
Definition TWO47 : Z := 0x800000000000.
(* [comment removed for export] *)
Definition end_hi2 (k : list kentry) (b n : expr) : option Z :=
  match xhi k b, xhi k n with
  | Some h, Some m =>
      Some (if Z.ltb (h + m) two64
            then match xhi k (eadd b n) with Some e => Z.min (h + m) e | None => h + m end
            else h + m)
  | _, _ => None
  end.
Definition end_hi2B (bc : bctx) (b n : expr) : option Z :=
  match xhiB bc b, xhiB bc n with
  | Some h, Some m =>
      Some (if Z.ltb (h + m) two64
            then match xhiB bc (eadd b n) with Some e => Z.min (h + m) e | None => h + m end
            else h + m)
  | _, _ => None
  end.
Lemma end_hi2B_eqf : forall fk, end_hi2B (mkbc fk) = end_hi2 fk.
Proof. intros. bcfe. unfold end_hi2B, end_hi2. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite end_hi2B_eqf : bceq.

(* [comment removed for export] *)
Definition shadow_band_ok (k : list kentry) (ms : list amap) (b n : expr) : bool :=
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_of k b n in
  (flat_x k sb sk sn && ranges_apart_x k bb bk n (ELit MID_LO) 0 (ELit (KHI - MID_LO))
   && lit_entry ms KRWLAZY LS_LO LS_LEN && lit_entry ms KRWLAZY HS_LO (KHI - HS_LO)
   && Z.leb LS_LO (shadow_off A + 512) && Z.leb (shadow_off A + MID_LO / 8) (LS_LO + LS_LEN)
   && Z.leb HS_LO (shadow_off A + KHI / 8) && Z.leb (shadow_off A + TWO47 / 8) KHI
   && match xlo k b, end_hi2 k b n with                                  (* [comment removed for export] *)
      | Some lo, Some eh => Z.leb 4096 lo && Z.leb eh TWO47
      | _, _ => false
      end)%bool.

Definition shadow_band_okB (bc : bctx) (ms : list amap) (b n : expr) : bool :=
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_ofB bc b n in
  (flat_xB bc sb sk sn && ranges_apart_xB bc bb bk n (ELit MID_LO) 0 (ELit (KHI - MID_LO))
   && lit_entry ms KRWLAZY LS_LO LS_LEN && lit_entry ms KRWLAZY HS_LO (KHI - HS_LO)
   && Z.leb LS_LO (shadow_off A + 512) && Z.leb (shadow_off A + MID_LO / 8) (LS_LO + LS_LEN)
   && Z.leb HS_LO (shadow_off A + KHI / 8) && Z.leb (shadow_off A + TWO47 / 8) KHI
   && match xloB bc b, end_hi2B bc b n with
      | Some lo, Some eh => Z.leb 4096 lo && Z.leb eh TWO47
      | _, _ => false
      end)%bool.

Lemma shadow_band_okB_eqf : forall fk, shadow_band_okB (mkbc fk) = shadow_band_ok fk.
Proof. intros. bcfe. unfold shadow_band_okB, shadow_band_ok. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite shadow_band_okB_eqf : bceq.

(* [comment removed for export] *)
Definition shadow_facts (k : list kentry) (ms : list amap) (b n : expr) : list kentry :=
  let '(sb, sk, sn) := shadow_of k b n in
  if (match find_containing k ms [KRWLAZY] sb sk sn with Some _ => true | None => false end
      || shadow_band_ok k ms b n)%bool
  then [KWr (SA sb sk) sn; KZero (SA sb sk) sn] else [].

Definition shadow_factsB (bc : bctx) (ms : list amap) (b n : expr) : list kentry :=
  let '(sb, sk, sn) := shadow_ofB bc b n in
  if (match find_containingB bc ms [KRWLAZY] sb sk sn with Some _ => true | None => false end
      || shadow_band_okB bc ms b n)%bool
  then [KWr (SA sb sk) sn; KZero (SA sb sk) sn] else [].

Lemma shadow_factsB_eqf : forall fk, shadow_factsB (mkbc fk) = shadow_facts fk.
Proof. intros. bcfe. unfold shadow_factsB, shadow_facts. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite shadow_factsB_eqf : bceq.



(* [comment removed for export] *)
Definition vis_cost (nhi : Z) : Z := nhi + nhi / 8 + 16384.

(* [comment removed for export] *)
Definition vis_add_ref (cs : acs) (b n : expr) (k : list kentry) : option (acs) :=
  let k0 := kn cs in
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_of k0 b n in
  match xhi k0 n with
  | Some nhi =>
  if (Z.leb 3 (ealign k0 b) && Z.leb 3 (ealign k0 n) && flat_x k0 bb bk n
      && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n
      && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_x k0 pb pk (snd p)
                           && ranges_apart_x k0 bb bk n pb pk (snd p) && ranges_apart_x k0 sb sk sn pb pk (snd p)) (a_vis cs)
      (* [comment removed for export] *)
      && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_x k0 pb pk (snd p) && ranges_apart_x k0 sb sk sn pb pk (snd p)) (a_ghost cs)
      && Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
  then Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_facts k0 (a_maps cs) b n ++ k) (nxt cs))
                (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs))
  else None
  | None => None
  end.
(* [comment removed for export] *)
Definition vis_add (cs : acs) (b n : expr) (k : list kentry) : option (acs) :=
  let k0 := kn cs in let bc := mkbc k0 in   (* [comment removed for export] *)
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_ofB bc b n in
  match xhiB bc n with
  | Some nhi =>
  if (Z.leb 3 (ealignB bc b) && Z.leb 3 (ealignB bc n) && flat_xB bc bb bk n
      && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n
      && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_xB bc pb pk (snd p)
                           && ranges_apart_xB bc bb bk n pb pk (snd p) && ranges_apart_xB bc sb sk sn pb pk (snd p)) (a_vis cs)
      (* [comment removed for export] *)
      && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_xB bc pb pk (snd p) && ranges_apart_xB bc sb sk sn pb pk (snd p)) (a_ghost cs)
      && Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
  then Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_factsB bc (a_maps cs) b n ++ k) (nxt cs))
                (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs))
  else None
  | None => None
  end.

Lemma vis_add_eq : forall cs b n k, vis_add cs b n k = vis_add_ref cs b n k.
Proof. intros. unfold vis_add, vis_add_ref. unfold ehi, elo. rewrite ?ealignB_eqf, ?flat_xB_eqf, ?ranges_apart_xB_eqf, ?shadow_factsB_eqf, ?shadow_ofB_eqf, ?xhiB_eqf. reflexivity. Qed.


(* [comment removed for export] *)
Fixpoint find_disj (k : list kentry) (b1 b2 : expr) : option (expr * Z * expr * expr * Z * expr) :=
  match k with
  | [] => None
  | KDisj (SA c1 o1) n1 (SA c2 o2) n2 :: r =>
      if (expr_eqb c1 b1 && expr_eqb c2 b2)%bool then Some (c1, o1, n1, c2, o2, n2)
      else if (expr_eqb c1 b2 && expr_eqb c2 b1)%bool then Some (c2, o2, n2, c1, o1, n1)
      else find_disj r b1 b2
  | _ :: r => find_disj r b1 b2
  end.
(* [comment removed for export] *)
Definition disj_side_fact (k : list kentry) (cA : expr) (oA : Z) (nA : expr) (cB : expr) (oB : Z) : option kentry :=
  match xlo2 k nA, base_range k cB with
  | Some n, Some (_, bhi) => if (Z.leb 0 n && Z.leb n (bhi + oB))%bool then Some (KRange (esub (eaddz cB oB) (eaddz cA oA)) n (bhi + oB)) else None
  | _, _ => None
  end.
Definition node_casedisj (cs : acs) (b1 b2 : expr) : option (acs * acs) :=
  let k := kn cs in
  match find_disj k b1 b2 with
  | Some (c1, o1, n1, c2, o2, n2) =>
      match flat_x k c1 o1 n1, flat_x k c2 o2 n2, disj_side_fact k c1 o1 n1 c2 o2, disj_side_fact k c2 o2 n2 c1 o1 with
      | true, true, Some K1, Some K2 => Some (add_kn cs [K1], add_kn cs [K2])
      | _, _, _, _ => None
      end
  | None => None
  end.

(* [comment removed for export] *)
Definition node_shdisj_ref (cs : acs) (b1 n1 b2 n2 : expr) : option acs :=
  let k := kn cs in
  let '(c1, o1) := split_lit b1 in let '(c2, o2) := split_lit b2 in
  let '(sb1, sk1, sn1) := shadow_of k b1 n1 in let '(sb2, sk2, sn2) := shadow_of k b2 n2 in
  if (Z.leb 3 (ealign k b1) && Z.leb 3 (ealign k n1) && Z.leb 3 (ealign k b2) && Z.leb 3 (ealign k n2)
      && flat_x k c1 o1 n1 && flat_x k c2 o2 n2 && flat_x k sb1 sk1 sn1 && flat_x k sb2 sk2 sn2
      && match end_hi2 k b1 n1, end_hi2 k b2 n2 with                       (* [comment removed for export] *)
         | Some e1, Some e2 => Z.leb e1 (2 ^ 47) && Z.leb e2 (2 ^ 47)
         | _, _ => false end
      && ranges_apart_x k c1 o1 n1 c2 o2 n2)%bool
  then Some (add_kn cs [KDisj (SA sb1 sk1) sn1 (SA sb2 sk2) sn2])
  else None.
(* [comment removed for export] *)
Definition node_shdisj (cs : acs) (b1 n1 b2 n2 : expr) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  let '(c1, o1) := split_lit b1 in let '(c2, o2) := split_lit b2 in
  let '(sb1, sk1, sn1) := shadow_ofB bc b1 n1 in let '(sb2, sk2, sn2) := shadow_ofB bc b2 n2 in
  if (Z.leb 3 (ealignB bc b1) && Z.leb 3 (ealignB bc n1) && Z.leb 3 (ealignB bc b2) && Z.leb 3 (ealignB bc n2)
      && flat_xB bc c1 o1 n1 && flat_xB bc c2 o2 n2 && flat_xB bc sb1 sk1 sn1 && flat_xB bc sb2 sk2 sn2
      && match end_hi2B bc b1 n1, end_hi2B bc b2 n2 with
         | Some e1, Some e2 => Z.leb e1 (2 ^ 47) && Z.leb e2 (2 ^ 47)
         | _, _ => false end
      && ranges_apart_xB bc c1 o1 n1 c2 o2 n2)%bool
  then Some (add_kn cs [KDisj (SA sb1 sk1) sn1 (SA sb2 sk2) sn2])
  else None.

Lemma node_shdisj_eq : forall cs b1 n1 b2 n2, node_shdisj cs b1 n1 b2 n2 = node_shdisj_ref cs b1 n1 b2 n2.
Proof. intros. unfold node_shdisj, node_shdisj_ref. unfold ehi, elo. rewrite ?ealignB_eqf, ?flat_xB_eqf, ?ranges_apart_xB_eqf, ?shadow_ofB_eqf, ?end_hi2B_eqf, ?xhiB_eqf. reflexivity. Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_len_ref (cs : acs) : option (expr * Z * Z) :=
  match reg_lit cs 11 with
  | Some len => if Z.ltb 0 len then Some (ELit (page_up len), page_up len, page_up len) else None
  | None =>
      let le := reg cs 11 in let k := kn cs in
      match xlo k le, xhi k le with
      | Some lo, Some hi =>
          if (Z.ltb 0 lo && Z.leb 12 (ealign k le) && Z.leb hi (2 ^ 46))%bool then Some (le, lo, hi) else None
      | _, _ => None
      end
  end.
(* [comment removed for export] *)
Definition mmap_len (cs : acs) : option (expr * Z * Z) :=
  match reg_lit cs 11 with
  | Some len => if Z.ltb 0 len then Some (ELit (page_up len), page_up len, page_up len) else None
  | None =>
      let le := reg cs 11 in let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      match xloB bc le, xhiB bc le with
      | Some lo, Some hi =>
          if (Z.ltb 0 lo && Z.leb 12 (ealignB bc le) && Z.leb hi (2 ^ 46))%bool then Some (le, lo, hi) else None
      | _, _ => None
      end
  end.

Lemma mmap_len_eq : forall cs, mmap_len cs = mmap_len_ref cs.
Proof. intros. unfold mmap_len, mmap_len_ref. unfold ehi, elo. rewrite ?ealignB_eqf, ?xhiB_eqf, ?xloB_eqf. reflexivity. Qed.


(* [comment removed for export] *)
Fixpoint inside_maps (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match ms with
  | [] => false
  | m :: rest => (negb (is_fog m) && xinside k b off len (am_base m) 0 (am_len m)) || inside_maps k rest b off len
  end.

Fixpoint inside_mapsB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match ms with
  | [] => false
  | m :: rest => (negb (is_fog m) && xinsideB bc b off len (am_base m) 0 (am_len m)) || inside_mapsB bc rest b off len
  end.

Lemma inside_mapsB_eqf : forall fk, inside_mapsB (mkbc fk) = inside_maps fk.
Proof.
  intros fk. apply functional_extensionality; intros ms. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros len. 
  revert b off len. induction ms as [|m rest IH]; intros; bcfe; [reflexivity|].
  cbn [inside_mapsB inside_maps]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[local] Hint Rewrite inside_mapsB_eqf : bceq.



(* [comment removed for export] *)
Definition lit_ivs (ms : list amap) : list (Z * Z) :=
  flat_map (fun m => if is_fog m then [] else
                     match am_base m, am_len m with
                     | ELit b, ELit l => [(zlit64 b, zlit64 b + zlit64 l)]
                     | _, _ => []
                     end) ms.
(* [comment removed for export] *)
Fixpoint band_covered_from (ivs : list (Z * Z)) (fuel : nat) (cur hi : Z) : bool :=
  if Z.leb hi cur then true else
  match fuel with
  | O => false
  | S f => match List.find (fun iv => (Z.leb (fst iv) cur && Z.ltb cur (snd iv))%bool) ivs with
           | Some iv => band_covered_from ivs f (snd iv) hi
           | None => false
           end
  end.
Definition band_covered (ms : list amap) (lo hi : Z) : bool :=
  let ivs := lit_ivs ms in band_covered_from ivs (length ivs) lo hi.

(* [comment removed for export] *)
Definition in_band (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  (band_covered ms MID_LO KHI && xinside k b off len (ELit MID_LO) 0 (ELit (KHI - MID_LO)))%bool.
Definition in_bandB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  (band_covered ms MID_LO KHI && xinsideB bc b off len (ELit MID_LO) 0 (ELit (KHI - MID_LO)))%bool.
Lemma in_bandB_eqf : forall fk, in_bandB (mkbc fk) = in_band fk.
Proof. intros. bcfe. unfold in_bandB, in_band. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite in_bandB_eqf : bceq.

Definition safe_range (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  ((match xhi k len, base_range k b with
    | Some lh, Some (lo, hi) =>
        (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))       (* [comment removed for export] *)
    | _, _ => false
    end)
   || xinside k b off len e_sp0 STK_OFF (ELit STK_LEN)                            (* [comment removed for export] *)
   || inside_maps k ms b off len
   || in_band k ms b off len)%bool.                                                (* [comment removed for export] *)

Definition safe_rangeB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  ((match xhiB bc len, base_rangeB bc b with
    | Some lh, Some (lo, hi) =>
        (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))       (* [comment removed for export] *)
    | _, _ => false
    end)
   || xinsideB bc b off len e_sp0 STK_OFF (ELit STK_LEN)                          (* [comment removed for export] *)
   || inside_mapsB bc ms b off len
   || in_bandB bc ms b off len)%bool.                                              (* [comment removed for export] *)

Lemma safe_rangeB_eqf : forall fk, safe_rangeB (mkbc fk) = safe_range fk.
Proof. intros. bcfe. unfold safe_rangeB, safe_range. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite safe_rangeB_eqf : bceq.



Definition grant_keep_b (k : list kentry) (ms : list amap) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w _ => Nat.leb w 8 && safe_range k ms b o (ELit (Z.of_nat w))
  | KZero (SA b o) l => safe_range k ms b o l
  | KBlob (SA b o) l _ => safe_range k ms b o l
  | KImg lo hi => true
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b o) n => safe_range k ms b o n
  | KFill (SA b o) l _ => safe_range k ms b o l
  | KUnk (SA b o) l => safe_range k ms b o l
  end.

Definition grant_keep_bB (bc : bctx) (ms : list amap) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w _ => Nat.leb w 8 && safe_rangeB bc ms b o (ELit (Z.of_nat w))
  | KZero (SA b o) l => safe_rangeB bc ms b o l
  | KBlob (SA b o) l _ => safe_rangeB bc ms b o l
  | KImg lo hi => true
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b o) n => safe_rangeB bc ms b o n
  | KFill (SA b o) l _ => safe_rangeB bc ms b o l
  | KUnk (SA b o) l => safe_rangeB bc ms b o l
  end.

Lemma grant_keep_bB_eqf : forall fk, grant_keep_bB (mkbc fk) = grant_keep_b fk.
Proof. intros. bcfe. unfold grant_keep_bB, grant_keep_b. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite grant_keep_bB_eqf : bceq.



Definition kn_grant_filter (k : list kentry) (ms : list amap) : list kentry :=
  kimg_clip (List.filter (grant_keep_b k ms) k).

Definition kn_grant_filterB (bc : bctx) (ms : list amap) : list kentry :=
  kimg_clip (List.filter (grant_keep_bB bc ms) (bc_fk bc)).

Lemma kn_grant_filterB_eqf : forall fk, kn_grant_filterB (mkbc fk) = kn_grant_filter fk.
Proof. intros. bcfe. unfold kn_grant_filterB, kn_grant_filter. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_grant_filterB_eqf : bceq.



(* [comment removed for export] *)
Definition gap_ok (cs : acs) (nhi : Z) : bool :=
  let cnt := Z.of_nat (n_res A + length (a_maps cs))%nat in
  Z.leb (FLOOR + nhi + a_totsz cs + cnt * (nhi + 4095)) CEIL.

Definition budget_ok (cs : acs) (extra : Z) : bool :=
  Z.leb (a_eager cs + a_abytes cs + extra) LIMIT.

(* [comment removed for export] *)
Definition kdisj_new (ms : list amap) (nb : expr) (ne : expr) : list kentry :=
  flat_map (fun m => if is_fog m then [] else
                     match am_base m with
                     | ELit _ => []
                     | mb => [KDisj (SA mb 0) (am_len m) (SA nb 0) ne]
                     end) ms.

(* [comment removed for export] *)
Definition with_maps0 (cs : acs) (ms : list amap) : acs :=
  ACS (a_ss cs) ms (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

(* [comment removed for export] *)
Definition add_entry (cs : acs) (sr : list expr) (k' : list kentry) (nx' : nat)
           (m : amap) (nhi : Z) (eager : bool) (ylo' : Z) : acs :=
  ACS (mk_ss (pc cs + 4) sr k' nx')
      (m :: a_maps cs) (a_totsz cs + nhi) ylo'
      (if eager then a_eager cs + nhi else a_eager cs)
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition null_kend (base ne : expr) (lb nlo : Z) : list kentry :=
  match ne with
  | ELit _ => []
  | _ => [KRange (eadd base ne) (lb + nlo) TOPMAX]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition iv_meets (c n : Z) (iv : Z * Z) : bool := (Z.ltb (fst iv) (c + n) && Z.ltb c (snd iv) && Z.ltb (fst iv) (snd iv))%bool.
Fixpoint lowbound_from (ivs : list (Z * Z)) (fuel : nat) (n c : Z) : Z :=
  match fuel with
  | O => c
  | S f => match List.find (iv_meets c n) ivs with
           | Some iv => lowbound_from ivs f n (Z.max c (page_up (snd iv)))
           | None => c
           end
  end.
Definition lowbound (ms : list amap) (n : Z) : Z :=
  let ivs := (img_lo A, img_hi A) :: lit_ivs ms in lowbound_from ivs (S (length ivs)) n 4096.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pd_ok (k : list kentry) : bool :=
  (Z.leb 12 (ealign k e_pd) &&
   match erange k (esub e_sp0 e_pd) with
   | Some (lo, hi) => (Z.leb 0 lo && Z.leb hi 4095)%bool
   | None => false
   end)%bool.
Definition pd_okB (bc : bctx) : bool :=
  (Z.leb 12 (ealignB bc e_pd) &&
   match erangeB bc (esub e_sp0 e_pd) with
   | Some (lo, hi) => (Z.leb 0 lo && Z.leb hi 4095)%bool
   | None => false
   end)%bool.
Lemma pd_okB_eqf : forall fk, pd_okB (mkbc fk) = pd_ok fk.
Proof. intros. bcfe. unfold pd_okB, pd_ok. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite pd_okB_eqf : bceq.
Definition pd_disj (k : list kentry) (bb : expr) (bk : Z) (ne : expr) : list kentry :=
  if pd_ok k then [KDisj (SA bb bk) ne (SA e_pd STK_OFF) (ELit STK_WTOP)] else [].

Definition grant_facts (k : list kentry) (ms : list amap) (v : nat) (base ne : expr) (lb nlo : Z) : list kentry :=
  KDisj (SA base 0) ne (SA e_sp0 STK_OFF) (ELit STK_LEN)
  :: KRange (EVar v) (lb / 4096) ((TOPMAX - nlo) / 4096)
  :: pd_disj k base 0 ne ++
  (if Z.ltb lb (img_hi A) then [KDisj (SA base 0) ne (SA (ELit (img_lo A)) 0) (ELit (img_hi A - img_lo A))] else [])
  ++ (if band_covered ms MID_LO KHI then [KDisj (SA base 0) ne (SA (ELit MID_LO) 0) (ELit (KHI - MID_LO))] else [])
  ++ null_kend base ne lb nlo.

Definition mmap_null (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  match mmap_len cs with
  | Some (ne, nlo, nhi) =>
      if (fresh_ok cs && expr_vars_lt (nxt cs) ne
          && gap_ok cs nhi && (negb eager || budget_ok cs nhi)
          && no_holes (a_maps cs))%bool then     (* [comment removed for export] *)
        let v := nxt cs in
        let base := escale 4096 (EVar v) in
        let lb := lowbound (a_maps cs) nlo in   (* [comment removed for export] *)
        let kfacts := grant_facts (kn cs) (a_maps cs) v base ne lb nlo ++ kdisj_new (a_maps cs) base ne in
        let kmem := [KWr (SA base 0) ne; KZero (SA base 0) ne] in
        let k' := kfacts ++ kn_grant_filter (kn cs) (a_maps cs) in
        let cs1 := add_entry cs (sr_upd (s_regs (a_ss cs)) 10 base) k' (S v) (AM base ne kind) nhi eager (a_ylo cs) in
        if visible then vis_add cs1 base ne (kmem ++ kn cs1) else Some cs1
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition fixed_args (cs : acs) (top : Z) : option (expr * Z * expr * Z * Z) :=
  let k := kn cs in let a := reg cs 10 in
  let '(b, off) := split_lit a in
  match mmap_len cs, xlo k a, xhi k a with
  | Some (ne, nlo, nhi), Some alo, Some ahi =>
      if (page_aligned k a && Z.ltb 0 alo && (Z.leb (img_hi A) alo || Z.leb TOPMAX top) && Z.leb (ahi + nhi) top && flat_x k b off ne)%bool then Some (b, off, ne, nlo, nhi) else None
  | _, _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition same_val (k : list kentry) (a b : expr) : bool :=
  if expr_eqb a b then true
  else (if lin_ge0 k [(a, 0%Z)] [(b, 0%Z)] then lin_ge0 k [(b, 0%Z)] [(a, 0%Z)] else false).
(* [comment removed for export] *)
Definition find_hole (k : list kentry) (ms : list amap) (a ne : expr) : option amap :=
  List.find (fun m => is_hole m && same_val k a (am_base m) && same_val k ne (am_len m)) ms.
(* [comment removed for export] *)
Definition unhole (ms : list amap) (h : amap) : list amap :=
  List.map (fun m => if (is_hole m && amap_eqb m h)%bool then AM (am_base m) (am_len m) KFOG else m) ms.

(* [comment removed for export] *)
Definition mmap_fixed_grant (cs : acs) (ms0 : list amap) (b : expr) (off : Z) (ne : expr) (nhi : Z)
           (kind : mkind) (eager visible : bool) : option acs :=
  let k := kn cs in
  let a := reg cs 10 in
  let m := AM a ne kind in
  let kmem := [KWr (SA b off) ne; KZero (SA b off) ne] in
  let ksh := if mkind_eqb kind KRWLAZY then flat_map (fun p => shadow_facts k [m] (fst p) (snd p)) (a_vis cs) else [] in
  let k' := ksh ++ kn_grant_filter k ms0 in
  let cs1 := add_entry (with_maps0 cs ms0) (s_regs (a_ss cs)) k' (nxt cs) m nhi eager (a_ylo cs) in
  if visible then vis_add cs1 a ne (kmem ++ kn cs1) else Some cs1.

Definition mmap_fixed_free (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  let k := kn cs in
  let a := reg cs 10 in
  match fixed_args cs CEIL with
  | Some (b, off, ne, nlo, nhi) =>
      if (no_fog (a_maps cs)
          && forallb (fun m => ranges_apart_x k b off ne (am_base m) 0 (am_len m)) (a_maps cs)
          && (negb eager || budget_ok cs nhi)
          && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) a)%bool
      then mmap_fixed_grant cs (a_maps cs) b off ne nhi kind eager visible
      else None
  | None =>
      (* [comment removed for export] *)
      match fixed_args cs CEIL with
      | Some (b, off, ne, nlo, nhi) =>
          match find_hole k (a_maps cs) a ne with
          | Some h =>
              let ms0 := unhole (a_maps cs) h in
              if (forallb (fun m => negb (is_hole m) || ranges_apart_x k b off ne (am_base m) 0 (am_len m)) ms0
                  && (negb eager || budget_ok cs nhi)
                  && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) a)%bool
              then mmap_fixed_grant cs ms0 b off ne nhi kind eager visible
              else None
          | None => None
          end
      | None => None
      end
  end.

(* [comment removed for export] *)
Definition kn_rezero (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.filter (fun K => match K with
                        | KWord _ _ _ | KBlob _ _ _ | KFill _ _ _ => kentry_apart_bp k sp ub uk un K
                        | _ => true
                        end) k.

Definition kn_rezeroB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.filter (fun K => match K with
                        | KWord _ _ _ | KBlob _ _ _ | KFill _ _ _ => kentry_apart_bpB bc sp ub uk un K
                        | _ => true
                        end) (bc_fk bc).

Lemma kn_rezeroB_eqf : forall fk, kn_rezeroB (mkbc fk) = kn_rezero fk.
Proof. intros. bcfe. unfold kn_rezeroB, kn_rezero. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_rezeroB_eqf : bceq.

Definition kn_rezeroM (k : list kentry) := kn_rezeroB (mkbc k).
Lemma kn_rezeroM_eq : kn_rezeroM = kn_rezero. Proof. apply functional_extensionality; intros k. unfold kn_rezeroM. apply kn_rezeroB_eqf. Qed.



(* [comment removed for export] *)
Definition rekind (ms : list amap) (m : amap) : list amap :=
  map (fun m' => if amap_eqb m' m then AM (am_base m') (am_len m') KRW else m') ms.

(* [comment removed for export] *)
Inductive fixed_in_arm := ArmE | ArmF | ArmG.

(* [comment removed for export] *)
Definition fixed_in_args_ref (cs : acs) (arm : fixed_in_arm) : option (expr * Z * expr * Z * Z * amap) :=
  match fixed_args cs TOPMAX with
  | Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in
      let kinds := match arm with ArmE => [KRW; KNONE; KNONELAZY] | ArmF => [KRWLAZY] | ArmG => [KRW; KNONE; KNONELAZY] end in
      match find_containing k (a_maps cs) kinds b off ne with
      | Some m =>
          if (expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then Some (b, off, ne, nlo, nhi, m) else None
      | None => None
      end
  | None => None
  end.
(* [comment removed for export] *)
Definition fixed_in_args (cs : acs) (arm : fixed_in_arm) : option (expr * Z * expr * Z * Z * amap) :=
  match fixed_args cs TOPMAX with
  | Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      let kinds := match arm with ArmE => [KRW; KNONE; KNONELAZY] | ArmF => [KRWLAZY] | ArmG => [KRW; KNONE; KNONELAZY] end in
      match find_containingB bc (a_maps cs) kinds b off ne with
      | Some m =>
          if (expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then Some (b, off, ne, nlo, nhi, m) else None
      | None => None
      end
  | None => None
  end.

Lemma fixed_in_args_eq : forall cs arm, fixed_in_args cs arm = fixed_in_args_ref cs arm.
Proof. intros. unfold fixed_in_args, fixed_in_args_ref. unfold ehi, elo. rewrite ?find_containingB_eqf. reflexivity. Qed.


(* [comment removed for export] *)
Definition mmap_fixed_in_ref (cs : acs) (arm : fixed_in_arm) : option acs :=
  match fixed_in_args cs arm with
  | Some (b, off, ne, nlo, nhi, m) =>
      let k := kn cs in
      if match arm with ArmE => budget_ok cs nhi | _ => true end then
        let k' := match arm with
                  | ArmE => kimg_clip (kn_unfill k b off ne)
                  | ArmF => kimg_clip (kn_rezero k b off ne)
                  | ArmG => kimg_clip (kn_cutout k b off ne)
                  end in
        let ms' := match arm with ArmF => a_maps cs | _ => rekind (a_maps cs) m end in
        let ss := a_ss cs in
        let cs1 := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       ms' (a_totsz cs) (a_ylo cs)
                       (match arm with ArmE => a_eager cs + nhi | _ => a_eager cs end)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
        match arm with ArmE => vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1) | _ => Some cs1 end
      else None
  | None => None
  end.
(* [comment removed for export] *)
Definition mmap_fixed_in (cs : acs) (arm : fixed_in_arm) : option acs :=
  match fixed_in_args cs arm with
  | Some (b, off, ne, nlo, nhi, m) =>
      let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      if match arm with ArmE => budget_ok cs nhi | _ => true end then
        let k' := match arm with
                  | ArmE => kimg_clip (kn_unfillB bc b off ne)
                  | ArmF => kimg_clip (kn_rezeroB bc b off ne)
                  | ArmG => kimg_clip (kn_cutoutB bc b off ne)
                  end in
        let ms' := match arm with ArmF => a_maps cs | _ => rekind (a_maps cs) m end in
        let ss := a_ss cs in
        let cs1 := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       ms' (a_totsz cs) (a_ylo cs)
                       (match arm with ArmE => a_eager cs + nhi | _ => a_eager cs end)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
        match arm with ArmE => vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1) | _ => Some cs1 end
      else None
  | None => None
  end.

Lemma mmap_fixed_in_eq : forall cs arm, mmap_fixed_in cs arm = mmap_fixed_in_ref cs arm.
Proof. intros. unfold mmap_fixed_in, mmap_fixed_in_ref. unfold ehi, elo. rewrite ?kn_cutoutB_eqf, ?kn_rezeroB_eqf, ?kn_unfillB_eqf. reflexivity. Qed.


(* [comment removed for export] *)
Definition ENOMEM_RET : Z := two64 - 12.

(* [comment removed for export] *)
Definition refuse (cs : acs) : acs := set_pc (set_reg cs 10 (ELit ENOMEM_RET)) (pc cs + 4).

(* [comment removed for export] *)
Definition replace_entry (ms : list amap) (m : amap) (pieces : list amap) : list amap :=
  flat_map (fun m' => if amap_eqb m' m then pieces else [m']) ms.

(* [comment removed for export] *)
Definition dest_lfact (a mb : expr) (lne : bool) : kentry :=
  if lne then KRange (esub a mb) 1 (two64 - 1) else KRange (esub a mb) 0 0.
Definition dest_rfact (a ne mb ml : expr) (rne : bool) : kentry :=
  if rne then KRange (esub (eadd mb ml) (eadd a ne)) 1 (two64 - 1) else KRange (esub (eadd mb ml) (eadd a ne)) 0 0.

Definition mmap_destroyed_with_ref (hole : bool) (cs : acs) (b : expr) (off : Z) (ne : expr) (m : amap) (lne rne : bool) : acs :=
  let k := kn cs in
  let a := reg cs 10 in
  let mb := am_base m in let ml := am_len m in
  let lp := if lne then [AM mb (esub a mb) (am_kind m)] else [] in
  let rp := if rne then [AM (eadd a ne) (esub (eadd mb ml) (eadd a ne)) (am_kind m)] else [] in
  let hp := if hole then [AM a ne KHOLE] else [] in      (* [comment removed for export] *)
  let ss := a_ss cs in
  ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit ENOMEM_RET))
             (dest_lfact a mb lne :: dest_rfact a ne mb ml rne :: kimg_clip (kn_cutout k b off ne)) (s_next ss))
      (hp ++ replace_entry (a_maps cs) m (lp ++ rp)) (a_totsz cs) (a_ylo cs) (a_eager cs)
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).
(* [comment removed for export] *)
Definition mmap_destroyed_with (hole : bool) (cs : acs) (b : expr) (off : Z) (ne : expr) (m : amap) (lne rne : bool) : acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  let a := reg cs 10 in
  let mb := am_base m in let ml := am_len m in
  let lp := if lne then [AM mb (esub a mb) (am_kind m)] else [] in
  let rp := if rne then [AM (eadd a ne) (esub (eadd mb ml) (eadd a ne)) (am_kind m)] else [] in
  let hp := if hole then [AM a ne KHOLE] else [] in      (* [comment removed for export] *)
  let ss := a_ss cs in
  ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit ENOMEM_RET))
             (dest_lfact a mb lne :: dest_rfact a ne mb ml rne :: kimg_clip (kn_cutoutB bc b off ne)) (s_next ss))
      (hp ++ replace_entry (a_maps cs) m (lp ++ rp)) (a_totsz cs) (a_ylo cs) (a_eager cs)
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

Lemma mmap_destroyed_with_eq : forall hole cs b off ne m lne rne, mmap_destroyed_with hole cs b off ne m lne rne = mmap_destroyed_with_ref hole cs b off ne m lne rne.
Proof. intros. unfold mmap_destroyed_with, mmap_destroyed_with_ref. unfold ehi, elo. rewrite ?kn_cutoutB_eqf. reflexivity. Qed.


(* [comment removed for export] *)
Definition dest_cases (cs : acs) (ne : expr) (m : amap) : list (bool * bool) :=
  let k := kn cs in
  let a := reg cs 10 in
  let mb := am_base m in let ml := am_len m in
  let ls := if lin_ge0 k [(a, -1)] [(mb, 0)] then [true]                                   (* [comment removed for export] *)
            else if (expr_eqb a mb || lin_ge0 k [(mb, 0)] [(a, 0)])%bool then [false]    (* [comment removed for export] *)
            else [true; false] in
  let rs := if lin_ge0 k [(mb, -1); (ml, 0)] [(a, 0); (ne, 0)] then [true]                 (* [comment removed for export] *)
            else if lin_ge0 k [(a, 0); (ne, 0)] [(mb, 0); (ml, 0)] then [false]           (* [comment removed for export] *)
            else [true; false] in
  flat_map (fun l => map (fun r => (l, r)) rs) ls.

Definition mmap_destroyed (hole : bool) (cs : acs) (b : expr) (off : Z) (ne : expr) (m : amap) : list acs :=
  map (fun lr => mmap_destroyed_with hole cs b off ne m (fst lr) (snd lr)) (dest_cases cs ne m).

(* [comment removed for export] *)
Definition mmap_gate (cs : acs) : option (Z * Z * bool) :=
  match reg_lit cs 17, reg_lit cs 12, reg_lit cs 13, reg_lit cs 14, reg_lit cs 15 with
  | Some 222, Some prot, Some flags, Some m1, Some 0 =>
      if negb (Z.eqb m1 (two64 - 1)) then None
      else Some (prot, flags, match reg_lit cs 10 with Some 0 => true | _ => false end)
  | _, _, _, _, _ => None
  end.

(* [comment removed for export] *)
Definition node_mmap2 (cs : acs) : option (acs * acs) :=
  match mmap_gate cs with
  | Some (prot, flags, isnull) =>
      let g := if isnull then
                 match prot, flags with
                 | 3, 0x22 => mmap_null cs KRW true true               (* [comment removed for export] *)
                 | 3, 0x4022 => mmap_null cs KRWLAZY false true        (* [comment removed for export] *)
                 | 0, 0x22 => mmap_null cs KNONE false false           (* [comment removed for export] *)
                 | 0, 0x4022 => mmap_null cs KNONELAZY false false     (* [comment removed for export] *)
                 | _, _ => None
                 end
               else
                 match prot, flags with
                 | 3, 0x4032 => mmap_fixed_free cs KRWLAZY false false  (* [comment removed for export] *)
                 | 3, 0x32 => mmap_fixed_free cs KRW true true          (* [comment removed for export] *)
                 | 0, 0x4032 => mmap_fixed_free cs KNONELAZY false false (* [comment removed for export] *)
                 | 0, 0x32 => mmap_fixed_free cs KNONE false false      (* [comment removed for export] *)
                 | 3, 0x104022 => mmap_fixed_free cs KRWLAZY false false   (* [comment removed for export] *)
                 | 0, 0x104022 => mmap_fixed_free cs KNONELAZY false false (* [comment removed for export] *)
                 | _, _ => None
                 end in
      match g with Some csG => Some (refuse cs, csG) | None => None end
  | None => None
  end.

(* [comment removed for export] *)
Definition mmap_nullB (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  match mmap_len cs with
  | Some (ne, nlo, nhi) =>
      if (fresh_ok cs && expr_vars_lt (nxt cs) ne
          && gap_ok cs nhi && (negb eager || budget_ok cs nhi)
          && no_holes (a_maps cs))%bool then     (* [comment removed for export] *)
        let v := nxt cs in
        let base := escale 4096 (EVar v) in
        let lb := lowbound (a_maps cs) nlo in   (* [comment removed for export] *)
        let kfacts := grant_facts (kn cs) (a_maps cs) v base ne lb nlo ++ kdisj_new (a_maps cs) base ne in
        let kmem := [KWr (SA base 0) ne; KZero (SA base 0) ne] in
        let k' := kfacts ++ kn_grant_filterB (mkbc (kn cs)) (a_maps cs) in
        let cs1 := add_entry cs (sr_upd (s_regs (a_ss cs)) 10 base) k' (S v) (AM base ne kind) nhi eager (a_ylo cs) in
        if visible then vis_add cs1 base ne (kmem ++ kn cs1) else Some cs1
      else None
  | None => None
  end.
Lemma mmap_nullB_eq : forall cs kind eager visible, mmap_nullB cs kind eager visible = mmap_null cs kind eager visible.
Proof. intros. unfold mmap_nullB, mmap_null. rewrite kn_grant_filterB_eqf. reflexivity. Qed.
Definition mmap_fixed_grantB (cs : acs) (ms0 : list amap) (b : expr) (off : Z) (ne : expr) (nhi : Z)
           (kind : mkind) (eager visible : bool) : option acs :=
  let k := kn cs in
  let a := reg cs 10 in
  let m := AM a ne kind in
  let kmem := [KWr (SA b off) ne; KZero (SA b off) ne] in
  let ksh := if mkind_eqb kind KRWLAZY then flat_map (fun p => shadow_facts k [m] (fst p) (snd p)) (a_vis cs) else [] in
  let k' := ksh ++ kn_grant_filterB (mkbc k) ms0 in
  let cs1 := add_entry (with_maps0 cs ms0) (s_regs (a_ss cs)) k' (nxt cs) m nhi eager (a_ylo cs) in
  if visible then vis_add cs1 a ne (kmem ++ kn cs1) else Some cs1.
Lemma mmap_fixed_grantB_eq : forall cs ms0 b off ne nhi kind eager visible,
  mmap_fixed_grantB cs ms0 b off ne nhi kind eager visible = mmap_fixed_grant cs ms0 b off ne nhi kind eager visible.
Proof. intros. unfold mmap_fixed_grantB, mmap_fixed_grant. rewrite kn_grant_filterB_eqf. reflexivity. Qed.
Definition mmap_fixed_freeB (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  let k := kn cs in
  let a := reg cs 10 in
  match fixed_args cs CEIL with
  | Some (b, off, ne, nlo, nhi) =>
      if (no_fog (a_maps cs)
          && forallb (fun m => ranges_apart_x k b off ne (am_base m) 0 (am_len m)) (a_maps cs)
          && (negb eager || budget_ok cs nhi)
          && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) a)%bool
      then mmap_fixed_grantB cs (a_maps cs) b off ne nhi kind eager visible
      else None
  | None =>
      (* [comment removed for export] *)
      match fixed_args cs CEIL with
      | Some (b, off, ne, nlo, nhi) =>
          match find_hole k (a_maps cs) a ne with
          | Some h =>
              let ms0 := unhole (a_maps cs) h in
              if (forallb (fun m => negb (is_hole m) || ranges_apart_x k b off ne (am_base m) 0 (am_len m)) ms0
                  && (negb eager || budget_ok cs nhi)
                  && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) a)%bool
              then mmap_fixed_grantB cs ms0 b off ne nhi kind eager visible
              else None
          | None => None
          end
      | None => None
      end
  end.
Lemma mmap_fixed_freeB_eq : forall cs kind eager visible, mmap_fixed_freeB cs kind eager visible = mmap_fixed_free cs kind eager visible.
Proof.
  intros. unfold mmap_fixed_freeB, mmap_fixed_free.
  replace mmap_fixed_grantB with mmap_fixed_grant; [reflexivity|].
  do 9 (apply functional_extensionality; intro). symmetry. apply mmap_fixed_grantB_eq.
Qed.
Definition node_mmap2B (cs : acs) : option (acs * acs) :=
  match mmap_gate cs with
  | Some (prot, flags, isnull) =>
      let g := if isnull then
                 match prot, flags with
                 | 3, 0x22 => mmap_nullB cs KRW true true               (* [comment removed for export] *)
                 | 3, 0x4022 => mmap_nullB cs KRWLAZY false true        (* [comment removed for export] *)
                 | 0, 0x22 => mmap_nullB cs KNONE false false           (* [comment removed for export] *)
                 | 0, 0x4022 => mmap_nullB cs KNONELAZY false false     (* [comment removed for export] *)
                 | _, _ => None
                 end
               else
                 match prot, flags with
                 | 3, 0x4032 => mmap_fixed_freeB cs KRWLAZY false false  (* [comment removed for export] *)
                 | 3, 0x32 => mmap_fixed_freeB cs KRW true true          (* [comment removed for export] *)
                 | 0, 0x4032 => mmap_fixed_freeB cs KNONELAZY false false (* [comment removed for export] *)
                 | 0, 0x32 => mmap_fixed_freeB cs KNONE false false      (* [comment removed for export] *)
                 | 3, 0x104022 => mmap_fixed_freeB cs KRWLAZY false false   (* [comment removed for export] *)
                 | 0, 0x104022 => mmap_fixed_freeB cs KNONELAZY false false (* [comment removed for export] *)
                 | _, _ => None
                 end in
      match g with Some csG => Some (refuse cs, csG) | None => None end
  | None => None
  end.
Lemma node_mmap2B_eq : forall cs, node_mmap2B cs = node_mmap2 cs.
Proof.
  intros. unfold node_mmap2B, node_mmap2.
  replace mmap_nullB with mmap_null by (do 4 (apply functional_extensionality; intro); symmetry; apply mmap_nullB_eq).
  replace mmap_fixed_freeB with mmap_fixed_free by (do 4 (apply functional_extensionality; intro); symmetry; apply mmap_fixed_freeB_eq).
  reflexivity.
Qed.

(* [comment removed for export] *)
Definition node_mmapin (hole : bool) (cs : acs) : option (acs * acs * list acs) :=
  match mmap_gate cs with
  | Some (prot, flags, false) =>
      let arm := match prot, flags with
                 | 3, 0x32 => Some ArmE
                 | 3, 0x4032 => Some ArmF
                 | 0, 0x32 => Some ArmG
                 | _, _ => None
                 end in
      match arm with
      | Some arm =>
          match fixed_in_args cs arm, mmap_fixed_in cs arm with
          | Some (b, off, ne, nlo, nhi, m), Some csO => Some (refuse cs, csO, mmap_destroyed hole cs b off ne m)
          | _, _ => None
          end
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_mprotect_ref (cs : acs) : option acs :=
  match reg_lit cs 17, reg_lit cs 12, fixed_args cs TOPMAX with
  | Some 226, Some 3, Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in
      match find_containing k (a_maps cs) [KNONE; KNONELAZY] b off ne with
      | Some m =>
          if (budget_ok cs nhi && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then
            let k' := kimg_clip (kn_unfill k b off ne) in
            let ss := a_ss cs in
            let cs1 := ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k' (s_next ss))
                           (rekind (a_maps cs) m) (a_totsz cs) (a_ylo cs) (a_eager cs + nhi)
                           (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
            vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1)
          else None
      | None => None
      end
  | _, _, _ => None
  end.
(* [comment removed for export] *)
Definition node_mprotect (cs : acs) : option acs :=
  match reg_lit cs 17, reg_lit cs 12, fixed_args cs TOPMAX with
  | Some 226, Some 3, Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      match find_containingB bc (a_maps cs) [KNONE; KNONELAZY] b off ne with
      | Some m =>
          if (budget_ok cs nhi && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then
            let k' := kimg_clip (kn_unfillB bc b off ne) in
            let ss := a_ss cs in
            let cs1 := ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k' (s_next ss))
                           (rekind (a_maps cs) m) (a_totsz cs) (a_ylo cs) (a_eager cs + nhi)
                           (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
            vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1)
          else None
      | None => None
      end
  | _, _, _ => None
  end.
Lemma node_mprotect_eq : forall cs, node_mprotect cs = node_mprotect_ref cs.
Proof. intros. unfold node_mprotect, node_mprotect_ref. unfold ehi, elo. rewrite ?find_containingB_eqf, ?kn_unfillB_eqf. reflexivity. Qed.


(* [comment removed for export] *)
Definition node_mprotect2 (cs : acs) : option (acs * acs) :=
  match node_mprotect cs with Some csG => Some (refuse cs, csG) | None => None end.

(* [comment removed for export] *)

Definition amap_match (k : list kentry) (b : expr) (n : expr) (m : amap) : bool :=
  (negb (is_fog m) && expr_eqb b (am_base m) && len_eqb k n (am_len m))%bool.

Definition amap_matchB (bc : bctx) (b : expr) (n : expr) (m : amap) : bool :=
  (negb (is_fog m) && expr_eqb b (am_base m) && len_eqbB bc n (am_len m))%bool.

Lemma amap_matchB_eqf : forall fk, amap_matchB (mkbc fk) = amap_match fk.
Proof. intros. bcfe. unfold amap_matchB, amap_match. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite amap_matchB_eqf : bceq.



(* [comment removed for export] *)
Definition node_munmap_ref (cs : acs) : option acs :=
  match reg_lit cs 17, mmap_len cs with
  | Some 215, Some (ne, nlo, nhi) =>
      let b := reg cs 10 in let k := kn cs in
      let '(bb, bk) := split_lit b in
      let gone := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in negb (ranges_apart_x k pb pk (snd p) bb bk ne)) (a_vis cs) in
      let kept := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in ranges_apart_x k pb pk (snd p) bb bk ne) (a_vis cs) in
      if (existsb (amap_match k b ne) (a_maps cs) && page_aligned k b && flat_x k bb bk ne
          && match xhi k b with Some hi => Z.ltb (hi + nhi) two64 | None => false end
          && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                               let '(sb, sk, sn) := shadow_of k (fst p) (snd p) in
                               Z.leb 3 (ealign k (fst p)) && Z.leb 3 (ealign k (snd p))
                               && xinside k pb pk (snd p) bb bk ne && kzero_x k k sb sk sn)
                     gone)%bool then
        let k1 := fold_left (fun kk p => let '(sb, sk, sn) := shadow_of k (fst p) (snd p) in kn_unfill kk sb sk sn) gone (kn_unfill k bb bk ne) in
        let ss := a_ss cs in
        Some (ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k1 (s_next ss))
                 (List.filter (fun m => negb (amap_match k b ne m)) (a_maps cs))
                 (a_totsz cs) (a_ylo cs) (a_eager cs) kept (gone ++ a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition node_munmap (cs : acs) : option acs :=
  match reg_lit cs 17, mmap_len cs with
  | Some 215, Some (ne, nlo, nhi) =>
      let b := reg cs 10 in let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      let '(bb, bk) := split_lit b in
      let gone := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in negb (ranges_apart_xB bc pb pk (snd p) bb bk ne)) (a_vis cs) in
      let kept := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in ranges_apart_xB bc pb pk (snd p) bb bk ne) (a_vis cs) in
      if (existsb (amap_matchB bc b ne) (a_maps cs) && page_alignedB bc b && flat_xB bc bb bk ne
          && match xhiB bc b with Some hi => Z.ltb (hi + nhi) two64 | None => false end
          && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                               let '(sb, sk, sn) := shadow_ofB bc (fst p) (snd p) in
                               Z.leb 3 (ealignB bc (fst p)) && Z.leb 3 (ealignB bc (snd p))
                               && xinsideB bc pb pk (snd p) bb bk ne && kzero_xB bc k sb sk sn)
                     gone)%bool then
        let k1 := fold_left (fun kk p => let '(sb, sk, sn) := shadow_ofB bc (fst p) (snd p) in kn_unfillM kk sb sk sn) gone (kn_unfillB bc bb bk ne) in
        let ss := a_ss cs in
        Some (ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k1 (s_next ss))
                 (List.filter (fun m => negb (amap_matchB bc b ne m)) (a_maps cs))
                 (a_totsz cs) (a_ylo cs) (a_eager cs) kept (gone ++ a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.

Lemma node_munmap_eq : forall cs, node_munmap cs = node_munmap_ref cs.
Proof. intros. unfold node_munmap, node_munmap_ref. unfold ehi, elo. rewrite ?amap_matchB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?kn_unfillB_eqf, ?kzero_xB_eqf, ?page_alignedB_eqf, ?ranges_apart_xB_eqf, ?shadow_ofB_eqf, ?xhiB_eqf, ?xinsideB_eqf, ?kn_unfillM_eq. reflexivity. Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition brk_req (cs : acs) : option Z :=
  match lit_diff (reg cs 10) (a_brk cs) with
  | Some d => if (Z.ltb 0 d && Z.eqb (d mod 4096) 0 && Z.leb d (2 ^ 40))%bool then Some d else None
  | None => None
  end.

(* [comment removed for export] *)
Definition brk_base_ok (cs : acs) (d : Z) : bool :=
  let k := kn cs in let b := a_brk cs in
  (page_aligned k b
   && match xlo k b, xhi k b with
      | Some lo, Some hi => Z.ltb 0 lo && Z.leb (img_hi A) lo && Z.leb (hi + d + 4096) (MID_LO + 2^32)
      | _, _ => false
      end)%bool.

(* [comment removed for export] *)
Definition brk_grow_facts (k : list kentry) (ms : list amap) (bb : expr) (bk d : Z) : list kentry :=
  KDisj (SA bb bk) (ELit (d + 4096)) (SA e_sp0 STK_OFF) (ELit STK_LEN)
  :: pd_disj k bb bk (ELit (d + 4096)) ++                                   (* [comment removed for export] *)
  (if band_covered ms MID_LO KHI then [KDisj (SA bb bk) (ELit (d + 4096)) (SA (ELit MID_LO) 0) (ELit (KHI - MID_LO))] else [])
  ++ flat_map (fun m => if is_fog m then [] else [KDisj (SA (am_base m) 0) (am_len m) (SA bb bk) (ELit (d + 4096))]) ms.

Definition brk_grow_possible (cs : acs) (d : Z) : bool :=
  (brk_base_ok cs d && budget_ok cs d && no_holes (a_maps cs))%bool.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition brk_grow_blocked (cs : acs) (d : Z) : bool :=
  let k := kn cs in let b := a_brk cs in
  (brk_base_ok cs d
   && existsb (fun m => negb (is_fog m)
                        && lin_ge0 k [(am_base m, -1); (am_len m, 0)] [(b, 0)]      (* [comment removed for export] *)
                        && lin_ge0 k [(b, d - 1)] [(am_base m, 0)])               (* [comment removed for export] *)
              (a_maps cs))%bool.

(* [comment removed for export] *)
Definition node_brk1 (cs : acs) : option acs :=
  match reg_lit cs 17 with
  | Some 214 =>
      let ok := match reg_lit cs 10 with
                | Some 0 => true
                | _ => match brk_req cs with Some d => brk_grow_blocked cs d | None => false end
                end in
      if ok then Some (set_pc (set_reg cs 10 (a_brk cs)) (pc cs + 4)) else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition node_brk2 (cs : acs) : option (acs * acs) :=
  match reg_lit cs 17, brk_req cs with
  | Some 214, Some d =>
      if (brk_grow_possible cs d && expr_vars_lt (nxt cs) (reg cs 10))%bool then
        let k := kn cs in let b := a_brk cs in let '(bb, bk) := split_lit b in
        let csA := set_pc (set_reg cs 10 b) (pc cs + 4) in
        let k' := brk_grow_facts k (a_maps cs) bb bk d ++ kn_grant_filter k (a_maps cs) in   (* [comment removed for export] *)
        let ss := a_ss cs in
        let csB := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       (AM b (ELit d) KRW :: a_maps cs) (a_totsz cs + d) (a_ylo cs) (a_eager cs + d)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (reg cs 10) (a_fd cs) (a_tidset cs) in
        match vis_add csB b (ELit d) (KWr (SA bb bk) (ELit d) :: KZero (SA bb bk) (ELit d) :: kn csB) with
        | Some csB' => Some (csA, csB')
        | None => None
        end
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)

Definition node_settid (cs : acs) : option acs :=
  match reg_lit cs 17 with
  | Some 96 =>
      if (negb (a_tidset cs) && fresh_ok cs)%bool then
        let v := nxt cs in let ss := a_ss cs in
        Some (ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (EVar v)) (KRange (EVar v) 1 (PID_MAX - 1) :: s_know ss) (S v))
                 (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) true)
      else None
  | _ => None
  end.

Definition node_exit (cs : acs) : option Z :=
  match reg_lit cs 17, reg_lit cs 10 with
  | Some 94, Some code => Some (Z.land code 255)
  | Some 93, Some code => Some (Z.land code 255)
  | _, _ => None
  end.

(* [comment removed for export] *)

Fixpoint list_set_nth {T} (i : nat) (x : T) (l : list T) : list T :=
  match l, i with
  | [], _ => []
  | _ :: r, O => x :: r
  | y :: r, S i' => y :: list_set_nth i' x r
  end.
Fixpoint list_insert_nth {T} (i : nat) (x : T) (l : list T) : list T :=
  match i, l with
  | O, _ => x :: l
  | S i', y :: r => y :: list_insert_nth i' x r
  | S _, [] => [x]
  end.

Definition fog_token (sz : Z) : amap := AM (ELit 0) (ELit sz) KFOG.

Definition with_maps (cs : acs) (ms : list amap) : acs :=
  ACS (a_ss cs) ms (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

(* [comment removed for export] *)
Definition node_fog (cs : acs) (i : nat) (sz : Z) : option acs :=
  match nth_error (a_maps cs) i with
  | Some m =>
      if (negb (is_fog m) && Z.leb 0 sz && Z.ltb sz two64
          && match xhi (kn cs) (am_len m) with Some h => Z.leb h sz | None => false end)%bool
      then Some (with_maps cs (list_set_nth i (fog_token sz) (a_maps cs)))
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition node_fognew (cs : acs) (i : nat) (sz : Z) : option acs :=
  if (Nat.leb i (length (a_maps cs)) && Z.leb 0 sz && Z.ltb sz two64)%bool
  then Some (with_maps cs (list_insert_nth i (fog_token sz) (a_maps cs)))
  else None.

(* [comment removed for export] *)
Definition node_ghost (cs : acs) (b n : expr) : option acs :=
  match xhi (kn cs) n with
  | Some nhi =>
      if (expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n && Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
      then Some (ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs ++ [(b, n)])
                     (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition vis_here (b n : expr) (p : expr * expr) : bool := (expr_eqb (fst p) b && expr_eqb (snd p) n)%bool.

(* [comment removed for export] *)
Definition stack_side (k : list kentry) (b : expr) : bool :=
  match erange k (esub b (eaddz e_sp0 STK_OFF)) with
  | Some (lo, hi) => (Z.leb 0 lo && Z.leb hi TWO47)%bool
  | None => false
  end.
Definition stack_sideB (bc : bctx) (b : expr) : bool :=
  match erangeB bc (esub b (eaddz e_sp0 STK_OFF)) with
  | Some (lo, hi) => (Z.leb 0 lo && Z.leb hi TWO47)%bool
  | None => false
  end.
Lemma stack_sideB_eqf : forall fk, stack_sideB (mkbc fk) = stack_side fk.
Proof. intros. unfold stack_sideB, stack_side. autorewrite with bceq. reflexivity. Qed.

Definition node_unvis_ref (cs : acs) (b n : expr) : option acs :=
  let k := kn cs in
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_of k b n in
  match xhi k b, xhi k n with
  | Some bh, Some nh =>
      if (existsb (vis_here b n) (a_vis cs)
          && Z.leb 3 (ealign k b) && Z.leb 3 (ealign k n) && flat_x k bb bk n   (* [comment removed for export] *)
          && flat_x k sb sk sn && kzero_x k k sb sk sn)%bool
      then
        let k1 := if stack_side k b then k else kn_unfill k bb bk n in   (* [comment removed for export] *)
        let k2 := kn_unfill k1 sb sk sn in
        let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) k2 (s_next ss))
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                  (List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) (a_ghost cs ++ [(b, n)])
                  (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition node_unvis (cs : acs) (b n : expr) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_ofB bc b n in
  match xhiB bc b, xhiB bc n with
  | Some bh, Some nh =>
      if (existsb (vis_here b n) (a_vis cs)
          && Z.leb 3 (ealignB bc b) && Z.leb 3 (ealignB bc n) && flat_xB bc bb bk n   (* [comment removed for export] *)
          && flat_xB bc sb sk sn && kzero_xB bc k sb sk sn)%bool
      then
        let k1 := if stack_sideB bc b then k else kn_unfillB bc bb bk n in   (* [comment removed for export] *)
        let k2 := kn_unfillM k1 sb sk sn in
        let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) k2 (s_next ss))
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                  (List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) (a_ghost cs ++ [(b, n)])
                  (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.

Lemma node_unvis_eq : forall cs b n, node_unvis cs b n = node_unvis_ref cs b n.
Proof. intros. unfold node_unvis, node_unvis_ref. unfold ehi, elo. rewrite ?ealignB_eqf, ?flat_xB_eqf, ?stack_sideB_eqf, ?kn_unfillB_eqf, ?kzero_xB_eqf, ?shadow_ofB_eqf, ?xhiB_eqf, ?kn_unfillM_eq. destruct (stack_side _ _); rewrite ?kn_unfillM_eq; reflexivity. Qed.


(* [comment removed for export] *)
Definition node_havocbrk (cs : acs) (lo hi : Z) : option acs :=
  match xlo (kn cs) (a_brk cs), xhi (kn cs) (a_brk cs) with
  | Some l, Some h =>
      if (fresh_ok cs && Z.leb lo l && Z.leb h hi)%bool then
        let v := nxt cs in let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) (KRange (EVar v) lo hi :: s_know ss) (S v))
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (EVar v) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition node_intro (cs : acs) (lo hi : Z) : option acs :=
  if (fresh_ok cs && Z.leb 0 lo && Z.leb lo hi && Z.ltb hi two64)%bool then
    let v := nxt cs in let ss := a_ss cs in
    Some (with_ss cs (mk_ss (s_pc ss) (s_regs ss) (KRange (EVar v) lo hi :: s_know ss) (S v)))
  else None.

(* [comment removed for export] *)
Definition SPIN_WORD : Z := 0x6f.
Definition node_spin (cs : acs) : bool :=
  (Z.leb 0 (pc cs) && Z.ltb (pc cs + 4) two64 &&
  match fetch_word segs (Z_to_bv 64 (pc cs)) with
  | Some w => Z.eqb (bv_unsigned w) SPIN_WORD
  | None => false
  end)%bool.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition summary_fill_ref (cs : acs) (entry : Z) (cmax : Z) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs, reg_lit cs 11 with
  | Some ret, Some c =>
      if negb (Z.ltb c cmax) then None else
      let dst := reg cs 10 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in
      let c8 := c mod 256 in
      match xlo k ne, xhi k ne, xhi k dst with
      | Some nlo, Some nhi, Some dhi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64)%bool then
            if (Z.eqb nhi 0) then after_call cs ret (Some dst) k else
            if (Z.eqb c8 0 && kzero_x k k db dk ne && kwritable_x k k db dk ne)%bool then after_call cs ret (Some dst) k else
            match (if off_image_x k db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if kwritable_x k k db dk ne then
              let k1 := kn_havoc k0 db dk ne in
              let k2 := if Z.ltb 0 nlo then (if Z.eqb c8 0 then KZero (SA db dk) ne else KFill (SA db dk) ne c8) :: k1 else k1 in
              after_call cs ret (Some dst) k2
            else None
            end
          else None
      | _, _, _ => None
      end
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition summary_fill (cs : acs) (entry : Z) (cmax : Z) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs, reg_lit cs 11 with
  | Some ret, Some c =>
      if negb (Z.ltb c cmax) then None else
      let dst := reg cs 10 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in
      let c8 := c mod 256 in
      match xloB bc ne, xhiB bc ne, xhiB bc dst with
      | Some nlo, Some nhi, Some dhi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64)%bool then
            if (Z.eqb nhi 0) then after_call cs ret (Some dst) k else
            if (Z.eqb c8 0 && kzero_xB bc k db dk ne && kwritable_xB bc k db dk ne)%bool then after_call cs ret (Some dst) k else
            match (if off_image_xB bc db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if kwritable_xB bc k db dk ne then
              let k1 := kn_havocM k0 db dk ne in
              let k2 := if Z.ltb 0 nlo then (if Z.eqb c8 0 then KZero (SA db dk) ne else KFill (SA db dk) ne c8) :: k1 else k1 in
              after_call cs ret (Some dst) k2
            else None
            end
          else None
      | _, _, _ => None
      end
  | _, _ => None
  end.

Lemma summary_fill_eq : forall cs entry cmax, summary_fill cs entry cmax = summary_fill_ref cs entry cmax.
Proof. intros. unfold summary_fill, summary_fill_ref. unfold ehi, elo. rewrite ?kwritable_xB_eqf, ?kzero_xB_eqf, ?off_image_xB_eqf, ?xhiB_eqf, ?xloB_eqf, ?kn_havocM_eq. reflexivity. Qed.


(* [comment removed for export] *)
Fixpoint copy_facts (fuel : nat) (k : list kentry) (sb : expr) (sk : Z) (db : expr) (dk : Z) (n : Z)
  : option (list kentry) :=
  match fuel with
  | O => Some []
  | S f =>
      if (Z.leb 8 n &&
          match kread8e k sb sk with Some _ => true | None => match kread_bytes 8 k sb sk with Some _ => true | None => false end end)%bool then
        match (match kread8e k sb sk with
               | Some v => Some v
               | None => match kread_bytes 8 k sb sk with
                         | Some bs => Some (ELit (zbytes_le_to_Z bs))
                         | None => None
                         end
               end), copy_facts f k sb (sk + 8) db (dk + 8) (n - 8) with
        | Some v, Some rest => Some (KWord (SA db dk) 8 v :: rest)
        | _, _ => None
        end
      else if Z.leb 1 n then (* [comment removed for export] *)
        match know_lookup segs k sb sk 1 false [] [], copy_facts f k sb (sk + 1) db (dk + 1) (n - 1) with
        | LHit v [] _, Some rest => Some (KWord (SA db dk) 1 v :: rest)
        | _, _ => None
        end
      else Some []
  end.

Fixpoint copy_factsB (bc : bctx) (fuel : nat) (sb : expr) (sk : Z) (db : expr) (dk : Z) (n : Z)
  : option (list kentry) :=
  match fuel with
  | O => Some []
  | S f =>
      if (Z.leb 8 n &&
          match kread8eB bc sb sk with Some _ => true | None => match kread_bytesB bc 8 sb sk with Some _ => true | None => false end end)%bool then
        match (match kread8eB bc sb sk with
               | Some v => Some v
               | None => match kread_bytesB bc 8 sb sk with
                         | Some bs => Some (ELit (zbytes_le_to_Z bs))
                         | None => None
                         end
               end), copy_factsB bc f sb (sk + 8) db (dk + 8) (n - 8) with
        | Some v, Some rest => Some (KWord (SA db dk) 8 v :: rest)
        | _, _ => None
        end
      else if Z.leb 1 n then (* [comment removed for export] *)
        match know_lookupB segs bc sb sk 1 false [] [], copy_factsB bc f sb (sk + 1) db (dk + 1) (n - 1) with
        | LHit v [] _, Some rest => Some (KWord (SA db dk) 1 v :: rest)
        | _, _ => None
        end
      else Some []
  end.

Lemma copy_factsB_eqf' : forall fk fuel, copy_factsB (mkbc fk) fuel = copy_facts fuel fk.
Proof.
  intros fk fuel. induction fuel as [|f IH]; bcfe; [reflexivity|].
  cbn [copy_factsB copy_facts]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
Lemma copy_factsB_eqf : forall fk, copy_factsB (mkbc fk) = (fun fuel => copy_facts fuel fk).
Proof. intros fk. apply functional_extensionality; intros fuel. apply copy_factsB_eqf'. Qed.
#[local] Hint Rewrite copy_factsB_eqf' copy_factsB_eqf : bceq.



(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kblob_prefix (k : list kentry) (sb : expr) (sk : Z) (db : expr) (dk : Z) (nlo : Z) : list kentry :=
  match List.find (fun K => match K with
                             | KBlob (SA b o) (ELit n0) _ => expr_eqb b sb && Z.eqb o sk && Z.ltb 0 n0 && Z.leb n0 nlo
                             | _ => false
                             end) k with
  | Some (KBlob _ (ELit n0) j) => [KBlob (SA db dk) (ELit n0) j]
  | _ => []
  end.

Definition summary_copy_ref (cs : acs) (entry : Z) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs with
  | Some ret =>
      let dst := reg cs 10 in let src := reg cs 11 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in let '(sb, sk) := split_lit src in
      match xlo k ne, xhi k ne, xhi k dst, xhi k src with
      | Some nlo, Some nhi, Some dhi, Some shi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64 && Z.ltb (shi + nhi) two64)%bool then
            if Z.eqb nhi 0 then after_call cs ret (Some dst) k else
            match (if off_image_x k db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if (kwritable_x k k db dk ne && ranges_apart_x k db dk ne sb sk ne)%bool then
              let k1 := kn_havoc k0 db dk ne in
              (* [comment removed for export] *)
              let nx := nxt cs in
              let words := if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat in
              let kfresh := map (fun i => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nx + NCS + i)%nat)) (seq 0 words) in
              let havoc_src := if (kwritable_x k k sb sk ne && flat_x k sb sk ne)%bool
                               then after_call2 cs ret (Some dst) (kfresh ++ kblob_prefix k sb sk db dk nlo ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: k1 else k1)) words else None in
              if (Z.ltb 0 nlo && kzero_x k k sb sk ne)%bool then after_call cs ret (Some dst) (KZero (SA db dk) ne :: k1)
              else match ne with
                   | ELit _ =>
                       if (Z.leb nhi 2048 && flat_x k sb sk ne)%bool then
                         match copy_facts (Z.to_nat nhi) k sb sk db dk nhi with
                         | Some kc => after_call cs ret (Some dst) (kc ++ k1)
                         | None => havoc_src
                         end
                       else havoc_src
                   | _ => havoc_src
                   end
            else None
            end
          else None
      | _, _, _, _ => None
      end
  | None => None
  end.
(* [comment removed for export] *)
Definition summary_copy (cs : acs) (entry : Z) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs with
  | Some ret =>
      let dst := reg cs 10 in let src := reg cs 11 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in let '(sb, sk) := split_lit src in
      match xloB bc ne, xhiB bc ne, xhiB bc dst, xhiB bc src with
      | Some nlo, Some nhi, Some dhi, Some shi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64 && Z.ltb (shi + nhi) two64)%bool then
            if Z.eqb nhi 0 then after_call cs ret (Some dst) k else
            match (if off_image_xB bc db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if (kwritable_xB bc k db dk ne && ranges_apart_xB bc db dk ne sb sk ne)%bool then
              let k1 := kn_havocM k0 db dk ne in
              (* [comment removed for export] *)
              let nx := nxt cs in
              let words := if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat in
              let kfresh := map (fun i => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nx + NCS + i)%nat)) (seq 0 words) in
              let havoc_src := if (kwritable_xB bc k sb sk ne && flat_xB bc sb sk ne)%bool
                               then after_call2 cs ret (Some dst) (kfresh ++ kblob_prefix k sb sk db dk nlo ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: k1 else k1)) words else None in
              if (Z.ltb 0 nlo && kzero_xB bc k sb sk ne)%bool then after_call cs ret (Some dst) (KZero (SA db dk) ne :: k1)
              else match ne with
                   | ELit _ =>
                       if (Z.leb nhi 2048 && flat_xB bc sb sk ne)%bool then
                         match copy_factsB bc (Z.to_nat nhi) sb sk db dk nhi with
                         | Some kc => after_call cs ret (Some dst) (kc ++ k1)
                         | None => havoc_src
                         end
                       else havoc_src
                   | _ => havoc_src
                   end
            else None
            end
          else None
      | _, _, _, _ => None
      end
  | None => None
  end.

Lemma summary_copy_eq : forall cs entry, summary_copy cs entry = summary_copy_ref cs entry.
Proof. intros. unfold summary_copy, summary_copy_ref. unfold ehi, elo. rewrite ?copy_factsB_eqf, ?flat_xB_eqf, ?kwritable_xB_eqf, ?kzero_xB_eqf, ?off_image_xB_eqf, ?ranges_apart_xB_eqf, ?xhiB_eqf, ?xloB_eqf, ?kn_havocM_eq. reflexivity. Qed.


(* [comment removed for export] *)
Definition summary_miz_ref (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (x_memiszero A)) then None else
  match ret_lit cs with
  | Some ret =>
      let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
      let '(bb, bk) := split_lit beg in
      let spm := eaddz sp (-16) in let '(qb, qk) := split_lit spm in
      match xlo k ne, xhi k ne, xhi k beg, xlo k sp, xhi k sp with
      | Some nlo, Some nhi, Some bhi, Some splo, Some sphi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.leb (bhi + nhi + 8) two64
              && Z.leb 16 splo && Z.ltb sphi two64
              && kwritable k k qb qk 16
              && ranges_apart_x k qb qk (ELit 16) bb bk ne && kzero_x k k bb bk ne)%bool
          then after_call cs ret (Some (ELit 1)) (kn_havoc k qb qk (ELit 16))
          else None
      | _, _, _, _, _ => None
      end
  | None => None
  end.
(* [comment removed for export] *)
Definition summary_miz (cs : acs) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) (x_memiszero A)) then None else
  match ret_lit cs with
  | Some ret =>
      let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
      let '(bb, bk) := split_lit beg in
      let spm := eaddz sp (-16) in let '(qb, qk) := split_lit spm in
      match xloB bc ne, xhiB bc ne, xhiB bc beg, xloB bc sp, xhiB bc sp with
      | Some nlo, Some nhi, Some bhi, Some splo, Some sphi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.leb (bhi + nhi + 8) two64
              && Z.leb 16 splo && Z.ltb sphi two64
              && kwritableB bc k qb qk 16
              && ranges_apart_xB bc qb qk (ELit 16) bb bk ne && kzero_xB bc k bb bk ne)%bool
          then after_call cs ret (Some (ELit 1)) (kn_havocB bc qb qk (ELit 16))
          else None
      | _, _, _, _, _ => None
      end
  | None => None
  end.

Lemma summary_miz_eq : forall cs, summary_miz cs = summary_miz_ref cs.
Proof. intros. unfold summary_miz, summary_miz_ref. unfold ehi, elo. rewrite ?kn_havocB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf, ?ranges_apart_xB_eqf, ?xhiB_eqf, ?xloB_eqf. reflexivity. Qed.


(* [comment removed for export] *)
Definition img_cov (k : list kentry) (a b : Z) : bool :=
  existsb (fun K => match K with KImg lo hi => Z.leb lo a && Z.leb b hi | _ => false end) k.

Definition img_covB (bc : bctx) (a b : Z) : bool :=
  existsb (fun K => match K with KImg lo hi => Z.leb lo a && Z.leb b hi | _ => false end) (bc_fk bc).
Lemma img_covB_eqf : forall fk, img_covB (mkbc fk) = img_cov fk.
Proof. intros. bcfe. unfold img_covB, img_cov. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite img_covB_eqf : bceq.



(* [comment removed for export] *)
Definition SEALED_W : Z := 0x3e64656c6165733c.

(* [comment removed for export] *)
Definition summary_istrncpy_ref (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (x_istrncpy A)) then None else
  match ret_lit cs, reg_lit cs 11, reg_lit cs 12 with
  | Some ret, Some src, Some n =>
      if negb (Z.eqb src (x_sealed A) && Z.eqb n 4095)%bool then None else
      let dst := reg cs 10 in
      let '(db, dk) := split_lit dst in
      match xhi k dst with
      | Some dhi =>
          match (if off_image_x k db dk (ELit 4095) then Some k
                 else match dst with ELit d => Some (kimg_cut k (d mod two64) 4095) | _ => None end) with
          | None => None
          | Some k0 =>
              if (Z.ltb (dhi + 4095) two64 && Z.leb 0 (x_sealed A) && Z.ltb (x_sealed A + 9) two64
                  && kwritable_x k k db dk (ELit 4095) && img_cov k0 (x_sealed A) (x_sealed A + 9)
                  && ranges_apart_x k db dk (ELit 4095) (ELit 0) (x_sealed A) (ELit 9))%bool then
                after_call cs ret (Some dst)
                  (KWord (SA db dk) 8 (ELit SEALED_W) :: KZero (SA db (dk + 8)) (ELit 4087) :: kn_havoc k0 db dk (ELit 4095))
              else None
          end
      | None => None
      end
  | _, _, _ => None
  end.
(* [comment removed for export] *)
Definition summary_istrncpy (cs : acs) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) (x_istrncpy A)) then None else
  match ret_lit cs, reg_lit cs 11, reg_lit cs 12 with
  | Some ret, Some src, Some n =>
      if negb (Z.eqb src (x_sealed A) && Z.eqb n 4095)%bool then None else
      let dst := reg cs 10 in
      let '(db, dk) := split_lit dst in
      match xhiB bc dst with
      | Some dhi =>
          match (if off_image_xB bc db dk (ELit 4095) then Some k
                 else match dst with ELit d => Some (kimg_cut k (d mod two64) 4095) | _ => None end) with
          | None => None
          | Some k0 =>
              if (Z.ltb (dhi + 4095) two64 && Z.leb 0 (x_sealed A) && Z.ltb (x_sealed A + 9) two64
                  && kwritable_xB bc k db dk (ELit 4095) && img_cov k0 (x_sealed A) (x_sealed A + 9)
                  && ranges_apart_xB bc db dk (ELit 4095) (ELit 0) (x_sealed A) (ELit 9))%bool then
                after_call cs ret (Some dst)
                  (KWord (SA db dk) 8 (ELit SEALED_W) :: KZero (SA db (dk + 8)) (ELit 4087) :: kn_havocM k0 db dk (ELit 4095))
              else None
          end
      | None => None
      end
  | _, _, _ => None
  end.

Lemma summary_istrncpy_eq : forall cs, summary_istrncpy cs = summary_istrncpy_ref cs.
Proof. intros. unfold summary_istrncpy, summary_istrncpy_ref. unfold ehi, elo. rewrite ?kwritable_xB_eqf, ?off_image_xB_eqf, ?ranges_apart_xB_eqf, ?xhiB_eqf, ?kn_havocM_eq. reflexivity. Qed.


(* [comment removed for export] *)
Definition popfree_facts (lb : expr) (lk : Z) (cnt c s : Z) (K : nat) : list kentry :=
  map (fun t => KWord (SA lb (lk + 4 * (cnt - 1 - Z.of_nat t))) 4 (ELit ((c + Z.of_nat t * s) / 16))) (seq 0 K).
Definition summary_popfree (cs : acs) (args : list expr) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (x_popfree A)) then None else
  match args, reg_lit cs 10, reg_lit cs 12, reg_lit cs 21, reg_lit cs 19 with
  | [ELit K], Some i, Some c, Some s, Some n =>
      let e := reg cs 11 in
      let cnt := n - i in
      let lo := eaddz e (- (4 * n)) in
      let '(lb, lk) := split_lit lo in
      match xlo k e, xhi k e with
      | Some el, Some eh =>
          if (Z.leb 0 i && Z.ltb i n && Z.leb (4 * n) el && Z.ltb eh two64 && Z.leb 0 c && Z.leb 0 s
              && Z.ltb (c + cnt * s) two64 && Z.leb 0 K && Z.leb K cnt && Z.ltb (pc cs + 32) two64
              && fresh_ok cs && kwritable_x k k lb lk (ELit (4 * cnt)) && off_image_x k lb lk (ELit (4 * cnt)))%bool then
            let k1 := kn_havoc k lb lk (ELit (4 * cnt)) in
            let kunk := if Z.ltb K cnt then [KUnk (SA lb lk) (ELit (4 * (cnt - K)))] else [] in
            let sr := s_regs (a_ss cs) in
            let sr' := sr_upd (sr_upd (sr_upd (sr_upd sr 10 (ELit n)) 12 (ELit (c + cnt * s)))
                                      14 (ELit ((c + (cnt - 1) * s) / 16))) 15 lo in
            Some (with_ss cs (mk_ss (pc cs + 32) sr' (popfree_facts lb lk cnt c s (Z.to_nat K) ++ kunk ++ k1) (nxt cs)))
          else None
      | _, _ => None
      end
  | _, _, _, _, _ => None
  end.

(* [comment removed for export] *)
Definition MAXVA_LEN : Z := 180.
Definition MAXVA_POST : list (nat * Z) :=
  [(10%nat, 0x7fffffffffff); (11%nat, 0xffffffffffffffff); (12%nat, 0x3333333333333333);
   (13%nat, 0x0f0f0f0f0f0f0f0f); (14%nat, 0x0101010101010101); (15%nat, 0x7fffc00000000000)].
Definition TWO46 : Z := 0x400000000000.
Definition summary_maxva (cs : acs) : option acs :=
  if (Z.eqb (x_maxva A) 0 || negb (Z.eqb (pc cs) (x_maxva A)))%bool then None else
  let k := kn cs in
  match xlo k (reg cs 10), xhi k (reg cs 10) with
  | Some lo, Some hi =>
      if (Z.leb TWO46 lo && Z.ltb hi TWO47)%bool
      then Some (set_pc (fold_left (fun c rv => set_reg c (fst rv) (ELit (snd rv))) MAXVA_POST cs) (pc cs + MAXVA_LEN))
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition kn_readable_x (k : list kentry) (rb : expr) (rk : Z) (ne : expr) : bool :=
  existsb (fun K => match K with
                    | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
                        xinside k rb rk ne kb kk len
                    | _ => false
                    end) k.



(* [comment removed for export] *)
Definition e_envp : expr := eadd e_sp0 (eadd (escale 8 (EVar V_ARGC)) (ELit 16)).
Definition e_auxv : expr := eadd e_envp (eadd (escale 8 (EVar V_ENVC)) (ELit 8)).
Definition e_str0 : expr := eaddz e_auxv 160.
Definition e_str1 : expr := eadd e_str0 (eaddz (EVar V_L0) 1).
Definition e_atrandom : expr := eadd e_str0 (escale 8 (EVar V_W)).
(* [comment removed for export] *)
Definition e_atr8 : expr :=   (* [comment removed for export] *)
  eadd (eadd (escale 4096 (EVar V_S1)) (eadd (escale 2 (EVar V_S2)) (escale 512 (EVar V_SP)))) (eadd (EVar V_ARGC) (eadd (EVar V_ENVC) (EVar V_W))).

(* [comment removed for export] *)
Definition e_argv1w : expr := EMd M_MUL (EAlu ALU_SLTU (ELit 1) (EVar V_ARGC)) e_str1.

(* [comment removed for export] *)
Definition node_envscan (cs : acs) : option acs :=
  let k := kn cs in
  if (Z.eqb (pc cs) (x_envscan A) && len_eqb k (reg cs 9) e_envp)%bool then
    Some (set_pc (set_reg (set_reg cs 9 (eadd (reg cs 9) (eadd (escale 8 (EVar V_ENVC)) (ELit 8)))) 10 (ELit 0)) (x_envscan_k A))
  else None.

(* [comment removed for export] *)
Definition node_pnscan (cs : acs) : option acs :=
  let k := kn cs in
  match reg_lit cs 10, reg_lit cs 12 with
  | Some p, Some 47 =>
      if (Z.eqb (pc cs) (x_pnscan A) && len_eqb k (reg cs 11) (eaddz e_str0 1)
          && kwritable k k (ELit 0) p 8 && Z.leb (img_lo A) p && Z.leb (p + 8) (img_hi A) && fresh_ok cs)%bool then
        let v := nxt cs in
        let k' := kn_havoc (kimg_cut k p 8) (ELit 0) p (ELit 8) in
        let ss := a_ss cs in
        Some (with_ss cs (mk_ss (x_pnscan_k A) (sr_upd (sr_upd (s_regs ss) 11 (EVar v)) 13 (ELit 0)) k' (S v)))
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition kw_argv1 (v : expr) : kentry := KWord (SA e_sp0 16) 8 v.

Definition node_layout (cs : acs) (args : list expr) : option acs :=
  let k := kn cs in
  if negb (existsb (kentry_eqb (kw_argv1 e_argv1w)) k) then None else
  let k' := List.filter (fun K => negb (kentry_eqb (kw_argv1 e_argv1w) K)) k in
  match args with
  | [ELit 1] => match xlo k (EVar V_ARGC) with
                | Some lo => if Z.leb 2 lo then Some (set_kn cs (kw_argv1 e_str1 :: k')) else None
                | None => None
                end
  | [ELit 0] => match xhi k (EVar V_ARGC) with
                | Some hi => if Z.leb hi 1 then Some (set_kn cs (kw_argv1 (ELit 0) :: k')) else None
                | None => None
                end
  | _ => None
  end.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kfp (K : kentry) : Z :=
  match K with
  | KWord a _ _ => a_off a | KZero a _ => a_off a | KBlob a _ _ => a_off a | KImg lo _ => lo | KAlign _ m => m
  | KRange _ lo _ => lo | KWr a _ => a_off a | KDisj a1 _ a2 _ => a_off a1 + a_off a2 | KFill a _ _ => a_off a | KUnk a _ => a_off a
  end.
Definition kn_sub_fast (live stored : list kentry) : bool :=
  let fl := List.map (fun K => (kfp K, K)) live in
  forallb (fun K => let f := kfp K in existsb (fun p => if Z.eqb f (fst p) then kentry_eqb K (snd p) else false) fl) stored.   (* [comment removed for export] *)
Lemma kn_sub_fast_sound : forall live stored,
  kn_sub_fast live stored = true -> forallb (fun K => existsb (kentry_eqb K) live) stored = true.
Proof.
  intros live stored H. unfold kn_sub_fast in H. apply forallb_forall. intros K HK.
  pose proof (proj1 (forallb_forall _ _) H K HK) as H1. cbv zeta in H1.
  apply existsb_exists in H1 as [p [Hp Hq]]. destruct (Z.eqb (kfp K) (fst p)); [|discriminate Hq].
  apply in_map_iff in Hp as [K' [<- HK']]. apply existsb_exists. exists K'. split; [exact HK' | exact Hq].
Qed.

(* [comment removed for export] *)
Definition zfp_key (z : Z) : positive := match z with Z0 => 1%positive | Zpos p => (p~0)%positive | Zneg p => (p~1)%positive end.
Lemma zfp_key_inj : forall a b, zfp_key a = zfp_key b -> a = b.
Proof. intros [|p|p] [|q|q] H; cbn in H; try discriminate H; try reflexivity; injection H as ->; reflexivity. Qed.
Definition kn_bucket (t : ptree (list kentry)) (f : Z) : list kentry :=
  match pt_get t (zfp_key f) with Some l => l | None => [] end.
Definition kn_index_add (t : ptree (list kentry)) (K : kentry) : ptree (list kentry) :=
  pt_set (zfp_key (kfp K)) (K :: kn_bucket t (kfp K)) t.
Definition kn_index (live : list kentry) : ptree (list kentry) := fold_left kn_index_add live (@PTLeaf (list kentry)).
Definition kn_sub_idx (live stored : list kentry) : bool :=
  let t := kn_index live in
  forallb (fun K => existsb (kentry_eqb K) (kn_bucket t (kfp K))) stored.
Lemma kn_bucket_add : forall t K f,
  kn_bucket (kn_index_add t K) f = if Z.eqb f (kfp K) then K :: kn_bucket t f else kn_bucket t f.
Proof.
  intros t K f. unfold kn_index_add. destruct (Z.eqb_spec f (kfp K)) as [->|Hne].
  - unfold kn_bucket at 1. rewrite pt_gss. reflexivity.
  - unfold kn_bucket at 1. rewrite pt_gso by (intros E; apply Hne; exact (zfp_key_inj _ _ E)). reflexivity.
Qed.
Lemma kn_index_existsb : forall (P : kentry -> bool) live t f,
  existsb P (kn_bucket (fold_left kn_index_add live t) f)
  = (existsb (fun K => if Z.eqb f (kfp K) then P K else false) live || existsb P (kn_bucket t f))%bool.
Proof.
  intros P live. induction live as [|K live IH]; intros t f; cbn [fold_left existsb]; [reflexivity|].
  rewrite IH, kn_bucket_add. destruct (Z.eqb f (kfp K)); cbn [existsb].
  - destruct (P K); cbn [orb]; [rewrite !Bool.orb_true_r; reflexivity | reflexivity].
  - reflexivity.
Qed.
Lemma kn_sub_idx_eq : forall live stored, kn_sub_idx live stored = kn_sub_fast live stored.
Proof.
  intros live stored. unfold kn_sub_idx, kn_sub_fast. cbv zeta. induction stored as [|K stored IH]; cbn [forallb]; [reflexivity|].
  rewrite IH. f_equal. unfold kn_index. rewrite kn_index_existsb. unfold kn_bucket. rewrite pt_get_leaf. cbn [existsb]. rewrite Bool.orb_false_r.
  clear. induction live as [|K' live IH]; cbn [map existsb fst snd]; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Definition entails (cs : acs) (ch : acs) : bool :=
  (Z.eqb (pc cs) (pc ch)
   && match s_log (a_ss ch) with [] => true | _ => false end
   && list_eqb expr_eqb (s_regs (a_ss cs)) (s_regs (a_ss ch))
   && kn_sub_idx (kn cs) (kn ch)     (* [comment removed for export] *)
   && list_eqb amap_eqb (a_maps cs) (a_maps ch)
   && list_eqb pair_eqb (a_vis cs) (a_vis ch)
   && list_eqb pair_eqb (a_ghost cs) (a_ghost ch)
   && expr_eqb (a_brk cs) (a_brk ch)
   && afd_eqb (a_fd cs) (a_fd ch)
   && Bool.eqb (a_tidset cs) (a_tidset ch)
   && Z.leb (a_totsz cs) (a_totsz ch) && Z.leb (a_ylo ch) (a_ylo cs)
   && Z.leb (a_eager cs) (a_eager ch) && Z.leb (a_abytes cs) (a_abytes ch))%bool.

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint esubst (J : nat) (e : expr) (x : expr) : expr :=
  match x with
  | ELit _ => x
  | EVar n => if Nat.eqb n J then e else x
  | EAlu op a b => mkAlu op (esubst J e a) (esubst J e b)
  | EAluw op a b => mkAluw op (esubst J e a) (esubst J e b)
  | EMd op a b => mkMd op (esubst J e a) (esubst J e b)
  | EMdw op a b => mkMdw op (esubst J e a) (esubst J e b)
  | EExt sx lo n a => EExt sx lo n (esubst J e a)
  | EBlob _ _ _ _ => x
  end.
(* [comment removed for export] *)
Definition asubst (J : nat) (e : expr) (a : saddr) : saddr := SA (esubst J e (a_base a)) (a_off a).
Definition ksubst (J : nat) (e : expr) (K : kentry) : kentry :=
  match K with
  | KWord a w v => KWord (asubst J e a) w (esubst J e v)
  | KZero a n => KZero (asubst J e a) (esubst J e n)
  | KBlob a n k => KBlob (asubst J e a) (esubst J e n) k
  | KImg lo hi => K
  | KAlign x m => KAlign (esubst J e x) m
  | KRange x lo hi => KRange (esubst J e x) lo hi
  | KWr a n => KWr (asubst J e a) (esubst J e n)
  | KDisj a1 n1 a2 n2 => KDisj (asubst J e a1) (esubst J e n1) (asubst J e a2) (esubst J e n2)
  | KFill a n c => KFill (asubst J e a) (esubst J e n) c
  | KUnk a n => KUnk (asubst J e a) (esubst J e n)
  end.
Definition psubst (J : nat) (e : expr) (p : expr * expr) : expr * expr := (esubst J e (fst p), esubst J e (snd p)).
Definition msubst (J : nat) (e : expr) (m : amap) : amap := AM (esubst J e (am_base m)) (esubst J e (am_len m)) (am_kind m).
Definition fsubst (J : nat) (e : expr) (f : afd) : afd :=
  match f with FdFile k l o => FdFile k (esubst J e l) (esubst J e o) | _ => f end.
(* [comment removed for export] *)
Definition inst (inv : acs) (J : nat) (e : expr) : acs :=
  ACS (mk_ss (pc inv) (map (esubst J e) (s_regs (a_ss inv))) (map (ksubst J e) (kn inv)) (nxt inv))
      (map (msubst J e) (a_maps inv)) (a_totsz inv) (a_ylo inv) (a_eager inv)
      (map (psubst J e) (a_vis inv)) (map (psubst J e) (a_ghost inv)) (a_abytes inv)
      (esubst J e (a_brk inv)) (fsubst J e (a_fd inv)) (a_tidset inv).

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint nt_set (t : list (option nat)) (i : nat) (d : nat) {struct i} : list (option nat) :=
  match i, t with
  | O, [] => [Some d]
  | O, _ :: rest => Some d :: rest
  | S j, [] => None :: nt_set [] j d
  | S j, x :: rest => x :: nt_set rest j d
  end.
Definition nt_get (t : list (option nat)) (i : nat) : option nat := nth i t None.
Lemma nt_get_set : forall t i d j, nt_get (nt_set t i d) j = if Nat.eqb j i then Some d else nt_get t j.
Proof.
  unfold nt_get. intros t i. revert t. induction i as [|i IH]; intros t d j; destruct t as [|x rest]; destruct j as [|j]; cbn [nt_set nth Nat.eqb]; try reflexivity.
  - destruct j; reflexivity.
  - rewrite IH. destruct (Nat.eqb j i); destruct j; reflexivity.
  - apply IH.
Qed.
(* [comment removed for export] *)
Fixpoint mk_fwd (m : list (nat * nat)) : option (list (option nat)) :=
  match m with
  | [] => Some []
  | (s, d) :: rest =>
      match mk_fwd rest with
      | Some t => match nt_get t s with None => Some (nt_set t s d) | Some _ => None end
      | None => None
      end
  end.
(* [comment removed for export] *)
Fixpoint mk_bwd (m : list (nat * nat)) : option (list (option nat)) :=
  match m with
  | [] => Some []
  | (s, d) :: rest =>
      match mk_bwd rest with
      | Some t => match nt_get t d with None => Some (nt_set t d s) | Some _ => None end
      | None => None
      end
  end.

Fixpoint erename (t : list (option nat)) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | EVar v => match nt_get t v with Some d => EVar d | None => e end
  | EAlu op a b => EAlu op (erename t a) (erename t b)
  | EAluw op a b => EAluw op (erename t a) (erename t b)
  | EMd op a b => EMd op (erename t a) (erename t b)
  | EMdw op a b => EMdw op (erename t a) (erename t b)
  | EExt sx lo n a => EExt sx lo n (erename t a)
  | EBlob _ _ _ _ => e
  end.
Definition arename (t : list (option nat)) (a : saddr) : saddr := SA (erename t (a_base a)) (a_off a).
Definition krename (t : list (option nat)) (K : kentry) : kentry :=
  match K with
  | KWord a w v => KWord (arename t a) w (erename t v)
  | KZero a n => KZero (arename t a) (erename t n)
  | KBlob a n k => KBlob (arename t a) (erename t n) k
  | KImg lo hi => K
  | KAlign x m => KAlign (erename t x) m
  | KRange x lo hi => KRange (erename t x) lo hi
  | KWr a n => KWr (arename t a) (erename t n)
  | KDisj a1 n1 a2 n2 => KDisj (arename t a1) (erename t n1) (arename t a2) (erename t n2)
  | KFill a n c => KFill (arename t a) (erename t n) c
  | KUnk a n => KUnk (arename t a) (erename t n)
  end.
Definition prename (t : list (option nat)) (p : expr * expr) : expr * expr := (erename t (fst p), erename t (snd p)).
Definition mrename (t : list (option nat)) (m : amap) : amap := AM (erename t (am_base m)) (erename t (am_len m)) (am_kind m).
Definition frename (t : list (option nat)) (f : afd) : afd :=
  match f with FdFile k l o => FdFile k (erename t l) (erename t o) | _ => f end.

(* [comment removed for export] *)
Fixpoint evars_all (ok : nat -> bool) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar v => ok v
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evars_all ok a && evars_all ok b
  | EExt _ _ _ a => evars_all ok a
  | EBlob _ _ _ _ => true
  end.
Definition kvars_all (ok : nat -> bool) (K : kentry) : bool :=
  match K with
  | KWord a _ v => evars_all ok (a_base a) && evars_all ok v
  | KZero a n | KBlob a n _ | KWr a n | KFill a n _ | KUnk a n => evars_all ok (a_base a) && evars_all ok n
  | KImg _ _ => true
  | KAlign x _ | KRange x _ _ => evars_all ok x
  | KDisj a1 n1 a2 n2 => evars_all ok (a_base a1) && evars_all ok n1 && evars_all ok (a_base a2) && evars_all ok n2
  end%bool.
Definition csvars_all (ok : nat -> bool) (cs : acs) : bool :=
  (forallb (evars_all ok) (s_regs (a_ss cs)) && forallb (kvars_all ok) (kn cs)
   && forallb (fun m => evars_all ok (am_base m) && evars_all ok (am_len m)) (a_maps cs)
   && forallb (fun p => evars_all ok (fst p) && evars_all ok (snd p)) (a_vis cs)
   && forallb (fun p => evars_all ok (fst p) && evars_all ok (snd p)) (a_ghost cs)
   && evars_all ok (a_brk cs)
   && match a_fd cs with FdFile _ l o => evars_all ok l && evars_all ok o | _ => true end)%bool.

(* [comment removed for export] *)
Fixpoint emaxv (e : expr) (acc : nat) : nat :=
  match e with
  | ELit _ => acc
  | EVar v => Nat.max acc (S v)
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => emaxv a (emaxv b acc)
  | EExt _ _ _ a => emaxv a acc
  | EBlob _ _ _ _ => acc
  end.
Definition kmaxv (K : kentry) (acc : nat) : nat :=
  match K with
  | KWord a _ v => emaxv (a_base a) (emaxv v acc)
  | KZero a n | KBlob a n _ | KWr a n | KFill a n _ | KUnk a n => emaxv (a_base a) (emaxv n acc)
  | KImg _ _ => acc
  | KAlign x _ | KRange x _ _ => emaxv x acc
  | KDisj a1 n1 a2 n2 => emaxv (a_base a1) (emaxv n1 (emaxv (a_base a2) (emaxv n2 acc)))
  end.
Definition csmaxv (cs : acs) : nat :=
  let acc := fold_right emaxv 0%nat (s_regs (a_ss cs)) in
  let acc := fold_right kmaxv acc (kn cs) in
  let acc := fold_right (fun m acc => emaxv (am_base m) (emaxv (am_len m) acc)) acc (a_maps cs) in
  let acc := fold_right (fun p acc => emaxv (fst p) (emaxv (snd p) acc)) acc (a_vis cs) in
  let acc := fold_right (fun p acc => emaxv (fst p) (emaxv (snd p) acc)) acc (a_ghost cs) in
  let acc := match a_fd cs with FdFile _ l o => emaxv l (emaxv o acc) | _ => acc end in
  emaxv (a_brk cs) acc.

Definition rename_cs (t : list (option nat)) (cs : acs) (nx : nat) : acs :=
  ACS (mk_ss (pc cs) (map (erename t) (s_regs (a_ss cs))) (map (krename t) (kn cs)) nx)
      (map (mrename t) (a_maps cs)) (a_totsz cs) (a_ylo cs) (a_eager cs)
      (map (prename t) (a_vis cs)) (map (prename t) (a_ghost cs)) (a_abytes cs)
      (erename t (a_brk cs)) (frename t (a_fd cs)) (a_tidset cs).

(* [comment removed for export] *)
Definition node_rename (gb : nat) (cs : acs) (m : list (nat * nat)) : option acs :=
  if forallb (fun p => Nat.leb gb (fst p) && Nat.leb gb (snd p)) m then
    match mk_fwd m, mk_bwd m with
    | Some fw, Some bw =>
        let ok (v : nat) := match nt_get fw v with Some _ => true | None => match nt_get bw v with Some _ => false | None => true end end in
        if (csvars_all ok cs && match s_log (a_ss cs) with [] => true | _ => false end)%bool then
          let cs1 := rename_cs fw cs 0%nat in
          Some (with_ss cs1 (mk_ss (pc cs1) (s_regs (a_ss cs1)) (kn cs1) (Nat.max gb (csmaxv cs1))))
        else None
    | _, _ => None
    end
  else None.

(* [comment removed for export] *)
Fixpoint bt_set (t : list bool) (i : nat) {struct i} : list bool :=
  match i, t with
  | O, [] => [true]
  | O, _ :: rest => true :: rest
  | S j, [] => false :: bt_set [] j
  | S j, x :: rest => x :: bt_set rest j
  end.
Definition bt_get (t : list bool) (i : nat) : bool := nth i t false.
(* [comment removed for export] *)
Fixpoint evars_fo (gb : nat) (e : expr) (acc : list nat * list bool) : list nat * list bool :=
  match e with
  | ELit _ => acc
  | EVar v => if Nat.ltb v gb then acc else if bt_get (snd acc) v then acc else (v :: fst acc, bt_set (snd acc) v)
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evars_fo gb b (evars_fo gb a acc)
  | EExt _ _ _ a => evars_fo gb a acc
  | EBlob _ _ _ _ => acc
  end.
Definition kvars_fo (gb : nat) (K : kentry) (acc : list nat * list bool) : list nat * list bool :=
  match K with
  | KWord a _ v => evars_fo gb v (evars_fo gb (a_base a) acc)
  | KZero a n | KBlob a n _ | KWr a n | KFill a n _ | KUnk a n => evars_fo gb n (evars_fo gb (a_base a) acc)
  | KImg _ _ => acc
  | KAlign x _ | KRange x _ _ => evars_fo gb x acc
  | KDisj a1 n1 a2 n2 => evars_fo gb n2 (evars_fo gb (a_base a2) (evars_fo gb n1 (evars_fo gb (a_base a1) acc)))
  end.
Definition csvars_fo (gb : nat) (cs : acs) : list nat :=
  let acc := fold_left (fun acc e => evars_fo gb e acc) (s_regs (a_ss cs)) ([], []) in
  let acc := fold_left (fun acc K => kvars_fo gb K acc) (kn cs) acc in
  let acc := fold_left (fun acc m => evars_fo gb (am_len m) (evars_fo gb (am_base m) acc)) (a_maps cs) acc in
  let acc := fold_left (fun acc p => evars_fo gb (snd p) (evars_fo gb (fst p) acc)) (a_vis cs) acc in
  let acc := fold_left (fun acc p => evars_fo gb (snd p) (evars_fo gb (fst p) acc)) (a_ghost cs) acc in
  let acc := match a_fd cs with FdFile _ l o => evars_fo gb o (evars_fo gb l acc) | _ => acc end in
  let acc := evars_fo gb (a_brk cs) acc in
  rev (fst acc).
Fixpoint number_from (i : nat) (l : list nat) : list (nat * nat) :=
  match l with [] => [] | v :: rest => (v, i) :: number_from (S i) rest end.
Definition compact_map (gb : nat) (cs : acs) : list (nat * nat) := number_from gb (csvars_fo gb cs).
Definition node_compact (gb : nat) (cs : acs) : option acs := node_rename gb cs (compact_map gb cs).

(* [comment removed for export] *)
Fixpoint regs_match_h (lo hi : nat) (seen : list nat) (rs ts : list expr) : bool :=
  match rs, ts with
  | [], [] => true
  | r :: rs', t :: ts' =>
      match t with
      | EVar v => if (Nat.leb lo v && Nat.ltb v hi)%bool
                  then (negb (existsb (Nat.eqb v) seen) && regs_match_h lo hi (v :: seen) rs' ts')%bool
                  else (expr_eqb r t && expr_vars_lt lo t && regs_match_h lo hi seen rs' ts')%bool
      | _ => (expr_eqb r t && expr_vars_lt lo t && regs_match_h lo hi seen rs' ts')%bool
      end
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition saddr_eqb_h (x y : saddr) : bool :=
  saddr_eqb x y || expr_eqb (eaddz (a_base x) (a_off x)) (eaddz (a_base y) (a_off y)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint cover1 (k : list kentry) (b : expr) (i : Z) : option Z :=
  match k with
  | [] => None
  | K :: rest =>
      let hit := match K with
                 | KWord (SA kb kk) w _ =>
                     if (expr_eqb b kb && Z.leb kk i && Z.ltb i (kk + Z.of_nat w))%bool then Some (kk + Z.of_nat w) else None
                 | KZero (SA kb kk) (ELit l) | KFill (SA kb kk) (ELit l) _ | KBlob (SA kb kk) (ELit l) _ | KUnk (SA kb kk) (ELit l) =>
                     if (expr_eqb b kb && Z.leb 0 l && Z.ltb l two64 && Z.leb kk i && Z.ltb i (kk + l))%bool then Some (kk + l) else None
                 | _ => None
                 end in
      match hit with Some e => Some e | None => cover1 rest b i end
  end.
Fixpoint cover_x (fuel : nat) (k : list kentry) (b : expr) (i : Z) (stop : Z) : bool :=
  match fuel with
  | O => false
  | S f => if Z.leb stop i then true else
           match cover1 k b i with
           | Some e => if Z.ltb i e then cover_x f k b e stop else false
           | None => false
           end
  end.
(* [comment removed for export] *)
Definition kunk_covered (k : list kentry) (K : kentry) : bool :=
  match K with
  | KUnk (SA b o) (ELit n) =>
      (Z.ltb 0 n && Z.leb n (2 ^ 40) && Z.leb (img_lo A) (img_hi A) && flat_x k b o (ELit n) && off_image_x k b o (ELit n) && cover_x (S (length k)) k b o (o + n))%bool
  | _ => false
  end.

Definition kentry_eqb_h (x y : kentry) : bool :=
  kentry_eqb x y ||
  match x, y with
  | KWord a w v, KWord a' w' v' => saddr_eqb_h a a' && Nat.eqb w w' && expr_eqb v v'
  | KZero a n, KZero a' n' => saddr_eqb_h a a' && expr_eqb n n'
  | KBlob a n k, KBlob a' n' k' => saddr_eqb_h a a' && expr_eqb n n' && Nat.eqb k k'
  | KWr a n, KWr a' n' => saddr_eqb_h a a' && expr_eqb n n'
  | KFill a n c, KFill a' n' c' => saddr_eqb_h a a' && expr_eqb n n' && Z.eqb c c'
  | KUnk a n, KUnk a' n' => saddr_eqb_h a a' && expr_eqb n n'
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition kflat_h (k : list kentry) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w _ => flat_x k b o (ELit (Z.of_nat w))
  | KZero (SA b o) n | KBlob (SA b o) n _ | KWr (SA b o) n | KFill (SA b o) n _ | KUnk (SA b o) n => flat_x k b o n
  | _ => true
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kimg_sub_covered (k : list kentry) (K : kentry) : bool :=
  match K with
  | KImg lo hi => existsb (fun X => match X with KImg lo' hi' => Z.leb lo' lo && Z.leb hi hi' | _ => false end) k
  | _ => false
  end.
Definition kn_incl1_h (k : list kentry) (K : kentry) : bool :=
  if existsb (fun X => kentry_eqb X K) k then true
  else if (if kflat_h k K then existsb (fun X => kentry_eqb_h X K) k else false) then true
  else if kimg_sub_covered k K then true
  else kunk_covered k K.
Definition kn_incl_h (k : list kentry) (tk : list kentry) : bool := forallb (kn_incl1_h k) tk.

Definition entails_h (lo hi : nat) (cs : acs) (ch : acs) : bool :=
  (Z.eqb (pc cs) (pc ch)
   && match s_log (a_ss ch) with [] => true | _ => false end
   && match s_resv (a_ss ch) with None => true | _ => false end
   && regs_match_h lo hi [] (s_regs (a_ss cs)) (s_regs (a_ss ch))
   && kn_incl_h (kn cs) (kn ch)
   && kn_vars_lt lo (kn ch) && maps_vars_lt lo (a_maps ch) && pairs_vars_lt lo (a_vis ch) && pairs_vars_lt lo (a_ghost ch)
   && expr_vars_lt lo (a_brk ch) && fd_vars_lt lo (a_fd ch)
   && list_eqb amap_eqb (a_maps cs) (a_maps ch)
   && list_eqb pair_eqb (a_vis cs) (a_vis ch)
   && list_eqb pair_eqb (a_ghost cs) (a_ghost ch)
   && expr_eqb (a_brk cs) (a_brk ch)
   && afd_eqb (a_fd cs) (a_fd ch)
   && Bool.eqb (a_tidset cs) (a_tidset ch)
   && Z.leb (a_totsz cs) (a_totsz ch) && Z.leb (a_ylo ch) (a_ylo cs)
   && Z.leb (a_eager cs) (a_eager ch) && Z.leb (a_abytes cs) (a_abytes ch))%bool.

(* [comment removed for export] *)
Inductive loopctx : Type :=
| LC (lc_head : Z) (lc_next : acs) (lc_lo lc_hi : nat)
| JC (jc_id : nat) (jc_st : acs) (jc_sh : shape) (jc_b jc_lo : nat).
Definition lc_bnd (c : loopctx) : nat := match c with LC _ _ _ hi => hi | JC _ _ _ b _ => b end.

(* [comment removed for export] *)
Definition loop_ok (cs0 : acs) (J : nat) (N : expr) (inv : acs) : option Z :=
  let lo := S J in let hi := nxt inv in
  if (fresh_ok cs0 && Nat.leb (nxt cs0) J && Nat.ltb J hi && fresh_ok inv
      && expr_vars_lt (nxt cs0) N
      && match s_log (a_ss inv) with [] => true | _ => false end
      && Nat.eqb (length (s_regs (a_ss inv))) 32
      && kn_vars_lt lo (kn inv) && maps_vars_lt lo (a_maps inv) && pairs_vars_lt lo (a_vis inv) && pairs_vars_lt lo (a_ghost inv)
      && expr_vars_lt lo (a_brk inv) && fd_vars_lt lo (a_fd inv)
      && forallb (fun r => match r with EVar v => true | _ => expr_vars_lt lo r end) (s_regs (a_ss inv))
      && regs_match_h lo hi [] (s_regs (a_ss inv)) (s_regs (a_ss inv)))%bool
  then match xhi (kn cs0) N with Some nhi => if Z.ltb nhi two64 then Some nhi else None | None => None end
  else None.

(* [comment removed for export] *)
Definition loop_body_state (J : nat) (N : expr) (nhi : Z) (inv : acs) : acs :=
  add_kn inv [KRange (EVar J) 0 (nhi - 1); KRange (esub N (EVar J)) 1 nhi].

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition branch_probe (cs : acs) : option expr :=
  match itab_lookup IT (pc cs) with
  | Some (Branch c rs1 rs2 _) =>
      Some (fst (cond_probe c (sr_get (s_regs (a_ss cs)) rs1) (sr_get (s_regs (a_ss cs)) rs2)))
  | _ => None
  end.

(* [comment removed for export] *)
Fixpoint diff_regs (i : nat) (ra rb : list expr) : list nat :=
  match ra, rb with
  | a :: ra', b :: rb' => if expr_eqb a b then diff_regs (S i) ra' rb' else i :: diff_regs (S i) ra' rb'
  | _, _ => []
  end.

(* [comment removed for export] *)
Definition node_diamond_join (nx : nat) (joinpc : Z) (rs : list nat) (ca cb : acs) : option acs :=
  let hv := nodup Nat.eq_dec (diff_regs 0 (s_regs (a_ss ca)) (s_regs (a_ss cb)) ++ rs) in
  let v0 := Nat.max nx (Nat.max (nxt ca) (nxt cb)) in
  let hi := (v0 + length hv)%nat in
  let regsJ := sr_fresh (s_regs (a_ss ca)) hv v0 in
  let knJ := List.filter (fun K => existsb (fun X => kentry_eqb X K) (kn cb)) (kn ca) in
  let csJ := with_ss ca (mk_ss joinpc regsJ knJ hi) in
  if (Z.eqb (pc ca) joinpc && Z.eqb (pc cb) joinpc
      && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) hv
      && Nat.eqb (length regsJ) 32
      && Nat.leb nx0 v0
      && entails_h v0 hi ca csJ && entails_h v0 hi cb csJ)%bool
  then Some csJ else None.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition via_ok (cs js : acs) (lo : nat) : bool :=
  (match s_log (a_ss js) with [] => true | _ => false end
   && Nat.eqb (length (s_regs (a_ss js))) 32
   && Nat.leb nx0 (nxt cs) && Nat.leb (nxt cs) lo && Nat.leb lo (nxt js))%bool.

(* [comment removed for export] *)
Definition node_abstractcell (cs : acs) (b : expr) (n : Z) : option acs :=
  let '(bb, bo) := split_lit b in
  let K := KUnk (SA bb bo) (ELit n) in
  if kunk_covered (kn cs) K then Some (set_kn cs (K :: kn_cutout (kn cs) bb bo (ELit n))) else None.

(* [comment removed for export] *)
Definition respell_ok (k : list kentry) (a e : expr) : bool :=
  match decide_branch k BC_EQ a e with
  | Some true => true
  | _ => (* [comment removed for export] *)
      match erange k (mkAlu ALU_SUB a e) with
      | Some (lo, hi) => Z.eqb lo 0 && Z.eqb hi 0
      | None => false
      end
  end.
Definition node_respell (cs : acs) (r : nat) (e : expr) : option acs :=
  if (Nat.ltb 0 r && Nat.ltb r 32 && expr_vars_lt (nxt cs) e && respell_ok (kn cs) (reg cs r) e)%bool
  then Some (set_reg cs r e) else None.

(* [comment removed for export] *)
Definition sa_of (b : expr) : saddr := let '(bb, bo) := split_lit b in SA bb bo.
Fixpoint hw_apply (k : list kentry) (a : saddr) (x : nat) (found : bool) : list kentry :=
  match k with
  | [] => []
  | KWord a' w v :: r =>
      if saddr_eqb a' a then (if found then hw_apply r a x true else KWord a' w (EVar x) :: hw_apply r a x true)
      else KWord a' w v :: hw_apply r a x found
  | K :: r => K :: hw_apply r a x found
  end.
(* [comment removed for export] *)
Fixpoint hw_val (k : list kentry) (a : saddr) : expr :=
  match k with
  | [] => ELit 0
  | KWord a' _ v :: r => if saddr_eqb a' a then v else hw_val r a
  | _ :: r => hw_val r a
  end.
Fixpoint hw_go (k : list kentry) (bs : list expr) (x : nat) : list kentry :=
  match bs with
  | [] => k
  | b :: r => hw_go (hw_apply k (sa_of b) x false) r (S x)
  end.
Definition node_havocwords (cs : acs) (bs : list expr) : option acs :=
  if fresh_ok cs then
    let ss := a_ss cs in
    Some (with_ss cs (mk_ss (s_pc ss) (s_regs ss) (hw_go (s_know ss) bs (s_next ss)) (s_next ss + length bs)))
  else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition STOPS : list Z :=
  [x_imemset A; x_imemcpy A; x_memset A; x_memcpy A; x_memiszero A; x_envscan A; x_pnscan A] ++ stops_more A.

(* [comment removed for export] *)
Fixpoint mk_itab_ranges_acc (rs : list (Z * nat)) (t : itab) : itab :=
  match rs with
  | [] => t
  | (lo, n) :: rs' => mk_itab_ranges_acc rs' (mk_itab_fuel segs n lo t)
  end.
Definition mk_itab_ranges (rs : list (Z * nat)) : itab := mk_itab_ranges_acc rs PTLeaf.

End WithSegs.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition BRK_ASLR : Z := 0x80000000.

(* [comment removed for export] *)
Definition K_RND : nat := 25.

(* [comment removed for export] *)
Definition e_auxb : expr * Z := split_lit e_auxv.
Definition e_atrb : expr * Z := split_lit e_atrandom.
Definition auxw (i : Z) (ty : Z) (v : expr) : list kentry :=
  [KWord (SA (fst e_auxb) (snd e_auxb + 16 * i)) 8 (ELit ty); KWord (SA (fst e_auxb) (snd e_auxb + 16 * i + 8)) 8 v].

(* [comment removed for export] *)
Definition init_kn_with (atr : kentry) (A : atable) : list kentry :=
  [KRange (EVar V_S1) 0xFFFF0000 0xFFFFFFFF; KRange (EVar V_S2) 0 255; KRange (EVar V_SP) 0 7;   (* [comment removed for export] *)
   KRange (eaddz e_atrandom 16) 0x7fff800000c0 0x800000000000; KRange e_atr8 0xFFFF0000001 0xFFFFFFFFFE7;   (* [comment removed for export] *)
   KRange e_sp0 0x7fff80000000 0x7fffffffff40; KRange e_pd 0x7fff80000000 0x7ffffffff000;                 (* [comment removed for export] *)
   KRange (eadd (escale 4096 (EVar V_S1)) (eadd (escale 2 (EVar V_S2)) (escale 512 (EVar V_SP)))) 0xFFFF0000000 0xFFFFFFFFFE8;
   KRange (EVar V_ARGC) 1 1024; KRange (EVar V_ENVC) 0 256; KRange (EVar V_L0) 0 131071; KRange (EVar V_L1) 0 131071;
   KRange (EVar V_UID) 0 0xFFFFFFFE; KRange (EVar V_HW) 0 0x3FFFFF;
   KRange (EVar V_W) 0 280000; KRange (EVar V_BRK) (img_hi A / 4096) ((img_hi A + BRK_ASLR) / 4096);
   KWr (SA e_sp0 (-8388608)) (ELit 8388608); KZero (SA e_sp0 (-8388608)) (ELit 8388608);
   KWord (SA e_sp0 0) 8 (EVar V_ARGC); KWord (SA e_sp0 8) 8 e_str0; kw_argv1 e_argv1w]
  (* [comment removed for export] *)
  ++ auxw 0 3 (ELit (ph_addr_z A)) ++ auxw 1 4 (ELit (ph_ent_z A)) ++ auxw 2 5 (ELit (ph_num_z A)) ++ auxw 3 16 (EVar V_HW) ++ auxw 4 6 (ELit 4096)
  ++ auxw 5 11 (EVar V_UID) ++ auxw 6 12 (EVar V_UID) ++ auxw 7 23 (ELit 0) ++ auxw 8 25 e_atrandom ++ auxw 9 0 (ELit 0)
  ++ [atr;
      KImg (img_lo A) (img_hi A); KWr (SA (ELit 0) (rw_lo A)) (ELit (rw_len A))].

(* [comment removed for export] *)
Definition atr_entry : kentry := KBlob (SA (fst e_atrb) (snd e_atrb)) (ELit 16) K_RND.
Definition atr_entry_zero : kentry := KZero (SA (fst e_atrb) (snd e_atrb)) (ELit 16).
(* [comment removed for export] *)
Definition init_kn (A : atable) : list kentry := init_kn_with atr_entry A.
(* [comment removed for export] *)
Definition init_kn_zero (A : atable) : list kentry := init_kn_with atr_entry_zero A.

Definition init_regs : list expr := sr_upd (repeat (ELit 0) 32) 2 e_sp0.
(* [comment removed for export] *)
Definition e_stkwlen : expr := esub (ELit STK_WTOP) e_pd.
Definition init_vis (A : atable) : list (expr * expr) :=
  [(ELit (img_lo A), ELit (img_hi A - img_lo A)); (eaddz e_pd STK_OFF, e_stkwlen)].

Definition init_acs_of_with (kn0 : list kentry) (A : atable) : acs :=
  ACS (mk_ss (a_entry A) init_regs kn0 NX0) [] (img_hi A - img_lo A) MBASE_MIN 0 (init_vis A) []
      (vis_cost (img_hi A - img_lo A) + vis_cost STK_WMAX) (escale 4096 (EVar V_BRK)) FdStd false.
Definition init_acs_of (A : atable) : acs := init_acs_of_with (init_kn A) A.        (* [comment removed for export] *)
Definition init_acs_of_zero (A : atable) : acs := init_acs_of_with (init_kn_zero A) A.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASAN : atable :=
  (* [comment removed for export] *)
  {| img_lo := 0x10000; img_hi := 0x5ff000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x30cb0; rw_lo := 0xa1000; rw_len := 0x55e000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x65814; x_imemcpy := 0x65798; x_memset := 0x9b5f4; x_memcpy := 0x9b1f0; x_memiszero := 0x65d60;
     x_istrncpy := 0x65c40; x_sealed := 0x11854; x_popfree := 0x372a8;
     x_maxva := 0x66e78;
     x_envscan := 0x8d834; x_envscan_k := 0x8d840; x_pnscan := 0x8d8f8; x_pnscan_k := 0x8d904;
     stops_more := [0x34f1c; 0x36540; 0x55b20; 0x5bed8; 0x5beec; 0x5bf00; 0x61890; 0x61960; 0x6eea8; 0x6fdb4; 0x6ff44; 0x79c9c; 0x700b4] |}.

(* [comment removed for export] *)
Definition ASAN_TEXT_LO : Z := 0x30cb0.
Definition ASAN_TEXT_N : nat := 114486.
Definition asan_init : acs := init_acs_of ASAN.

(* [comment removed for export] *)
Definition BOTH : atable :=
  {| img_lo := 0x10000; img_hi := 0x5ff000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x30cdc; rw_lo := 0xa1000; rw_len := 0x55e000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x65840; x_imemcpy := 0x657c4; x_memset := 0x9ad74; x_memcpy := 0x9a970; x_memiszero := 0x65d8c;
     x_istrncpy := 0x65c6c; x_sealed := 0x11874; x_popfree := 0x372d4;
     x_maxva := 0x66ea4;
     x_envscan := 0x8cfb4; x_envscan_k := 0x8cfc0; x_pnscan := 0x8d078; x_pnscan_k := 0x8d084;
     stops_more := [0x34f48; 0x3656c; 0x55b4c; 0x5bf04; 0x5bf18; 0x5bf2c; 0x618bc; 0x6198c; 0x6eed4; 0x6fde0; 0x6ff70; 0x79cc8; 0x700e0] |}.
Definition BOTH_TEXT_LO : Z := 0x30cdc.
Definition BOTH_TEXT_N : nat := 113931.
Definition both_init : acs := init_acs_of BOTH.

End APC.
