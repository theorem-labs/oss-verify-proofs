(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec AxSymExec3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Module AX2B.
Import AX2.
Create HintDb bceq discriminated.

(* [comment removed for export] *)
Definition bv_signedF {n} (b : bv n) : Z :=
  let u := bv_unsigned b in
  match n with
  | 12%N => if Z.ltb u 2048 then u else (u - 4096)%Z
  | 13%N => if Z.ltb u 4096 then u else (u - 8192)%Z
  | 20%N => if Z.ltb u 524288 then u else (u - 1048576)%Z
  | 21%N => if Z.ltb u 1048576 then u else (u - 2097152)%Z
  | _ => bv_signed b
  end.
Lemma bv_signed_small : forall n (b : bv n) h, bv_half_modulus n = h -> bv_modulus n = (2 * h)%Z ->
  bv_signed b = if Z.ltb (bv_unsigned b) h then bv_unsigned b else (bv_unsigned b - 2 * h)%Z.
Proof.
  intros n b h Hh Hm. pose proof (bv_unsigned_in_range _ b) as H. rewrite Hm in H.
  unfold bv_signed, bv_swrap, bv_wrap. rewrite Hh, Hm.
  destruct (Z.ltb (bv_unsigned b) h) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E].
  - rewrite Z.mod_small by lia. lia.
  - replace (bv_unsigned b + h)%Z with ((bv_unsigned b - h) + 1 * (2 * h))%Z by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.
Lemma bv_signedF_eq : forall n (b : bv n), bv_signedF b = bv_signed b.
Proof.
  intros n b. unfold bv_signedF.
  destruct (N.eq_dec n 12) as [->|N12]; [symmetry; apply (bv_signed_small 12 b 2048); reflexivity|].
  destruct (N.eq_dec n 13) as [->|N13]; [symmetry; apply (bv_signed_small 13 b 4096); reflexivity|].
  destruct (N.eq_dec n 20) as [->|N20]; [symmetry; apply (bv_signed_small 20 b 524288); reflexivity|].
  destruct (N.eq_dec n 21) as [->|N21]; [symmetry; apply (bv_signed_small 21 b 1048576); reflexivity|].
  destruct n as [|p]; [reflexivity|].
  repeat (destruct p as [p|p|]; try reflexivity; try (exfalso; first [apply N12; reflexivity|apply N13; reflexivity|apply N20; reflexivity|apply N21; reflexivity])).
Qed.
(* [comment removed for export] *)
Definition bvu64 (z : Z) : Z := zmod64 z.
Lemma bvu64_eq : forall z, bvu64 z = bv_unsigned (Z_to_bv 64 z).
Proof. intros z. unfold bvu64. rewrite zmod64_eq, Z_to_bv_unsigned. reflexivity. Qed.
(* [comment removed for export] *)
Lemma bv_signedF_eqf : @bv_signedF = @bv_signed.
Proof. apply functional_extensionality_dep; intros n. apply functional_extensionality; intros b. apply bv_signedF_eq. Qed.
Lemma bvu64_eqf : bvu64 = (fun z => bv_unsigned (Z_to_bv 64 z)).
Proof. apply functional_extensionality; intros z. apply bvu64_eq. Qed.
#[export] Hint Rewrite bv_signedF_eqf bvu64_eqf : bceq.
(* [comment removed for export] *)
Definition sg64 (a : Z) : Z := if Z.ltb a 9223372036854775808 then a else (a - 18446744073709551616)%Z.
Definition lit_branchF (c : branch_cond) (x y : Z) : bool :=
  let a := zmod64 x in let b := zmod64 y in
  match c with
  | BC_EQ => Z.eqb a b
  | BC_NE => negb (Z.eqb a b)
  | BC_LT => Z.ltb (sg64 a) (sg64 b)
  | BC_GE => negb (Z.ltb (sg64 a) (sg64 b))
  | BC_LTU => Z.ltb a b
  | BC_GEU => negb (Z.ltb a b)
  end.
Lemma bvu_zmod64 : forall z, bv_unsigned (Z_to_bv 64 z) = zmod64 z.
Proof. intros z. rewrite zmod64_eq, Z_to_bv_unsigned. reflexivity. Qed.
Lemma bvs_sg64 : forall z, bv_signed (Z_to_bv 64 z) = sg64 (zmod64 z).
Proof.
  intros z. rewrite (bv_signed_small 64 (Z_to_bv 64 z) 9223372036854775808 eq_refl eq_refl), bvu_zmod64. reflexivity.
Qed.
Lemma lit_branchF_eq : forall c x y, lit_branchF c x y = lit_branch c x y.
Proof.
  intros c x y. unfold lit_branchF, lit_branch, branch_taken, bv_eqb, bv_ltu, bv_lts.
  rewrite ?bvs_sg64, ?bvu_zmod64. destruct c; reflexivity.
Qed.
Lemma lit_branchF_eqf : lit_branchF = lit_branch.
Proof. apply functional_extensionality; intros c. apply functional_extensionality; intros x. apply functional_extensionality; intros y. apply lit_branchF_eq. Qed.
#[export] Hint Rewrite lit_branchF_eqf : bceq.
(* [comment removed for export] *)
Definition jalrF (z i : Z) : Z := zmod64 (Z.land (zmod64 z + i) (-2)).
Lemma jalrF_eqf : jalrF = (fun z i => (Z.land (bv_wrap 64 z + i) (-2) mod 2^64)%Z).
Proof.
  apply functional_extensionality; intros z. apply functional_extensionality; intros i.
  unfold jalrF. rewrite !zmod64_eq. reflexivity.
Qed.
#[export] Hint Rewrite jalrF_eqf : bceq.
(* [comment removed for export] *)
Definition ext_lim (sx : bool) (n : nat) : Z :=
  match n with
  | 1%nat => if sx then 128 else 256
  | 2%nat => if sx then 32768 else 65536
  | 4%nat => if sx then 2147483648 else 4294967296
  | _ => if sx then (2 ^ (8 * Z.of_nat n) / 2)%Z else (2 ^ (8 * Z.of_nat n))%Z
  end.
Lemma ext_lim_eqf : ext_lim = (fun sx n => if sx then (2 ^ (8 * Z.of_nat n) / 2)%Z else (2 ^ (8 * Z.of_nat n))%Z).
Proof.
  apply functional_extensionality; intros sx. apply functional_extensionality; intros n.
  destruct n as [|[|[|[|[|n]]]]]; destruct sx; reflexivity.
Qed.
#[export] Hint Rewrite ext_lim_eqf : bceq.

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

(* [comment removed for export] *)
Definition is_kdisj (K : kentry) : bool := match K with KDisj _ _ _ _ => true | _ => false end.
Definition kdisj_of (kn : list kentry) : list kentry := List.filter is_kdisj kn.
Lemma kdisj_apart_kdisj_of : forall allkn kn, kdisj_apart allkn (kdisj_of kn) = kdisj_apart allkn kn.
Proof.
  intros allkn kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1.
  apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2.
  induction kn as [|K rest IH]; [reflexivity|]. unfold kdisj_of. cbn [List.filter is_kdisj].
  destruct K; cbn [kdisj_apart]; rewrite <- IH; reflexivity.
Qed.
Lemma kdisj_apart_x_kdisj_of : forall allkn kn, kdisj_apart_x allkn (kdisj_of kn) = kdisj_apart_x allkn kn.
Proof.
  intros allkn kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1.
  apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2.
  induction kn as [|K rest IH]; [reflexivity|]. unfold kdisj_of. cbn [List.filter is_kdisj].
  destruct K; cbn [kdisj_apart_x]; rewrite <- IH; reflexivity.
Qed.

Record bctx : Type := BC {
  bc_fk : list kentry;      (* [comment removed for export] *)
  bc_ffk : list kentry;     (* [comment removed for export] *)
  bc_kd : list kentry;      (* [comment removed for export] *)
  bc_fs : list sfact;       (* [comment removed for export] *)
  bc_ri : rindex;           (* [comment removed for export] *)
  bc_rl : list ((Z * list fterm * list fterm) * (Z * Z));  (* [comment removed for export] *)
  bc_brt : list (expr * option (Z * Z))  (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition mkbc0 (fk : list kentry) (fs : list sfact) (tbl : list (expr * option (Z * Z))) : bctx :=
  BC fk (facts_of fk) (kdisj_of fk) fs (mk_ri (facts_of fk)) (mk_rl (facts_of fk)) tbl.
(* [comment removed for export] *)
Fixpoint brt_lookup (t : list (expr * option (Z * Z))) (e : expr) : option (option (Z * Z)) :=
  match t with
  | [] => None
  | (b, r) :: rest => if expr_eqb e b then Some r else brt_lookup rest e
  end.
(* [comment removed for export] *)
Definition BRT_OK (fk : list kentry) (t : list (expr * option (Z * Z))) : Prop :=
  forall e r, brt_lookup t e = Some r -> base_range fk e = r.

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
         else isect_opt (find_range_linc (bc_rl bc) (fst l) (snd l))      (* [comment removed for export] *)
              (match lin_range (erange bc) (fst l) (snd l) with
              | Some (lo, hi) =>
                  (* [comment removed for export] *)
                  let q := zdiv64 lo in   (* [comment removed for export] *)
                  if Z.eqb q (zdiv64 hi) then Some ((lo - q * two64)%Z, (hi - q * two64)%Z) else None
              | None => None
              end)) with
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
          | None, Some s => Some (0%Z, (two64 / 2 ^ s - 1)%Z)
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
              if Z.ltb (ah * 2 ^ s') (2 ^ 31) then Some ((al * 2 ^ s')%Z, (ah * 2 ^ s')%Z)
              else if (Z.ltb ah two64 && Z.leb ((two64 - al) * 2 ^ s') (2 ^ 31))%bool
              then Some ((two64 - (two64 - al) * 2 ^ s')%Z, (two64 - (two64 - ah) * 2 ^ s')%Z)
              else None
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
              then Some ((al * bl)%Z, (ah * bh)%Z)
              else if (Z.eqb al ah && Z.leb 0 al && Z.leb 0 bl && Z.leb bl bh && Z.eqb (al * bl / two64) (al * bh / two64))%bool
              then Some ((al * bl - (al * bl / two64) * two64)%Z, (al * bh - (al * bl / two64) * two64)%Z)
              else None
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

(* [comment removed for export] *)
Definition base_rangeB (bc : bctx) (e : expr) : option (Z * Z) :=
  match e with
  | ELit z => let v := zmod64 z in Some (v, v)
  | _ => match brt_lookup (bc_brt bc) e with Some r => r | None => erangeB bc e end
  end.

Definition ealignB (bc : bctx) (e : expr) : Z := Z.max (ealign0 (bc_ffk bc) e) (pageup_align e).

Definition lin_nowrapB (bc : bctx) (e : expr) : bool :=
  let l := lin_of e in
  match lin_range (erangeB bc) (fst l) (snd l) with
  | Some (lo, hi) => if (Z.leb 0 lo && Z.ltb hi two64)%bool then true else nowrap_by_fact (bc_ffk bc) (fst l) (snd l) lo hi
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
Lemma bc_fk_mkbc0 : forall fk fs tbl, bc_fk (mkbc0 fk fs tbl) = fk. Proof. reflexivity. Qed.
Lemma bc_ffk_mkbc0 : forall fk fs tbl, bc_ffk (mkbc0 fk fs tbl) = facts_of fk. Proof. reflexivity. Qed.
Lemma bc_kd_mkbc0 : forall fk fs tbl, bc_kd (mkbc0 fk fs tbl) = kdisj_of fk. Proof. reflexivity. Qed.
#[export] Hint Rewrite bc_kd_mkbc0 kdisj_apart_kdisj_of kdisj_apart_x_kdisj_of : bceq.
Lemma find_rangeI_mkbc0 : forall fk fs tbl, find_rangeI (bc_ri (mkbc0 fk fs tbl)) = find_range (facts_of fk).
Proof. intros. apply functional_extensionality. intros e. apply find_rangeI_eq. Qed.
#[export] Hint Rewrite bc_fk_mkbc0 bc_ffk_mkbc0 find_rangeI_mkbc0 : bceq.
Ltac bcfe := repeat (apply functional_extensionality; intros ?).

Lemma find_range_lincB_eqf0 : forall fk fs tbl, find_range_linc (bc_rl (mkbc0 fk fs tbl)) = find_range_lin (facts_of fk).
Proof. intros. bcfe. cbn [bc_rl mkbc0]. apply find_range_linc_eq. Qed.
#[export] Hint Rewrite find_range_lincB_eqf0 : bceq.

Lemma erange_fB_eqf0 : forall fk fs tbl fuel, erange_fB fuel (mkbc0 fk fs tbl) = erange_f fuel (facts_of fk).
Proof.
  intros fk fs tbl fuel. induction fuel as [|f IH]; bcfe; [reflexivity|].
  cbn [erange_fB erange_f]. rewrite IH. (repeat first [ rewrite find_rangeI_mkbc0 | rewrite find_range_lincB_eqf0 ]). reflexivity.
Qed.
#[export] Hint Rewrite erange_fB_eqf0 : bceq.

Lemma erange0B_eqf0 : forall fk fs tbl, erange0B (mkbc0 fk fs tbl) = erange0 fk.
Proof. intros. bcfe. unfold erange0B, erange0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite erange0B_eqf0 : bceq.
Lemma erangeB_eqf0 : forall fk fs tbl, erangeB (mkbc0 fk fs tbl) = erange fk.
Proof. intros. bcfe. unfold erangeB, erange. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite erangeB_eqf0 : bceq.
Lemma base_rangeB_eqf0 : forall fk fs tbl, BRT_OK fk tbl -> base_rangeB (mkbc0 fk fs tbl) = base_range fk.
Proof.
  intros fk fs tbl HT. bcfe. unfold base_rangeB. cbn [bc_brt mkbc0].
  destruct (brt_lookup tbl x) as [r|] eqn:HL.
  - pose proof (HT _ _ HL) as E. unfold base_range in E |- *. destruct x; try exact (eq_sym E). rewrite zmod64_eq. reflexivity.
  - unfold base_range. autorewrite with bceq. destruct x; try reflexivity. rewrite zmod64_eq. reflexivity.
Qed.
Lemma ealignB_eqf0 : forall fk fs tbl, ealignB (mkbc0 fk fs tbl) = ealign fk.
Proof. intros. bcfe. unfold ealignB, ealign. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite ealignB_eqf0 : bceq.
Lemma lin_nowrapB_eqf0 : forall fk fs tbl, lin_nowrapB (mkbc0 fk fs tbl) = lin_nowrap fk.
Proof. intros. bcfe. unfold lin_nowrapB, lin_nowrap. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_nowrapB_eqf0 : bceq.
Lemma srl_expandB_eqf0 : forall fk fs tbl, srl_expandB (mkbc0 fk fs tbl) = srl_expand fk.
Proof.
  intros fk fs tbl. apply functional_extensionality; intros ts. 
  induction ts as [|[k a] rest IH]; intros; bcfe; [reflexivity|].
  cbn [srl_expandB srl_expand]. rewrite IH. (repeat first [ rewrite ealignB_eqf0 | rewrite lin_nowrapB_eqf0 ]). reflexivity.
Qed.
#[export] Hint Rewrite srl_expandB_eqf0 : bceq.
Lemma fact_nowrapB_eqf0 : forall fk fs tbl, fact_nowrapB (mkbc0 fk fs tbl) = fact_nowrap fk.
Proof. intros. bcfe. unfold fact_nowrapB, fact_nowrap. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite fact_nowrapB_eqf0 : bceq.
Lemma sum_fact_xB_eqf0 : forall fk fs tbl, sum_fact_xB (mkbc0 fk fs tbl) = sum_fact_x fk.
Proof. intros. bcfe. unfold sum_fact_xB, sum_fact_x. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite sum_fact_xB_eqf0 : bceq.
Lemma sum_factsB_eqf0 : forall fk fs tbl, sum_factsB (mkbc0 fk fs tbl) = sum_facts fk.
Proof.
  intros fk fs tbl. apply functional_extensionality; intros kn. 
  induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [sum_factsB sum_facts]. rewrite IH. (repeat first [ rewrite fact_nowrapB_eqf0 | rewrite sum_fact_xB_eqf0 ]). reflexivity.
Qed.
#[export] Hint Rewrite sum_factsB_eqf0 : bceq.


(* [comment removed for export] *)
Definition brt_keys (fk : list kentry) : list expr :=
  nubE (flat_map (fun K => match K with KWr (SA (ELit _) _) _ => [] | KWr (SA b _) _ => [b] | _ => [] end) fk).
Definition mk_brt (bc : bctx) (keys : list expr) : list (expr * option (Z * Z)) :=
  map (fun b => (b, base_rangeB bc b)) keys.
(* [comment removed for export] *)
Definition mkbc_fs (fk : list kentry) : list sfact := sum_factsB (mkbc0 fk [] []) fk.
Definition mkbc1 (fk : list kentry) : bctx := mkbc0 fk (mkbc_fs fk) [].
Definition mkbc (fk : list kentry) : bctx :=
  let fs := mkbc_fs fk in mkbc0 fk fs (mk_brt (mkbc0 fk fs []) (brt_keys fk)).   (* [comment removed for export] *)
Lemma BRT_OK_nil : forall fk, BRT_OK fk [].
Proof. intros fk e r H. discriminate H. Qed.
Lemma brt_lookup_map : forall (f : expr -> option (Z * Z)) keys e r,
  brt_lookup (map (fun b => (b, f b)) keys) e = Some r -> r = f e.
Proof.
  intros f keys e r. induction keys as [|b rest IH]; cbn; [discriminate|].
  destruct (expr_eqb e b) eqn:E; [|exact IH]. intros H. injection H as <-. apply p_expr_eqb_eq in E. subst. reflexivity.
Qed.
Lemma mk_brt_ok : forall fk keys, BRT_OK fk (mk_brt (mkbc1 fk) keys).
Proof.
  intros fk keys e r H. unfold mk_brt in H. apply brt_lookup_map in H. subst r.
  unfold mkbc1. rewrite (base_rangeB_eqf0 _ _ _ (BRT_OK_nil fk)). reflexivity.
Qed.
Lemma bc_fk_mkbc : forall fk, bc_fk (mkbc fk) = fk. Proof. reflexivity. Qed.
Lemma bc_ffk_mkbc : forall fk, bc_ffk (mkbc fk) = facts_of fk. Proof. reflexivity. Qed.
Lemma bc_kd_mkbc : forall fk, bc_kd (mkbc fk) = kdisj_of fk. Proof. reflexivity. Qed.
#[export] Hint Rewrite bc_kd_mkbc : bceq.
Lemma mkbc_unfold : forall fk, mkbc fk = mkbc0 fk (mkbc_fs fk) (mk_brt (mkbc1 fk) (brt_keys fk)).
Proof. reflexivity. Qed.
Lemma bc_fs_mkbc : forall fk, bc_fs (mkbc fk) = sum_facts fk fk.
Proof. intros. rewrite mkbc_unfold. cbn [bc_fs mkbc0]. unfold mkbc_fs. rewrite sum_factsB_eqf0. reflexivity. Qed.
Lemma find_rangeI_mkbc : forall fk, find_rangeI (bc_ri (mkbc fk)) = find_range (facts_of fk).
Proof. intros. rewrite mkbc_unfold. apply find_rangeI_mkbc0. Qed.
#[export] Hint Rewrite bc_fk_mkbc bc_ffk_mkbc bc_fs_mkbc find_rangeI_mkbc : bceq.
Lemma erange_fB_eqf : forall fk fuel, erange_fB fuel (mkbc fk) = erange_f fuel (facts_of fk).
Proof. intros. rewrite mkbc_unfold. apply erange_fB_eqf0. Qed.
#[export] Hint Rewrite erange_fB_eqf : bceq.

Lemma erange0B_eqf : forall fk, erange0B (mkbc fk) = erange0 fk.
Proof. intros. rewrite mkbc_unfold. apply erange0B_eqf0. Qed.
#[export] Hint Rewrite erange0B_eqf : bceq.
Lemma erangeB_eqf : forall fk, erangeB (mkbc fk) = erange fk.
Proof. intros. rewrite mkbc_unfold. apply erangeB_eqf0. Qed.
#[export] Hint Rewrite erangeB_eqf : bceq.
Lemma base_rangeB_eqf : forall fk, base_rangeB (mkbc fk) = base_range fk.
Proof. intros. rewrite mkbc_unfold. apply base_rangeB_eqf0. apply mk_brt_ok. Qed.
#[export] Hint Rewrite base_rangeB_eqf : bceq.
Lemma ealignB_eqf : forall fk, ealignB (mkbc fk) = ealign fk.
Proof. intros. rewrite mkbc_unfold. apply ealignB_eqf0. Qed.
#[export] Hint Rewrite ealignB_eqf : bceq.
Lemma lin_nowrapB_eqf : forall fk, lin_nowrapB (mkbc fk) = lin_nowrap fk.
Proof. intros. rewrite mkbc_unfold. apply lin_nowrapB_eqf0. Qed.
#[export] Hint Rewrite lin_nowrapB_eqf : bceq.
Lemma srl_expandB_eqf : forall fk, srl_expandB (mkbc fk) = srl_expand fk.
Proof. intros. rewrite mkbc_unfold. apply srl_expandB_eqf0. Qed.
#[export] Hint Rewrite srl_expandB_eqf : bceq.
Lemma fact_nowrapB_eqf : forall fk, fact_nowrapB (mkbc fk) = fact_nowrap fk.
Proof. intros. rewrite mkbc_unfold. apply fact_nowrapB_eqf0. Qed.
#[export] Hint Rewrite fact_nowrapB_eqf : bceq.
Lemma sum_fact_xB_eqf : forall fk, sum_fact_xB (mkbc fk) = sum_fact_x fk.
Proof. intros. rewrite mkbc_unfold. apply sum_fact_xB_eqf0. Qed.
#[export] Hint Rewrite sum_fact_xB_eqf : bceq.
Lemma sum_factsB_eqf : forall fk, sum_factsB (mkbc fk) = sum_facts fk.
Proof. intros. rewrite mkbc_unfold. apply sum_factsB_eqf0. Qed.
#[export] Hint Rewrite sum_factsB_eqf : bceq.

Definition lin_test_relB (bc : bctx) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match bc_fs bc with
  | [] => false
  | fs => if lin_test_with (erangeB bc) fs c ts test then true
          else existsb (fun f => lin_test_with (erangeB bc) [f] c ts test) fs
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
   let d := lsub_e (snd l2) (snd l1) in
   let test := fun lo hi => (Z.leb n1 lo || Z.leb hi (- n2))%bool in
   if lin_testB bc (fst l2 + k2 - fst l1 - k1)%Z d test then true
   else (* [comment removed for export] *)
     let '(c2, t2) := srl_expandB bc d in lin_testB bc (fst l2 + k2 - fst l1 - k1 + c2)%Z t2 test)%bool.

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
    lin_testB bc (sc * c + c2 + c3 + (sc - 1))%Z t3 (fun lo _ => Z.leb 0 lo)   (* [comment removed for export] *)
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
        | Some (lo1, hi1), Some h1, Some l2 =>
            if (Z.leb (lo2 + k2) (lo1 + k1) && Z.leb (hi1 + k1 + h1) (lo2 + k2 + l2))%bool then true
            else if (Z.leb (lo2 + k2) (lo1 + k1) && Z.leb 0 (lo1 + k1) && Z.ltb (hi1 + k1 + h1) two64)%bool   (* [comment removed for export] *)
                 then match xhiB bc (EAlu ALU_ADD (EAlu ALU_ADD b1 (ELit k1)) n1) with
                      | Some e => Z.leb e (lo2 + k2 + l2)
                      | None => false
                      end
                 else false
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
  else if kdisj_apartB bc (bc_kd bc) b1 k1 n1 b2 k2 n2 then true
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

Definition end_hi0B (bc : bctx) (b : expr) (k : Z) (n : expr) (lo1 hi1 h1 : Z) : option Z :=
  match n with
  | ELit _ => None
  | _ => if (if Z.leb 0 (lo1 + k) then Z.ltb (hi1 + k + h1) two64 else false)
         then match find_rangeI (bc_ri bc) (mkAlu ALU_ADD (mkAlu ALU_ADD b (ELit k)) n) with
              | Some (_, ehi) => Some ehi
              | None => None
              end
         else None
  end.
Fixpoint end_hi_winB (ks : list kentry) (bc : bctx) (b : expr) (k : Z) (n : expr) : option Z :=
  match ks with
  | [] => None
  | K :: rest =>
      match (match K with
             | KWr (SA mb mk) ml =>
                 match ml with
                 | ELit _ => None
                 | _ => match base_rangeB bc mb, xhiB bc ml with
                        | Some (mlo, mhi), Some mh => if xinsideB bc b k n mb mk ml then end_hi0B bc mb mk ml mlo mhi mh else None
                        | _, _ => None
                        end
                 end
             | _ => None
             end) with
      | Some e => Some e
      | None => end_hi_winB rest bc b k n
      end
  end.
Definition end_hiB (bc : bctx) (b : expr) (k : Z) (n : expr) (lo1 hi1 h1 : Z) : option Z :=
  match end_hi0B bc b k n lo1 hi1 h1 with
  | Some e => Some e
  | None => match n with ELit _ => None | _ => end_hi_winB (bc_fk bc) bc b k n end
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
    else if kdisj_apart_xB bc (bc_kd bc) b1 k1 n1 b2 k2 n2 then true
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
Proof. intros. bcfe. unfold lin_test_relB, lin_test_rel. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_test_relB_eqf : bceq.
Lemma lin_testB_eqf : forall fk, lin_testB (mkbc fk) = lin_test fk.
Proof. intros. bcfe. unfold lin_testB, lin_test. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_testB_eqf : bceq.
Lemma lin_srangeB_eqf : forall fk, lin_srangeB (mkbc fk) = lin_srange fk.
Proof. intros. bcfe. unfold lin_srangeB, lin_srange. (repeat first [ rewrite erangeB_eqf | rewrite srl_expandB_eqf ]). reflexivity. Qed.
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
Proof. intros. bcfe. unfold ranges_apartB, ranges_apart. autorewrite with bceq. reflexivity. Qed.
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
Lemma end_hi0B_eqf : forall fk, end_hi0B (mkbc fk) = end_hi0 fk.
Proof. intros. bcfe. unfold end_hi0B, end_hi0. (repeat first [ rewrite find_rangeI_mkbc ]). reflexivity. Qed.
#[export] Hint Rewrite end_hi0B_eqf : bceq.
Lemma end_hi_winB_eqf : forall fk ks, end_hi_winB ks (mkbc fk) = end_hi_win ks fk.
Proof. intros fk ks. bcfe. induction ks as [|K rest IH]; [reflexivity|]. cbn [end_hi_winB end_hi_win]. rewrite IH. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite end_hi_winB_eqf : bceq.
Lemma end_hiB_eqf : forall fk, end_hiB (mkbc fk) = end_hi fk.
Proof. intros. bcfe. unfold end_hiB, end_hi. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite end_hiB_eqf : bceq.
Lemma ranges_apart_xB_eqf : forall fk, ranges_apart_xB (mkbc fk) = ranges_apart_x fk.
Proof. intros. bcfe. unfold ranges_apart_xB, ranges_apart_x. (repeat first [ rewrite kdisj_apart_x_kdisj_of | rewrite bc_kd_mkbc | rewrite base_rangeB_eqf | rewrite xhiB_eqf | rewrite lin_ge0B_eqf | rewrite ranges_apartB_eqf | rewrite kdisj_apart_xB_eqf | rewrite end_hiB_eqf ]). reflexivity. Qed.
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
  cbn [disj_sides_xB disj_sides_x]. rewrite IH. (repeat first [ rewrite sub_itv_xB_eqf ]). reflexivity.
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
Proof. intros. bcfe. unfold ranges_apart_pB, ranges_apart_p. (repeat first [ rewrite base_rangeB_eqf | rewrite lin_apartB_eqf | rewrite xhiB_eqf | rewrite lin_ge0B_eqf | rewrite end_hiB_eqf | rewrite in_sidesB_eqf | rewrite in_sides_xB_eqf ]). reflexivity. Qed.
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

Definition and_high_splitB (bc : bctx) (a bk : expr) (j c : Z) (dts rts : list (Z * expr)) : expr :=
  let m := (2 ^ j)%Z in
  let cA := (c - c mod m)%Z in
  let r := unlin ((c mod m)%Z, rts) in
  let whole := match erangeB bc a with
               | Some _ => mkMd M_MUL (ELit m) (mkSrlB bc a j)
               | None => mkAlu ALU_ADD (unlin (cA, dts)) (mkAlu ALU_AND r bk)
               end in
  match erangeB bc r with
  | Some (lo, hi) =>
      if Z.eqb (lo / m) (hi / m) then unlin ((cA + (lo / m) * m)%Z, dts)
      else whole
  | None => whole
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
                | ((_ :: _) as dts, (_ :: _) as rts) => and_high_splitB bc a b j (fst l) dts rts
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
Inductive mtree : Type := MHit | MLit (w : Z) | MUn (m : mtree) | MBin (m1 m2 : mtree) | MNo.
Fixpoint markS (s e : expr) : mtree :=
  if expr_eqb e s then MHit else
  match e with
  | ELit w => MLit (wrap64 w)
  | EVar _ => MNo
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => MBin (markS s a) (markS s b)
  | EExt _ _ _ a => MUn (markS s a)
  | EBlob _ _ _ _ => MNo
  end.
Fixpoint evalM (e : expr) (m : mtree) (z : Z) {struct m} : option Z :=
  match m with
  | MHit => Some z
  | MLit w => Some w
  | MNo => None
  | MBin m1 m2 =>
      match e with
      | EAlu op a b => match evalM a m1 z with
                       | Some x => match evalM b m2 z with Some y => Some (zfast op x y) | None => None end
                       | None => None
                       end
      | EAluw op a b => match evalM a m1 z with
                        | Some x => match evalM b m2 z with Some y => Some (zfastw op x y) | None => None end
                        | None => None
                        end
      | EMd op a b => match evalM a m1 z with
                      | Some x => match evalM b m2 z with Some y => Some (zfastm op x y) | None => None end
                      | None => None
                      end
      | EMdw op a b => match evalM a m1 z with
                       | Some x => match evalM b m2 z with Some y => Some (zmdw op x y) | None => None end
                       | None => None
                       end
      | _ => None
      end
  | MUn m1 =>
      match e with
      | EExt sx lo n a => match evalM a m1 z with Some x => Some (zext_fast sx lo n x) | None => None end
      | _ => None
      end
  end.
Lemma evalM_markS : forall s z e, evalM e (markS s e) z = evalS s z e.
Proof.
  intros s z e. induction e; cbn [markS evalS]; destruct (expr_eqb _ s); cbn [evalM];
    rewrite ?IHe1, ?IHe2, ?IHe; reflexivity.
Qed.
Lemma evalM_markSf : forall s e, evalM e (markS s e) = (fun z => evalS s z e).
Proof. intros. apply functional_extensionality; intros z. apply evalM_markS. Qed.
(* [comment removed for export] *)
Fixpoint mdef (m : mtree) : bool :=
  match m with
  | MHit | MLit _ => true
  | MNo => false
  | MUn a => mdef a
  | MBin a b => if mdef a then mdef b else false
  end.
Lemma mdef_markS : forall s e, mdef (markS s e) = evalS_def s e.
Proof.
  intros s e. induction e; cbn [markS evalS_def]; destruct (expr_eqb _ s); cbn [mdef];
    rewrite ?IHe1, ?IHe2, ?IHe; reflexivity.
Qed.
Fixpoint all_eval_toM (e : expr) (m : mtree) (v lo : Z) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c => match evalM e m (wrap64 lo) with
           | Some w => if Z.eqb w v then all_eval_toM e m v (lo + 1) c else false
           | None => false
           end
  end.
Definition probeM (e : expr) (m : mtree) (v z : Z) : bool :=
  match evalM e m (wrap64 z) with Some w => Z.eqb w v | None => false end.
Lemma all_eval_toM_eq : forall s e v cnt lo, all_eval_toM e (markS s e) v lo cnt = all_eval_toS s e v lo cnt.
Proof.
  intros s e v cnt. induction cnt as [|c IH]; intros lo; [reflexivity|].
  cbn [all_eval_toM all_eval_toS]. rewrite evalM_markS, IH. reflexivity.
Qed.
Lemma probeM_eq : forall s e v z, probeM e (markS s e) v z = probeS s e v z.
Proof. intros. unfold probeM, probeS. rewrite evalM_markS. reflexivity. Qed.
Lemma probeM_eqf : forall s e, probeM e (markS s e) = probeS s e.
Proof. intros. apply functional_extensionality; intros v. apply functional_extensionality; intros z. apply probeM_eq. Qed.
Lemma all_eval_toM_eqf : forall s e, all_eval_toM e (markS s e) = all_eval_toS s e.
Proof.
  intros. apply functional_extensionality; intros v. apply functional_extensionality; intros lo.
  apply functional_extensionality; intros cnt. apply all_eval_toM_eq.
Qed.

Fixpoint conc_tryB (bc : bctx) (e : expr) (cands : list expr) : option Z :=
  match cands with
  | [] => None
  | s :: rest =>
      if closedb s then conc_tryB bc e rest else
      let m := markS s e in        (* [comment removed for export] *)
      if negb (mdef m) then conc_tryB bc e rest else
      match base_rangeB bc s with     (* [comment removed for export] *)
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            match evalM e m (wrap64 lo) with
            | Some v =>
                if (if Z.ltb hi lo then true
                     else if probeM e m v hi then probeM e m v (lo + (hi - lo) / 2)%Z else false) then
                  if all_eval_toM e m v lo (Z.to_nat (hi - lo + 1)) then Some v
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

(* [comment removed for export] *)
Definition subexprs_init (e : expr) : list expr :=
  match e with
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => subexprs a ++ subexprs b
  | EExt _ _ _ a => subexprs a
  | _ => []
  end.
Definition pivot_self (re : option (Z * Z)) : option Z :=
  match re with
  | Some (lo, hi) => if Z.leb (hi - lo) conc_limit then (if Z.ltb hi lo then Some (wrap64 lo) else if Z.eqb hi lo then Some (wrap64 lo) else None) else None
  | None => None
  end.
Definition concretize_reB (bc : bctx) (e : expr) (re : option (Z * Z)) : option Z :=
  if closedb e then eval_closed e else
  match conc_tryB bc e (nubE (subexprs_init e)) with
  | Some v => Some v
  | None => pivot_self re
  end.

Definition foldKB (bc : bctx) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => let re := erangeB bc e in
         match re with
         | Some (lo, hi) => if Z.eqb lo hi then ELit lo
                            else match concretize_reB bc e re with Some v => ELit v | None => e end
         | None => match concretize_reB bc e re with Some v => ELit v | None => e end   (* [comment removed for export] *)
         end
  end.

(* [comment removed for export] *)
Definition lin_periodkB (bc : bctx) (e : expr) (k : Z) : bool :=
  let l := lin_of e in lin_testB bc (fst l) (snd l) (period_test k).
Definition lin_periodB (bc : bctx) (e : expr) : option Z :=
  let l := lin_of e in
  let k0 := match lin_range (erangeB bc) (fst l) (snd l) with Some (lo, _) => (lo / two64)%Z | None => 0%Z end in
  if lin_periodkB bc e k0 then Some k0
  else if (if Z.eqb k0 (-1) then false else lin_periodkB bc e (-1)) then Some (-1)%Z
  else if (if Z.eqb k0 0 then false else lin_periodkB bc e 0) then Some 0%Z
  else None.
Definition ltu_shiftB (bc : bctx) (a b : expr) : option bool :=
  match lin_periodB bc a, lin_periodB bc b with
  | Some ka, Some kb =>
      let la := lin_of a in let lb := lin_of b in
      if lin_testB bc (fst lb - kb * two64 - 1 - (fst la - ka * two64))%Z (lsub_e (snd lb) (snd la)) (fun lo _ => Z.leb 0 lo) then Some true
      else if lin_testB bc (fst la - ka * two64 - (fst lb - kb * two64))%Z (lsub_e (snd la) (snd lb)) (fun lo _ => Z.leb 0 lo) then Some false
      else None
  | _, _ => None
  end.

Definition lin_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
  let ltu := if lin_ge0B bc [(b, (-1)%Z)] [(a, 0%Z)] then Some true
             else if lin_ge0B bc [(a, 0%Z)] [(b, 0%Z)] then Some false
             else ltu_shiftB bc a b in
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
      else
      if (match ltu_shiftB bc a b with Some true => true | _ => match ltu_shiftB bc b a with Some true => true | _ => false end end)
      then Some (match c with BC_EQ => false | _ => true end)
      else None
  end.

Definition decide_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
  match a, b with
  | ELit x, ELit y => Some (lit_branchF c x y)
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

(* [comment removed for export] *)
Definition roundup_idiom1B (bc : bctx) (x y : expr) (m c : Z) : option expr :=
  match pow2_log (m + 1) with
  | Some k =>
      if (Z.leb 0 c && Z.leb 0 m
          && lin_modk_zero (lin_of (mkAlu ALU_ADD (mkAlu ALU_ADD x y) (ELit c))) (2 ^ k)
          && match erangeB bc x with Some (_, hi) => Z.ltb (hi + c + m) two64 | None => false end)%bool
      then Some (mkMd M_MUL (ELit (m + 1)) (mkSrlB bc (mkAlu ALU_ADD x (ELit (c + m))) k))
      else None
  | None => None
  end.
Definition roundup_idiomB (bc : bctx) (a b : expr) : option expr :=
  match b with
  | ELit c =>
      match find_and_term 8 a with
      | Some (y, m) => roundup_idiom1B bc (mkAlu ALU_SUB a (EAlu ALU_AND y (ELit m))) y m c
      | None => None
      end
  | _ => None
  end.
Definition mkAluK0B (bc : bctx) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_ADD => match roundup_idiomB bc a b with Some e => e | None => mkAlu op a b end   (* [comment removed for export] *)
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
  | ALU_SLL | ALU_SRL | ALU_SRA =>   (* [comment removed for export] *)
      match is_lit b with
      | Some _ => mkAluw op a b
      | None => match lin_lowbits_knB bc b 5 with
                | Some s => mkAluw op a (ELit s)
                | None => mkAluw op a b
                end
      end
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
        | Some (lo, hi) => if Z.ltb hi (ext_lim sx n) then e else v
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

(* [comment removed for export] *)
Definition ranges_apart_r1B (bc : bctx) (r1 : option (Z * Z)) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match r1, base_rangeB bc b2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
      | _, _ => false
      end) then true
  else if kdisj_apartB bc (bc_kd bc) b1 k1 n1 b2 k2 n2 then true
  else lin_apartB bc b1 k1 n1 b2 k2 n2.
Lemma ranges_apart_r1B_eq : forall bc b1 k1 n1 b2 k2 n2,
  ranges_apart_r1B bc (base_rangeB bc b1) b1 k1 n1 b2 k2 n2 = ranges_apartB bc b1 k1 n1 b2 k2 n2.
Proof. reflexivity. Qed.
Fixpoint log_lookupRB (bc : bctx) (r1 : option (Z * Z)) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupRB bc r1 rest rb rk n sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          if ranges_apart_r1B bc r1 rb rk (Z.of_nat n) kb kk (Z.of_nat w)
          then log_lookupRB bc r1 rest rb rk n sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupRB bc r1 rest rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
          end
      end
  end.
Lemma log_lookupRB_eq : forall bc log rb rk n sx hints acc,
  log_lookupRB bc (base_rangeB bc rb) log rb rk n sx hints acc = log_lookupB bc log rb rk n sx hints acc.
Proof.
  intros bc log rb. induction log as [|[[kb kk] w v] rest IH]; intros; [reflexivity|].
  cbn [log_lookupRB log_lookupB]. rewrite ranges_apart_r1B_eq, !IH. reflexivity.
Qed.

(* [comment removed for export] *)
Definition rel_litZ (rb : expr) (rk : Z) (rn : Z) (kb : expr) (kk : Z) (l0 : Z) : rangerel :=
  if expr_eqb rb kb then
    let kn := zmod64 l0 in
    if (Z.leb kk rk && Z.leb (rk + rn) (kk + kn))%bool then RInside (rk - kk)
    else if (Z.leb (rk + rn) kk || Z.leb (kk + kn) rk)%bool then RDisjoint
    else RPartial
  else RUnknown.
Lemma rel_litZ_eqf : rel_litZ = (fun rb rk rn kb kk l0 => rel_lit rb rk rn kb kk (l0 mod 2^64)%Z).
Proof.
  do 6 (apply functional_extensionality; intros ?). unfold rel_litZ, rel_lit. rewrite zmod64_eq. reflexivity.
Qed.
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
              match rel_litZ rb rk (Z.of_nat n) kb kk l0 with
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
              match rel_litZ rb rk (Z.of_nat n) kb kk l0 with
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

Definition sym_readRB (segs : list Segment) (ss : sym_state) (bc : bctx) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat * list kentry) :=
  match log_lookupRB bc (base_rangeB bc (a_base a)) (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
  | LStuck => None
  | LHit v scs hints =>
      Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss, [])
  | LMiss scs hints =>
      match know_lookupAB bc segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extKB bc v, flat_scB bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss, [])
      | LMiss scs' hints' =>
          (* [comment removed for export] *)
          let i := s_next ss in
          (* [comment removed for export] *)
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let rvx := match sc_reads scr with [] => mkExt sx' 0 n (EVar i) | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rvx, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i,
                if rec_onb (bc_fk bc) then [krec a n rv] else [])   (* [comment removed for export] *)
      end
  end.
Definition sym_readB (segs : list Segment) (ss : sym_state) (bc : bctx) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match sym_readRB segs ss bc scr a n sx' with
  | Some (v, scs, scr', nx', _) => Some (v, scs, scr', nx')
  | None => None
  end.

Definition sym_stepB (bc : bctx) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_signedF imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluwKB bc ALU_ADD (g rs) (ELit (bv_signedF imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (sset ss rd (mkMdKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (sset ss rd (ELit (bvu64 (Z.shiftl (bv_signedF imm) 12))) (p + 4)) [] scr
  | Auipc rd imm => SOk (sset ss rd (ELit (bvu64 (Z.shiftl (bv_signedF imm) 12 + p))) (p + 4)) [] scr
  | Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (bvu64 (p + bv_signedF imm))) [] scr
  | Jalr rd rs1 imm =>
      match conc_exprB bc (g rs1) with
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (jalrF z (bv_signedF imm))) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let tk := bvu64 (p + bv_signedF imm) in
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
      let a := to_saddrKB bc (g rs) (bv_signedF imm) in
      match sym_readRB segs ss bc scr a n sx' with
      | None => SStop
      | Some (v, scs, scr', nx', recs) =>
          SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                   (s_log ss) (recs ++ s_know ss) nx' (s_resv ss)) scs scr'   (* [comment removed for export] *)
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrKB bc (g rs1) (bv_signedF imm) in
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
(* [comment removed for export] *)
Definition mk_kix0 (kn : list kentry) : kix :=
  let r := kx_build kn xH in KX kn (fst (fst r)) (snd (fst r)) (snd r).
Definition mk_kix (kn : list kentry) : kix := mk_kix0 (krec_rest kn).
(* [comment removed for export] *)
Lemma krec_head_rest : forall kn, krec_head kn ++ krec_rest kn = kn.
Proof. induction kn as [|K rest IH]; [reflexivity|]. cbn. destruct (kwrappedb K); [cbn; rewrite IH; reflexivity|reflexivity]. Qed.
Lemma krec_rest_app : forall W kn, forallb kwrappedb W = true -> krec_rest (W ++ kn) = krec_rest kn.
Proof. induction W as [|K W IH]; intros kn H; [reflexivity|]. cbn in H |- *. destruct (kwrappedb K); [exact (IH kn H)|discriminate]. Qed.
Lemma krec_head_wrapped : forall kn, forallb kwrappedb (krec_head kn) = true.
Proof. induction kn as [|K rest IH]; [reflexivity|]. cbn. destruct (kwrappedb K) eqn:E; [cbn; rewrite E; exact IH|reflexivity]. Qed.
Lemma facts_of_kunwrap_head : forall kn, facts_of (kunwrap_head kn) = facts_of kn.
Proof.
  intros kn. rewrite !facts_of_filter. induction kn as [|K rest IH]; [reflexivity|]. cbn [kunwrap_head].
  destruct (kwrappedb K) eqn:W; [|reflexivity]. cbn [List.filter]. rewrite IH.
  destruct K as [? ? v| | | | | | | | |]; try discriminate. cbn in W |- *. destruct v as [| | | | | |sx lo m e|]; try discriminate.
  destruct sx; [discriminate|]. destruct lo; [|discriminate]. do 8 (destruct m as [|m]; [discriminate|]). destruct m; [reflexivity|discriminate].
Qed.
Lemma mk_kix_recs : forall W kn, forallb kwrappedb W = true -> mk_kix (W ++ kn) = mk_kix kn.
Proof. intros W kn H. unfold mk_kix. rewrite (krec_rest_app W kn H). reflexivity. Qed.
Lemma facts_of_recs : forall W kn, forallb kwrappedb W = true -> facts_of (W ++ kn) = facts_of kn.
Proof.
  intros W kn H. rewrite !facts_of_filter. induction W as [|K W IH]; [reflexivity|]. cbn in H |- *.
  destruct K as [? ? v| | | | | | | | |]; try discriminate. cbn. destruct v as [| | | | | |sx lo m e|]; try discriminate.
  destruct sx; [discriminate|]. destruct lo; [|discriminate]. apply IH.
  do 8 (destruct m as [|m]; [discriminate|]). destruct m; [exact H|discriminate].
Qed.
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
  cbn [know_lookupA0B]. rewrite ?rel_litZ_eqf. cbv beta.
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
  cbn [know_lookupA0B]. rewrite ?rel_litZ_eqf. cbv beta. unfold kx_candf in HC.
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
  kx_select (mk_kix0 kn) rb rk = if is_lit0 rb then List.filter (kx_cand0 (gran rk)) kn else List.filter kx_candf kn.
Proof.
  intros kn rb rk. unfold kx_select, mk_kix0.
  destruct (kx_build kn 1%positive) as [[w0 gr] wf] eqn:Hb. cbn [kx_gran kx_w0 kx_wf fst snd].
  destruct (kx_build_spec kn 1%positive w0 gr wf Hb) as (A & B & C).
  destruct (is_lit0 rb); [|exact C].
  rewrite B, A. rewrite (kx_merge_filters (narrow_in (gran rk)) kx_wide0 kn 1%positive (narrow_not_wide (gran rk))).
  apply filter_ext. intros K. symmetry. apply kx_cand0_split.
Qed.

Theorem know_lookupA0I_eq : forall bc kn segs rb rk n sx hints acc,
  know_lookupA0I bc (mk_kix0 kn) segs rb rk n sx hints acc = know_lookupA0B bc segs kn rb rk n sx hints acc.
Proof.
  intros bc kn segs rb rk n sx hints acc. unfold know_lookupA0I.
  destruct hints as [|h hs]; [|reflexivity]. destruct n as [|n]; [reflexivity|].
  rewrite kx_select_eq. destruct (is_lit0 rb) eqn:L.
  - apply is_lit0_true in L. subst rb. apply know_lookupA0B_filter0.
  - apply know_lookupA0B_filterf. exact L.
Qed.

(* [comment removed for export] *)
Fixpoint know_byte_litB (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z) : option Z :=
  match kn with
  | [] => None
  | K :: rest =>
      match K with
      | KWord (SA kb kk) w (ELit z) =>
          match rel_lit rb rk 1 kb kk (Z.of_nat w) with
          | RInside d => Some (((z mod two64) / 2 ^ (8 * d)) mod 256)%Z
          | _ => know_byte_litB segs rest rb rk
          end
      | KZero (SA kb kk) (ELit l0) =>
          match rel_lit rb rk 1 kb kk (zmod64 l0) with
          | RInside _ => Some 0%Z
          | _ => know_byte_litB segs rest rb rk
          end
      | KFill (SA kb kk) (ELit l0) c =>
          match rel_lit rb rk 1 kb kk (zmod64 l0) with
          | RInside _ => Some (c mod 256)%Z
          | _ => know_byte_litB segs rest rb rk
          end
      | KImg lo hi =>
          match rb with
          | ELit 0 =>
              if (Z.leb lo rk && Z.ltb rk hi)%bool then
                match seg_rom segs (Z_to_bv 64 rk) with
                | Some b => Some (bv_unsigned b)
                | None => None
                end
              else know_byte_litB segs rest rb rk
          | _ => know_byte_litB segs rest rb rk
          end
      | _ => know_byte_litB segs rest rb rk
      end
  end.
Lemma know_byte_litB_eq : forall segs kn rb rk, know_byte_litB segs kn rb rk = know_byte_lit segs kn rb rk.
Proof.
  intros segs kn rb rk. induction kn as [|K rest IH]; [reflexivity|].
  cbn [know_byte_litB know_byte_lit]. rewrite IH.
  destruct K as [[kb kk] w v|[kb kk] [l0| | | | | | |]|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] [l0| | | | | | |] c|[kb kk] len];
    rewrite ?zmod64_eq; reflexivity.
Qed.
Lemma know_byte_lit_skip0 : forall segs K rest rk,
  kx_cand0 (gran rk) K = false ->
  know_byte_lit segs (K :: rest) (ELit 0) rk = know_byte_lit segs rest (ELit 0) rk.
Proof.
  intros segs K rest rk HC. cbn [know_byte_lit]. unfold kx_cand0, kx_wide0 in HC.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
    cbn [lit0_extent] in HC; rewrite ?zmod64_eq in HC; try reflexivity.
  - (* [comment removed for export] *)
    destruct v as [z| | | | | | |]; try reflexivity.
    destruct (is_lit0 kb) eqn:L.
    + apply is_lit0_true in L. subst kb. cbn [lit0_extent] in HC. rewrite rel_lit_same.
      destruct (Z.leb kk rk && Z.leb (rk + 1) (kk + Z.of_nat w))%bool eqn:E.
      * exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
        destruct (ext_fits kk (kk + Z.of_nat w)) eqn:F; [|discriminate].
        rewrite (gran_between kk (kk + Z.of_nat w) rk) in HC; [discriminate|lia|lia|exact F].
      * destruct (Z.leb (rk + 1) kk || Z.leb (kk + Z.of_nat w) rk)%bool; reflexivity.
    + destruct kb as [z'| | | | | | |]; try (rewrite rel_lit_other by reflexivity; reflexivity).
      cbn in L. destruct z'; try discriminate; rewrite rel_lit_other by reflexivity; reflexivity.
  - (* [comment removed for export] *)
    destruct len as [l0| | | | | | |]; try reflexivity.
    destruct (is_lit0 kb) eqn:L.
    + apply is_lit0_true in L. subst kb. cbn [lit0_extent] in HC. rewrite ?zmod64_eq in HC. rewrite rel_lit_same.
      destruct (Z.leb kk rk && Z.leb (rk + 1) (kk + l0 mod 2 ^ 64))%bool eqn:E.
      * exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
        destruct (ext_fits kk (kk + l0 mod 2 ^ 64)) eqn:F; [|discriminate].
        rewrite (gran_between kk (kk + l0 mod 2 ^ 64) rk) in HC; [discriminate|lia|lia|exact F].
      * destruct (Z.leb (rk + 1) kk || Z.leb (kk + l0 mod 2 ^ 64) rk)%bool; reflexivity.
    + destruct kb as [z'| | | | | | |]; try (rewrite rel_lit_other by reflexivity; reflexivity).
      cbn in L. destruct z'; try discriminate; rewrite rel_lit_other by reflexivity; reflexivity.
  - (* [comment removed for export] *)
    destruct (ext_fits lo hi) eqn:F; [|discriminate].
    destruct (Z.leb lo rk && Z.ltb rk hi)%bool eqn:E; [|reflexivity].
    exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    rewrite (gran_between lo hi rk) in HC; [discriminate|lia|lia|exact F].
  - (* [comment removed for export] *)
    destruct len as [l0| | | | | | |]; try reflexivity.
    destruct (is_lit0 kb) eqn:L.
    + apply is_lit0_true in L. subst kb. cbn [lit0_extent] in HC. rewrite ?zmod64_eq in HC. rewrite rel_lit_same.
      destruct (Z.leb kk rk && Z.leb (rk + 1) (kk + l0 mod 2 ^ 64))%bool eqn:E.
      * exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
        destruct (ext_fits kk (kk + l0 mod 2 ^ 64)) eqn:F; [|discriminate].
        rewrite (gran_between kk (kk + l0 mod 2 ^ 64) rk) in HC; [discriminate|lia|lia|exact F].
      * destruct (Z.leb (rk + 1) kk || Z.leb (kk + l0 mod 2 ^ 64) rk)%bool; reflexivity.
    + destruct kb as [z'| | | | | | |]; try (rewrite rel_lit_other by reflexivity; reflexivity).
      cbn in L. destruct z'; try discriminate; rewrite rel_lit_other by reflexivity; reflexivity.
Qed.
Lemma know_byte_lit_skipf : forall segs K rest rb rk,
  is_lit0 rb = false -> kx_candf K = false ->
  know_byte_lit segs (K :: rest) rb rk = know_byte_lit segs rest rb rk.
Proof.
  intros segs K rest rb rk Hrb HC. cbn [know_byte_lit]. unfold kx_candf in HC.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
    try reflexivity; try discriminate.
  - (* [comment removed for export] *) destruct v as [z| | | | | | |]; try reflexivity.
    destruct (is_lit0 kb) eqn:L; [|discriminate].
    rewrite rel_lit_other; [reflexivity|]. rewrite (is_lit0_eqb rb kb L). exact Hrb.
  - (* [comment removed for export] *) destruct rb as [z| | | | | | |]; try reflexivity. cbn in Hrb. destruct z; try reflexivity. discriminate.
Qed.
Lemma know_byte_lit_filter0 : forall segs l rk,
  know_byte_lit segs (List.filter (kx_cand0 (gran rk)) l) (ELit 0) rk = know_byte_lit segs l (ELit 0) rk.
Proof.
  intros segs l rk. induction l as [|K rest IH]; [reflexivity|].
  cbn [List.filter]. destruct (kx_cand0 (gran rk) K) eqn:HC.
  - cbn [know_byte_lit]. rewrite !IH.
    destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; reflexivity.
  - rewrite know_byte_lit_skip0 by exact HC. apply IH.
Qed.
Lemma know_byte_lit_filterf : forall segs l rb rk,
  is_lit0 rb = false ->
  know_byte_lit segs (List.filter kx_candf l) rb rk = know_byte_lit segs l rb rk.
Proof.
  intros segs l rb rk Hrb. induction l as [|K rest IH]; [reflexivity|].
  cbn [List.filter]. destruct (kx_candf K) eqn:HC.
  - cbn [know_byte_lit]. rewrite !IH.
    destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; reflexivity.
  - rewrite know_byte_lit_skipf by assumption. apply IH.
Qed.
Definition know_byte_litI (segs : list Segment) (kx : kix) (rb : expr) (rk : Z) : option Z :=
  know_byte_litB segs (kx_select kx rb rk) rb rk.
Lemma know_byte_litI_eq : forall segs kn rb rk, know_byte_litI segs (mk_kix0 kn) rb rk = know_byte_lit segs kn rb rk.
Proof.
  intros segs kn rb rk. unfold know_byte_litI. rewrite know_byte_litB_eq, kx_select_eq.
  destruct (is_lit0 rb) eqn:L.
  - apply is_lit0_true in L. subst rb. apply know_byte_lit_filter0.
  - apply know_byte_lit_filterf. exact L.
Qed.
Fixpoint know_bytes_litI (segs : list Segment) (kx : kix) (rb : expr) (rk : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match know_byte_litI segs kx rb rk, know_bytes_litI segs kx rb (rk + 1) n' with
            | Some b, Some r => Some (b :: r)
            | _, _ => None
            end
  end.
Lemma know_bytes_litI_eq : forall segs kn rb n rk, know_bytes_litI segs (mk_kix0 kn) rb rk n = know_bytes_lit segs kn rb rk n.
Proof.
  intros segs kn rb n. induction n as [|n IH]; intros rk; [reflexivity|].
  cbn [know_bytes_litI know_bytes_lit]. rewrite know_byte_litI_eq, IH. reflexivity.
Qed.

(* [comment removed for export] *)
Definition know_lookupABI (bc : bctx) (kx : kix) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match know_lookupA0B bc segs (krec_head kn) rb rk n sx hints acc with   (* [comment removed for export] *)
  | LMiss acc0 hints0 =>
  match know_lookupA0I bc kx segs rb rk n sx hints0 acc0 with
  | LMiss acc' hints' =>
      match know_bytes_lit segs kn rb rk n with
      | Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
      | None => LMiss acc' hints'
      end
  | r => r
  end
  | r => r
  end.
(* [comment removed for export] *)
Lemma know_lookupA0B_wrapped_app : forall bc segs W l rb rk n sx hints acc,
  forallb kwrappedb W = true ->
  know_lookupA0B bc segs (W ++ l) rb rk n sx hints acc =
  match know_lookupA0B bc segs W rb rk n sx hints acc with
  | LMiss acc' hints' => know_lookupA0B bc segs l rb rk n sx hints' acc'
  | r => r
  end.
Proof.
  intros bc segs W. induction W as [|K W IH]; intros l rb rk n sx hints acc H; [reflexivity|].
  cbn in H. destruct K as [[kb kk] w v| | | | | | | | |]; try discriminate.
  destruct (kwrappedb (KWord (SA kb kk) w v)); [|discriminate].
  cbn [know_lookupA0B app]. destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)); try reflexivity; apply IH; exact H.
Qed.
Lemma know_lookupABI_eq1 : forall bc kn segs rb rk n sx hints acc,
  know_lookupABI bc (mk_kix kn) segs kn rb rk n sx hints acc = know_lookupAB bc segs kn rb rk n sx hints acc.
Proof.
  intros. unfold know_lookupABI, know_lookupAB, mk_kix.
  assert (EF : know_lookupA0I bc (mk_kix0 (krec_rest kn)) segs = know_lookupA0B bc segs (krec_rest kn))
    by (bcfe; apply know_lookupA0I_eq).
  rewrite EF.
  transitivity (match know_lookupA0B bc segs (krec_head kn ++ krec_rest kn) rb rk n sx hints acc with
                | LMiss acc' hints' =>
                    match know_bytes_lit segs kn rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
                    | None => LMiss acc' hints'
                    end
                | r => r
                end).
  - rewrite (know_lookupA0B_wrapped_app bc segs (krec_head kn) (krec_rest kn)) by apply krec_head_wrapped.
    destruct (know_lookupA0B bc segs (krec_head kn) rb rk n sx hints acc); reflexivity.
  - rewrite krec_head_rest. reflexivity.
Qed.
Lemma know_lookupABI_eq : forall bc kn segs,
  know_lookupABI bc (mk_kix kn) segs kn = know_lookupAB bc segs kn.
Proof. intros. bcfe. apply know_lookupABI_eq1. Qed.
Local Close Scope Z_scope.

Definition sym_readRBI (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat * list kentry) :=
  match log_lookupRB bc (base_rangeB bc (a_base a)) (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
  | LStuck => None
  | LHit v scs hints =>
      Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss, [])
  | LMiss scs hints =>
      match know_lookupABI bc kx segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extKB bc v, flat_scB bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss, [])
      | LMiss scs' hints' =>
          (* [comment removed for export] *)
          let i := s_next ss in
          (* [comment removed for export] *)
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let rvx := match sc_reads scr with [] => mkExt sx' 0 n (EVar i) | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rvx, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i,
                if rec_onb (bc_fk bc) then [krec a n rv] else [])   (* [comment removed for export] *)
      end
  end.
Definition sym_readBI (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match sym_readRBI segs ss bc kx scr a n sx' with
  | Some (v, scs, scr', nx', _) => Some (v, scs, scr', nx')
  | None => None
  end.


Definition sym_stepBI (bc : bctx) (kx : kix) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_signedF imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluwKB bc ALU_ADD (g rs) (ELit (bv_signedF imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (sset ss rd (mkMdKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (sset ss rd (ELit (bvu64 (Z.shiftl (bv_signedF imm) 12))) (p + 4)) [] scr
  | Auipc rd imm => SOk (sset ss rd (ELit (bvu64 (Z.shiftl (bv_signedF imm) 12 + p))) (p + 4)) [] scr
  | Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (bvu64 (p + bv_signedF imm))) [] scr
  | Jalr rd rs1 imm =>
      match conc_exprB bc (g rs1) with
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (jalrF z (bv_signedF imm))) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let tk := bvu64 (p + bv_signedF imm) in
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
      let a := to_saddrKB bc (g rs) (bv_signedF imm) in
      match sym_readRBI segs ss bc kx scr a n sx' with
      | None => SStop
      | Some (v, scs, scr', nx', recs) =>
          SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                   (s_log ss) (recs ++ s_know ss) nx' (s_resv ss)) scs scr'   (* [comment removed for export] *)
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrKB bc (g rs1) (bv_signedF imm) in
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


Lemma sym_readRBI_eqf : forall segs ss bc, sym_readRBI segs ss bc (mk_kix (s_know ss)) = sym_readRB segs ss bc.
Proof. intros. bcfe. unfold sym_readRBI, sym_readRB. rewrite know_lookupABI_eq. reflexivity. Qed.
Lemma sym_readBI_eqf : forall segs ss bc, sym_readBI segs ss bc (mk_kix (s_know ss)) = sym_readB segs ss bc.
Proof. intros. bcfe. unfold sym_readBI, sym_readB. rewrite sym_readRBI_eqf. reflexivity. Qed.
Lemma sym_stepBI_eq : forall bc segs i ss scr,
  sym_stepBI bc (mk_kix (s_know ss)) segs i ss scr = sym_stepB bc segs i ss scr.
Proof. intros. unfold sym_stepBI, sym_stepB. rewrite sym_readRBI_eqf, sym_readBI_eqf. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xinside_num_r1B (bc : bctx) (r1 : option (Z * Z)) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match xloB bc b2, xhiB bc b2 with
  | Some lo2, Some hi2 =>
      if Z.eqb lo2 hi2 then
        match r1, xhiB bc n1, xloB bc n2 with
        | Some (lo1, hi1), Some h1, Some l2 =>
            if (Z.leb (lo2 + k2) (lo1 + k1) && Z.leb (hi1 + k1 + h1) (lo2 + k2 + l2))%bool then true
            else if (Z.leb (lo2 + k2) (lo1 + k1) && Z.leb 0 (lo1 + k1) && Z.ltb (hi1 + k1 + h1) two64)%bool   (* [comment removed for export] *)
                 then match xhiB bc (EAlu ALU_ADD (EAlu ALU_ADD b1 (ELit k1)) n1) with
                      | Some e => Z.leb e (lo2 + k2 + l2)
                      | None => false
                      end
                 else false
        | _, _, _ => false
        end
      else false
  | _, _ => false
  end.
Definition xinside_r1B (bc : bctx) (r1 : option (Z * Z)) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if shares_var b1 b2 then xinside0B bc b1 k1 n1 b2 k2 n2
  else if novars b2 then xinside_num_r1B bc r1 b1 k1 n1 b2 k2 n2 else false.
Lemma xinside_r1B_eq : forall bc b1 k1 n1 b2 k2 n2,
  xinside_r1B bc (base_rangeB bc b1) b1 k1 n1 b2 k2 n2 = xinsideB bc b1 k1 n1 b2 k2 n2.
Proof. reflexivity. Qed.

Fixpoint know_lookupA0RB (bc : bctx) (r1 : option (Z * Z)) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  let know_lookup := know_lookupA0RB bc r1 in
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
              match rel_litZ rb rk (Z.of_nat n) kb kk l0 with
              | RInside _ => LHit (ELit 0) acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  (* [comment removed for export] *)
                  if xinside_r1B bc r1 rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
                  match hints with
                  | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinside_r1B bc r1 rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
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
              match rel_litZ rb rk (Z.of_nat n) kb kk l0 with
              | RInside _ => LHit hit acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  if xinside_r1B bc r1 rb rk (elen n) kb kk len then LHit hit acc hints else
                  match hints with
                  | true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinside_r1B bc r1 rb rk (elen n) kb kk len then LHit hit acc hints else
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


Lemma know_lookupA0RB_eqf : forall bc segs rb kn,
  know_lookupA0RB bc (base_rangeB bc rb) segs kn rb = know_lookupA0B bc segs kn rb.
Proof.
  intros bc segs rb kn. induction kn as [|K rest IH]; [reflexivity|].
  cbn [know_lookupA0RB know_lookupA0B]. rewrite IH. reflexivity.
Qed.
Lemma know_lookupA0RB_eq : forall bc segs kn rb rk n sx hints acc,
  know_lookupA0RB bc (base_rangeB bc rb) segs kn rb rk n sx hints acc = know_lookupA0B bc segs kn rb rk n sx hints acc.
Proof. intros. rewrite know_lookupA0RB_eqf. reflexivity. Qed.
Definition know_lookupA0RI (bc : bctx) (r1 : option (Z * Z)) (kx : kix) (segs : list Segment) (rb : expr) (rk : Z)
           (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match hints, n with
  | [], S _ => know_lookupA0RB bc r1 segs (kx_select kx rb rk) rb rk n sx [] acc
  | _, _ => know_lookupA0RB bc r1 segs (kx_kn kx) rb rk n sx hints acc
  end.
Lemma know_lookupA0RI_eqf : forall bc kx segs rb rk n sx,
  know_lookupA0RI bc (base_rangeB bc rb) kx segs rb rk n sx = know_lookupA0I bc kx segs rb rk n sx.
Proof.
  intros. apply functional_extensionality; intros hints. apply functional_extensionality; intros acc.
  unfold know_lookupA0RI, know_lookupA0I. rewrite !know_lookupA0RB_eqf. reflexivity.
Qed.
Definition know_lookupABRI (bc : bctx) (r1 : option (Z * Z)) (kx : kix) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match know_lookupA0RB bc r1 segs (krec_head kn) rb rk n sx hints acc with   (* [comment removed for export] *)
  | LMiss acc0 hints0 =>
  match know_lookupA0RI bc r1 kx segs rb rk n sx hints0 acc0 with
  | LMiss acc' hints' =>
      match know_bytes_lit segs kn rb rk n with
      | Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
      | None => LMiss acc' hints'
      end
  | r => r
  end
  | r => r
  end.
Lemma know_lookupABRI_eqf : forall bc kx segs kn rb rk n sx,
  know_lookupABRI bc (base_rangeB bc rb) kx segs kn rb rk n sx = know_lookupABI bc kx segs kn rb rk n sx.
Proof.
  intros. apply functional_extensionality; intros hints. apply functional_extensionality; intros acc.
  unfold know_lookupABRI, know_lookupABI. rewrite !know_lookupA0RB_eqf, !know_lookupA0RI_eqf. reflexivity.
Qed.

(* [comment removed for export] *)
Definition r1_thresh (r1 : option (Z * Z)) (rk rn : Z) (r2 : option (Z * Z)) : option (Z * Z) :=
  match r1, r2 with
  | Some (lo1, hi1), Some (lo2, hi2) => Some ((hi1 + rk + rn - lo2)%Z, (lo1 + rk - hi2)%Z)
  | _, _ => None
  end.
Definition thresh_apart (th : option (Z * Z)) (kk w : Z) : bool :=
  match th with Some (t1, t2) => (Z.leb t1 kk || Z.leb (kk + w) t2)%bool | None => false end.
Lemma thresh_apart_eq : forall r1 rk rn bc kb kk w,
  thresh_apart (r1_thresh r1 rk rn (base_rangeB bc kb)) kk w =
  (match r1, base_rangeB bc kb with
   | Some (lo1, hi1), Some (lo2, hi2) => (Z.leb (hi1 + rk + rn) (lo2 + kk) || Z.leb (hi2 + kk + w) (lo1 + rk))%bool
   | _, _ => false
   end).
Proof.
  intros. unfold thresh_apart, r1_thresh. destruct r1 as [[lo1 hi1]|]; [|reflexivity].
  destruct (base_rangeB bc kb) as [[lo2 hi2]|]; [|reflexivity].
  f_equal; apply Bool.eq_true_iff_eq; rewrite !Z.leb_le; lia.
Qed.
Definition LMEMO_OK (bc : bctx) (r1 : option (Z * Z)) (rk rn : Z) (memo : list (expr * option (Z * Z))) : Prop :=
  forall kb th, brt_lookup memo kb = Some th -> th = r1_thresh r1 rk rn (base_rangeB bc kb).
Fixpoint log_lookupRB2 (bc : bctx) (r1 : option (Z * Z)) (memo : list (expr * option (Z * Z))) (log : list sentry)
         (rb : expr) (rk : Z) (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupRB2 bc r1 memo rest rb rk n sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          let '(th, memo') := match brt_lookup memo kb with
                              | Some th => (th, memo)
                              | None => let th := r1_thresh r1 rk (Z.of_nat n) (base_rangeB bc kb) in (th, (kb, th) :: memo)
                              end in
          if thresh_apart th kk (Z.of_nat w) then log_lookupRB2 bc r1 memo' rest rb rk n sx hints acc
          else if kdisj_apartB bc (bc_kd bc) rb rk (Z.of_nat n) kb kk (Z.of_nat w) then log_lookupRB2 bc r1 memo' rest rb rk n sx hints acc
          else if lin_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w) then log_lookupRB2 bc r1 memo' rest rb rk n sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupRB2 bc r1 memo' rest rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
          end
      end
  end.
Lemma log_lookupRB2_eq : forall bc r1 log rb rk n sx hints acc memo,
  LMEMO_OK bc r1 rk (Z.of_nat n) memo ->
  log_lookupRB2 bc r1 memo log rb rk n sx hints acc = log_lookupRB bc r1 log rb rk n sx hints acc.
Proof.
  intros bc r1 log rb rk n sx. induction log as [|[[kb kk] w v] rest IH]; intros hints acc memo HM; [reflexivity|].
  cbn [log_lookupRB2 log_lookupRB].
  destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)); try reflexivity; [apply IH; exact HM|].
  assert (STEP : forall th memo', th = r1_thresh r1 rk (Z.of_nat n) (base_rangeB bc kb) -> LMEMO_OK bc r1 rk (Z.of_nat n) memo' ->
    (if thresh_apart th kk (Z.of_nat w) then log_lookupRB2 bc r1 memo' rest rb rk n sx hints acc
     else if kdisj_apartB bc (bc_kd bc) rb rk (Z.of_nat n) kb kk (Z.of_nat w) then log_lookupRB2 bc r1 memo' rest rb rk n sx hints acc
     else if lin_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w) then log_lookupRB2 bc r1 memo' rest rb rk n sx hints acc
     else match hints with
          | false :: _ => LStuck
          | _ => log_lookupRB2 bc r1 memo' rest rb rk n sx (tl hints) (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
          end)
    = (if ranges_apart_r1B bc r1 rb rk (Z.of_nat n) kb kk (Z.of_nat w) then log_lookupRB bc r1 rest rb rk n sx hints acc
       else match hints with
            | false :: _ => LStuck
            | _ => log_lookupRB bc r1 rest rb rk n sx (tl hints) (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
            end)).
  { intros th memo' -> HM'. rewrite thresh_apart_eq. unfold ranges_apart_r1B.
    destruct (match r1, base_rangeB bc kb with
              | Some (lo1, hi1), Some (lo2, hi2) => (Z.leb (hi1 + rk + Z.of_nat n) (lo2 + kk) || Z.leb (hi2 + kk + Z.of_nat w) (lo1 + rk))%bool
              | _, _ => false end); [apply IH; exact HM'|].
    destruct (kdisj_apartB _ _ _ _ _ _ _ _); [apply IH; exact HM'|].
    destruct (lin_apartB _ _ _ _ _ _ _); [apply IH; exact HM'|].
    destruct hints as [|[|] hs]; first [reflexivity | apply IH; exact HM']. }
  destruct (brt_lookup memo kb) as [th|] eqn:HL.
  - apply STEP; [exact (HM _ _ HL)|exact HM].
  - apply STEP; [reflexivity|].
    intros kb' th' H'. cbn [brt_lookup] in H'. destruct (expr_eqb kb' kb) eqn:E.
    + injection H' as <-. apply p_expr_eqb_eq in E. subst kb'. reflexivity.
    + exact (HM _ _ H').
Qed.
Lemma LMEMO_OK_nil : forall bc r1 rk rn, LMEMO_OK bc r1 rk rn [].
Proof. intros bc r1 rk rn kb th H. discriminate H. Qed.

Definition sym_readRBI2 (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat * list kentry) :=
  let r1 := base_rangeB bc (a_base a) in
  match log_lookupRB2 bc r1 [] (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
  | LStuck => None
  | LHit v scs hints =>
      Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss, [])
  | LMiss scs hints =>
      match know_lookupABRI bc r1 kx segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extKB bc v, flat_scB bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss, [])
      | LMiss scs' hints' =>
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let rvx := match sc_reads scr with [] => mkExt sx' 0 n (EVar i) | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rvx, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i,
                if rec_onb (bc_fk bc) then [krec a n rv] else [])
      end
  end.
Lemma sym_readRBI2_eq : forall segs ss bc kx, sym_readRBI2 segs ss bc kx = sym_readRBI segs ss bc kx.
Proof.
  intros. bcfe. unfold sym_readRBI2, sym_readRBI. cbv zeta.
  rewrite (log_lookupRB2_eq _ _ _ _ _ _ _ _ _ _ (LMEMO_OK_nil _ _ _ _)), know_lookupABRI_eqf. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kx_relb (rb : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA kb _) _ _ | KBlob (SA kb _) _ _ => expr_eqb rb kb
  | KZero (SA kb _) _ | KFill (SA kb _) _ _ => (expr_eqb rb kb || shares_var rb kb || novars kb)%bool
  | _ => false
  end.
Lemma xinside_r1B_other : forall bc r1 b1 k1 n1 b2 k2 n2,
  shares_var b1 b2 = false -> novars b2 = false -> xinside_r1B bc r1 b1 k1 n1 b2 k2 n2 = false.
Proof. intros. unfold xinside_r1B. rewrite H, H0. reflexivity. Qed.
Lemma know_lookupA0RB_skipr : forall bc r1 segs K rest rb rk n sx acc,
  is_lit0 rb = false -> kx_relb rb K = false ->
  know_lookupA0RB bc r1 segs (K :: rest) rb rk (S n) sx [] acc = know_lookupA0RB bc r1 segs rest rb rk (S n) sx [] acc.
Proof.
  intros bc r1 segs K rest rb rk n sx acc Hrb HC.
  cbn [know_lookupA0RB]. rewrite ?rel_litZ_eqf. cbv beta. unfold kx_relb in HC.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
    try reflexivity.
  - rewrite rel_lit_other by exact HC. reflexivity.
  - apply Bool.orb_false_iff in HC as [HC H3]. apply Bool.orb_false_iff in HC as [H1 H2].
    rewrite (xinside_r1B_other _ _ _ _ _ _ _ _ H2 H3).
    destruct len as [l0| | | | | | |]; try reflexivity. rewrite rel_lit_other by exact H1. reflexivity.
  - rewrite HC. reflexivity.
  - destruct rb as [z| | | | | | |]; try reflexivity. cbn in Hrb. destruct z; try reflexivity. discriminate.
  - apply Bool.orb_false_iff in HC as [HC H3]. apply Bool.orb_false_iff in HC as [H1 H2].
    cbv zeta. rewrite (xinside_r1B_other _ _ _ _ _ _ _ _ H2 H3).
    destruct len as [l0| | | | | | |]; try reflexivity. rewrite rel_lit_other by exact H1. reflexivity.
Qed.
Lemma know_lookupA0RB_filterr : forall bc r1 segs l rb rk n sx acc,
  is_lit0 rb = false ->
  know_lookupA0RB bc r1 segs (List.filter (kx_relb rb) l) rb rk (S n) sx [] acc = know_lookupA0RB bc r1 segs l rb rk (S n) sx [] acc.
Proof.
  intros bc r1 segs l rb rk n sx acc Hrb. revert acc. induction l as [|K rest IH]; intros acc; [reflexivity|].
  cbn [List.filter]. destruct (kx_relb rb K) eqn:HC.
  - cbn [know_lookupA0RB]. rewrite !IH.
    destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity.
  - rewrite know_lookupA0RB_skipr by assumption. apply IH.
Qed.

Definition qmemo : Type := list (expr * list kentry).
Fixpoint qm_lookup (qm : qmemo) (rb : expr) : option (list kentry) :=
  match qm with
  | [] => None
  | (b, l) :: rest => if expr_eqb rb b then Some l else qm_lookup rest rb
  end.
Definition QM_OK (kx : kix) (qm : qmemo) : Prop :=
  forall rb l, qm_lookup qm rb = Some l -> l = List.filter (kx_relb rb) (kx_wf kx).
Lemma QM_OK_nil : forall kx, QM_OK kx [].
Proof. intros kx rb l H. discriminate H. Qed.
(* [comment removed for export] *)
Definition kx_cands (kx : kix) (qm : qmemo) (rb : expr) (rk : Z) : list kentry * qmemo :=
  if is_lit0 rb then (kx_merge (kx_bucket (kx_gran kx) (gran rk)) (kx_w0 kx), qm)
  else match qm_lookup qm rb with
       | Some l => (l, qm)
       | None => let l := List.filter (kx_relb rb) (kx_wf kx) in (l, (rb, l) :: qm)
       end.
Lemma kx_cands_ok : forall kx qm rb rk l qm',
  QM_OK kx qm -> kx_cands kx qm rb rk = (l, qm') ->
  QM_OK kx qm' /\ l = (if is_lit0 rb then kx_select kx rb rk else List.filter (kx_relb rb) (kx_wf kx)).
Proof.
  intros kx qm rb rk l qm' HQ H. unfold kx_cands in H. unfold kx_select.
  destruct (is_lit0 rb) eqn:L.
  - injection H as <- <-. split; [exact HQ|reflexivity].
  - destruct (qm_lookup qm rb) as [l0|] eqn:HL.
    + injection H as <- <-. split; [exact HQ|]. exact (HQ _ _ HL).
    + injection H as <- <-. split; [|reflexivity].
      intros rb' l' H'. cbn [qm_lookup] in H'. destruct (expr_eqb rb' rb) eqn:E.
      * injection H' as <-. apply p_expr_eqb_eq in E. subst rb'. reflexivity.
      * exact (HQ _ _ H').
Qed.
(* [comment removed for export] *)
Fixpoint know_lookupW (bc : bctx) (r1 : option (Z * Z)) (segs : list Segment) (l : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match l with
  | [] => LMiss acc hints
  | KWord (SA kb kk) w v :: rest =>
      if (if Z.leb kk rk then Z.leb (rk + Z.of_nat n) (kk + Z.of_nat w) else false)
      then LHit (mkExt sx (Z.to_nat (rk - kk)) n v) acc hints
      else know_lookupW bc r1 segs rest rb rk n sx hints acc
  | K :: rest =>
      match know_lookupA0RB bc r1 segs [K] rb rk n sx hints acc with
      | LMiss acc' hints' => know_lookupW bc r1 segs rest rb rk n sx hints' acc'
      | r => r
      end
  end.
Lemma know_lookupA0RB_step : forall bc r1 segs K rest rb rk n sx hints acc,
  know_lookupA0RB bc r1 segs (K :: rest) rb rk n sx hints acc
  = match know_lookupA0RB bc r1 segs [K] rb rk n sx hints acc with
    | LMiss acc' hints' => know_lookupA0RB bc r1 segs rest rb rk n sx hints' acc'
    | r => r
    end.
Proof.
  intros. cbn [know_lookupA0RB].
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity.
  - destruct (rel_lit _ _ _ _ _ _); reflexivity.
  - destruct len; try (destruct (rel_litZ _ _ _ _ _ _)); try reflexivity;
      repeat match goal with |- context [if ?c then _ else _] => destruct c; try reflexivity end;
      destruct hints as [|[|] hs]; reflexivity.
  - destruct (expr_eqb rb kb); [|reflexivity]. destruct (Z.leb kk rk); [|reflexivity].
    destruct len; repeat match goal with |- context [if ?c then _ else _] => destruct c; try reflexivity end;
      try (destruct hints as [|[|] hs]; reflexivity).
  - destruct rb; try reflexivity. destruct z; try reflexivity.
    destruct (Z.leb lo rk && Z.leb (rk + Z.of_nat n) hi)%bool; [|reflexivity]. destruct (img_bytes segs rk n); reflexivity.
  - destruct len; try (destruct (rel_litZ _ _ _ _ _ _)); try reflexivity;
      repeat match goal with |- context [if ?c then _ else _] => destruct c; try reflexivity end;
      destruct hints as [|[|] hs]; reflexivity.
Qed.
Lemma know_lookupW_eq : forall bc r1 segs l rb rk n sx hints acc,
  (forall kb kk w v, In (KWord (SA kb kk) w v) l -> expr_eqb rb kb = true) ->
  know_lookupW bc r1 segs l rb rk n sx hints acc = know_lookupA0RB bc r1 segs l rb rk n sx hints acc.
Proof.
  intros bc r1 segs l rb rk n sx. induction l as [|K rest IH]; intros hints acc HW; [reflexivity|].
  assert (IH' : forall hints' acc', know_lookupW bc r1 segs rest rb rk n sx hints' acc' = know_lookupA0RB bc r1 segs rest rb rk n sx hints' acc')
    by (intros; apply IH; intros kb kk w v Hin; apply (HW kb kk w v); right; exact Hin).
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
    try (cbn [know_lookupW]; rewrite (know_lookupA0RB_step bc r1 segs _ rest); match goal with |- match ?X with _ => _ end = _ => destruct X end; try reflexivity; apply IH').
  cbn [know_lookupW know_lookupA0RB]. unfold rel_lit. rewrite (HW kb kk w v (or_introl eq_refl)).
  destruct (Z.leb kk rk) eqn:E1; cbn [andb].
  - destruct (Z.leb (rk + Z.of_nat n) (kk + Z.of_nat w)) eqn:E2; [reflexivity|].
    rewrite IH'. destruct (Z.leb (rk + Z.of_nat n) kk || Z.leb (kk + Z.of_nat w) rk)%bool; reflexivity.
  - rewrite IH'. destruct (Z.leb (rk + Z.of_nat n) kk || Z.leb (kk + Z.of_nat w) rk)%bool; reflexivity.
Qed.
Definition know_lookupA0RIq (bc : bctx) (r1 : option (Z * Z)) (kx : kix) (qm : qmemo) (segs : list Segment) (rb : expr) (rk : Z)
           (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres * qmemo :=
  match hints, n with
  | [], S _ => let '(l, qm') := kx_cands kx qm rb rk in
               ((if is_lit0 rb then know_lookupA0RB bc r1 segs l rb rk n sx [] acc
                 else know_lookupW bc r1 segs l rb rk n sx [] acc), qm')   (* [comment removed for export] *)
  | _, _ => (know_lookupA0RB bc r1 segs (kx_kn kx) rb rk n sx hints acc, qm)
  end.
Lemma know_lookupA0RIq_eq : forall bc r1 kx qm segs rb rk n sx hints acc,
  QM_OK kx qm ->
  fst (know_lookupA0RIq bc r1 kx qm segs rb rk n sx hints acc) = know_lookupA0RI bc r1 kx segs rb rk n sx hints acc
  /\ QM_OK kx (snd (know_lookupA0RIq bc r1 kx qm segs rb rk n sx hints acc)).
Proof.
  intros bc r1 kx qm segs rb rk n sx hints acc HQ. unfold know_lookupA0RIq, know_lookupA0RI.
  destruct hints as [|h hs]; [|split; [reflexivity|exact HQ]]. destruct n as [|n]; [split; [reflexivity|exact HQ]|].
  destruct (kx_cands kx qm rb rk) as [l qm'] eqn:HC. cbn [fst snd].
  destruct (kx_cands_ok _ _ _ _ _ _ HQ HC) as [HQ' ->]. split; [|exact HQ'].
  unfold kx_select. destruct (is_lit0 rb) eqn:L; [reflexivity|].
  rewrite know_lookupW_eq; [apply know_lookupA0RB_filterr; exact L|].
  intros kb kk w v Hin. apply filter_In in Hin as [_ Hr]. exact Hr.
Qed.
Definition know_lookupABRIq (bc : bctx) (r1 : option (Z * Z)) (kx : kix) (qm : qmemo) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres * qmemo :=
  match know_lookupA0RB bc r1 segs (krec_head kn) rb rk n sx hints acc with   (* [comment removed for export] *)
  | LMiss acc0 hints0 =>
  let '(r, qm') := know_lookupA0RIq bc r1 kx qm segs rb rk n sx hints0 acc0 in
  (match r with
   | LMiss acc' hints' =>
      match know_bytes_lit segs kn rb rk n with
      | Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
      | None => LMiss acc' hints'
      end
   | r => r
   end, qm')
  | r => (r, qm)
  end.
Lemma know_lookupABRIq_eq : forall bc r1 kx qm segs kn rb rk n sx hints acc,
  QM_OK kx qm ->
  fst (know_lookupABRIq bc r1 kx qm segs kn rb rk n sx hints acc) = know_lookupABRI bc r1 kx segs kn rb rk n sx hints acc
  /\ QM_OK kx (snd (know_lookupABRIq bc r1 kx qm segs kn rb rk n sx hints acc)).
Proof.
  intros bc r1 kx qm segs kn rb rk n sx hints acc HQ. unfold know_lookupABRIq, know_lookupABRI.
  destruct (know_lookupA0RB bc r1 segs (krec_head kn) rb rk n sx hints acc) as [|acc0 hints0|]; try (split; [reflexivity|exact HQ]).
  destruct (know_lookupA0RIq_eq bc r1 kx qm segs rb rk n sx hints0 acc0 HQ) as [E HQ'].
  destruct (know_lookupA0RIq bc r1 kx qm segs rb rk n sx hints0 acc0) as [r qm']. cbn [fst snd] in E, HQ' |- *. subst r.
  split; [|exact HQ']. destruct (know_lookupA0RI _ _ _ _ _ _ _ _ _ _); reflexivity.
Qed.

Definition sym_readRBI3 (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (qm : qmemo) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat * list kentry) * qmemo :=
  let r1 := base_rangeB bc (a_base a) in
  match log_lookupRB2 bc r1 [] (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
  | LStuck => (None, qm)
  | LHit v scs hints =>
      (Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss, []), qm)
  | LMiss scs hints =>
      let '(r, qm') := know_lookupABRIq bc r1 kx qm segs (s_know ss) (a_base a) (a_off a) n sx' hints scs in
      (match r with
       | LStuck => None
       | LHit v scs' hints' =>
          Some (extKB bc v, flat_scB bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss, [])
       | LMiss scs' hints' =>
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let rvx := match sc_reads scr with [] => mkExt sx' 0 n (EVar i) | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rvx, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i,
                if rec_onb (bc_fk bc) then [krec a n rv] else [])
       end, qm')
  end.
Lemma sym_readRBI3_eq : forall segs ss bc kx qm scr a n sx',
  QM_OK kx qm ->
  fst (sym_readRBI3 segs ss bc kx qm scr a n sx') = sym_readRBI segs ss bc kx scr a n sx'
  /\ QM_OK kx (snd (sym_readRBI3 segs ss bc kx qm scr a n sx')).
Proof.
  intros segs ss bc kx qm scr a n sx' HQ. rewrite <- sym_readRBI2_eq. unfold sym_readRBI3, sym_readRBI2. cbv zeta.
  destruct (log_lookupRB2 _ _ _ _ _ _ _ _ _ _) as [|scs hints|]; try (split; [reflexivity|exact HQ]).
  destruct (know_lookupABRIq_eq bc (base_rangeB bc (a_base a)) kx qm segs (s_know ss) (a_base a) (a_off a) n sx' hints scs HQ) as [E HQ'].
  destruct (know_lookupABRIq _ _ _ _ _ _ _ _ _ _ _ _) as [r qm']. cbn [fst snd] in E, HQ' |- *. subst r.
  split; [|exact HQ']. destruct (know_lookupABRI _ _ _ _ _ _ _ _ _ _ _); reflexivity.
Qed.
Definition sym_readBI3 (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (qm : qmemo) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) * qmemo :=
  let '(r, qm') := sym_readRBI3 segs ss bc kx qm scr a n sx' in
  (match r with
   | Some (v, scs, scr', nx', _) => Some (v, scs, scr', nx')
   | None => None
   end, qm').
Lemma sym_readBI3_eq : forall segs ss bc kx qm scr a n sx',
  QM_OK kx qm ->
  fst (sym_readBI3 segs ss bc kx qm scr a n sx') = sym_readBI segs ss bc kx scr a n sx'
  /\ QM_OK kx (snd (sym_readBI3 segs ss bc kx qm scr a n sx')).
Proof.
  intros segs ss bc kx qm scr a n sx' HQ. unfold sym_readBI3, sym_readBI.
  destruct (sym_readRBI3_eq segs ss bc kx qm scr a n sx' HQ) as [E HQ'].
  destruct (sym_readRBI3 _ _ _ _ _ _ _ _ _) as [r qm']. cbn [fst snd] in E, HQ' |- *. subst r.
  split; [reflexivity|exact HQ'].
Qed.

(* [comment removed for export] *)
Definition sym_stepBI3 (bc : bctx) (kx : kix) (qm : qmemo) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts)
  : stepres * qmemo :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in
      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrKB bc (g rs) (bv_signedF imm) in
      let '(r, qm') := sym_readRBI3 segs ss bc kx qm scr a n sx' in
      (match r with
       | None => SStop
       | Some (v, scs, scr', nx', recs) =>
          SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                   (s_log ss) (recs ++ s_know ss) nx' (s_resv ss)) scs scr'
       end, qm')
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        let '(r, qm') := sym_readBI3 segs ss bc kx qm scr a n (amo_sx wd) in
        (match r with
         | None => SStop
         | Some (v, scs, scr', nx') =>
            SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                     (s_log ss) (s_know ss) nx' (Some a)) scs scr'
         end, qm')
      else (SStop, qm)
  | Amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | None => (SStop, qm)
      | Some aop =>
          let n := msize_bytes (amo_sz wd) in
          let e := g rs1 in
          if amo_alignedbB bc e wd then
            let a := to_saddrKB bc e 0 in
            match resv_inval (s_resv ss) a with
            | None => (SStop, qm)
            | Some r' =>
                let '(r, qm') := sym_readBI3 segs ss bc kx qm scr a n (amo_sx wd) in
                (match r with
                 | None => SStop
                 | Some (vold, scs, scr', nx') =>
                    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
                             (SE a n (amo_newvalB bc wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
                        (scs ++ storeok_scB bc a n) scr'
                 end, qm')
            end
          else (SStop, qm)
      end
  | _ => (sym_stepBI bc kx segs i ss scr, qm)
  end.
Lemma sym_stepBI3_eq : forall bc kx qm segs i ss scr,
  QM_OK kx qm ->
  fst (sym_stepBI3 bc kx qm segs i ss scr) = sym_stepBI bc kx segs i ss scr
  /\ QM_OK kx (snd (sym_stepBI3 bc kx qm segs i ss scr)).
Proof.
  intros bc kx qm segs i ss scr HQ. unfold sym_stepBI3.
  destruct i; try (split; [reflexivity|exact HQ]); cbv zeta; unfold sym_stepBI.
  - (* [comment removed for export] *)
    match goal with |- context [sym_readRBI3 ?sg ?s ?b ?k ?q ?sc ?a ?n ?sx] =>
      destruct (sym_readRBI3_eq sg s b k q sc a n sx HQ) as [E HQ'];
      destruct (sym_readRBI3 sg s b k q sc a n sx) as [r qm']; cbn [fst snd] in E, HQ' |- *; rewrite <- E end.
    split; [destruct r as [[[[[? ?] ?] ?] ?]|]; reflexivity | exact HQ'].
  - (* [comment removed for export] *)
    destruct (amo_alignedbB _ _ _); [|split; [reflexivity|exact HQ]].
    match goal with |- context [sym_readBI3 ?sg ?s ?b ?k ?q ?sc ?a ?n ?sx] =>
      destruct (sym_readBI3_eq sg s b k q sc a n sx HQ) as [E HQ'];
      destruct (sym_readBI3 sg s b k q sc a n sx) as [r qm']; cbn [fst snd] in E, HQ' |- *; rewrite <- E end.
    split; [destruct r as [[[[? ?] ?] ?]|]; reflexivity | exact HQ'].
  - (* [comment removed for export] *)
    destruct (amo_aluop _); [|split; [reflexivity|exact HQ]].
    destruct (amo_alignedbB _ _ _); [|split; [reflexivity|exact HQ]].
    destruct (resv_inval _ _); [|split; [reflexivity|exact HQ]].
    match goal with |- context [sym_readBI3 ?sg ?s ?b ?k ?q ?sc ?a ?n ?sx] =>
      destruct (sym_readBI3_eq sg s b k q sc a n sx HQ) as [E HQ'];
      destruct (sym_readBI3 sg s b k q sc a n sx) as [r qm']; cbn [fst snd] in E, HQ' |- *; rewrite <- E end.
    split; [destruct r as [[[[? ?] ?] ?]|]; reflexivity | exact HQ'].
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
Proof. intros. bcfe. unfold mkSrlB, mkSrl. (repeat first [ rewrite erangeB_eqf | rewrite lin_nowrapB_eqf | rewrite lin_nowrap_lB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite mkSrlB_eqf : bceq.
Lemma lowbitsB_eqf : forall fk, lowbitsB (mkbc fk) = lowbits fk.
Proof.
  intros fk. apply functional_extensionality; intros e.
  induction e; bcfe; cbn [lowbitsB lowbits]; rewrite ?IHe1, ?IHe2, ?IHe; (repeat first [ rewrite ealignB_eqf | rewrite lin_lowbits_knB_eqf ]); reflexivity.
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
Proof. intros. bcfe. unfold and_high_splitB, and_high_split. (repeat first [ rewrite erangeB_eqf | rewrite mkSrlB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite and_high_splitB_eqf : bceq.
Lemma and_low_splitB_eqf : forall fk, and_low_splitB (mkbc fk) = and_low_split fk.
Proof. intros. bcfe. unfold and_low_splitB, and_low_split. (repeat first [ rewrite erangeB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite and_low_splitB_eqf : bceq.
Lemma narrow_maskB_eqf : forall fk, narrow_maskB (mkbc fk) = narrow_mask fk.
Proof. intros. bcfe. unfold narrow_maskB, narrow_mask. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite narrow_maskB_eqf : bceq.
Lemma mkAnd0B_eqf : forall fk, mkAnd0B (mkbc fk) = mkAnd0 fk.
Proof. intros. bcfe. unfold mkAnd0B, mkAnd0. (repeat first [ rewrite ealignB_eqf | rewrite coeffs_divkB_eqf | rewrite lin_lowbits_knB_eqf | rewrite mkSrlB_eqf | rewrite lowbitsB_eqf | rewrite lsplit_divB_eqf | rewrite and_high_splitB_eqf | rewrite and_low_splitB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite mkAnd0B_eqf : bceq.
Lemma mkAndB_eqf : forall fk, mkAndB (mkbc fk) = mkAnd fk.
Proof. intros. bcfe. unfold mkAndB, mkAnd. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkAndB_eqf : bceq.
Lemma mkAndKB_eqf : forall fk, mkAndKB (mkbc fk) = mkAndK fk.
Proof. intros. bcfe. unfold mkAndKB, mkAndK. (repeat first [ rewrite mkAndB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite mkAndKB_eqf : bceq.
Lemma or_disjointB_eqf : forall fk, or_disjointB (mkbc fk) = or_disjoint fk.
Proof. intros. bcfe. unfold or_disjointB, or_disjoint. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite or_disjointB_eqf : bceq.
Lemma mkOrB_eqf : forall fk, mkOrB (mkbc fk) = mkOr fk.
Proof. intros. bcfe. unfold mkOrB, mkOr. (repeat first [ rewrite mkAndKB_eqf | rewrite or_disjointB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite mkOrB_eqf : bceq.
Lemma base_rangeB_nonlit : forall fk s, closedb s = false -> base_rangeB (mkbc fk) s = erangeB (mkbc fk) s.
Proof.
  intros fk s H. rewrite base_rangeB_eqf, erangeB_eqf. unfold base_range. destruct s; try reflexivity. cbn in H. discriminate.
Qed.
Lemma conc_tryB_eqf : forall fk, conc_tryB (mkbc fk) = conc_try fk.
Proof.
  intros fk. apply functional_extensionality; intros e. apply functional_extensionality; intros cands. 
  induction cands as [|s rest IH]; intros; bcfe; [reflexivity|].
  cbn [conc_tryB conc_try]. rewrite IH. destruct (closedb s) eqn:C; [reflexivity|].
  cbv zeta. rewrite mdef_markS, evalM_markSf, probeM_eqf, all_eval_toM_eqf, (base_rangeB_nonlit fk s C).
  autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite conc_tryB_eqf : bceq.
Lemma concretizeB_eqf : forall fk, concretizeB (mkbc fk) = concretize fk.
Proof. intros. bcfe. unfold concretizeB, concretize. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite concretizeB_eqf : bceq.
(* [comment removed for export] *)
Lemma evalS_self : forall e z, evalS e z e = Some z.
Proof. intros e z. destruct e; cbn [evalS]; rewrite kx_expr_eqb_refl; reflexivity. Qed.
Lemma evalS_def_self : forall e, evalS_def e e = true.
Proof. intros e. destruct e; cbn [evalS_def]; rewrite kx_expr_eqb_refl; reflexivity. Qed.
Lemma wrap64_mod : forall z, wrap64 z = (z mod two64)%Z.
Proof.
  intros z. unfold wrap64. destruct (Z.leb 0 z && Z.ltb z two64)%bool eqn:E; [|reflexivity].
  apply andb_prop in E as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. symmetry. apply Z.mod_small. lia.
Qed.
Lemma wrap64_eqb_near : forall lo hi, (0 < hi - lo <= conc_limit)%Z -> Z.eqb (wrap64 hi) (wrap64 lo) = false.
Proof.
  intros lo hi H. rewrite !wrap64_mod. unfold conc_limit in H. unfold two64.
  destruct (Z.eqb_spec (hi mod 2 ^ 64) (lo mod 2 ^ 64)) as [E|NE]; [|reflexivity]. exfalso.
  pose proof (Z.div_mod hi (2 ^ 64) ltac:(lia)) as Dh. pose proof (Z.div_mod lo (2 ^ 64) ltac:(lia)) as Dl.
  assert (hi - lo = 2 ^ 64 * (hi / 2 ^ 64 - lo / 2 ^ 64))%Z by lia.
  assert (2 ^ 64 = 18446744073709551616)%Z as P by reflexivity. rewrite P in *. nia.
Qed.
Lemma conc_tryB_self : forall bc e re,
  closedb e = false -> base_rangeB bc e = re ->
  conc_tryB bc e [e] = pivot_self re.
Proof.
  intros bc e re HC HR. cbn [conc_tryB]. cbv zeta. rewrite mdef_markS, evalM_markSf, probeM_eqf, all_eval_toM_eqf.
  rewrite HC, evalS_def_self. cbn [negb]. rewrite HR. unfold pivot_self.
  destruct re as [[lo hi]|]; [|reflexivity].
  destruct (Z.leb (hi - lo) conc_limit) eqn:HW; [|reflexivity]. cbn beta.
  rewrite evalS_self. destruct (Z.ltb hi lo) eqn:HL.
  - replace (Z.to_nat (hi - lo + 1)) with 0%nat by (apply Z.ltb_lt in HL; lia). reflexivity.
  - unfold probeS. rewrite !evalS_self. apply Z.ltb_ge in HL. apply Z.leb_le in HW.
    destruct (Z.eqb_spec hi lo) as [->|NE].
    + rewrite Z.eqb_refl. replace (lo + (lo - lo) / 2)%Z with lo by (rewrite Z.sub_diag; cbn; lia). rewrite Z.eqb_refl.
      replace (Z.to_nat (lo - lo + 1)) with 1%nat by lia. cbn [all_eval_toS]. rewrite evalS_self, Z.eqb_refl. reflexivity.
    + rewrite (wrap64_eqb_near lo hi) by lia. reflexivity.
Qed.
Lemma conc_tryB_app : forall bc e l1 l2,
  conc_tryB bc e (l1 ++ l2) = match conc_tryB bc e l1 with Some v => Some v | None => conc_tryB bc e l2 end.
Proof.
  intros bc e l1 l2. induction l1 as [|s rest IH]; [reflexivity|]. cbn [conc_tryB app]. rewrite IH. cbv zeta.
  destruct (closedb s); [reflexivity|]. destruct (negb (mdef (markS s e))); [reflexivity|].
  destruct (base_rangeB bc s) as [[lo hi]|]; [|reflexivity].
  destruct (Z.leb (hi - lo) conc_limit); [|reflexivity].
  destruct (evalM e (markS s e) (wrap64 lo)) as [v|]; [|reflexivity].
  match goal with |- (if ?c then _ else _) = _ => destruct c; [|reflexivity] end.
  destruct (all_eval_toM e (markS s e) v lo _); reflexivity.
Qed.
Fixpoint ecnt (e : expr) : nat :=
  match e with
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => S (ecnt a + ecnt b)
  | EExt _ _ _ a => S (ecnt a)
  | _ => 1%nat
  end.
Lemma subexprs_split : forall e, subexprs e = subexprs_init e ++ [e].
Proof. intros e. destruct e; cbn [subexprs subexprs_init]; rewrite <- ?app_assoc; reflexivity. Qed.
Lemma subexprs_le : forall e s, In s (subexprs e) -> (ecnt s <= ecnt e)%nat.
Proof.
  induction e; intros s Hs; cbn [subexprs] in Hs;
  repeat (apply in_app_or in Hs; destruct Hs as [Hs|Hs]);
  try (destruct Hs as [<-|[]]); cbn [ecnt]; try lia;
  try (apply IHe1 in Hs; cbn; lia); try (apply IHe2 in Hs; cbn; lia); try (apply IHe in Hs; cbn; lia).
Qed.
Lemma subexprs_init_lt : forall e s, In s (subexprs_init e) -> (ecnt s < ecnt e)%nat.
Proof.
  intros e s Hs. destruct e; cbn [subexprs_init] in Hs; try (destruct Hs);
  repeat (apply in_app_or in Hs; destruct Hs as [Hs|Hs]); try (apply subexprs_le in Hs; cbn; lia).
Qed.
Lemma memE_In_false : forall e l, (forall x, In x l -> x <> e) -> memE e l = false.
Proof.
  intros e l H. induction l as [|x r IH]; [reflexivity|]. cbn. destruct (expr_eqb e x) eqn:E.
  - apply p_expr_eqb_eq in E. exfalso. apply (H x); [left; reflexivity | symmetry; exact E].
  - apply IH. intros y Hy. apply H. right. exact Hy.
Qed.
Lemma nubE_acc_app_last : forall l acc e,
  (forall x, In x l -> x <> e) -> (forall x, In x acc -> x <> e) ->
  nubE_acc (l ++ [e]) acc = nubE_acc l acc ++ [e].
Proof.
  induction l as [|y r IH]; intros acc e Hl Hacc.
  - cbn. rewrite (memE_In_false e acc Hacc). reflexivity.
  - cbn. destruct (memE y acc) eqn:M.
    + apply IH; [intros x Hx; apply Hl; right; exact Hx | exact Hacc].
    + rewrite IH; [reflexivity | intros x Hx; apply Hl; right; exact Hx |].
      intros x [<-|Hx]; [apply Hl; left; reflexivity | apply Hacc; exact Hx].
Qed.
Lemma nubE_subexprs : forall e, nubE (subexprs e) = nubE (subexprs_init e) ++ [e].
Proof.
  intros e. unfold nubE. rewrite subexprs_split. apply nubE_acc_app_last; [|intros x []].
  intros x Hx ->. apply subexprs_init_lt in Hx. lia.
Qed.
Lemma concretize_reB_eq : forall fk e, concretize_reB (mkbc fk) e (erangeB (mkbc fk) e) = concretizeB (mkbc fk) e.
Proof.
  intros fk e. unfold concretize_reB, concretizeB. destruct (closedb e) eqn:HC; [reflexivity|].
  rewrite nubE_subexprs, conc_tryB_app, (conc_tryB_self _ _ _ HC (base_rangeB_nonlit fk e HC)). reflexivity.
Qed.
Lemma foldKB_eqf : forall fk, foldKB (mkbc fk) = foldK fk.
Proof.
  intros. bcfe. unfold foldKB, foldK. cbv zeta. rewrite !concretize_reB_eq. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite foldKB_eqf : bceq.
Lemma lin_periodkB_eqf : forall fk, lin_periodkB (mkbc fk) = lin_periodk fk.   (* [comment removed for export] *)
Proof. intros. bcfe. unfold lin_periodkB, lin_periodk. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_periodkB_eqf : bceq.
Lemma lin_periodB_eqf : forall fk, lin_periodB (mkbc fk) = lin_period fk.
Proof. intros. bcfe. unfold lin_periodB, lin_period. (repeat first [ rewrite erangeB_eqf | rewrite lin_periodkB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite lin_periodB_eqf : bceq.
Lemma ltu_shiftB_eqf : forall fk, ltu_shiftB (mkbc fk) = ltu_shift fk.
Proof. intros. bcfe. unfold ltu_shiftB, ltu_shift. (repeat first [ rewrite lin_testB_eqf | rewrite lin_periodB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite ltu_shiftB_eqf : bceq.
Lemma lin_branchB_eqf : forall fk, lin_branchB (mkbc fk) = lin_branch fk.
Proof. intros. bcfe. unfold lin_branchB, lin_branch. (repeat first [ rewrite erangeB_eqf | rewrite lin_ge0B_eqf | rewrite ltu_shiftB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite lin_branchB_eqf : bceq.
Lemma decide_branchB_eqf : forall fk, decide_branchB (mkbc fk) = decide_branch fk.
Proof. intros. bcfe. unfold decide_branchB, decide_branch. (repeat first [ rewrite lit_branchF_eqf | rewrite erangeB_eqf | rewrite lin_branchB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite decide_branchB_eqf : bceq.
Lemma mkSltB_eqf : forall fk, mkSltB (mkbc fk) = mkSlt fk.
Proof. intros. bcfe. unfold mkSltB, mkSlt. (repeat first [ rewrite decide_branchB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite mkSltB_eqf : bceq.
Lemma roundup_idiom1B_eqf : forall fk, roundup_idiom1B (mkbc fk) = roundup_idiom1 fk.
Proof. intros. bcfe. unfold roundup_idiom1B, roundup_idiom1. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite roundup_idiom1B_eqf : bceq.
Lemma roundup_idiomB_eqf : forall fk, roundup_idiomB (mkbc fk) = roundup_idiom fk.
Proof. intros. bcfe. unfold roundup_idiomB, roundup_idiom. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite roundup_idiomB_eqf : bceq.
Lemma mkAluK0B_eqf : forall fk, mkAluK0B (mkbc fk) = mkAluK0 fk.
Proof. intros. bcfe. unfold mkAluK0B, mkAluK0. (repeat first [ rewrite mkSrlB_eqf | rewrite mkAndB_eqf | rewrite mkAndKB_eqf | rewrite mkOrB_eqf | rewrite mkSltB_eqf | rewrite roundup_idiomB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite mkAluK0B_eqf : bceq.
Lemma mkAluKB_eqf : forall fk, mkAluKB (mkbc fk) = mkAluK fk.
Proof. intros. bcfe. unfold mkAluKB, mkAluK. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkAluKB_eqf : bceq.
Lemma mkMdKB_eqf : forall fk, mkMdKB (mkbc fk) = mkMdK fk.
Proof. intros. bcfe. unfold mkMdKB, mkMdK. (repeat first [ rewrite mkAluKB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite mkMdKB_eqf : bceq.
Lemma zband32B_eqf : forall fk, zband32B (mkbc fk) = zband32 fk.
Proof. intros. bcfe. unfold zband32B, zband32. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite zband32B_eqf : bceq.
Lemma mkAluwK0B_eqf : forall fk, mkAluwK0B (mkbc fk) = mkAluwK0 fk.
Proof. intros. bcfe. unfold mkAluwK0B, mkAluwK0. (repeat first [ rewrite erangeB_eqf | rewrite lin_lowbits_knB_eqf | rewrite zband32B_eqf ]). reflexivity. Qed.
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
  cbn [wr_coveredB wr_covered]. rewrite IH. (repeat first [ rewrite xloB_eqf | rewrite xinsideB_eqf ]). reflexivity.
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
Proof. intros. bcfe. unfold to_saddrKB, to_saddrK. (repeat first [ rewrite concretizeB_eqf ]). reflexivity. Qed.
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
  cbn [log_lookupB log_lookup]. rewrite IH. (repeat first [ rewrite ranges_apartB_eqf ]). reflexivity.
Qed.
#[export] Hint Rewrite log_lookupB_eqf : bceq.
Lemma know_lookupA0B_eqf : forall fk, know_lookupA0B (mkbc fk) = know_lookupA0 fk.
Proof.
  intros fk. apply functional_extensionality; intros segs. apply functional_extensionality; intros kn. 
  induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [know_lookupA0B know_lookupA0]. rewrite IH. (repeat first [ rewrite erangeB_eqf | rewrite xinsideB_eqf ]). rewrite ?rel_litZ_eqf. reflexivity.
Qed.
#[export] Hint Rewrite know_lookupA0B_eqf : bceq.
Lemma know_lookupAB_eqf : forall fk, know_lookupAB (mkbc fk) = know_lookupA fk.
Proof. intros. bcfe. unfold know_lookupAB, know_lookupA. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite know_lookupAB_eqf : bceq.
Lemma sym_readRB_eqf : forall fk segs ss, sym_readRB segs ss (mkbc fk) = sym_readR segs ss fk.
Proof. intros. bcfe. unfold sym_readRB, sym_readR. rewrite log_lookupRB_eq. (repeat first [ rewrite bc_fk_mkbc | rewrite extKB_eqf | rewrite flat_scB_eqf | rewrite log_lookupB_eqf | rewrite know_lookupAB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite sym_readRB_eqf : bceq.
Lemma sym_readB_eqf : forall fk segs ss, sym_readB segs ss (mkbc fk) = sym_read segs ss fk.
Proof. intros. bcfe. unfold sym_readB, sym_read. (repeat first [ rewrite sym_readRB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite sym_readB_eqf : bceq.
Lemma know_lookupB_eqf : forall fk segs, know_lookupB segs (mkbc fk) = know_lookup segs fk.
Proof. intros. bcfe. unfold know_lookupB, know_lookup. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite know_lookupB_eqf : bceq.

Lemma sym_stepB_eq : forall segs i ss scr,
  sym_stepB (mkbc (facts_of (s_know ss))) segs i ss scr = sym_step segs i ss scr.
Proof. intros. unfold sym_stepB, sym_step. (repeat first [ rewrite bv_signedF_eqf | rewrite bvu64_eqf | rewrite jalrF_eqf | rewrite decide_branchB_eqf | rewrite mkAluKB_eqf | rewrite mkMdKB_eqf | rewrite mkAluwKB_eqf | rewrite flat_scB_eqf | rewrite storeok_scB_eqf | rewrite conc_exprB_eqf | rewrite enum_branchB_eqf | rewrite to_saddrKB_eqf | rewrite amo_alignedbB_eqf | rewrite amo_newvalB_eqf | rewrite sym_readRB_eqf | rewrite sym_readB_eqf ]). reflexivity. Qed.
(* [comment removed for export] *)
Definition kext (kn' kn : list kentry) : Prop := exists W, forallb kwrappedb W = true /\ kn' = W ++ kn.
Lemma kext_refl : forall kn, kext kn kn.
Proof. intros kn. exists []. split; reflexivity. Qed.
Lemma kext_trans : forall k3 k2 k1, kext k3 k2 -> kext k2 k1 -> kext k3 k1.
Proof.
  intros k3 k2 k1 [W2 [H2 ->]] [W1 [H1 ->]]. exists (W2 ++ W1). split; [|rewrite app_assoc; reflexivity].
  rewrite forallb_app, H2, H1. reflexivity.
Qed.
Lemma kext_facts : forall kn' kn, kext kn' kn -> facts_of kn' = facts_of kn.
Proof. intros kn' kn [W [H ->]]. apply facts_of_recs. exact H. Qed.
Lemma kext_kix : forall kn' kn, kext kn' kn -> mk_kix kn' = mk_kix kn.
Proof. intros kn' kn [W [H ->]]. apply mk_kix_recs. exact H. Qed.
Lemma sym_readR_recs : forall segs ss fk scr a n sx v scs scr' nx recs,
  sym_readR segs ss fk scr a n sx = Some (v, scs, scr', nx, recs) -> forallb kwrappedb recs = true.
Proof.
  intros segs ss fk scr a n sx v scs scr' nx recs H. unfold sym_readR in H.
  repeat (lazymatch type of H with
          | Some _ = Some _ => injection H as _ _ _ _ <-
          | (match ?x with _ => _ end) = _ => destruct x
          | (if ?x then _ else _) = _ => destruct x
          end); try discriminate; try reflexivity.
  destruct (rec_onb fk); reflexivity.
Qed.
Lemma sym_step_kext : forall segs i ss scr ss' scs scr',
  sym_step segs i ss scr = SOk ss' scs scr' -> kext (s_know ss') (s_know ss).
Proof.
  intros segs i ss scr ss' scs scr' H. unfold sym_step, sym_read in H.
  destruct i; try discriminate;
  try (lazymatch type of H with
       | (match sym_readR ?sg ?s0 ?f ?sc ?a ?n ?sx with _ => _ end) = _ =>
           destruct (sym_readR sg s0 f sc a n sx) as [[[[[v scs0] scr0] nx0] recs]|] eqn:ER; [|discriminate];
           injection H as <- _ _; exists recs; split; [exact (sym_readR_recs _ _ _ _ _ _ _ _ _ _ _ _ ER)|reflexivity]
       end);
  repeat (lazymatch type of H with
          | SOk _ _ _ = SOk _ _ _ => injection H as <- _ _
          | (match ?x with _ => _ end) = _ => destruct x
          | (let (_, _) := ?x in _) = _ => destruct x
          | (if ?x then _ else _) = _ => destruct x
          end); try discriminate; try apply kext_refl.
Qed.
(* [comment removed for export] *)
Lemma sym_readR_next : forall segs ss fk scr a n sx v scs scr' nx recs,
  sym_readR segs ss fk scr a n sx = Some (v, scs, scr', nx, recs) -> nx = s_next ss \/ nx = S (s_next ss).
Proof.
  intros segs ss fk scr a n sx v scs scr' nx recs H. unfold sym_readR in H.
  repeat (lazymatch type of H with
          | Some _ = Some _ => injection H as _ _ _ <- _
          | (match ?x with _ => _ end) = _ => destruct x
          | (if ?x then _ else _) = _ => destruct x
          end); try discriminate; auto.
Qed.
Lemma sym_step_next_le : forall segs i ss scr ss' scs scr',
  sym_step segs i ss scr = SOk ss' scs scr' -> (s_next ss <= s_next ss')%nat.
Proof.
  intros segs i ss scr ss' scs scr' H. unfold sym_step, sym_read in H.
  destruct i; try discriminate;
  try (lazymatch type of H with
       | context [sym_readR ?sg ?s0 ?f ?sc ?a ?n ?sx] =>
           destruct (sym_readR sg s0 f sc a n sx) as [[[[[v scs0] scr0] nx0] recs]|] eqn:ER;
           [pose proof (sym_readR_next _ _ _ _ _ _ _ _ _ _ _ _ ER) as HN|]
       end);
  repeat (lazymatch type of H with
          | SOk _ _ _ = SOk _ _ _ => injection H as <- _ _
          | (match ?x with _ => _ end) = _ => destruct x
          | (let (_, _) := ?x in _) = _ => destruct x
          | (if ?x then _ else _) = _ => destruct x
          end); try discriminate; cbn [s_next sset sjump]; try lia.
  all: destruct HN as [-> | ->]; lia.
Qed.
Lemma sym_step_next_leb : forall segs i ss scr ss' scs scr',
  sym_step segs i ss scr = SOk ss' scs scr' -> Nat.leb (s_next ss) (s_next ss') = true.
Proof. intros. apply Nat.leb_le. eapply sym_step_next_le. eassumption. Qed.

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
  | SOk ss' scs scr' => SOk (cap_rd K i ss') (x_filterB bc ss ss' scs) scr'   (* [comment removed for export] *)
  | SStop => SStop
  end.


Lemma zf_coversB_eqf : forall fk, zf_coversB (mkbc fk) = zf_covers fk.
Proof. intros. bcfe. unfold zf_coversB, zf_covers. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite zf_coversB_eqf : bceq.
Lemma kentry_overlayB_eqf : forall fk, kentry_overlayB (mkbc fk) = kentry_overlay fk.
Proof. intros. bcfe. unfold kentry_overlayB, kentry_overlay. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kentry_overlayB_eqf : bceq.
Lemma kentry_readableB_eqf : forall fk, kentry_readableB (mkbc fk) = kentry_readable fk.
Proof. intros. bcfe. unfold kentry_readableB, kentry_readable. (repeat first [ rewrite kentry_overlayB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite kentry_readableB_eqf : bceq.
Lemma kn_readableB_eqf : forall fk, kn_readableB (mkbc fk) = kn_readable segs fk.
Proof. intros. bcfe. unfold kn_readableB, kn_readable. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_readableB_eqf : bceq.
Lemma kn_overlayB_eqf : forall fk, kn_overlayB (mkbc fk) = kn_overlay segs fk.
Proof. intros. bcfe. unfold kn_overlayB, kn_overlay. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_overlayB_eqf : bceq.

Lemma x_dischargeableB_eq : forall ss ss' rb sc,
  x_dischargeableB (mkbc (facts_of (s_know ss))) ss ss' rb sc = x_dischargeable segs ss ss' rb sc.
Proof. intros. unfold x_dischargeableB, x_dischargeable. (repeat first [ rewrite bc_fk_mkbc ]). reflexivity. Qed.
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
  destruct (sym_step segs i ss scr) as [ss' scs scr'|] eqn:E; [|reflexivity].
  rewrite (sym_step_next_leb _ _ _ _ _ _ _ E). rewrite x_filterB_eq. reflexivity.
Qed.
Lemma sym_stepX_kext : forall K i ss scr ss' scs scr',
  sym_stepX segs K i ss scr = SOk ss' scs scr' -> kext (s_know ss') (s_know ss).
Proof.
  intros K i ss scr ss' scs scr' H. unfold sym_stepX in H.
  destruct (sym_step segs i ss scr) as [ss1 scs1 scr1|] eqn:E; [|discriminate].
  destruct (Nat.leb (s_next ss) (s_next ss1)); [|discriminate]. injection H as <- _ _.
  rewrite cap_rd_know. exact (sym_step_kext _ _ _ _ _ _ _ E).
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
  rewrite <- (kext_facts _ _ (sym_stepX_kext _ _ _ _ _ _ _ E)). apply IH.
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
Lemma sym_execTX_go_kext : forall t K fuel first stops ss ck kn0,
  kext (s_know ck) kn0 -> kext (s_know ss) kn0 ->
  kext (s_know (sym_execTX_go segs t K fuel first stops ss ck)) kn0.
Proof.
  intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck kn0 Hck Hss.
  - cbn. destruct (s_clean ss); [exact Hss|exact Hck].
  - cbn [sym_execTX_go].
    destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [destruct (s_clean ss); [exact Hss|exact Hck]|].
    destruct (itab_lookup t (s_pc ss)) as [i|]; [|destruct (s_clean ss); [exact Hss|exact Hck]].
    destruct (sym_stepX segs K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|destruct (s_clean ss); [exact Hss|exact Hck]].
    destruct scs; [|destruct (s_clean ss); [exact Hss|exact Hck]].
    pose proof (kext_trans _ _ _ (sym_stepX_kext _ _ _ _ _ _ _ E) Hss) as HK.
    apply IH; [|exact HK]. destruct (s_clean ss'); [exact HK|exact Hck].
Qed.
Lemma sym_execTX_kext : forall t K fuel first stops ss,
  kext (s_know (sym_execTX segs t K fuel first stops ss)) (s_know ss).
Proof.
  intros. unfold sym_execTX. apply sym_execTX_go_kext; (replace (s_know (clr ss)) with (s_know ss) by (destruct ss; reflexivity)); apply kext_refl.
Qed.
Lemma sym_execTX_facts : forall t K fuel first stops ss,
  facts_of (s_know (sym_execTX segs t K fuel first stops ss)) = facts_of (s_know ss).
Proof. intros. apply kext_facts. apply sym_execTX_kext. Qed.
(* [comment removed for export] *)
Definition sym_stepXBI (bc : bctx) (kx : kix) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match sym_stepBI bc kx segs i ss scr with
  | SOk ss' scs scr' => SOk (cap_rd K i ss') (x_filterB bc ss ss' scs) scr'   (* [comment removed for export] *)
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
  rewrite <- (kext_facts _ _ (sym_stepX_kext _ _ _ _ _ _ _ E)), <- (kext_kix _ _ (sym_stepX_kext _ _ _ _ _ _ _ E)). apply IH.
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
           else if lin_ge0B bc [(wb, k)] [(kb, kk); (len, 0%Z)] then ([K], [], hints)   (* [comment removed for export] *)
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
        | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints)
               else if lin_ge0B bc [(a_base wa, k)] [(kb, kk); (len, 0%Z)] then ([K], [], hints)   (* [comment removed for export] *)
               else ([], [], hints)
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
Proof. intros. bcfe. unfold kcutB, kcut. (repeat first [ rewrite lin_ge0B_eqf ]). reflexivity. Qed.
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
Proof. intros. bcfe. unfold prune_zfB, prune_zf. (repeat first [ rewrite lin_ge0B_eqf | rewrite kcutB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite prune_zfB_eqf : bceq.
Lemma prune1pB_eqf : forall fk, prune1pB (mkbc fk) = prune1p fk.
Proof. intros. bcfe. unfold prune1pB, prune1p. (repeat first [ rewrite lin_ge0B_eqf | rewrite ranges_apart_pB_eqf | rewrite prune_zfB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite prune1pB_eqf : bceq.
Lemma ranges_apart_pcB_eqf : forall fk, ranges_apart_pcB (mkbc fk) = ranges_apart_pc fk.
Proof. intros. bcfe. unfold ranges_apart_pcB, ranges_apart_pc. (repeat first [ rewrite lin_apartB_eqf | rewrite xhiB_eqf | rewrite lin_ge0B_eqf | rewrite end_hiB_eqf | rewrite in_sidesB_eqf | rewrite in_sides_xB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite ranges_apart_pcB_eqf : bceq.
Lemma prune1pcB_eqf : forall fk, prune1pcB (mkbc fk) = prune1pc fk.
Proof. intros. bcfe. unfold prune1pcB, prune1pc. (repeat first [ rewrite kzero_cutB_eqf | rewrite kfill_cutB_eqf | rewrite kunk_cutB_eqf | rewrite prune1pB_eqf | rewrite ranges_apart_pcB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite prune1pcB_eqf : bceq.
Lemma prunepcB_eqf : forall fk, prunepcB (mkbc fk) = prunepc fk.
Proof.
  intros fk. apply functional_extensionality; intros sp. apply functional_extensionality; intros wa. apply functional_extensionality; intros w. apply functional_extensionality; intros wv. apply functional_extensionality; intros kn. 
  induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [prunepcB prunepc]. rewrite IH. (repeat first [ rewrite base_rangeB_eqf | rewrite prune1pcB_eqf ]). reflexivity.
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
      (destruct (Z.leb (k + Z.of_nat w) kk); cbn [fst List.filter]; [rewrite HK; reflexivity |];
       match goal with |- context [if ?c then _ else _] => destruct c end; cbn [fst List.filter];
       [rewrite HK; reflexivity | apply kcut_nofacts; exact Hm]).
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
  (repeat first [ rewrite mk_sprepB_eqf | rewrite prunepcB_eqf ]). reflexivity.
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
Definition prune1pcK0 (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
  (br2 : option (Z * Z)) : pk_res :=
  let k := a_off wa in
  let wb := a_base wa in
  let zfK (mk : saddr -> expr -> kentry) (kb : expr) (kk : Z) (len : expr) :=
    if same then
      match len with
      | ELit l0 => PRepl (ktrim mk kb kk l0 k w)
      | _ => if Z.leb (k + Z.of_nat w) kk then PKeep
             else if lin_ge0B bc [(wb, k)] [(kb, kk); (len, 0%Z)] then PKeep   (* [comment removed for export] *)
             else PRepl (kcutB bc mk wb k (elen w) kb kk len)
      end
    else let ap := ranges_apart_pcB bc sp wb k (elen w) br2 kb kk len in   (* [comment removed for export] *)
    if ap then PKeep
    else match kcutB bc mk wb k (elen w) kb kk len with
         | [] => if ap then PKeep else PRepl []
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
      else let ap := ranges_apart_pcB bc sp wb k (elen w) br2 kb kk (elen w') in   (* [comment removed for export] *)
      if ap then PKeep
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool then PKeep
      else if ap then PKeep else PRepl []
  | KBlob (SA kb kk) len bk =>
      if same then
        match len with
        | ELit l0 => let l := (l0 mod 2 ^ 64)%Z in
                     if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool then PKeep else PRepl []
        | _ => if Z.leb (k + Z.of_nat w) kk then PKeep
               else if lin_ge0B bc [(wb, k)] [(kb, kk); (len, 0%Z)] then PKeep   (* [comment removed for export] *)
               else PRepl []
        end
      else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk len then PKeep else PRepl []
  end.

Lemma prune1pcK0_eq : forall fk sp wa w wv K br2 same,
  (match kbase K with Some kb => same = expr_eqb kb (a_base wa) | None => True end) ->
  pk_list K (prune1pcK0 (mkbc fk) sp wa w wv K same br2) = fst (fst (prune1pc fk sp wa w wv K [] br2)).
Proof.
  intros fk sp wa w wv K br2 same H.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    cbn [kbase] in H; try subst same; unfold prune1pcK0, prune1pc, prune1p, prune_zf, kzero_cut, kfill_cut, kunk_cut;
    (repeat first [ rewrite lin_ge0B_eqf | rewrite ranges_apart_pB_eqf | rewrite kcutB_eqf | rewrite ranges_apart_pcB_eqf ]); cbn [a_base a_off]; pk_crush.
Qed.

(* [comment removed for export] *)
Definition pk_keepb (wa : saddr) (w : nat) (K : kentry) (same : bool) : bool :=
  let k := a_off wa in
  match K with
  | KImg lo hi =>
      match a_base wa with
      | ELit Z0 => (Z.leb hi k || Z.leb (k + Z.of_nat w) lo) && Z.ltb lo hi
      | _ => false
      end
  | KZero (SA _ kk) (ELit l0) | KFill (SA _ kk) (ELit l0) _ | KUnk (SA _ kk) (ELit l0) =>
      if same then (let l := zmod64 l0 in (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk) && Z.ltb 0 l && Z.eqb l l0)
      else false
  | _ => false
  end%bool.
Definition prune1pcK (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
  (br2 : option (Z * Z)) (fa : bool) : pk_res :=
  if fa then PKeep else   (* [comment removed for export] *)
  if pk_keepb wa w K same then PKeep else prune1pcK0 bc sp wa w wv K same br2.

Lemma ktrim_keep : forall mk kb kk l0 k w,
  (let l := zmod64 l0 in (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk) && Z.ltb 0 l && Z.eqb l l0)%bool = true ->
  ktrim mk kb kk l0 k w = [mk (SA kb kk) (ELit l0)].
Proof.
  intros mk kb kk l0 k w H. cbn zeta in H. rewrite zmod64_eq in H.
  apply andb_prop in H as [H Hl]. apply andb_prop in H as [H Hp].
  apply Z.eqb_eq in Hl. apply Z.ltb_lt in Hp. unfold ktrim. rewrite Hl.
  apply Bool.orb_true_iff in H. destruct H as [H|H]; apply Z.leb_le in H.
  - rewrite Z.min_r by lia. replace (Z.ltb kk (kk + l0)) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (Z.ltb (Z.max kk (k + Z.of_nat w)) (kk + l0)) with false by (symmetry; apply Z.ltb_ge; lia).
    cbn [app]. f_equal. f_equal. f_equal. lia.
  - rewrite Z.min_l by lia. replace (Z.ltb kk k) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite Z.max_l by lia. replace (Z.ltb kk (kk + l0)) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [app]. f_equal. f_equal. f_equal. lia.
Qed.
Lemma kimg_keep : forall lo hi k (w : nat),
  ((Z.leb hi k || Z.leb (k + Z.of_nat w) lo) && Z.ltb lo hi)%bool = true ->
  (if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else []) ++
  (if Z.ltb (Z.max lo (k + Z.of_nat w)) hi then [KImg (Z.max lo (k + Z.of_nat w)) hi] else []) = [KImg lo hi].
Proof.
  intros lo hi k w H. apply andb_prop in H as [H Hl]. apply Z.ltb_lt in Hl.
  apply Bool.orb_true_iff in H. destruct H as [H|H]; apply Z.leb_le in H.
  - rewrite Z.min_r by lia. replace (Z.ltb lo hi) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (Z.ltb (Z.max lo (k + Z.of_nat w)) hi) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - destruct (Z.ltb lo (Z.min k hi)) eqn:E; [apply Z.ltb_lt in E; lia|].
    rewrite Z.max_l by lia. replace (Z.ltb lo hi) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma prune1pc_keep : forall fk sp wa w wv K br2 same,
  (match kbase K with Some kb => same = expr_eqb kb (a_base wa) | None => True end) ->
  pk_keepb wa w K same = true ->
  fst (fst (prune1pc fk sp wa w wv K [] br2)) = [K].
Proof.
  intros fk sp [wb k] w wv K br2 same H G. cbn [a_base a_off] in H.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    cbn [kbase] in H; cbn [pk_keepb a_base a_off] in G; try discriminate G.
  - destruct len as [l0| | | | | | |]; try discriminate G. subst same. destruct (expr_eqb kb wb) eqn:E; [|discriminate G].
    unfold prune1pc. cbn [a_base a_off]. rewrite E. unfold prune1p, prune_zf. cbn [a_base a_off]. rewrite E. cbn [fst].
    apply ktrim_keep. exact G.
  - destruct wb as [z| | | | | | |]; try discriminate G. destruct z; try discriminate G.
    unfold prune1pc, prune1p. cbn [a_base a_off fst]. apply kimg_keep. exact G.
  - destruct len as [l0| | | | | | |]; try discriminate G. subst same. destruct (expr_eqb kb wb) eqn:E; [|discriminate G].
    unfold prune1pc. cbn [a_base a_off]. rewrite E. unfold prune1p, prune_zf. cbn [a_base a_off]. rewrite E. cbn [fst].
    apply ktrim_keep. exact G.
  - destruct len as [l0| | | | | | |]; try discriminate G. subst same. destruct (expr_eqb kb wb) eqn:E; [|discriminate G].
    unfold prune1pc. cbn [a_base a_off]. rewrite E. unfold prune1p, prune_zf. cbn [a_base a_off]. rewrite E. cbn [fst].
    apply ktrim_keep. exact G.
Qed.
(* [comment removed for export] *)
Definition kbkl (K : kentry) : option (expr * Z * expr) :=
  match K with
  | KWord (SA kb kk) w _ => Some (kb, kk, elen w)
  | KZero (SA kb kk) len | KUnk (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ => Some (kb, kk, len)
  | _ => None
  end.
Lemma kbkl_kbase : forall K kb kk len, kbkl K = Some (kb, kk, len) -> kbase K = Some kb.
Proof. intros K kb kk len H. destruct K as [[? ?] ? ?|[? ?] ?|[? ?] ? ?| | | |[? ?] ?| |[? ?] ? ?|[? ?] ?]; cbn in H |- *; congruence. Qed.
(* [comment removed for export] *)
Lemma prune1pc_apart : forall fk sp wa w wv K br2 kb kk len,
  kbkl K = Some (kb, kk, len) -> expr_eqb kb (a_base wa) = false ->
  ranges_apart_pc fk sp (a_base wa) (a_off wa) (elen w) br2 kb kk len = true ->
  fst (fst (prune1pc fk sp wa w wv K [] br2)) = [K].
Proof.
  intros fk sp [wb k] w wv K br2 kb kk len HK HE HA. cbn [a_base a_off] in HE, HA.
  destruct K as [[b o] w' v|[b o] ln|[b o] ln bk|lo hi|e' m'|e' lo' hi'|[b o] en|c1 m1 c2 m2|[b o] ln fc|[b o] ln];
    cbn [kbkl] in HK; try discriminate HK; injection HK as <- <- <-;
    unfold prune1pc; cbn [a_base a_off]; rewrite HE, HA; reflexivity.
Qed.
(* [comment removed for export] *)
Definition FA_OK (fk : list kentry) (sp : sprep) (wa : saddr) (w : nat) (br2 : option (Z * Z)) (K : kentry) (fa : bool) : Prop :=
  fa = true -> exists kb kk len, kbkl K = Some (kb, kk, len) /\ expr_eqb kb (a_base wa) = false
                /\ ranges_apart_pcB (mkbc fk) sp (a_base wa) (a_off wa) (elen w) br2 kb kk len = true.
Lemma prune1pcK_eq : forall fk sp wa w wv K br2 same fa,
  (match kbase K with Some kb => same = expr_eqb kb (a_base wa) | None => True end) ->
  FA_OK fk sp wa w br2 K fa ->
  pk_list K (prune1pcK (mkbc fk) sp wa w wv K same br2 fa) = fst (fst (prune1pc fk sp wa w wv K [] br2)).
Proof.
  intros fk sp wa w wv K br2 same fa H HFA. unfold prune1pcK.
  destruct fa.
  - destruct (HFA eq_refl) as (kb & kk & len & HK & HE & HA). cbn [pk_list]. symmetry.
    eapply prune1pc_apart; [exact HK|exact HE|]. rewrite <- ranges_apart_pcB_eqf. exact HA.
  - destruct (pk_keepb wa w K same) eqn:G.
    + cbn [pk_list]. symmetry. exact (prune1pc_keep fk sp wa w wv K br2 same H G).
    + apply prune1pcK0_eq. exact H.
Qed.
Lemma FA_OK_false : forall fk sp wa w br2 K, FA_OK fk sp wa w br2 K false.
Proof. intros fk sp wa w br2 K H. discriminate H. Qed.

(* [comment removed for export] *)
Local Open Scope Z_scope.
(* [comment removed for export] *)
Lemma lin_range_shift : forall rng c ts,
  lin_range rng c ts = match lin_range rng 0 ts with Some (lo, hi) => Some ((c + lo)%Z, (c + hi)%Z) | None => None end.
Proof.
  intros rng c ts. induction ts as [|[k a] rest IH]; cbn [lin_range].
  - f_equal. f_equal; lia.
  - rewrite IH. destruct (rng a) as [[al ah]|]; [|destruct (lin_range rng 0 rest) as [[? ?]|]; reflexivity].
    destruct (lin_range rng 0 rest) as [[lo hi]|]; [|reflexivity].
    destruct (Z.leb 0 k); f_equal; f_equal; lia.
Qed.
(* [comment removed for export] *)
Definition cand_withB (bc : bctx) (fs : list sfact) (ts : list (Z * expr)) : list (Z * Z) :=
  match sum_subst fs ts 0 0 false with
  | (ts', (lo0, hi0), true) =>
      match lin_range (erangeB bc) 0 ts' with
      | Some (lo, hi) => [((lo + lo0)%Z, (hi + hi0)%Z)]
      | None => []
      end
  | _ => []
  end.
Definition lt_candsB (bc : bctx) (ts : list (Z * expr)) : list (Z * Z) :=
  (match lin_range (erangeB bc) 0 ts with Some i => [i] | None => [] end)
  ++ match bc_fs bc with
     | [] => []
     | fs => cand_withB bc fs ts ++ flat_map (fun f => cand_withB bc [f] ts) fs
     end.
Definition cands_test (c : Z) (test : Z -> Z -> bool) (l : list (Z * Z)) : bool :=
  existsb (fun i => test (c + fst i)%Z (c + snd i)%Z) l.
Lemma cands_test_app : forall c test l1 l2, cands_test c test (l1 ++ l2) = (cands_test c test l1 || cands_test c test l2)%bool.
Proof. intros. unfold cands_test. apply existsb_app. Qed.
Lemma lin_test_withB_cands : forall bc fs c ts test,
  lin_test_with (erangeB bc) fs c ts test = cands_test c test (cand_withB bc fs ts).
Proof.
  intros. unfold lin_test_with, cand_withB.
  destruct (sum_subst fs ts 0 0 false) as [[ts' [lo0 hi0]] hit]. destruct hit; [|reflexivity].
  rewrite lin_range_shift. destruct (lin_range (erangeB bc) 0 ts') as [[lo hi]|]; [|reflexivity].
  cbn. rewrite Bool.orb_false_r. f_equal; lia.
Qed.
Lemma lin_testB_cands : forall bc c ts test,
  lin_testB bc c ts test = cands_test c test (lt_candsB bc ts).
Proof.
  intros. unfold lin_testB, lt_candsB. rewrite cands_test_app.
  assert (REL : lin_test_relB bc c ts test = cands_test c test (match bc_fs bc with [] => [] | fs => cand_withB bc fs ts ++ flat_map (fun f => cand_withB bc [f] ts) fs end)).
  { unfold lin_test_relB. destruct (bc_fs bc) as [|f0 fs0] eqn:HF; [reflexivity|].
    rewrite cands_test_app, lin_test_withB_cands.
    destruct (cands_test c test (cand_withB bc (f0 :: fs0) ts)); [reflexivity|]. cbn [orb].
    generalize (f0 :: fs0) as l. intros l. induction l as [|f rest IH]; [reflexivity|].
    cbn [existsb flat_map]. rewrite cands_test_app, lin_test_withB_cands, IH. reflexivity. }
  rewrite REL. rewrite lin_range_shift. destruct (lin_range (erangeB bc) 0 ts) as [[lo hi]|]; cbn [cands_test existsb app fst snd]; [|reflexivity].
  destruct (test (c + lo) (c + hi)); reflexivity.
Qed.

(* [comment removed for export] *)
Definition ge0_stage : Type := (Z * Z * list (Z * Z))%type.
Definition ge0_eval (st : list ge0_stage) (c : Z) : bool :=
  existsb (fun x => match x with (m, s, cands) => cands_test (m * c + s)%Z (fun lo _ => Z.leb 0 lo) cands end) st.
Definition ge0_stagesB (bc : bctx) (d : list (Z * expr)) : list ge0_stage :=
  (1%Z, 0%Z, lt_candsB bc d) ::
  (let '(c2, t2) := srl_expandB bc d in
   (1%Z, c2, lt_candsB bc t2) ::
   ((if has_srl t2 then let '(c3, t3) := srl_expandB bc t2 in [(1%Z, (c2 + c3)%Z, lt_candsB bc t3)] else [])
    ++ (let j := srl_scale_need d in
        if (if Z.ltb 0 j then Z.leb j 24 else false) then
          let sc := (2 ^ j)%Z in
          let ts' := List.map (fun t => ((sc * fst t)%Z, snd t)) d in
          let '(c2', t2') := srl_expandB bc ts' in
          let '(c3', t3') := (if has_srl t2' then srl_expandB bc t2' else (0%Z, t2')) in
          [(sc, (c2' + c3' + (sc - 1))%Z, lt_candsB bc t3')]   (* [comment removed for export] *)
        else []))).
Lemma cands_test_ge0 : forall c s cands,
  cands_test (c + s) (fun lo _ => Z.leb 0 lo) cands = cands_test (1 * c + s) (fun lo _ => Z.leb 0 lo) cands.
Proof. intros. f_equal. lia. Qed.
Lemma lin_ge0B_staged : forall bc pos neg,
  lin_ge0B bc pos neg =
  (xt_nowrapB bc pos && xt_nowrapB bc neg && ge0_eval (ge0_stagesB bc (lsub_e (xt_lin pos) (xt_lin neg))) (xt_const pos - xt_const neg))%bool.
Proof.
  intros. unfold lin_ge0B, lin_ge0_scaledB, ge0_stagesB, ge0_eval.
  set (d := lsub_e (xt_lin pos) (xt_lin neg)). set (c := (xt_const pos - xt_const neg)%Z).
  destruct (xt_nowrapB bc pos); [|reflexivity]. destruct (xt_nowrapB bc neg); [|reflexivity]. cbn [andb].
  rewrite !lin_testB_cands. cbn [existsb].
  replace (1 * c + 0)%Z with c by lia.
  destruct (cands_test c _ (lt_candsB bc d)); [reflexivity|]. cbn [orb].
  destruct (srl_expandB bc d) as [c2 t2]. cbn [existsb]. rewrite lin_testB_cands.
  replace (1 * c + c2)%Z with (c + c2)%Z by lia.
  destruct (cands_test (c + c2) _ (lt_candsB bc t2)); [reflexivity|]. cbn [orb].
  rewrite existsb_app.
  destruct (has_srl t2).
  - destruct (srl_expandB bc t2) as [c3 t3]. cbn [existsb]. rewrite lin_testB_cands.
    replace (1 * c + (c2 + c3))%Z with (c + c2 + c3)%Z by lia.
    destruct (cands_test (c + c2 + c3) _ (lt_candsB bc t3)); [reflexivity|]. cbn [orb].
    destruct (if Z.ltb 0 (srl_scale_need d) then Z.leb (srl_scale_need d) 24 else false); [|reflexivity].
    destruct (srl_expandB bc (map _ d)) as [c2' t2'].
    destruct (if has_srl t2' then srl_expandB bc t2' else (0%Z, t2')) as [c3' t3']. cbn [existsb].
    rewrite lin_testB_cands. rewrite Bool.orb_false_r.
    match goal with |- cands_test ?a _ _ = cands_test ?b _ _ => replace b with a by lia; reflexivity end.
  - cbn [existsb app].
    destruct (if Z.ltb 0 (srl_scale_need d) then Z.leb (srl_scale_need d) 24 else false); [|reflexivity].
    destruct (srl_expandB bc (map _ d)) as [c2' t2'].
    destruct (if has_srl t2' then srl_expandB bc t2' else (0%Z, t2')) as [c3' t3']. cbn [existsb].
    rewrite lin_testB_cands. rewrite Bool.orb_false_r.
    rewrite ?Bool.orb_false_l.
    match goal with |- cands_test ?a _ _ = cands_test ?b _ _ => replace b with a by lia; reflexivity end.
Qed.

(* [comment removed for export] *)
Definition ap_stagesB (bc : bctx) (d : list (Z * expr)) : list (Z * list (Z * Z)) :=
  (0%Z, lt_candsB bc d) :: (let '(c2, t2) := srl_expandB bc d in [(c2, lt_candsB bc t2)]).
Definition ap_eval (st : list (Z * list (Z * Z))) (c n1 n2 : Z) : bool :=
  existsb (fun x => match x with (s, cands) => cands_test (c + s)%Z (fun lo hi => (Z.leb n1 lo || Z.leb hi (- n2))%bool) cands end) st.
Lemma lin_apart0B_staged : forall bc b1 k1 n1 b2 k2 n2,
  lin_apart0B bc b1 k1 n1 b2 k2 n2 =
  (lin_nowrapRB bc b1 && lin_nowrapRB bc b2 &&
   ap_eval (ap_stagesB bc (lsub_e (snd (lin_of b2)) (snd (lin_of b1)))) (fst (lin_of b2) + k2 - fst (lin_of b1) - k1) n1 n2)%bool.
Proof.
  intros. unfold lin_apart0B, ap_stagesB, ap_eval. cbv zeta.
  destruct (lin_nowrapRB bc b1); [|reflexivity]. destruct (lin_nowrapRB bc b2); [|reflexivity]. cbn [andb existsb].
  rewrite !lin_testB_cands. rewrite Z.add_0_r.
  destruct (cands_test _ _ (lt_candsB bc _)); [reflexivity|]. cbn [orb].
  destruct (srl_expandB bc _) as [c2 t2]. cbn [existsb]. rewrite lin_testB_cands, Bool.orb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ge0_eval_hd : forall c cands rest lo hi,
  Z.leb 0 (c + lo) = true ->
  ge0_eval ((1%Z, 0%Z, (lo, hi) :: cands) :: rest) c = true.
Proof. intros. cbn. replace (1 * c + 0 + lo)%Z with (c + lo)%Z by lia. rewrite H. reflexivity. Qed.
(* [comment removed for export] *)
Lemma lt_candsB_hd : forall bc d lo hi,
  lin_range (erangeB bc) 0 d = Some (lo, hi) -> exists rest, lt_candsB bc d = (lo, hi) :: rest.
Proof. intros bc d lo hi H. unfold lt_candsB. rewrite H. cbn. eexists. reflexivity. Qed.
Lemma lin_ge0B_fast : forall bc pos neg lo hi,
  xt_nowrapB bc pos = true -> xt_nowrapB bc neg = true ->
  lin_range (erangeB bc) 0 (lsub_e (xt_lin pos) (xt_lin neg)) = Some (lo, hi) ->
  Z.leb 0 (xt_const pos - xt_const neg + lo) = true ->
  lin_ge0B bc pos neg = true.
Proof.
  intros bc pos neg lo hi N1 N2 HR HT. rewrite lin_ge0B_staged, N1, N2. cbn [andb].
  unfold ge0_stagesB. destruct (lt_candsB_hd _ _ _ _ HR) as [rest ->].
  apply ge0_eval_hd. exact HT.
Qed.
Lemma lin_apart0B_fast : forall bc b1 k1 n1 b2 k2 n2 lo hi,
  lin_nowrapRB bc b1 = true -> lin_nowrapRB bc b2 = true ->
  lin_range (erangeB bc) 0 (lsub_e (snd (lin_of b2)) (snd (lin_of b1))) = Some (lo, hi) ->
  (let c := (fst (lin_of b2) + k2 - fst (lin_of b1) - k1)%Z in Z.leb n1 (c + lo) || Z.leb (c + hi) (- n2))%bool = true ->
  lin_apart0B bc b1 k1 n1 b2 k2 n2 = true.
Proof.
  intros bc b1 k1 n1 b2 k2 n2 lo hi N1 N2 HR HT. rewrite lin_apart0B_staged, N1, N2. cbn [andb].
  unfold ap_stagesB. destruct (lt_candsB_hd _ _ _ _ HR) as [rest ->]. cbn [ap_eval existsb cands_test fst snd].
  cbv zeta in HT. rewrite Z.add_0_r. rewrite HT. reflexivity.
Qed.

Lemma ranges_apartB_by_lin : forall bc b1 k1 n1 b2 k2 n2,
  shares_var b1 b2 = true -> lin_apart0B bc b1 k1 n1 b2 k2 n2 = true -> ranges_apartB bc b1 k1 n1 b2 k2 n2 = true.
Proof.
  intros bc b1 k1 n1 b2 k2 n2 HS HL. unfold ranges_apartB.
  match goal with |- (if ?c then true else _) = true => destruct c; [reflexivity|] end.
  destruct (kdisj_apartB _ _ _ _ _ _ _ _); [reflexivity|]. unfold lin_apartB. rewrite HS. exact HL.
Qed.
Lemma ranges_apart_xB_by_lin : forall bc b1 k1 n1 b2 k2 n2,
  match n1, n2 with ELit _, ELit _ => False | _, _ => True end ->
  shares_var b1 b2 = true ->
  (lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] = true \/ lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)] = true) ->
  ranges_apart_xB bc b1 k1 n1 b2 k2 n2 = true.
Proof.
  intros bc b1 k1 n1 b2 k2 n2 HN HS HL. unfold ranges_apart_xB.
  assert (GEN : forall (x : bool), (if x then true
    else if kdisj_apart_xB bc (bc_kd bc) b1 k1 n1 b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]) = true).
  { intros x. destruct x; [reflexivity|]. destruct (kdisj_apart_xB _ _ _ _ _ _ _ _); [reflexivity|].
    rewrite HS. cbn [negb]. destruct HL as [-> | ->]; [reflexivity|]. destruct (lin_ge0B _ _ _); reflexivity. }
  destruct n1; try apply GEN. destruct n2; try apply GEN. destruct HN.
Qed.

(* [comment removed for export] *)
Record apq := APQ {
  aq_sh : bool;                     (* [comment removed for export] *)
  aq_nw1 : bool; aq_nw2 : bool;     (* [comment removed for export] *)
  aq_c : Z; aq_ia : option (Z * Z); (* [comment removed for export] *)
  aq_c1 : Z; aq_i1 : option (Z * Z);   (* [comment removed for export] *)
  aq_nwl : bool; aq_c2 : Z; aq_i2 : option (Z * Z); aq_len : expr   (* [comment removed for export] *)
}.
Definition mk_apq (bc : bctx) (b1 b2 n2 : expr) : apq :=
  let l1 := lin_of b1 in let l2 := lin_of b2 in
  APQ (shares_var b1 b2) (lin_nowrapRB bc b1) (lin_nowrapRB bc b2)
      (fst l2 - fst l1)%Z (lin_range (erangeB bc) 0 (lsub_e (snd l2) (snd l1)))
      (xt_const [(b2, 0%Z)] - xt_const [(b1, 0%Z)])%Z (lin_range (erangeB bc) 0 (lsub_e (xt_lin [(b2, 0%Z)]) (xt_lin [(b1, 0%Z)])))
      (lin_nowrapRB bc n2) (xt_const [(b1, 0%Z)] - xt_const [(b2, 0%Z); (n2, 0%Z)])%Z
      (lin_range (erangeB bc) 0 (lsub_e (xt_lin [(b1, 0%Z)]) (xt_lin [(b2, 0%Z); (n2, 0%Z)]))) n2.
(* [comment removed for export] *)
Definition wlit_nw (bc : bctx) (w : nat) : bool := lin_nowrapRB bc (ELit (Z.of_nat w)).
Definition wlit_c (w : nat) : Z := xt_const [(ELit (Z.of_nat w), 0%Z)].
(* [comment removed for export] *)
Definition apq_fast_lit (q : apq) (k1 m1 k2 m2 : Z) : bool :=
  (aq_sh q && aq_nw1 q && aq_nw2 q &&
   match aq_ia q with
   | Some (lo, hi) => let c := (aq_c q + k2 - k1)%Z in (Z.leb m1 (c + lo) || Z.leb (c + hi) (- m2))
   | None => false
   end)%bool.
(* [comment removed for export] *)
Definition apq_fast_sym (q : apq) (k1 : Z) (wnw : bool) (wc : Z) (k2 : Z) (n2 : expr) : bool :=
  (aq_sh q &&
   ((aq_nw2 q && aq_nw1 q && wnw &&
     match aq_i1 q with Some (lo, _) => Z.leb 0 (aq_c1 q + k2 - k1 - wc + lo) | None => false end)
    || (expr_eqb n2 (aq_len q) && aq_nw1 q && aq_nw2 q && aq_nwl q &&
        match aq_i2 q with Some (lo, _) => Z.leb 0 (aq_c2 q + k1 - k2 + lo) | None => false end)))%bool.

Lemma apq_fast_lit_ok : forall bc b1 b2 n2 k1 m1 k2 m2,
  apq_fast_lit (mk_apq bc b1 b2 n2) k1 m1 k2 m2 = true -> lin_apartB bc b1 k1 m1 b2 k2 m2 = true.
Proof.
  intros bc b1 b2 n2 k1 m1 k2 m2 H. unfold apq_fast_lit, mk_apq in H. cbn [aq_sh aq_nw1 aq_nw2 aq_ia aq_c] in H.
  destruct (shares_var b1 b2) eqn:HS; [|discriminate]. destruct (lin_nowrapRB bc b1) eqn:N1; [|discriminate].
  destruct (lin_nowrapRB bc b2) eqn:N2; [|discriminate]. cbn [andb] in H.
  destruct (lin_range _ _ _) as [[lo hi]|] eqn:HR; [|discriminate].
  unfold lin_apartB. rewrite HS. eapply lin_apart0B_fast; [exact N1|exact N2|exact HR|].
  cbv zeta in H |- *. revert H. match goal with |- ?a = true -> ?b = true => replace b with a; [exact (fun h => h)|] end.
  f_equal; [f_equal; lia | f_equal; lia].
Qed.

Lemma xt_lin_lit : forall b k z, xt_lin [(b, k); (ELit z, 0%Z)] = xt_lin [(b, 0%Z)].
Proof. intros. reflexivity. Qed.
Lemma xt_lin_k : forall b k, xt_lin [(b, k)] = xt_lin [(b, 0%Z)].
Proof. intros. reflexivity. Qed.
Lemma xt_lin_k2 : forall b k n, xt_lin [(b, k); (n, 0%Z)] = xt_lin [(b, 0%Z); (n, 0%Z)].
Proof. intros. reflexivity. Qed.

Lemma apq_fast_sym_ok : forall bc sp b1 k1 (w : nat) br2 b2 k2 n2 q,
  q = mk_apq bc b1 b2 (aq_len q) ->
  match n2 with ELit _ => False | _ => True end ->
  apq_fast_sym q k1 (wlit_nw bc w) (wlit_c w) k2 n2 = true ->
  ranges_apart_pcB bc sp b1 k1 (elen w) br2 b2 k2 n2 = true.
Proof.
  intros bc sp b1 k1 w br2 b2 k2 n2 q Hq Hn H.
  assert (GEN : shares_var b1 b2 = true ->
    (lin_ge0B bc [(b2, k2)] [(b1, k1); (elen w, 0%Z)] = true \/ lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)] = true) ->
    ranges_apart_pcB bc sp b1 k1 (elen w) br2 b2 k2 n2 = true).
  { intros HS HL. unfold ranges_apart_pcB, elen.
    assert (G2 : forall x : bool, (if x then true else if in_sides_xB bc (sp_Dx sp) b2 k2 n2 then true
              else if negb (shares_var b1 b2) then false
              else if lin_ge0B bc [(b2, k2)] [(b1, k1); (ELit (Z.of_nat w), 0%Z)] then true
              else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]) = true).
    { intros x. destruct x; [reflexivity|]. destruct (in_sides_xB _ _ _ _ _); [reflexivity|]. rewrite HS. cbn [negb].
      unfold elen in HL. destruct HL as [-> | ->]; [reflexivity|]. destruct (lin_ge0B _ _ _); reflexivity. }
    destruct n2; try apply G2. destruct Hn. }
  unfold apq_fast_sym in H. rewrite Hq in H. unfold mk_apq in H.
  cbn [aq_sh aq_nw1 aq_nw2 aq_i1 aq_c1 aq_i2 aq_c2 aq_nwl aq_len] in H.
  destruct (shares_var b1 b2) eqn:HS; [|discriminate]. cbn [andb] in H. apply GEN; [reflexivity|].
  apply Bool.orb_true_iff in H. destruct H as [H|H].
  - left. destruct (lin_nowrapRB bc b2) eqn:N2; [|discriminate]. destruct (lin_nowrapRB bc b1) eqn:N1; [|discriminate].
    destruct (wlit_nw bc w) eqn:NW; [|discriminate]. cbn [andb] in H.
    destruct (lin_range _ _ _) as [[lo hi]|] eqn:HR; [|discriminate].
    eapply lin_ge0B_fast with (lo := lo) (hi := hi).
    + cbn [xt_nowrapB]. rewrite N2. reflexivity.
    + cbn [xt_nowrapB]. unfold wlit_nw in NW. unfold elen. rewrite N1, NW. reflexivity.
    + unfold elen. rewrite xt_lin_lit, xt_lin_k. exact HR.
    + revert H. match goal with |- ?a = true -> ?b = true => replace b with a; [exact (fun h => h)|] end.
      f_equal. unfold wlit_c, elen. cbn [xt_const]. lia.
  - right. destruct (expr_eqb n2 _) eqn:EL; [|discriminate]. apply p_expr_eqb_eq in EL.
    destruct (lin_nowrapRB bc b1) eqn:N1; [|discriminate]. destruct (lin_nowrapRB bc b2) eqn:N2; [|discriminate].
    destruct (lin_nowrapRB bc (aq_len q)) eqn:NL; [|discriminate]. cbn [andb] in H.
    destruct (lin_range _ _ _) as [[lo hi]|] eqn:HR; [|discriminate].
    rewrite <- EL in NL, HR, H.
    eapply lin_ge0B_fast with (lo := lo) (hi := hi).
    + cbn [xt_nowrapB]. rewrite N1. reflexivity.
    + cbn [xt_nowrapB]. rewrite N2, NL. reflexivity.
    + rewrite xt_lin_k, xt_lin_k2. exact HR.
    + revert H. match goal with |- ?a = true -> ?b = true => replace b with a; [exact (fun h => h)|] end.
      f_equal. cbn [xt_const]. lia.
Qed.


(* [comment removed for export] *)
Lemma ranges_apartB_lit_by_lin : forall bc b1 k1 n1 b2 k2 n2,
  lin_apartB bc b1 k1 n1 b2 k2 n2 = true -> ranges_apartB bc b1 k1 n1 b2 k2 n2 = true.
Proof.
  intros. unfold ranges_apartB.
  match goal with |- (if ?c then true else _) = true => destruct c; [reflexivity|] end.
  destruct (kdisj_apartB _ _ _ _ _ _ _ _); [reflexivity|]. exact H.
Qed.
Lemma apq_fast_lit_okX : forall bc b1 b2 n2 k1 z1 k2 z2,
  apq_fast_lit (mk_apq bc b1 b2 n2) k1 (zlit64 z1) k2 (zlit64 z2) = true ->
  ranges_apart_xB bc b1 k1 (ELit z1) b2 k2 (ELit z2) = true.
Proof. intros. unfold ranges_apart_xB. apply ranges_apartB_lit_by_lin. eapply apq_fast_lit_ok. exact H. Qed.
Lemma apq_fast_sym_okX : forall bc b1 k1 (w : nat) b2 k2 n2 q,
  q = mk_apq bc b1 b2 (aq_len q) ->
  match n2 with ELit _ => False | _ => True end ->
  apq_fast_sym q k1 (wlit_nw bc w) (wlit_c w) k2 n2 = true ->
  ranges_apart_xB bc b1 k1 (elen w) b2 k2 n2 = true.
Proof.
  intros bc b1 k1 w b2 k2 n2 q Hq Hn H.
  apply ranges_apart_xB_by_lin; [unfold elen; destruct n2; try exact I; destruct Hn| |].
  - unfold apq_fast_sym in H. rewrite Hq in H. unfold mk_apq in H. cbn [aq_sh] in H.
    destruct (shares_var b1 b2); [reflexivity|discriminate].
  - unfold apq_fast_sym in H. rewrite Hq in H. unfold mk_apq in H.
    cbn [aq_sh aq_nw1 aq_nw2 aq_i1 aq_c1 aq_i2 aq_c2 aq_nwl aq_len] in H.
    destruct (shares_var b1 b2) eqn:HS; [|discriminate]. cbn [andb] in H.
    apply Bool.orb_true_iff in H. destruct H as [H|H].
    + left. destruct (lin_nowrapRB bc b2) eqn:N2; [|discriminate]. destruct (lin_nowrapRB bc b1) eqn:N1; [|discriminate].
      destruct (wlit_nw bc w) eqn:NW; [|discriminate]. cbn [andb] in H.
      destruct (lin_range _ _ _) as [[lo hi]|] eqn:HR; [|discriminate].
      eapply lin_ge0B_fast with (lo := lo) (hi := hi).
      * cbn [xt_nowrapB]. rewrite N2. reflexivity.
      * cbn [xt_nowrapB]. unfold wlit_nw in NW. unfold elen. rewrite N1, NW. reflexivity.
      * unfold elen. rewrite xt_lin_lit, xt_lin_k. exact HR.
      * revert H. match goal with |- ?a = true -> ?b = true => replace b with a; [exact (fun h => h)|] end.
        f_equal. unfold wlit_c, elen. cbn [xt_const]. lia.
    + right. destruct (expr_eqb n2 _) eqn:EL; [|discriminate]. apply p_expr_eqb_eq in EL.
      destruct (lin_nowrapRB bc b1) eqn:N1; [|discriminate]. destruct (lin_nowrapRB bc b2) eqn:N2; [|discriminate].
      destruct (lin_nowrapRB bc (aq_len q)) eqn:NL; [|discriminate]. cbn [andb] in H.
      destruct (lin_range _ _ _) as [[lo hi]|] eqn:HR; [|discriminate].
      rewrite <- EL in NL, HR, H.
      eapply lin_ge0B_fast with (lo := lo) (hi := hi).
      * cbn [xt_nowrapB]. rewrite N1. reflexivity.
      * cbn [xt_nowrapB]. rewrite N2, NL. reflexivity.
      * rewrite xt_lin_k, xt_lin_k2. exact HR.
      * revert H. match goal with |- ?a = true -> ?b = true => replace b with a; [exact (fun h => h)|] end.
        f_equal. cbn [xt_const]. lia.
Qed.
(* [comment removed for export] *)
Fixpoint aq_lookup (l : list (expr * apq)) (e : expr) : option apq :=
  match l with
  | [] => None
  | (b, q) :: rest => if expr_eqb e b then Some q else aq_lookup rest e
  end.
Lemma aq_lookup_map : forall (f : expr -> apq) keys e q,
  aq_lookup (map (fun b => (b, f b)) keys) e = Some q -> q = f e.
Proof.
  intros f keys e q. induction keys as [|b rest IH]; cbn; [discriminate|].
  destruct (expr_eqb e b) eqn:E; [|exact IH]. intros H. injection H as <-. apply p_expr_eqb_eq in E. subst. reflexivity.
Qed.
Local Close Scope Z_scope.
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
      match prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 false with
      | PKeep => chainK bc rest K same_of br2
      | PRepl l => chain_slow bc rest l
      end
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint chainK2 (bc : bctx) (sxs : list stx) (K : kentry) (okb : option expr) (same_of : positive -> bool) (br2 : option (Z * Z))
         (fa_of : stx -> kentry -> bool) : list kentry :=
  match sxs with
  | [] => [K]
  | sx :: rest =>
      match prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 (fa_of sx K) with
      | PKeep => chainK2 bc rest K okb same_of br2 fa_of
      | PRepl l =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2 bc rest K' okb same_of br2 fa_of else chain_slow bc rest [K']
                                  | None => chain_slow bc rest [K']
                                  end) l
          | None => chain_slow bc rest l
          end
      end
  end.
Definition fa_none : stx -> kentry -> bool := fun _ _ => false.


Fixpoint entriesV (bc : bctx) (sxs : list stx) (kn : list kentry) (t : ntab) : list kentry :=
  match kn with
  | [] => []
  | K :: rest =>
      match kbase K with
      | Some kb => let '(r, t') := intern bc t kb in
                   let '(bid, bi) := r in
                   chainK2 bc sxs K (Some kb) (Pos.eqb bid) (bi_br bi) fa_none ++ entriesV bc sxs rest t'
      | None => chainK2 bc sxs K None (fun _ => false) None fa_none ++ entriesV bc sxs rest t
      end
  end.
Fixpoint stores_part (bc : bctx) (sxs : list stx) : list kentry :=   (* [comment removed for export] *)
  match sxs with
  | [] => []
  | sx :: newer => stores_part bc newer ++ chainK2 bc newer (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx) fa_none
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
  assert (E : pk_list K (prune1pcK (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 false)
              = fst (fst (prune1pcB (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K [] (obrB (mkbc fk) K)))).
  { autorewrite with bceq. destruct (kbase K) as [kb|] eqn:HB.
    - destruct HK as [-> HK]. apply Forall_cons_iff in HK as [HK1 HK].
      unfold obrB. rewrite HB. apply prune1pcK_eq; [rewrite HB; exact HK1 | apply FA_OK_false].
    - unfold obrB. rewrite HB. subst br2. apply prune1pcK_eq; [rewrite HB; exact I | apply FA_OK_false]. }
  destruct (prune1pcK _ _ _ _ _ K _ br2 false) as [|l]; cbn [pk_list] in E.
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
Lemma chainK2_eq : forall fk sxs K okb same_of br2 fa_of,
  Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))) sxs ->
  okb = kbase K ->
  match okb with
  | Some kb => br2 = base_rangeB (mkbc fk) kb /\ Forall (fun sx => same_of (sx_bid sx) = expr_eqb kb (a_base (sx_a sx))) sxs
  | None => br2 = None
  end ->
  (forall sx K', In sx sxs -> kbase K' = kbase K -> FA_OK fk (sx_sp sx) (sx_a sx) (sx_w sx) br2 K' (fa_of sx K')) ->
  chainK2 (mkbc fk) sxs K okb same_of br2 fa_of = chain_slow (mkbc fk) sxs [K].
Proof.
  intros fk sxs. induction sxs as [|sx rest IH]; intros K okb same_of br2 fa_of HS Hokb HK HFA; [reflexivity|].
  apply Forall_cons_iff in HS as [H1 HS]. cbn [chainK2 chain_slow flat_map]. rewrite app_nil_r.
  unfold g1cB at 1.
  assert (E : pk_list K (prune1pcK (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 (fa_of sx K))
              = fst (fst (prune1pcB (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K [] (obrB (mkbc fk) K)))).
  { (repeat first [ rewrite prune1pcB_eqf ]). unfold obrB. rewrite <- Hokb. destruct okb as [kb|].
    - destruct HK as [-> HK]. apply Forall_cons_iff in HK as [HK1 HK].
      apply prune1pcK_eq; [rewrite <- Hokb; exact HK1 | apply HFA; [left; reflexivity | reflexivity]].
    - subst br2. apply prune1pcK_eq; [rewrite <- Hokb; exact I | apply HFA; [left; reflexivity | reflexivity]]. }
  assert (HFA' : forall sx0 K', In sx0 rest -> kbase K' = kbase K -> FA_OK fk (sx_sp sx0) (sx_a sx0) (sx_w sx0) br2 K' (fa_of sx0 K'))
    by (intros sx0 K' Hi HB; apply HFA; [right; exact Hi | exact HB]).
  destruct (prune1pcK _ _ _ _ _ K _ br2 _) as [|l]; cbn [pk_list] in E; rewrite <- E.
  - apply IH; [exact HS|exact Hokb| |exact HFA']. destruct okb as [kb|]; [|exact HK].
    destruct HK as [Hbr HK]. apply Forall_cons_iff in HK as [_ HK]. exact (conj Hbr HK).
  - destruct okb as [kb|]; [|reflexivity]. rewrite (chain_slow_flat_map _ rest l).
    f_equal. apply functional_extensionality. intros K'.
    destruct (kbase K') as [kb'|] eqn:HB'; [|reflexivity].
    destruct (expr_eqb kb' kb) eqn:EQ; [|reflexivity].
    apply p_expr_eqb_eq in EQ. subst kb'.
    apply IH; [exact HS|symmetry; exact HB'| |].
    + destruct HK as [Hbr HK]. apply Forall_cons_iff in HK as [_ HK]. exact (conj Hbr HK).
    + intros sx0 K'' Hi HB''. apply HFA'; [exact Hi|]. rewrite HB'', HB'. exact Hokb.
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
      rewrite chainK2_eq; [apply chain_slow_eq; exact (Forall_SX_sp _ _ _ HS) | exact (Forall_SX_sp _ _ _ HS) | symmetry; exact HB | | intros; apply FA_OK_false].
      cbn [bi_br]. split; [reflexivity|]. exact (Forall_SX_same _ _ _ _ _ HT' HIn HS').
    + rewrite (IH t HT HS). f_equal.
      rewrite chainK2_eq; [apply chain_slow_eq; exact (Forall_SX_sp _ _ _ HS) | exact (Forall_SX_sp _ _ _ HS) | symmetry; exact HB | | intros; apply FA_OK_false].
      reflexivity.
Qed.

Lemma stores_part_eq : forall fk t sxs,
  NTI (mkbc fk) t -> Forall (SX_OK (mkbc fk) t) sxs ->
  stores_part (mkbc fk) sxs = SPRo fk (map strip sxs).
Proof.
  intros fk t sxs HT. induction sxs as [|sx newer IH]; intros HS; [reflexivity|].
  apply Forall_cons_iff in HS as [H1 HS]. cbn [stores_part SPRo map]. rewrite (IH HS). f_equal.
  destruct H1 as (HIn & Hbr & _). destruct (sx_a sx) as [b o] eqn:Ea. cbn [a_base a_off] in HIn, Hbr.
  rewrite chainK2_eq; [unfold kw, strip; rewrite Ea; apply chain_slow_eq; exact (Forall_SX_sp _ _ _ HS) | exact (Forall_SX_sp _ _ _ HS) | reflexivity | | intros; apply FA_OK_false].
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
         (br2 : option (Z * Z)) (fa_of : stx -> kentry -> bool) : list kentry :=
  match fl with
  | [] => [K]
  | (sx, rest) :: fl' =>
      match prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 (fa_of sx K) with
      | PKeep => chainKF bc fl' K okb same_of br2 fa_of
      | PRepl l =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2 bc rest K' okb same_of br2 fa_of else chain_slow bc rest [K']
                                  | None => chain_slow bc rest [K']
                                  end) l
          | None => chain_slow bc rest l
          end
      end
  end.

(* [comment removed for export] *)
Fixpoint alookupP {T : Type} (l : list (positive * T)) (p : positive) : option T :=
  match l with
  | [] => None
  | (q, x) :: rest => if Pos.eqb p q then Some x else alookupP rest p
  end.
Fixpoint store_bases (sxs : list stx) : list (positive * expr) :=
  match sxs with
  | [] => []
  | sx :: rest => let r := store_bases rest in
                  match alookupP r (sx_bid sx) with Some _ => r | None => (sx_bid sx, a_base (sx_a sx)) :: r end
  end.
Fixpoint mk_aqs (bc : bctx) (sbs : list (positive * expr)) (kb len : expr) : list (positive * apq) :=
  match sbs with
  | [] => []
  | (bid, sb) :: rest => if (shares_var sb kb && negb (expr_eqb sb kb))%bool then (bid, mk_apq bc sb kb len) :: mk_aqs bc rest kb len
                         else mk_aqs bc rest kb len
  end.
Definition fa_entry (bc : bctx) (aqs : list (positive * apq)) (kb : expr) (sx : stx) (K : kentry) : bool :=
  match aqs with
  | [] => false
  | _ =>
    match kbkl K with
    | Some (kb', kk', len') =>
        if expr_eqb kb' kb then
          match alookupP aqs (sx_bid sx) with
          | Some q =>
              match len' with
              | ELit z2 => apq_fast_lit q (a_off (sx_a sx)) (zlit64 (Z.of_nat (sx_w sx))) kk' (zlit64 z2)
              | _ => apq_fast_sym q (a_off (sx_a sx)) (wlit_nw bc (sx_w sx)) (wlit_c (sx_w sx)) kk' len'
              end
          | None => false
          end
        else false
    | None => false
    end
  end.
Fixpoint entriesG (bc : bctx) (sbs : list (positive * expr)) (sxs : list stx) (gl : ptree gfl) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | Some ei =>
           let okb := kbase K in
           let same_of := match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end in
           let br2 := match okb with Some _ => ei_br ei | None => None end in
           let fa_of := match okb, kbkl K with
                        | Some kb, Some (_, _, len) => fa_entry bc (mk_aqs bc sbs kb len) kb
                        | _, _ => fa_none
                        end in
           match pt_get gl (ei_gid ei) with
           | Some (g, fl) => if inb g ei then chainKF bc fl K okb same_of br2 fa_of else chainK2 bc sxs K okb same_of br2 fa_of
           | None => chainK2 bc sxs K okb same_of br2 fa_of
           end
       | None => chainK2 bc sxs K None (fun _ => false) None fa_none
       end) ++ entriesG bc sbs sxs gl rest irest
  | _, _ => []
  end.

Definition carryG (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxs bc log nt_empty in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, _) := r in
  stores_part bc sxs ++ entriesG bc (store_bases sxs) sxs (mk_gl (gs_bnds gs) sxs) kn infos.

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
  forall fa, prune1pcK bc sp wa w wv K false (base_rangeB bc kb) fa = PKeep.
Proof.
  intros bc sp wa w wv K kb kk m lo1 hi1 lo2 hi2 HB HD Hsp Hbr Hnum fa. destruct fa; [reflexivity|].
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [kbase kdescr] in HB, HD; try discriminate; injection HB as ->;
    try (injection HD as <- <-); try (destruct len as [z| | | | | | |]; try discriminate; injection HD as <- <-);
    unfold prune1pcK; (destruct (pk_keepb _ _ _ _); [reflexivity|]); unfold prune1pcK0; cbn [a_base a_off]; unfold ranges_apart_pcB; cbn [elen]; rewrite Hsp, Hbr;
    match goal with |- context [if ((?a <=? ?b) || (?c <=? ?d))%Z then _ else _] =>
      replace ((a <=? b) || (c <=? d))%Z%bool with true; [reflexivity|];
      symmetry; apply Bool.orb_true_iff; destruct Hnum as [H|H]; [left|right]; apply Z.leb_le; rewrite ?zlit64_idem; lia end.
Qed.

Lemma prune1pcK_keep_img : forall bc sp wa w wv lo hi m lo1 hi1 lo2 hi2 same br2,
  kdescr (KImg lo hi) = Some (ELit 0%Z, lo, Some m) ->
  expr_eqb (ELit 0%Z) (a_base wa) = false ->
  sp_rng sp = Some (lo1, hi1) -> base_rangeB bc (ELit 0%Z) = Some (lo2, hi2) ->
  (hi1 + a_off wa + zlit64 (Z.of_nat w) <= lo2 + lo \/ hi2 + lo + m <= lo1 + a_off wa)%Z ->
  forall fa, prune1pcK bc sp wa w wv (KImg lo hi) same br2 fa = PKeep.
Proof.
  intros bc sp wa w wv lo hi m lo1 hi1 lo2 hi2 same br2 HD Hne Hsp Hbr Hnum fa. destruct fa; [reflexivity|].
  cbn [kdescr] in HD. destruct (Z.ltb (hi - lo) (2 ^ 64)) eqn:Hlt; [|discriminate]. injection HD as <-.
  unfold prune1pcK. destruct (pk_keepb _ _ _ _); [reflexivity|]. unfold prune1pcK0. destruct wa as [wb k]. cbn [a_base a_off] in *.
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

Lemma chainKF_eq : forall bc g sxs K okb same_of br2 fa_of,
  (forall sx, In sx sxs -> verdict sx g = true ->
     prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 (fa_of sx K) = PKeep) ->
  chainKF bc (mk_fl g sxs) K okb same_of br2 fa_of = chainK2 bc sxs K okb same_of br2 fa_of.
Proof.
  intros bc g sxs. induction sxs as [|sx rest IH]; intros K okb same_of br2 fa_of Hf; [reflexivity|].
  cbn [mk_fl chainK2].
  assert (IH' : chainKF bc (mk_fl g rest) K okb same_of br2 fa_of = chainK2 bc rest K okb same_of br2 fa_of)
    by (apply IH; intros; apply Hf; [right|]; assumption).
  destruct (verdict sx g) eqn:Hv.
  - rewrite (Hf sx (or_introl eq_refl) Hv). exact IH'.
  - cbn [chainKF]. destruct (prune1pcK _ _ _ _ _ K _ br2 _); [exact IH'|reflexivity].
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
Definition SBS_OK (sxs : list stx) (sbs : list (positive * expr)) : Prop :=
  forall bid sb, In (bid, sb) sbs -> exists sx0, In sx0 sxs /\ bid = sx_bid sx0 /\ sb = a_base (sx_a sx0).
Lemma alookupP_In : forall (T : Type) (l : list (positive * T)) p x, alookupP l p = Some x -> In (p, x) l.
Proof.
  intros T l. induction l as [|[q y] rest IH]; cbn; intros p x H; [discriminate|].
  destruct (Pos.eqb_spec p q) as [->|NE]; [injection H as <-; left; reflexivity | right; exact (IH _ _ H)].
Qed.
Lemma store_bases_ok : forall sxs, SBS_OK sxs (store_bases sxs).
Proof.
  induction sxs as [|sx rest IH]; intros bid sb Hin; [destruct Hin|].
  cbn [store_bases] in Hin. destruct (alookupP (store_bases rest) (sx_bid sx)).
  - destruct (IH _ _ Hin) as (sx0 & H0 & H1 & H2). exists sx0. split; [right; exact H0|]. split; assumption.
  - destruct Hin as [Hin|Hin].
    + injection Hin as <- <-. exists sx. split; [left; reflexivity|]. split; reflexivity.
    + destruct (IH _ _ Hin) as (sx0 & H0 & H1 & H2). exists sx0. split; [right; exact H0|]. split; assumption.
Qed.
Lemma mk_aqs_lookup : forall bc sbs kb len bid q,
  alookupP (mk_aqs bc sbs kb len) bid = Some q ->
  exists sb, In (bid, sb) sbs /\ expr_eqb sb kb = false /\ q = mk_apq bc sb kb len.
Proof.
  intros bc sbs kb len. induction sbs as [|[bid' sb'] rest IH]; cbn [mk_aqs]; intros bid q H; [discriminate|].
  destruct (shares_var sb' kb && negb (expr_eqb sb' kb))%bool eqn:C.
  - cbn [alookupP] in H. destruct (Pos.eqb_spec bid bid') as [->|NE].
    + injection H as <-. exists sb'. split; [left; reflexivity|]. apply andb_prop in C as [_ C].
      split; [destruct (expr_eqb sb' kb); [discriminate|reflexivity] | reflexivity].
    + destruct (IH _ _ H) as (sb & H1 & H2 & H3). exists sb. split; [right; exact H1|]. split; assumption.
  - destruct (IH _ _ H) as (sb & H1 & H2 & H3). exists sb. split; [right; exact H1|]. split; assumption.
Qed.
Lemma expr_eqb_false_sym : forall a b, expr_eqb a b = false -> expr_eqb b a = false.
Proof.
  intros a b H. destruct (expr_eqb b a) eqn:E; [|reflexivity].
  apply p_expr_eqb_eq in E. subst. rewrite p_expr_eqb_refl in H. discriminate.
Qed.
Lemma ranges_apart_pcB_by_lin_lit : forall bc sp b1 k1 z1 br2 b2 k2 z2,
  lin_apartB bc b1 k1 (zlit64 z1) b2 k2 (zlit64 z2) = true ->
  ranges_apart_pcB bc sp b1 k1 (ELit z1) br2 b2 k2 (ELit z2) = true.
Proof.
  intros. unfold ranges_apart_pcB. cbv zeta.
  match goal with |- (if ?c then true else _) = true => destruct c; [reflexivity|] end.
  destruct (in_sidesB _ _ _ _ _); [reflexivity|]. exact H.
Qed.
Lemma fa_entry_ok : forall fk t sxs sbs kb len sx K' br2,
  NTI (mkbc fk) t -> Forall (SX_OK (mkbc fk) t) sxs -> SBS_OK sxs sbs ->
  In sx sxs -> kbase K' = Some kb ->
  FA_OK fk (sx_sp sx) (sx_a sx) (sx_w sx) br2 K' (fa_entry (mkbc fk) (mk_aqs (mkbc fk) sbs kb len) kb sx K').
Proof.
  intros fk t sxs sbs kb len sx K' br2 HT HS HSB Hsx HB Hfa. unfold fa_entry in Hfa.
  destruct (mk_aqs (mkbc fk) sbs kb len) as [|a0 arest] eqn:EA; [discriminate|]. rewrite <- EA in Hfa.
  destruct (kbkl K') as [[[kb' kk'] len']|] eqn:HK; [|discriminate].
  destruct (expr_eqb kb' kb) eqn:EK; [|discriminate]. apply p_expr_eqb_eq in EK. subst kb'.
  destruct (alookupP _ (sx_bid sx)) as [q|] eqn:HL; [|discriminate].
  destruct (mk_aqs_lookup _ _ _ _ _ _ HL) as (sb & Hin & Hne & ->).
  destruct (HSB _ _ Hin) as (sx0 & Hsx0 & Hbid & ->).
  (* [comment removed for export] *)
  pose proof (proj1 (Forall_forall _ _) HS sx Hsx) as (SXin & _ & _).
  pose proof (proj1 (Forall_forall _ _) HS sx0 Hsx0) as (SX0in & _ & _).
  pose proof (nt_same_eq _ _ _ _ _ _ HT SX0in SXin) as EQB. rewrite <- Hbid, Pos.eqb_refl in EQB.
  symmetry in EQB. apply p_expr_eqb_eq in EQB. rewrite EQB in Hne, Hfa. clear EQB.
  exists kb, kk', len'. split; [first [reflexivity | exact HK]|]. split; [apply expr_eqb_false_sym; exact Hne|].
  destruct len' as [z2| | | | | | |].
  - apply ranges_apart_pcB_by_lin_lit. unfold elen. eapply apq_fast_lit_ok. exact Hfa.
  - apply (apq_fast_sym_ok (mkbc fk) (sx_sp sx) (a_base (sx_a sx)) (a_off (sx_a sx)) (sx_w sx) br2 kb kk' _ (mk_apq (mkbc fk) (a_base (sx_a sx)) kb len)); [reflexivity|exact I|exact Hfa].
  - apply (apq_fast_sym_ok (mkbc fk) (sx_sp sx) (a_base (sx_a sx)) (a_off (sx_a sx)) (sx_w sx) br2 kb kk' _ (mk_apq (mkbc fk) (a_base (sx_a sx)) kb len)); [reflexivity|exact I|exact Hfa].
  - apply (apq_fast_sym_ok (mkbc fk) (sx_sp sx) (a_base (sx_a sx)) (a_off (sx_a sx)) (sx_w sx) br2 kb kk' _ (mk_apq (mkbc fk) (a_base (sx_a sx)) kb len)); [reflexivity|exact I|exact Hfa].
  - apply (apq_fast_sym_ok (mkbc fk) (sx_sp sx) (a_base (sx_a sx)) (a_off (sx_a sx)) (sx_w sx) br2 kb kk' _ (mk_apq (mkbc fk) (a_base (sx_a sx)) kb len)); [reflexivity|exact I|exact Hfa].
  - apply (apq_fast_sym_ok (mkbc fk) (sx_sp sx) (a_base (sx_a sx)) (a_off (sx_a sx)) (sx_w sx) br2 kb kk' _ (mk_apq (mkbc fk) (a_base (sx_a sx)) kb len)); [reflexivity|exact I|exact Hfa].
  - apply (apq_fast_sym_ok (mkbc fk) (sx_sp sx) (a_base (sx_a sx)) (a_off (sx_a sx)) (sx_w sx) br2 kb kk' _ (mk_apq (mkbc fk) (a_base (sx_a sx)) kb len)); [reflexivity|exact I|exact Hfa].
  - apply (apq_fast_sym_ok (mkbc fk) (sx_sp sx) (a_base (sx_a sx)) (a_off (sx_a sx)) (sx_w sx) br2 kb kk' _ (mk_apq (mkbc fk) (a_base (sx_a sx)) kb len)); [reflexivity|exact I|exact Hfa].
Qed.

Lemma entriesG_eq : forall fk sxs sbs bnds kn infos t1,
  NTI (mkbc fk) t1 -> Forall (SX_OK (mkbc fk) t1) sxs -> SBS_OK sxs sbs -> Forall2 (EINF (mkbc fk) t1) kn infos ->
  entriesG (mkbc fk) sbs sxs (mk_gl bnds sxs) kn infos = chainRo fk (map strip sxs) kn.
Proof.
  intros fk sxs sbs bnds kn infos t1 HT HS HSB HF. induction HF as [|K oi rest irest HK HF IH].
  - cbn. clear. induction sxs as [|sx r IH]; [reflexivity|]. cbn. destruct (strip sx). exact IH.
  - cbn [entriesG]. change (K :: rest) with ([K] ++ rest). rewrite chainRo_app, IH. f_equal.
    rewrite <- (chain_slow_eq fk sxs [K] (Forall_SX_sp _ _ _ HS)).
    pose proof (Forall_SX_sp _ _ _ HS) as HSP.
    destruct oi as [ei|]; cbn [EINF] in HK.
    + destruct HK as (HD & HIn & Hbr).
      set (fa_of := match kbase K, kbkl K with
                    | Some kb, Some (_, _, len) => fa_entry (mkbc fk) (mk_aqs (mkbc fk) sbs kb len) kb
                    | _, _ => fa_none
                    end).
      assert (HFA : forall br2 sx K', In sx sxs -> kbase K' = kbase K -> FA_OK fk (sx_sp sx) (sx_a sx) (sx_w sx) br2 K' (fa_of sx K')).
      { intros br2 sx K' Hsx HB'. subst fa_of. destruct (kbase K) as [kb|] eqn:HBK; [|apply FA_OK_false].
        destruct (kbkl K) as [[[? ?] len]|]; [|apply FA_OK_false].
        eapply fa_entry_ok; [exact HT|exact HS|exact HSB|exact Hsx|exact HB']. }
      (* [comment removed for export] *)
      assert (FULL : forall okb, okb = kbase K ->
        chainK2 (mkbc fk) sxs K okb
          (match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end)
          (match okb with Some _ => ei_br ei | None => None end) fa_of = chain_slow (mkbc fk) sxs [K]).
      { intros okb Hokb. apply chainK2_eq; [exact HSP|exact Hokb| |intros sx K' Hsx HB'; apply HFA; [exact Hsx|exact HB']].
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
    + apply chainK2_eq; [exact HSP| symmetry; apply kdescr_None_kbase; exact HK | reflexivity | intros; apply FA_OK_false].
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
  rewrite (stores_part_eq _ _ _ HT0 HS0), (entriesG_eq _ _ _ _ _ _ _ HT1 HS1 (store_bases_ok sxs) HF), Hmap. reflexivity.
Qed.

(* [comment removed for export] *)
Definition carryK (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | [_], [] | [_; _], [] => carryB bc log kn []
  | _, [] => (carryG bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma carryK_eq : forall log kn hints,
  carryK (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof.
  intros log kn hints. unfold carryK. destruct log as [|s older]; [reflexivity|].
  destruct hints as [|h hs]; [|destruct older as [|? [|? ?]]; apply carryB_eq].
  destruct older as [|s2 [|s3 older]]; [apply carryB_eq|apply carryB_eq|].
  rewrite carry_vertical, carryG_eq. reflexivity.
Qed.

End AX2B.
