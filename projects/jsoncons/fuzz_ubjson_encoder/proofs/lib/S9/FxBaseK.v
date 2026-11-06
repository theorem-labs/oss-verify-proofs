(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From Stdlib Require PrimInt63 Uint63.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec AxSymExec3K AxSymExec3BK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import FxImgK FxKnownBitsK.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Import ListNotations.

Module BXIK.
Import PrimInt63.
Definition B61 : int := 2305843009213693952%uint63.
Definition B62 : int := 4611686018427387904%uint63.
Definition i0 : int := 0%uint63.
End BXIK.
Module BASFK.
Import AX2K. Import AX2BK.
Local Open Scope Z_scope.
Local Close Scope Z_scope.

Fixpoint neqb4 (a b : nat) {struct a} : bool :=
  match a, b with
  | S (S (S (S a'))), S (S (S (S b'))) => neqb4 a' b'
  | _, _ => Nat.eqb a b
  end.
Lemma neqb4_eq : forall a b, neqb4 a b = Nat.eqb a b.
Proof.
  intros a. induction a as [a IH] using lt_wf_ind. intros b.
  destruct a as [|[|[|[|a']]]]; try reflexivity.
  destruct b as [|[|[|[|b']]]]; try reflexivity.
  cbn [neqb4 Nat.eqb]. apply IH. lia.
Qed.
Fixpoint expr_eqbF (x y : expr) : bool :=
  match x, y with
  | ELit a, ELit b => Z.eqb a b
  | EVar a, EVar b => neqb4 a b
  | EAlu o a b, EAlu o' a' b' => if aluop_eqb o o' then if expr_eqbF a a' then expr_eqbF b b' else false else false
  | EAluw o a b, EAluw o' a' b' => if aluop_eqb o o' then if expr_eqbF a a' then expr_eqbF b b' else false else false
  | EMd o a b, EMd o' a' b' => if mulop_eqb o o' then if expr_eqbF a a' then expr_eqbF b b' else false else false
  | EMdw o a b, EMdw o' a' b' => if mulop_eqb o o' then if expr_eqbF a a' then expr_eqbF b b' else false else false
  | EExt s l n a, EExt s' l' n' a' =>
      if Bool.eqb s s' then if neqb4 l l' then if neqb4 n n' then expr_eqbF a a' else false else false else false
  | EBlob s k i n, EBlob s' k' i' n' =>
      if Bool.eqb s s' then if neqb4 k k' then if Z.eqb i i' then neqb4 n n' else false else false else false
  | _, _ => false
  end.
Lemma expr_eqbF_eq : forall x y, expr_eqbF x y = expr_eqb x y.
Proof.
  induction x; destruct y; cbn [expr_eqbF expr_eqb]; rewrite ?neqb4_eq, ?IHx, ?IHx1, ?IHx2; try reflexivity;
    repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.
Lemma expr_eqbF_fe : expr_eqbF = expr_eqb.
Proof. apply functional_extensionality; intros x. apply functional_extensionality; intros y. apply expr_eqbF_eq. Qed.
Lemma expr_eqbF_refl : forall x, expr_eqbF x x = true.
Proof. intros x. rewrite expr_eqbF_eq. apply kx_expr_eqb_refl. Qed.
Lemma expr_eqbF_true : forall x y, expr_eqbF x y = true -> x = y.
Proof. intros x y H. rewrite expr_eqbF_eq in H. apply p_expr_eqb_eq. exact H. Qed.
Local Open Scope Z_scope.

Fixpoint find_rangeF (kn : list kentry) (e : expr) : option (Z * Z) :=
  match kn with
  | [] => None
  | KRange e' lo hi :: rest =>
      if expr_eqbF e e' then Some (lo, hi) else
      match e with
      | ELit _ => find_rangeF rest e
      | _ =>
        let '(v, c) := lit_strip e in
        let '(v', c') := lit_strip e' in
        if expr_eqbF v v' then
          let d := (c - c')%Z in
          if (if Z.leb 0 lo then if Z.leb lo hi then if Z.ltb hi two64 then if Z.leb 0 (lo + d) then Z.ltb (hi + d) two64 else false else false else false else false)
          then Some ((lo + d)%Z, (hi + d)%Z) else find_rangeF rest e
        else find_rangeF rest e
      end
  | _ :: rest => find_rangeF rest e
  end.
Lemma find_rangeF_eq : forall kn e, find_rangeF kn e = find_range kn e.
Proof.
  induction kn as [|K rest IH]; intros e; [reflexivity|]. cbn [find_rangeF find_range]. rewrite !IH.
  destruct K as [a w v|a l|a l k|lo hi|e' m|e' lo hi|a n|c1 m1 c2 m2|a l c|a l]; try reflexivity.
  rewrite expr_eqbF_eq. destruct (expr_eqb e e'); [reflexivity|].
  destruct e; try reflexivity;
    (match goal with |- context [lit_strip ?x] => destruct (lit_strip x) as [v0 c0] end;
     destruct (lit_strip e') as [v' c']; rewrite expr_eqbF_eq; destruct (expr_eqb v0 v'); [|reflexivity];
     change (2 ^ 64) with two64;
     destruct (Z.leb 0 lo); destruct (Z.leb lo hi); destruct (Z.ltb hi two64); destruct (Z.leb 0 (lo + (c0 - c'))); reflexivity).
Qed.
Definition find_rangeIF (ri : rindex) (e : expr) : option (Z * Z) := find_rangeF (ri_bucket ri (vkey_of e)) e.
Lemma find_rangeIF_eq : forall ri e, find_rangeIF ri e = find_rangeI ri e.
Proof. intros. unfold find_rangeIF, find_rangeI. apply find_rangeF_eq. Qed.
Lemma find_rangeIF_fe : find_rangeIF = find_rangeI.
Proof. repeat (apply functional_extensionality; intros ?). apply find_rangeIF_eq. Qed.

Fixpoint erange_fBF (fuel : nat) (bc : bctx) (e : expr) {struct fuel} : option (Z * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
  let erange := erange_fBF fuel' in
  match find_rangeIF (bc_ri bc) e with
  | Some r => Some (clampi r)
  | None =>
  match (let l := lin_of e in
         if lin_trivial l then None
         else match lin_range (erange bc) (fst l) (snd l) with
              | Some (lo, hi) =>

                  let q := zdiv64 lo in
                  if Z.eqb q (zdiv64 hi) then Some ((lo - q * two64)%Z, (hi - q * two64)%Z) else None
              | None => None
              end) with
  | Some r => Some r
  | None =>
  match e with
  | ELit z => let v := zmod64 z in Some (v, v)
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

          let ra := erange bc a in
          match (match b, ra with
                 | ELit m, Some (al, ah) =>
                     let m' := (m mod two64)%Z in
                     let j := Z.log2 (m' + 1) in
                     if (if (if Z.eqb (m' + 1) (2 ^ j) then Z.leb (al / 2 ^ j) (ah / 2 ^ j) else false) then Z.eqb (al / 2 ^ j) (ah / 2 ^ j) else false)
                     then Some ((al mod 2 ^ j)%Z, (ah mod 2 ^ j)%Z)
                     else let jh := Z.log2 (two64 - m') in
                          if (if Z.eqb (two64 - m') (2 ^ jh) then Z.ltb jh 64 else false)
                          then Some ((al - al mod 2 ^ jh)%Z, (ah - ah mod 2 ^ jh)%Z)
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

      if sx then Some (0%Z, two64m1) else Some (0%Z, Z.min (2 ^ (8 * Z.of_nat n) - 1) (two64 - 1))%Z
  end
  end
  end
  end.
Lemma erange_fBF_fe : forall fuel, erange_fBF fuel = erange_fB fuel.
Proof.
  induction fuel as [|f IH]; apply functional_extensionality; intros bc; apply functional_extensionality; intros e; [reflexivity|].
  cbn [erange_fBF erange_fB]. rewrite IH, find_rangeIF_eq. reflexivity.
Qed.
Definition erange0BF (bc : bctx) (e : expr) : option (Z * Z) := erange_fBF erange_fuel bc e.
Definition erangeBF (bc : bctx) (e : expr) : option (Z * Z) :=
  let r := erange0BF bc e in
  let '(e', s) := deand e in
  if Z.eqb s 0 then r else

  let g := lin_galign (lin_of e) in
  let rnd := fun p : Z * Z => Some (round_itv g (fst p) (snd p)) in
  match erange0BF bc (unlin (lin_of e')) with
  | Some (lo', hi') =>
      if Z.leb s lo' then
        match r with
        | Some (lo, hi) => rnd (Z.max lo (lo' - s), Z.min hi hi')
        | None => rnd ((lo' - s)%Z, hi')
        end
      else match r with Some p => rnd p | None => None end
  | None => match r with Some p => rnd p | None => None end
  end.
Lemma erangeBF_fe : erangeBF = erangeB.
Proof.
  apply functional_extensionality; intros bc; apply functional_extensionality; intros e.
  unfold erangeBF, erangeB, erange0BF, erange0B. rewrite erange_fBF_fe. reflexivity.
Qed.

Definition zb (z : Z) : option PrimInt63.int :=
  match z with
  | Z0 => Some BXIK.B61
  | Zpos p => match IMGFK.p2i p 60 BXIK.i0 BXIK.i0 with Some v => Some (PrimInt63.add BXIK.B61 v) | None => None end
  | Zneg p => match IMGFK.p2i p 60 BXIK.i0 BXIK.i0 with Some v => Some (PrimInt63.sub BXIK.B61 v) | None => None end
  end.
Lemma wB63 : Uint63.wB = 2 ^ 63. Proof. reflexivity. Qed.
Lemma zb_spec : forall z a, zb z = Some a -> Uint63.to_Z a = z + 2 ^ 61 /\ - 2 ^ 60 < z < 2 ^ 60.
Proof.
  intros z a H. assert (EB : Uint63.to_Z BXIK.B61 = 2 ^ 61) by reflexivity.
  destruct z as [|p|p]; cbn [zb] in H.
  - injection H as <-. rewrite EB. split; lia.
  - destruct (IMGFK.p2i p 60 BXIK.i0 BXIK.i0) as [v|] eqn:E; [|discriminate]. injection H as <-.
    apply IMGFK.p2i_spec in E; [|change (Uint63.to_Z BXIK.i0) with 0; lia|change (Uint63.to_Z BXIK.i0) with 0; change (2 ^ 0) with 1; lia].
    change (Uint63.to_Z BXIK.i0) with 0 in E. change (Z.of_nat 60) with 60 in E. change (2 ^ 0) with 1 in E. destruct E as [E1 E2].
    rewrite Uint63.add_spec, EB, E1, wB63. rewrite Z.mod_small by lia. split; lia.
  - destruct (IMGFK.p2i p 60 BXIK.i0 BXIK.i0) as [v|] eqn:E; [|discriminate]. injection H as <-.
    apply IMGFK.p2i_spec in E; [|change (Uint63.to_Z BXIK.i0) with 0; lia|change (Uint63.to_Z BXIK.i0) with 0; change (2 ^ 0) with 1; lia].
    change (Uint63.to_Z BXIK.i0) with 0 in E. change (Z.of_nat 60) with 60 in E. change (2 ^ 0) with 1 in E. destruct E as [E1 E2].
    rewrite Uint63.sub_spec, EB, E1, wB63. rewrite Z.mod_small by lia. split; lia.
Qed.

Definition rng63 (r : option (Z * Z)) : option (PrimInt63.int * PrimInt63.int) :=
  match r with
  | Some (lo, hi) => match zb lo, zb hi with Some x, Some y => Some (x, y) | _, _ => None end
  | None => None
  end.

Definition ins (T : list (Z * expr)) : list (Z * expr) := fold_right (fun t acc => lins (fst t) (snd t) acc) [] T.
Definition nonnil {A : Type} (l : list A) : bool := match l with [] => false | _ => true end.

Definition wide (r : option (Z * Z)) : bool := match r with Some (lo, hi) => negb (Z.leb (hi - lo) conc_limit) | None => true end.

Definition pfail (bc : bctx) (e s : expr) : bool :=
  if closedb s then true else if evalS_def s e then wide (erangeB bc s) else true.

Record binfo : Type := BI {
  bi_b : expr;
  bi_er : option (Z * Z);
  bi_nf : bool;
  bi_c0 : Z;
  bi_triv : bool;
  bi_A : option (Z * Z);
  bi_W : bool;
  bi_e63 : option (PrimInt63.int * PrimInt63.int);
  bi_fa : option (PrimInt63.int * PrimInt63.int * bool)
}.
Definition fuel63 : nat := Nat.pred erange_fuel.
Definition nf_test (B : expr) (T1 T2 : list (Z * expr)) : bool :=
  if nonnil T1 then if nonnil T2 then if expr_eqb (lterms T1) B then if expr_eqb (lterms T2) B then
    if closedb B then false else Z.eqb (snd (deand B)) 0 else false else false else false else false.

Definition pfailm (bc : bctx) (B : expr) (er : option (Z * Z)) (s : expr) : bool :=
  if closedb s then true else if evalS_def s B then wide (if expr_eqb s B then er else erangeBF bc s) else true.

Definition fa_of (A : option (Z * Z)) : option (PrimInt63.int * PrimInt63.int * bool) :=
  match A with
  | Some (lo0, hi0) =>
      if Z.ltb lo0 hi0 then
        match zb lo0, zb hi0 with
        | Some l, Some h => Some (l, h, wide (Some (lo0, hi0)))
        | _, _ => None
        end
      else None
  | None => None
  end.
Definition mk_binfo (bc : bctx) (B : expr) : binfo :=
  let L := lin_of B in
  let T1 := ins (snd L) in
  let T2 := ins T1 in
  let er := erangeBF bc B in
  if nf_test B T1 T2 then
    let A := lin_range (erange_fBF fuel63 bc) 0 T1 in
    BI B er true (fst L) (match T1 with [(k, _)] => Z.eqb k 1 | _ => false end)
       A (forallb (pfailm bc B er) (subexprs B)) (rng63 er) (fa_of A)
  else BI B er false 0 false None false (rng63 er) None.

Lemma bi_er_eq : forall bc B, bi_er (mk_binfo bc B) = erangeB bc B.
Proof. intros. unfold mk_binfo. rewrite ?erangeBF_fe, ?erange_fBF_fe. cbv zeta. destruct (nf_test _ _ _); reflexivity. Qed.
Lemma bi_b_eq : forall bc B, bi_b (mk_binfo bc B) = B.
Proof. intros. unfold mk_binfo. rewrite ?erangeBF_fe, ?erange_fBF_fe. cbv zeta. destruct (nf_test _ _ _); reflexivity. Qed.

Definition erange_add (bc : bctx) (bi : binfo) (cc : Z) : option (Z * Z) :=
  match find_rangeIF (bc_ri bc) (EAlu ALU_ADD (bi_b bi) (ELit cc)) with
  | Some r => Some (clampi r)
  | None =>
    let c := snorm (bi_c0 bi + snorm cc) in
    match (if (if Z.eqb c 0 then bi_triv bi else false) then None
           else match bi_A bi with
                | Some (lo0, hi0) =>
                    let lo := lo0 + c in let hi := hi0 + c in let q := zdiv64 lo in
                    if Z.eqb q (zdiv64 hi) then Some (lo - q * two64, hi - q * two64) else None
                | None => None
                end) with
    | Some r => Some r
    | None =>
        match erange_fBF fuel63 bc (bi_b bi), erange_fBF fuel63 bc (ELit cc) with
        | Some (al, ah), Some (bl, bh) =>
            if Z.ltb (ah + bh) two64 then Some (al + bl, ah + bh)
            else if Z.leb two64 (al + bl) then Some (al + bl - two64, ah + bh - two64)
            else None
        | _, _ => None
        end
    end
  end.

Definition bsum (B : expr) (cc : Z) : expr := if Z.eqb cc 0 then B else EAlu ALU_ADD B (ELit cc).

Definition addc (bi : binfo) (hask : bool) (k imm : Z) : Z :=
  if hask then snorm (snorm (bi_c0 bi + snorm k) + snorm imm) else snorm (bi_c0 bi + snorm imm).

Definition bsum_range (bc : bctx) (bi : binfo) (cc : Z) : option (Z * Z) :=
  if Z.eqb cc 0 then bi_er bi else erange_add bc bi cc.

Definition bsum_noconc (bi : binfo) (cc : Z) (r : option (Z * Z)) : bool :=
  if bi_W bi then (if Z.eqb cc 0 then true else wide r) else false.

Definition bcache : Type := list binfo.
Fixpoint bfind (c : bcache) (B : expr) : option binfo :=
  match c with
  | [] => None
  | bi :: r => if expr_eqbF B (bi_b bi) then Some bi else bfind r B
  end.
Definition bget (bc : bctx) (c : bcache) (B : expr) : binfo * bcache :=
  match bfind c B with
  | Some bi => (bi, c)
  | None => let bi := mk_binfo bc B in (bi, bi :: c)
  end.
Definition BCOK (bc : bctx) (c : bcache) : Prop := forall bi, In bi c -> bi = mk_binfo bc (bi_b bi).
Lemma BCOK_nil : forall bc, BCOK bc []. Proof. intros bc bi []. Qed.
Lemma bfind_spec : forall bc c B bi, BCOK bc c -> bfind c B = Some bi -> bi = mk_binfo bc B.
Proof.
  intros bc c B bi. induction c as [|b r IH]; intros H F; [discriminate|]. cbn [bfind] in F.
  rewrite expr_eqbF_eq in F. destruct (expr_eqb B (bi_b b)) eqn:E.
  - injection F as <-. apply p_expr_eqb_eq in E. subst B. apply H. left. reflexivity.
  - apply IH; [|exact F]. intros x Hx. apply H. right. exact Hx.
Qed.
Lemma bget_spec : forall bc c B, BCOK bc c -> fst (bget bc c B) = mk_binfo bc B /\ BCOK bc (snd (bget bc c B)).
Proof.
  intros bc c B H. unfold bget. destruct (bfind c B) as [bi|] eqn:F; cbn [fst snd].
  - split; [apply (bfind_spec bc c B bi H F)|exact H].
  - split; [reflexivity|]. intros x [<-|Hx]; [rewrite bi_b_eq; reflexivity|apply H; exact Hx].
Qed.

Lemma ladd_lit : forall L c, ladd L (c, []) = (snorm (fst L + c), ins (snd L)).
Proof. reflexivity. Qed.
Lemma lin_range_shift0 : forall rng c ts,
  lin_range rng c ts = match lin_range rng 0 ts with Some (lo, hi) => Some (lo + c, hi + c) | None => None end.
Proof.
  intros rng c ts. induction ts as [|[k a] rest IH]; [reflexivity|]. cbn [lin_range]. rewrite IH.
  destruct (rng a) as [[al ah]|]; [|reflexivity]. destruct (lin_range rng 0 rest) as [[lo hi]|]; [|reflexivity].
  destruct (Z.leb 0 k); f_equal; f_equal; ring.
Qed.
Lemma erange_fB_add : forall f bc a b, erange_fB (S f) bc (EAlu ALU_ADD a b) =
  match find_rangeI (bc_ri bc) (EAlu ALU_ADD a b) with
  | Some r => Some (clampi r)
  | None =>
    match (let l := lin_of (EAlu ALU_ADD a b) in
           if lin_trivial l then None
           else match lin_range (erange_fB f bc) (fst l) (snd l) with
                | Some (lo, hi) => let q := zdiv64 lo in if Z.eqb q (zdiv64 hi) then Some ((lo - q * two64)%Z, (hi - q * two64)%Z) else None
                | None => None
                end) with
    | Some r => Some r
    | None =>
        match erange_fB f bc a, erange_fB f bc b with
        | Some (al, ah), Some (bl, bh) =>
            if Z.ltb (ah + bh) two64 then Some ((al + bl)%Z, (ah + bh)%Z)
            else if Z.leb two64 (al + bl) then Some ((al + bl - two64)%Z, (ah + bh - two64)%Z)
            else None
        | _, _ => None
        end
    end
  end.
Proof. reflexivity. Qed.
Lemma lin_trivial_eq : forall c T, lin_trivial (c, T) = if Z.eqb c 0 then (match T with [(k, _)] => Z.eqb k 1 | _ => false end) else false.
Proof. intros c T. unfold lin_trivial. destruct T as [|[k a] [|t r]]; destruct (Z.eqb c 0); reflexivity. Qed.
Lemma pfailm_eq : forall bc B s, pfailm bc B (erangeB bc B) s = pfail bc B s.
Proof.
  intros bc B s. unfold pfailm, pfail. rewrite ?erangeBF_fe. destruct (closedb s); [reflexivity|]. destruct (evalS_def s B); [|reflexivity].
  destruct (expr_eqb s B) eqn:E; [|reflexivity]. apply p_expr_eqb_eq in E. subst s. reflexivity.
Qed.
Lemma mk_binfo_nf : forall bc B, bi_nf (mk_binfo bc B) = true ->
  nf_test B (ins (snd (lin_of B))) (ins (ins (snd (lin_of B)))) = true /\
  mk_binfo bc B = BI B (erangeB bc B) true (fst (lin_of B)) (match ins (snd (lin_of B)) with [(k, _)] => Z.eqb k 1 | _ => false end)
                     (lin_range (erange_fB fuel63 bc) 0 (ins (snd (lin_of B)))) (forallb (pfail bc B) (subexprs B)) (rng63 (erangeB bc B))
                     (fa_of (lin_range (erange_fB fuel63 bc) 0 (ins (snd (lin_of B))))).
Proof.
  intros bc B H. unfold mk_binfo in *. rewrite ?erangeBF_fe, ?erange_fBF_fe in *. cbv zeta in *.
  destruct (nf_test B (ins (snd (lin_of B))) (ins (ins (snd (lin_of B))))); [|discriminate].
  split; [reflexivity|]. f_equal. apply forallb_ext_in || idtac.
  clear H. induction (subexprs B) as [|s r IH]; [reflexivity|]. cbn [forallb]. rewrite pfailm_eq, IH. reflexivity.
Qed.
Lemma nf_spec : forall bc B, bi_nf (mk_binfo bc B) = true ->
  nonnil (ins (snd (lin_of B))) = true /\ nonnil (ins (ins (snd (lin_of B)))) = true /\
  lterms (ins (snd (lin_of B))) = B /\ lterms (ins (ins (snd (lin_of B)))) = B /\ closedb B = false /\ snd (deand B) = 0.
Proof.
  intros bc B H. destruct (mk_binfo_nf bc B H) as [H1 _]. unfold nf_test in H1.
  destruct (nonnil (ins (snd (lin_of B)))); [|discriminate]. destruct (nonnil (ins (ins (snd (lin_of B))))); [|discriminate].
  destruct (expr_eqb (lterms (ins (snd (lin_of B)))) B) eqn:E1; [|discriminate].
  destruct (expr_eqb (lterms (ins (ins (snd (lin_of B))))) B) eqn:E2; [|discriminate].
  destruct (closedb B); [discriminate|]. apply Z.eqb_eq in H1. apply p_expr_eqb_eq in E1, E2. repeat split; assumption.
Qed.
Lemma unlin_nonnil : forall c T, nonnil T = true -> unlin (c, T) = bsum (lterms T) c.
Proof. intros c T H. unfold unlin, bsum. cbn [fst snd]. destruct T; [discriminate|reflexivity]. Qed.
Lemma mkAlu_add_A : forall bc B k imm, bi_nf (mk_binfo bc B) = true ->
  mkAlu ALU_ADD (EAlu ALU_ADD B (ELit k)) (ELit imm) = bsum B (addc (mk_binfo bc B) true k imm).
Proof.
  intros bc B k imm H. destruct (nf_spec bc B H) as (N1 & N2 & L1 & L2 & _ & _).
  destruct (mk_binfo_nf bc B H) as [_ EQ]. rewrite EQ. unfold addc. cbn [bi_c0].
  unfold mkAlu. cbn [is_lit].
  change (lin_of (EAlu ALU_ADD B (ELit k))) with (ladd (lin_of B) (snorm k, [])).
  change (lin_of (ELit imm)) with (snorm imm, @nil (Z * expr)).
  rewrite !ladd_lit. cbn [fst snd]. rewrite unlin_nonnil by exact N2. rewrite L2. reflexivity.
Qed.
Lemma mkAlu_add_B : forall bc B imm, bi_nf (mk_binfo bc B) = true -> is_lit B = None ->
  mkAlu ALU_ADD B (ELit imm) = bsum B (addc (mk_binfo bc B) false 0 imm).
Proof.
  intros bc B imm H HL. destruct (nf_spec bc B H) as (N1 & N2 & L1 & L2 & _ & _).
  destruct (mk_binfo_nf bc B H) as [_ EQ]. rewrite EQ. unfold addc. cbn [bi_c0].
  unfold mkAlu. rewrite HL.
  change (lin_of (ELit imm)) with (snorm imm, @nil (Z * expr)).
  rewrite ladd_lit. cbn [fst snd]. rewrite unlin_nonnil by exact N1. rewrite L1. reflexivity.
Qed.
Lemma erange_add_eq : forall bc B cc, bi_nf (mk_binfo bc B) = true ->
  erange_add bc (mk_binfo bc B) cc = erangeB bc (EAlu ALU_ADD B (ELit cc)).
Proof.
  intros bc B cc H. destruct (nf_spec bc B H) as (_ & _ & _ & _ & _ & DZ).
  unfold erangeB. cbn [deand]. destruct (deand B) as [a' s1] eqn:ED. cbn [snd] in DZ. subst s1.
  change (Z.eqb (0 + 0) 0) with true. cbv iota.
  unfold erange0B. change erange_fuel with (S fuel63). rewrite erange_fB_add.
  destruct (mk_binfo_nf bc B H) as [_ EQ]. rewrite EQ. unfold erange_add. cbn [bi_b bi_c0 bi_triv bi_A]. rewrite find_rangeIF_eq, ?erange_fBF_fe.
  destruct (find_rangeI (bc_ri bc) (EAlu ALU_ADD B (ELit cc))) as [r|]; [reflexivity|].
  change (lin_of (EAlu ALU_ADD B (ELit cc))) with (ladd (lin_of B) (snorm cc, [])).
  rewrite ladd_lit. cbv zeta. cbn [fst snd]. rewrite lin_trivial_eq.
  rewrite (lin_range_shift0 (erange_fB fuel63 bc) (snorm (fst (lin_of B) + snorm cc)) (ins (snd (lin_of B)))).
  destruct (lin_range (erange_fB fuel63 bc) 0 (ins (snd (lin_of B)))) as [[lo0 hi0]|]; reflexivity.
Qed.
Lemma bsum_range_eq : forall bc B cc, bi_nf (mk_binfo bc B) = true ->
  bsum_range bc (mk_binfo bc B) cc = erangeB bc (bsum B cc).
Proof.
  intros bc B cc H. unfold bsum_range, bsum. destruct (Z.eqb cc 0); [apply bi_er_eq|]. apply erange_add_eq. exact H.
Qed.

Lemma nubE_acc_in : forall l acc s, In s (nubE_acc l acc) -> In s l.
Proof.
  induction l as [|x r IH]; intros acc s H; [exact H|]. cbn [nubE_acc] in H.
  destruct (memE x acc); [right; apply (IH _ _ H)|]. destruct H as [<-|H]; [left; reflexivity|right; apply (IH _ _ H)].
Qed.
Lemma conc_fail : forall bc e l, (forall s, In s l -> pfail bc e s = true) -> conc_tryB bc e l = None.
Proof.
  intros bc e l. induction l as [|s r IH]; intros H; [reflexivity|]. cbn [conc_tryB].
  assert (Hr : conc_tryB bc e r = None) by (apply IH; intros x Hx; apply H; right; exact Hx).
  pose proof (H s (or_introl eq_refl)) as P. unfold pfail in P.
  destruct (closedb s); [exact Hr|]. destruct (evalS_def s e); cbn [negb]; [|exact Hr].
  unfold wide in P. destruct (erangeB bc s) as [[lo hi]|]; [|exact Hr].
  destruct (Z.leb (hi - lo) conc_limit); [discriminate|exact Hr].
Qed.
Lemma evalS_def_lit : forall s z, evalS_def s (ELit z) = true.
Proof. intros. cbn [evalS_def]. destruct (expr_eqb (ELit z) s); reflexivity. Qed.
Lemma conc_none : forall bc B cc, bi_nf (mk_binfo bc B) = true ->
  bsum_noconc (mk_binfo bc B) cc (erangeB bc (bsum B cc)) = true -> concretizeB bc (bsum B cc) = None.
Proof.
  intros bc B cc H HN. destruct (nf_spec bc B H) as (_ & _ & _ & _ & CL & _).
  destruct (mk_binfo_nf bc B H) as [_ EQ]. rewrite EQ in HN. unfold bsum_noconc in HN. cbn [bi_W] in HN.
  destruct (forallb (pfail bc B) (subexprs B)) eqn:W; [|discriminate].
  rewrite forallb_forall in W. unfold bsum in *. unfold concretizeB.
  destruct (Z.eqb cc 0).
  - rewrite CL. apply conc_fail. intros s Hs. apply W. apply (nubE_acc_in _ _ _ Hs).
  - cbn [closedb]. rewrite CL. cbn [andb]. apply conc_fail. intros s Hs. apply nubE_acc_in in Hs.
    cbn [subexprs] in Hs. apply in_app_or in Hs. destruct Hs as [Hs|Hs].
    + unfold pfail. destruct (closedb s) eqn:Cs; [reflexivity|]. cbn [evalS_def].
      destruct (expr_eqb (EAlu ALU_ADD B (ELit cc)) s) eqn:E.
      * apply p_expr_eqb_eq in E. subst s. exact HN.
      * pose proof (W s Hs) as P. unfold pfail in P. rewrite Cs in P.
        destruct (evalS_def s B); [destruct (expr_eqb (ELit cc) s); exact P|reflexivity].
    + apply in_app_or in Hs. destruct Hs as [Hs|Hs].
      * destruct Hs as [<-|[]]. reflexivity.
      * destruct Hs as [<-|[]]. unfold pfail. cbn [closedb]. rewrite CL. cbn [andb].
        destruct (evalS_def (EAlu ALU_ADD B (ELit cc)) (EAlu ALU_ADD B (ELit cc))); [exact HN|reflexivity].
Qed.

Local Notation "'φ' x" := (Uint63.to_Z x) (at level 0).
Definition I61 : PrimInt63.int := Uint63.of_Z (2 ^ 61).
Definition I63m : PrimInt63.int := Uint63.of_Z 63.
Definition I1 : PrimInt63.int := Uint63.of_Z 1.
Definition I0 : PrimInt63.int := Uint63.of_Z 0.

Inductive pex : Type :=
| PHole
| PLit (i : PrimInt63.int)
| PAlu (op : aluop) (a b : pex)
| PMul (a b : pex)
| PBad.
Fixpoint pcompile (s e : expr) : pex :=
  if expr_eqb e s then PHole else
  match e with
  | ELit w => match IMGFK.z61 (wrap64 w) with Some i => PLit i | None => PBad end
  | EAlu op a b =>
      match op with
      | ALU_ADD | ALU_SUB | ALU_AND | ALU_OR | ALU_XOR | ALU_SRL | ALU_SLL | ALU_SLTU => PAlu op (pcompile s a) (pcompile s b)
      | _ => PBad
      end
  | EMd M_MUL a b => PMul (pcompile s a) (pcompile s b)
  | _ => PBad
  end.

Definition chk61 (t : PrimInt63.int) : option PrimInt63.int := if PrimInt63.ltb t I61 then Some t else None.
Fixpoint evalP (p : pex) (z : PrimInt63.int) : option PrimInt63.int :=
  match p with
  | PHole => Some z
  | PLit i => Some i
  | PAlu op a b =>
      match evalP a z with
      | Some x =>
          match evalP b z with
          | Some y =>
              match op with
              | ALU_ADD => chk61 (PrimInt63.add x y)
              | ALU_SUB => if PrimInt63.leb y x then Some (PrimInt63.sub x y) else None
              | ALU_AND => chk61 (PrimInt63.land x y)
              | ALU_OR => chk61 (PrimInt63.lor x y)
              | ALU_XOR => chk61 (PrimInt63.lxor x y)
              | ALU_SRL => chk61 (PrimInt63.lsr x (PrimInt63.land y I63m))
              | ALU_SLL => let p := PrimInt63.land y I63m in
                           if PrimInt63.ltb x (PrimInt63.lsr I61 p) then Some (PrimInt63.lsl x p) else None
              | ALU_SLTU => Some (if PrimInt63.ltb x y then I1 else I0)
              | _ => None
              end
          | None => None
          end
      | None => None
      end
  | PMul a b =>
      match evalP a z with
      | Some x =>
          match evalP b z with
          | Some y => let '(hi, lo) := PrimInt63.mulc x y in
                      if PrimInt63.eqb hi I0 then chk61 lo else None
          | None => None
          end
      | None => None
      end
  | PBad => None
  end.
Lemma phi_I61 : φ I61 = 2 ^ 61. Proof. reflexivity. Qed.
Lemma phi_I63m : φ I63m = 63. Proof. reflexivity. Qed.
Lemma phi_I1 : φ I1 = 1. Proof. reflexivity. Qed.
Lemma phi_I0 : φ I0 = 0. Proof. reflexivity. Qed.
Lemma chk61_spec : forall t r, chk61 t = Some r -> r = t /\ φ t < 2 ^ 61.
Proof.
  intros t r H. unfold chk61 in H. rewrite IMGFK.ltb_b, phi_I61 in H.
  destruct (Z.ltb_spec (φ t) (2 ^ 61)); [injection H as <-; split; [reflexivity|assumption]|discriminate].
Qed.
Lemma land63_bound : forall a, 0 <= Z.land a 63 <= 63.
Proof.
  intros a. change 63 with (Z.ones 6) at 1 2. rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound a (2 ^ 6) ltac:(lia)) as H. change (2 ^ 6) with 64 in H. lia.
Qed.
Lemma evalP_alu : forall op x y r, φ x < 2 ^ 61 -> φ y < 2 ^ 61 ->
  (match op with
   | ALU_ADD => chk61 (PrimInt63.add x y)
   | ALU_SUB => if PrimInt63.leb y x then Some (PrimInt63.sub x y) else None
   | ALU_AND => chk61 (PrimInt63.land x y)
   | ALU_OR => chk61 (PrimInt63.lor x y)
   | ALU_XOR => chk61 (PrimInt63.lxor x y)
   | ALU_SRL => chk61 (PrimInt63.lsr x (PrimInt63.land y I63m))
   | ALU_SLL => let p := PrimInt63.land y I63m in
                if PrimInt63.ltb x (PrimInt63.lsr I61 p) then Some (PrimInt63.lsl x p) else None
   | ALU_SLTU => Some (if PrimInt63.ltb x y then I1 else I0)
   | _ => None
   end) = Some r ->
  zfast op (φ x) (φ y) = φ r /\ φ r < 2 ^ 61.
Proof.
  intros op x y r Hx Hy H.
  pose proof (Uint63.to_Z_bounded x) as Bx. pose proof (Uint63.to_Z_bounded y) as By. rewrite wB63 in Bx, By.
  assert (T64 : two64 = 2 ^ 64) by reflexivity.
  destruct op; try discriminate.
  -   apply chk61_spec in H. destruct H as [-> H]. rewrite Uint63.add_spec, wB63, Z.mod_small in * by lia.
    cbn [zfast]. cbv zeta. rewrite T64. destruct (Z.ltb_spec (φ x + φ y) (2 ^ 64)); [split; [reflexivity|assumption]|lia].
  -   rewrite IMGFK.leb_b in H. destruct (Z.leb_spec (φ y) (φ x)) as [L|L]; [|discriminate]. injection H as <-.
    rewrite Uint63.sub_spec, wB63, Z.mod_small by lia. cbn [zfast]. cbv zeta.
    destruct (Z.leb_spec 0 (φ x - φ y)); [split; [reflexivity|lia]|lia].
  -   cbv zeta in H. rewrite IMGFK.ltb_b in H.
    assert (EP : φ (PrimInt63.land y I63m) = Z.land (φ y) 63) by (rewrite Uint63.land_spec', phi_I63m; reflexivity).
    pose proof (land63_bound (φ y)) as BP.
    rewrite Uint63.lsr_spec, phi_I61, EP in H.
    destruct (Z.ltb_spec (φ x) (2 ^ 61 / 2 ^ Z.land (φ y) 63)) as [L|L]; [|discriminate]. injection H as <-.
    set (p := Z.land (φ y) 63) in *.
    assert (PP : 0 < 2 ^ p) by (apply Z.pow_pos_nonneg; lia).
    assert (M : φ x * 2 ^ p < 2 ^ 61).
    { pose proof (Z.mul_div_le (2 ^ 61) (2 ^ p) PP). nia. }
    rewrite Uint63.lsl_spec, EP, wB63. fold p. rewrite Z.mod_small by nia.
    cbn [zfast]. fold p. rewrite Z.shiftl_mul_pow2 by lia. unfold land64. rewrite T64.
    destruct (Z.leb_spec 0 (φ x * 2 ^ p)); [|nia]. destruct (Z.ltb_spec (φ x * 2 ^ p) (2 ^ 64)); [|lia]. cbn [andb].
    split; [reflexivity|exact M].
  -   injection H as <-. cbn [zfast]. rewrite IMGFK.ltb_b. destruct (Z.ltb (φ x) (φ y)); [rewrite phi_I1|rewrite phi_I0]; split; try reflexivity; lia.
  -   apply chk61_spec in H. destruct H as [-> H]. rewrite Uint63.lxor_spec' in *. cbn [zfast]. split; [reflexivity|assumption].
  -   apply chk61_spec in H. destruct H as [-> H].
    assert (EP : φ (PrimInt63.land y I63m) = Z.land (φ y) 63) by (rewrite Uint63.land_spec', phi_I63m; reflexivity).
    rewrite Uint63.lsr_spec, EP in *. cbn [zfast]. rewrite Z.shiftr_div_pow2 by (apply Z.land_nonneg; lia). split; [reflexivity|assumption].
  -   apply chk61_spec in H. destruct H as [-> H]. rewrite Uint63.lor_spec' in *. cbn [zfast]. split; [reflexivity|assumption].
  -   apply chk61_spec in H. destruct H as [-> H]. rewrite Uint63.land_spec' in *. cbn [zfast]. split; [reflexivity|assumption].
Qed.
Lemma evalP_mul : forall x y r, φ x < 2 ^ 61 -> φ y < 2 ^ 61 ->
  (let '(hi, lo) := PrimInt63.mulc x y in if PrimInt63.eqb hi I0 then chk61 lo else None) = Some r ->
  zfastm M_MUL (φ x) (φ y) = φ r /\ φ r < 2 ^ 61.
Proof.
  intros x y r Hx Hy H. pose proof (Uint63.mulc_spec x y) as MS.
  destruct (PrimInt63.mulc x y) as [hi lo]. cbn [fst snd] in MS.
  destruct (PrimInt63.eqb hi I0) eqn:E; [|discriminate]. apply Uint63.eqb_correct in E. subst hi. rewrite phi_I0 in MS.
  apply chk61_spec in H. destruct H as [-> H].
  pose proof (Uint63.to_Z_bounded lo) as Bl.
  cbn [zfastm]. unfold land64. assert (T64 : two64 = 2 ^ 64) by reflexivity. rewrite T64, MS. change (0 * Uint63.wB) with 0. rewrite Z.add_0_l.
  destruct (Z.leb_spec 0 (φ lo)); [|lia]. destruct (Z.ltb_spec (φ lo) (2 ^ 64)); [|lia]. split; [reflexivity|exact H].
Qed.
Lemma evalP_sound : forall s e z r, φ z < 2 ^ 61 -> evalP (pcompile s e) z = Some r ->
  evalS s (φ z) e = Some (φ r) /\ φ r < 2 ^ 61.
Proof.
  intros s e z. induction e; intros r Hz H; cbn [pcompile evalS] in *;
    match type of H with context [expr_eqb ?x s] => destruct (expr_eqb x s) eqn:E end;
    try (cbn [evalP] in H; injection H as <-; split; [reflexivity|exact Hz]).
  -   destruct (IMGFK.z61 (wrap64 z0)) as [i|] eqn:EZ; [|discriminate]. cbn [evalP] in H. injection H as <-.
    destruct (IMGFK.z61_spec _ _ EZ) as [E1 E2]. rewrite E1. split; [reflexivity|lia].
  - discriminate.
  -   destruct op; try discriminate; cbn [evalP] in H;
      (destruct (evalP (pcompile s e1) z) as [x|] eqn:EA; [|discriminate]; destruct (evalP (pcompile s e2) z) as [y|] eqn:EB; [|discriminate];
       destruct (IHe1 x Hz eq_refl) as [A1 A2]; destruct (IHe2 y Hz eq_refl) as [B1 B2]; rewrite A1, B1;
       match goal with |- context [zfast ?o _ _] => destruct (evalP_alu o x y r A2 B2 H) as [C1 C2] end; rewrite C1; split; [reflexivity|exact C2]).
  - discriminate.
  -   destruct op; try discriminate. cbn [evalP] in H.
    destruct (evalP (pcompile s e1) z) as [x|] eqn:EA; [|discriminate]. destruct (evalP (pcompile s e2) z) as [y|] eqn:EB; [|discriminate].
    destruct (IHe1 x Hz eq_refl) as [A1 A2]. destruct (IHe2 y Hz eq_refl) as [B1 B2]. rewrite A1, B1.
    destruct (evalP_mul x y r A2 B2 H) as [C1 C2]. rewrite C1. split; [reflexivity|exact C2].
  - discriminate.
  - discriminate.
  - discriminate.
Qed.
Fixpoint all_eval_toSF (s e : expr) (p : pex) (v : Z) (vi : PrimInt63.int) (lo : Z) (loi : PrimInt63.int) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c =>
      match evalP p loi with
      | Some r => if PrimInt63.eqb r vi then all_eval_toSF s e p v vi (lo + 1) (PrimInt63.add loi I1) c else false
      | None => match evalS s (wrap64 lo) e with
                | Some w => if Z.eqb w v then all_eval_toSF s e p v vi (lo + 1) (PrimInt63.add loi I1) c else false
                | None => false
                end
      end
  end.
Lemma eqb_b : forall x y, PrimInt63.eqb x y = Z.eqb (φ x) (φ y).
Proof.
  intros x y. destruct (Z.eqb_spec (φ x) (φ y)) as [H|H].
  - apply Uint63.to_Z_inj in H. subst. apply Uint63.eqb_refl.
  - destruct (PrimInt63.eqb x y) eqn:E; [|reflexivity]. apply Uint63.eqb_correct in E. subst. contradiction.
Qed.
Lemma all_eval_toSF_eq : forall s e v vi cnt lo loi, φ vi = v -> φ loi = lo -> lo + Z.of_nat cnt <= 2 ^ 61 ->
  all_eval_toSF s e (pcompile s e) v vi lo loi cnt = all_eval_toS s e v lo cnt.
Proof.
  intros s e v vi cnt. induction cnt as [|c IH]; intros lo loi Hv Hl Hb; [reflexivity|]. cbn [all_eval_toSF all_eval_toS].
  pose proof (Uint63.to_Z_bounded loi) as Bl. rewrite Nat2Z.inj_succ in Hb.
  assert (EW : wrap64 lo = lo).
  { unfold wrap64. assert (T64 : two64 = 2 ^ 64) by reflexivity. rewrite T64. destruct (Z.leb_spec 0 lo); [|lia]. destruct (Z.ltb_spec lo (2 ^ 64)); [reflexivity|lia]. }
  assert (EN : φ (PrimInt63.add loi I1) = lo + 1) by (rewrite Uint63.add_spec, phi_I1, wB63, Hl, Z.mod_small by lia; reflexivity).
  destruct (evalP (pcompile s e) loi) as [r|] eqn:EP.
  - apply evalP_sound in EP; [|lia]. destruct EP as [EP _]. rewrite EW, <- Hl, EP, eqb_b, Hv.
    destruct (Z.eqb (φ r) v); [|reflexivity]. rewrite Hl. apply IH; [exact Hv|exact EN|lia].
  - destruct (evalS s (wrap64 lo) e) as [w|]; [|reflexivity]. destruct (Z.eqb w v); [|reflexivity]. apply IH; [exact Hv|exact EN|lia].
Qed.

Inductive dex : Type :=
| DHole | DLit (w : Z) | DRef (i : nat)
| DAlu (op : aluop) (a b : dex) | DAluw (op : aluop) (a b : dex)
| DMd (op : mulop) (a b : dex) | DMdw (op : mulop) (a b : dex)
| DExt (sx : bool) (lo n : nat) (a : dex)
| DLet (a body : dex) (e0 : expr)
| DEval (e0 : expr).
Fixpoint evalD (s : expr) (env : list Z) (d : dex) (z : Z) : option Z :=
  match d with
  | DHole => Some z
  | DLit w => Some w
  | DRef i => nth_error env i
  | DAlu op a b => match evalD s env a z with
                   | Some x => match evalD s env b z with Some y => Some (zfast op x y) | None => None end
                   | None => None
                   end
  | DAluw op a b => match evalD s env a z with
                    | Some x => match evalD s env b z with Some y => Some (zfastw op x y) | None => None end
                    | None => None
                    end
  | DMd op a b => match evalD s env a z with
                  | Some x => match evalD s env b z with Some y => Some (zfastm op x y) | None => None end
                  | None => None
                  end
  | DMdw op a b => match evalD s env a z with
                   | Some x => match evalD s env b z with Some y => Some (zmdw op x y) | None => None end
                   | None => None
                   end
  | DExt sx lo n a => match evalD s env a z with Some x => Some (zext_fast sx lo n x) | None => None end
  | DLet a body e0 => match evalD s env a z with
                      | Some va => evalD s (va :: env) body z
                      | None => evalS s z e0
                      end
  | DEval e0 => evalS s z e0
  end.

Fixpoint chain_base (e : expr) : expr :=
  match e with
  | EAlu _ a (ELit _) => chain_base a
  | EAlu _ (ELit _) b => chain_base b
  | EAluw _ a (ELit _) => chain_base a
  | EAluw _ (ELit _) b => chain_base b
  | EMd _ a (ELit _) => chain_base a
  | EMd _ (ELit _) b => chain_base b
  | EMdw _ a (ELit _) => chain_base a
  | EMdw _ (ELit _) b => chain_base b
  | EExt _ _ _ a => chain_base a
  | _ => e
  end.

Definition shareable (e : expr) : bool :=
  match e with
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b =>
      match a with ELit _ => false | _ => match b with ELit _ => false | _ => true end end
  | _ => false
  end.
Fixpoint sfind (stk : list expr) (e : expr) (i : nat) : option nat :=
  match stk with
  | [] => None
  | a :: r => if expr_eqbF e a then Some i else sfind r e (S i)
  end.
Fixpoint dcomp (fuel : nat) (s : expr) (stk : list expr) (e : expr) : dex :=
  match fuel with
  | O => DEval e
  | S f =>
      if expr_eqbF e s then DHole else
      match sfind stk e O with
      | Some i => DRef i
      | None =>
          let bin (mk : dex -> dex -> dex) (a b : expr) : dex :=
            let A := chain_base a in
            if (if shareable A then expr_eqbF A (chain_base b) else false)
            then DLet (dcomp f s stk A) (mk (dcomp f s (A :: stk) a) (dcomp f s (A :: stk) b)) e
            else mk (dcomp f s stk a) (dcomp f s stk b) in
          match e with
          | ELit w => DLit (wrap64 w)
          | EVar _ => DEval e
          | EAlu op a b => bin (DAlu op) a b
          | EAluw op a b => bin (DAluw op) a b
          | EMd op a b => bin (DMd op) a b
          | EMdw op a b => bin (DMdw op) a b
          | EExt sx lo n a => DExt sx lo n (dcomp f s stk a)
          | EBlob _ _ _ _ => DEval e
          end
      end
  end.
Lemma evalS_unfold : forall s z e, evalS s z e =
  if expr_eqb e s then Some z else
  match e with
  | ELit w => Some (wrap64 w)
  | EVar _ => None
  | EAlu op a b => match evalS s z a with Some x => match evalS s z b with Some y => Some (zfast op x y) | None => None end | None => None end
  | EAluw op a b => match evalS s z a with Some x => match evalS s z b with Some y => Some (zfastw op x y) | None => None end | None => None end
  | EMd op a b => match evalS s z a with Some x => match evalS s z b with Some y => Some (zfastm op x y) | None => None end | None => None end
  | EMdw op a b => match evalS s z a with Some x => match evalS s z b with Some y => Some (zmdw op x y) | None => None end | None => None end
  | EExt sx lo n a => match evalS s z a with Some x => Some (zext_fast sx lo n x) | None => None end
  | EBlob _ _ _ _ => None
  end.
Proof. intros s z e. destruct e; reflexivity. Qed.
Definition stk_ok (s : expr) (z : Z) (stk : list expr) (env : list Z) : Prop := Forall2 (fun a v => evalS s z a = Some v) stk env.
Lemma sfind_spec : forall s z stk env e k i, stk_ok s z stk env -> sfind stk e k = Some i ->
  exists v, nth_error env (i - k) = Some v /\ evalS s z e = Some v /\ (k <= i)%nat.
Proof.
  intros s z stk env e k i H. revert k i. induction H as [|a v stk' env' Hav H IH]; intros k i F; [discriminate|].
  cbn [sfind] in F. destruct (expr_eqbF e a) eqn:E.
  - injection F as <-. apply expr_eqbF_true in E. subst a. exists v. rewrite Nat.sub_diag. split; [reflexivity|]. split; [exact Hav|lia].
  - destruct (IH _ _ F) as (v' & N & EV & LE). exists v'. split; [|split; [exact EV|lia]].
    replace (i - k)%nat with (S (i - S k)) by lia. exact N.
Qed.
Lemma dcomp_ok : forall fuel s stk e env z, stk_ok s z stk env -> evalD s env (dcomp fuel s stk e) z = evalS s z e.
Proof.
  induction fuel as [|f IH]; intros s stk e env z H; [reflexivity|].
  cbn [dcomp]. rewrite (evalS_unfold s z e), expr_eqbF_eq.
  destruct (expr_eqb e s) eqn:EP; [reflexivity|].
  destruct (sfind stk e O) as [i|] eqn:SF.
  { destruct (sfind_spec s z stk env e O i H SF) as (v & N & EV & _). rewrite Nat.sub_0_r in N. cbn [evalD]. rewrite N.
    rewrite (evalS_unfold s z e), EP in EV. symmetry. exact EV. }
  assert (BIN : forall (mk : dex -> dex -> dex) (g : Z -> Z -> Z) a b,
            (forall env' da db, evalD s env' (mk da db) z = match evalD s env' da z with Some x => match evalD s env' db z with Some y => Some (g x y) | None => None end | None => None end) ->
            evalS s z e = match evalS s z a with Some x => match evalS s z b with Some y => Some (g x y) | None => None end | None => None end ->
            evalD s env (let A := chain_base a in
                         if (if shareable A then expr_eqbF A (chain_base b) else false)
                         then DLet (dcomp f s stk A) (mk (dcomp f s (A :: stk) a) (dcomp f s (A :: stk) b)) e
                         else mk (dcomp f s stk a) (dcomp f s stk b)) z
            = match evalS s z a with Some x => match evalS s z b with Some y => Some (g x y) | None => None end | None => None end).
  { intros mk g a b Hmk He. cbv zeta.
    destruct (if shareable (chain_base a) then expr_eqbF (chain_base a) (chain_base b) else false).
    - cbn [evalD]. rewrite (IH s stk (chain_base a) env z H).
      destruct (evalS s z (chain_base a)) as [va|] eqn:EA; [|exact He].
      assert (H' : stk_ok s z (chain_base a :: stk) (va :: env)) by (constructor; [exact EA|exact H]).
      rewrite Hmk, (IH s _ a _ z H'), (IH s _ b _ z H'). reflexivity.
    - rewrite Hmk, (IH s stk a env z H), (IH s stk b env z H). reflexivity. }
  destruct e as [w|n|op a b|op a b|op a b|op a b|sx lo n a|sx k i n]; try reflexivity;
    try (cbn [evalD]; rewrite (evalS_unfold s z _), EP; reflexivity).
  - apply (BIN (DAlu op) (zfast op)); [reflexivity|]. rewrite (evalS_unfold s z (EAlu op a b)), EP. reflexivity.
  - apply (BIN (DAluw op) (zfastw op)); [reflexivity|]. rewrite (evalS_unfold s z (EAluw op a b)), EP. reflexivity.
  - apply (BIN (DMd op) (zfastm op)); [reflexivity|]. rewrite (evalS_unfold s z (EMd op a b)), EP. reflexivity.
  - apply (BIN (DMdw op) (zmdw op)); [reflexivity|]. rewrite (evalS_unfold s z (EMdw op a b)), EP. reflexivity.
  - cbn [evalD]. rewrite (IH s stk a env z H). reflexivity.
Qed.
Definition DFUEL : nat := 160.
Definition dcomp0 (s e : expr) : dex := dcomp DFUEL s [] e.
Lemma dcomp0_ok : forall s e z, evalD s [] (dcomp0 s e) z = evalS s z e.
Proof. intros. unfold dcomp0. apply dcomp_ok. constructor. Qed.

Fixpoint all_eval_toSD (s : expr) (d : dex) (v lo : Z) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c => match evalD s [] d (wrap64 lo) with
           | Some w => if Z.eqb w v then all_eval_toSD s d v (lo + 1) c else false
           | None => false
           end
  end.
Lemma all_eval_toSD_eq : forall s e v cnt lo, all_eval_toSD s (dcomp0 s e) v lo cnt = all_eval_toS s e v lo cnt.
Proof.
  intros s e v cnt. induction cnt as [|c IH]; intros lo; [reflexivity|]. cbn [all_eval_toSD all_eval_toS].
  rewrite dcomp0_ok. destruct (evalS s (wrap64 lo) e) as [w|]; [|reflexivity]. destruct (Z.eqb w v); [apply IH|reflexivity].
Qed.
Fixpoint all_eval_toSG (s e : expr) (p : pex) (d : dex) (v : Z) (vi : PrimInt63.int) (lo : Z) (loi : PrimInt63.int) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c =>
      match evalP p loi with
      | Some r => if PrimInt63.eqb r vi then all_eval_toSG s e p d v vi (lo + 1) (PrimInt63.add loi I1) c else false
      | None => all_eval_toSD s d v lo (S c)
      end
  end.
Lemma all_eval_toSG_eq : forall s e v vi cnt lo loi, φ vi = v -> φ loi = lo -> lo + Z.of_nat cnt <= 2 ^ 61 ->
  all_eval_toSG s e (pcompile s e) (dcomp0 s e) v vi lo loi cnt = all_eval_toS s e v lo cnt.
Proof.
  intros s e v vi cnt. induction cnt as [|c IH]; intros lo loi Hv Hl Hb; [reflexivity|]. cbn [all_eval_toSG].
  pose proof (Uint63.to_Z_bounded loi) as Bl.
  destruct (evalP (pcompile s e) loi) as [r|] eqn:EP; [|apply all_eval_toSD_eq].
  cbn [all_eval_toS]. rewrite Nat2Z.inj_succ in Hb.
  assert (EW : wrap64 lo = lo).
  { unfold wrap64. assert (T64 : two64 = 2 ^ 64) by reflexivity. rewrite T64. destruct (Z.leb_spec 0 lo); [|lia]. destruct (Z.ltb_spec lo (2 ^ 64)); [reflexivity|lia]. }
  assert (EN : φ (PrimInt63.add loi I1) = lo + 1) by (rewrite Uint63.add_spec, phi_I1, wB63, Hl, Z.mod_small by lia; reflexivity).
  apply evalP_sound in EP; [|lia]. destruct EP as [EP _]. rewrite EW, <- Hl, EP, eqb_b, Hv.
  destruct (Z.eqb (φ r) v); [|reflexivity]. rewrite Hl. apply IH; [exact Hv|exact EN|lia].
Qed.

Definition sweepGd (s e : expr) (d : dex) (v lo : Z) (cnt : nat) : bool :=
  match IMGFK.z61 v, IMGFK.z61 lo, IMGFK.z61 (lo + Z.of_nat cnt) with
  | Some vi, Some loi, Some _ => all_eval_toSG s e (pcompile s e) d v vi lo loi cnt
  | _, _, _ => all_eval_toSD s d v lo cnt
  end.
Lemma sweepGd_eq : forall s e v lo cnt, sweepGd s e (dcomp0 s e) v lo cnt = all_eval_toS s e v lo cnt.
Proof.
  intros s e v lo cnt. unfold sweepGd.
  destruct (IMGFK.z61 v) as [vi|] eqn:E1; [|apply all_eval_toSD_eq]. destruct (IMGFK.z61 lo) as [loi|] eqn:E2; [|apply all_eval_toSD_eq].
  destruct (IMGFK.z61 (lo + Z.of_nat cnt)) as [x|] eqn:E3; [|apply all_eval_toSD_eq].
  destruct (IMGFK.z61_spec _ _ E1) as [A1 _]. destruct (IMGFK.z61_spec _ _ E2) as [A2 _]. destruct (IMGFK.z61_spec _ _ E3) as [_ A3].
  apply all_eval_toSG_eq; [exact A1|exact A2|lia].
Qed.
Definition probeD (s : expr) (d : dex) (v z : Z) : bool :=
  match evalD s [] d (wrap64 z) with Some w => Z.eqb w v | None => false end.
Lemma probeD_eq : forall s e v z, probeD s (dcomp0 s e) v z = probeS s e v z.
Proof. intros. unfold probeD, probeS. rewrite dcomp0_ok. reflexivity. Qed.

Definition sweepF (s e : expr) (v lo : Z) (cnt : nat) : bool := sweepGd s e (dcomp0 s e) v lo cnt.
Lemma sweepF_eq : forall s e v lo cnt, sweepF s e v lo cnt = all_eval_toS s e v lo cnt.
Proof. intros. unfold sweepF. apply sweepGd_eq. Qed.
Lemma sweepF_fe : sweepF = all_eval_toS.
Proof. repeat (apply functional_extensionality; intros ?). apply sweepF_eq. Qed.

Fixpoint nvl (e : expr) : Z :=
  match e with
  | ELit _ => 0
  | EVar _ | EBlob _ _ _ _ => 1
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => nvl a + nvl b
  | EExt _ _ _ a => nvl a
  end.

Fixpoint subxN (e : expr) : list (expr * Z) * Z :=
  match e with
  | ELit _ => ([(e, 0)], 0)
  | EVar _ | EBlob _ _ _ _ => ([(e, 1)], 1)
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b =>
      let '(la, na) := subxN a in let '(lb, nb) := subxN b in (la ++ lb ++ [(e, na + nb)], na + nb)
  | EExt _ _ _ a => let '(la, na) := subxN a in (la ++ [(e, na)], na)
  end.

Fixpoint bump (x : expr) (nx : Z) (a : list (expr * Z * Z)) : list (expr * Z * Z) :=
  match a with
  | [] => [(x, nx, 1)]
  | (y, ny, c) :: r => if expr_eqb x y then (y, ny, c + 1) :: r else (y, ny, c) :: bump x nx r
  end.
Definition counts (l : list (expr * Z)) : list (expr * Z * Z) := fold_left (fun a p => bump (fst p) (snd p) a) l [].

Fixpoint bumpF (x : expr) (nx : Z) (a : list (expr * Z * Z)) : list (expr * Z * Z) :=
  match a with
  | [] => [(x, nx, 1)]
  | (y, ny, c) :: r => if expr_eqbF x y then (y, ny, c + 1) :: r else (y, ny, c) :: bumpF x nx r
  end.
Definition countsF (l : list (expr * Z)) : list (expr * Z * Z) := fold_left (fun a p => bumpF (fst p) (snd p) a) l [].
Fixpoint evalS_defF (s e : expr) : bool :=
  if expr_eqbF e s then true else
  match e with
  | ELit _ => true
  | EVar _ => false
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if evalS_defF s a then evalS_defF s b else false
  | EExt _ _ _ a => evalS_defF s a
  | EBlob _ _ _ _ => false
  end.
Fixpoint conc_tryBF (bc : bctx) (e : expr) (nve : Z) (cands : list (expr * Z * Z)) : option Z :=
  match cands with
  | [] => None
  | (s, nvs, c) :: rest =>
      if closedb s then conc_tryBF bc e nve rest else
      if negb (Z.eqb (c * nvs) nve) then conc_tryBF bc e nve rest else
      if negb (evalS_def s e) then conc_tryBF bc e nve rest else
      match erangeB bc s with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            match evalS s (wrap64 lo) e with
            | Some v =>
                if (if Z.ltb hi lo then true
                     else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2)%Z else false) then
                  if sweepF s e v lo (Z.to_nat (hi - lo + 1)) then Some v
                  else conc_tryBF bc e nve rest
                else conc_tryBF bc e nve rest
            | None => conc_tryBF bc e nve rest
            end
          else conc_tryBF bc e nve rest
      | None => conc_tryBF bc e nve rest
      end
  end.
Definition concretizeBF (bc : bctx) (e : expr) : option Z :=
  if closedb e then eval_closed e else let '(l, n) := subxN e in conc_tryBF bc e n (counts l).
Definition foldKBF (bc : bctx) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match erangeB bc e with
         | Some (lo, hi) => if Z.eqb lo hi then ELit lo
                            else match concretizeBF bc e with Some v => ELit v | None => e end
         | None => match concretizeBF bc e with Some v => ELit v | None => e end
         end
  end.

Lemma subxN_spec : forall e, subxN e = (map (fun t => (t, nvl t)) (subexprs e), nvl e).
Proof.
  induction e; cbn [subxN subexprs nvl map]; try reflexivity;
    rewrite ?IHe1, ?IHe2, ?IHe; rewrite ?map_app; reflexivity.
Qed.

Fixpoint cntE (s : expr) (l : list expr) : Z :=
  match l with [] => 0 | t :: r => (if expr_eqb t s then 1 else 0) + cntE s r end.
Lemma cntE_app : forall s l1 l2, cntE s (l1 ++ l2) = cntE s l1 + cntE s l2.
Proof. intros s l1 l2. induction l1 as [|t r IH]; [reflexivity|]. cbn [app cntE]. rewrite IH. ring. Qed.
Fixpoint esz (e : expr) : nat :=
  match e with
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => S (esz a + esz b)
  | EExt _ _ _ a => S (esz a)
  | _ => 1%nat
  end.
Lemma subexprs_sz : forall e t, In t (subexprs e) -> (esz t <= esz e)%nat.
Proof.
  induction e; intros t H; cbn [subexprs] in H; cbn [esz];
    try (destruct H as [<-|[]]; cbn [esz]; lia);
    try (apply in_app_or in H; destruct H as [H|H]; [apply IHe1 in H; lia|];
         apply in_app_or in H; destruct H as [H|H]; [apply IHe2 in H; lia|]; destruct H as [<-|[]]; cbn [esz]; lia).
  apply in_app_or in H; destruct H as [H|H]; [apply IHe in H; lia|]. destruct H as [<-|[]]; cbn [esz]; lia.
Qed.
Lemma cntE_small : forall s l, (forall t, In t l -> (esz t < esz s)%nat) -> cntE s l = 0.
Proof.
  intros s l H. induction l as [|t r IH]; [reflexivity|]. cbn [cntE].
  destruct (expr_eqb t s) eqn:E.
  - apply p_expr_eqb_eq in E. subst t. specialize (H s (or_introl eq_refl)). lia.
  - rewrite IH; [reflexivity|]. intros x Hx. apply H. right. exact Hx.
Qed.
Lemma cntE_self : forall s, cntE s (subexprs s) = 1.
Proof.
  intros s. destruct s; cbn [subexprs cntE]; rewrite ?kx_expr_eqb_refl; try reflexivity;
    rewrite ?cntE_app; cbn [cntE]; rewrite ?kx_expr_eqb_refl;
    rewrite !cntE_small; try reflexivity; intros t Ht; apply subexprs_sz in Ht; cbn [esz]; lia.
Qed.

Lemma evalS_def_count : forall s e, evalS_def s e = true -> nvl e = cntE s (subexprs e) * nvl s.
Proof.
  intros s e. induction e; cbn [evalS_def]; intros H;
    match type of H with (if expr_eqb ?x ?y then _ else _) = true => destruct (expr_eqb x y) eqn:E end;
    try (apply p_expr_eqb_eq in E; subst s; rewrite cntE_self; ring);
    try discriminate.
  - cbn [subexprs cntE nvl]. rewrite E. ring.
  - destruct (evalS_def s e1) eqn:E1; [|discriminate]. cbn [subexprs nvl]. rewrite !cntE_app. cbn [cntE]. rewrite E, (IHe1 eq_refl), (IHe2 H). ring.
  - destruct (evalS_def s e1) eqn:E1; [|discriminate]. cbn [subexprs nvl]. rewrite !cntE_app. cbn [cntE]. rewrite E, (IHe1 eq_refl), (IHe2 H). ring.
  - destruct (evalS_def s e1) eqn:E1; [|discriminate]. cbn [subexprs nvl]. rewrite !cntE_app. cbn [cntE]. rewrite E, (IHe1 eq_refl), (IHe2 H). ring.
  - destruct (evalS_def s e1) eqn:E1; [|discriminate]. cbn [subexprs nvl]. rewrite !cntE_app. cbn [cntE]. rewrite E, (IHe1 eq_refl), (IHe2 H). ring.
  - cbn [subexprs nvl]. rewrite cntE_app. cbn [cntE]. rewrite E, (IHe H). ring.
Qed.

Definition keys (a : list (expr * Z * Z)) : list expr := map (fun q => fst (fst q)) a.
Lemma eqb_iff : forall x y, expr_eqb x y = true <-> x = y.
Proof. intros x y. split; [apply p_expr_eqb_eq|intros ->; apply kx_expr_eqb_refl]. Qed.
Lemma memE_in : forall x l, memE x l = true <-> In x l.
Proof.
  intros x l. induction l as [|y r IH]; cbn [memE In]; [split; [discriminate|intros []]|].
  destruct (expr_eqb x y) eqn:E.
  - apply eqb_iff in E. subst. split; [left; reflexivity|reflexivity].
  - rewrite IH. split; [right; assumption|]. intros [->|H]; [rewrite kx_expr_eqb_refl in E; discriminate|exact H].
Qed.
Lemma bump_keys : forall x nx a, keys (bump x nx a) = if memE x (keys a) then keys a else keys a ++ [x].
Proof.
  intros x nx a. induction a as [|[[y ny] c] r IH]; [reflexivity|]. cbn [bump keys map fst memE].
  destruct (expr_eqb x y); [reflexivity|]. cbn [keys map fst]. fold (keys (bump x nx r)). fold (keys r). rewrite IH.
  destruct (memE x (keys r)); reflexivity.
Qed.
Lemma keys_fold : forall (L : list (expr * Z)) a acc, (forall x, memE x acc = memE x (keys a)) ->
  keys (fold_left (fun a p => bump (fst p) (snd p) a) L a) = keys a ++ nubE_acc (map fst L) acc.
Proof.
  induction L as [|[x nx] r IH]; intros a acc H; cbn [fold_left map fst snd nubE_acc]; [rewrite app_nil_r; reflexivity|].
  pose proof (bump_keys x nx a) as BK. rewrite (H x). destruct (memE x (keys a)) eqn:M.
  - rewrite (IH (bump x nx a) acc); [rewrite BK; reflexivity|]. intros y. rewrite BK. apply H.
  - rewrite (IH (bump x nx a) (x :: acc)); [rewrite BK, <- app_assoc; reflexivity|].
    intros y. rewrite BK. cbn [memE].
    destruct (memE y (keys a ++ [x])) eqn:M2.
    + apply memE_in in M2. apply in_app_or in M2. destruct M2 as [M2|[<-|[]]].
      * apply memE_in in M2. rewrite H, M2. destruct (expr_eqb y x); reflexivity.
      * rewrite kx_expr_eqb_refl. reflexivity.
    + destruct (expr_eqb y x) eqn:E.
      * apply eqb_iff in E. subst y. assert (C : memE x (keys a ++ [x]) = true) by (apply memE_in, in_or_app; right; left; reflexivity).
        rewrite C in M2. discriminate.
      * rewrite H. destruct (memE y (keys a)) eqn:M3; [|reflexivity].
        assert (C : memE y (keys a ++ [x]) = true) by (apply memE_in, in_or_app; left; apply memE_in; exact M3).
        rewrite C in M2. discriminate.
Qed.
Lemma keys_counts : forall L, keys (counts L) = nubE (map fst L).
Proof. intros L. unfold counts, nubE. rewrite (keys_fold L [] []); [reflexivity|]. intros x. reflexivity. Qed.

Definition CINV (a : list (expr * Z * Z)) (done : list expr) : Prop :=
  List.NoDup (keys a) /\ (forall t, In t done -> In t (keys a)) /\
  (forall y ny c, In (y, ny, c) a -> ny = nvl y /\ c = cntE y done).
Lemma cntE_notin : forall s l, ~ In s l -> cntE s l = 0.
Proof.
  intros s l H. induction l as [|t r IH]; [reflexivity|]. cbn [cntE]. destruct (expr_eqb t s) eqn:E.
  - apply eqb_iff in E. subst t. exfalso. apply H. left. reflexivity.
  - rewrite IH; [reflexivity|]. intros C. apply H. right. exact C.
Qed.
Lemma cntE_snoc : forall s l x, cntE s (l ++ [x]) = cntE s l + (if expr_eqb x s then 1 else 0).
Proof. intros. rewrite cntE_app. cbn [cntE]. ring. Qed.
Lemma bump_inv : forall x a done, CINV a done -> CINV (bump x (nvl x) a) (done ++ [x]).
Proof.
  intros x a done (ND & CO & EN). unfold CINV. rewrite bump_keys.
  destruct (memE x (keys a)) eqn:M.
  - split; [exact ND|]. split.
    + intros t Ht. apply in_app_or in Ht. destruct Ht as [Ht|[<-|[]]]; [apply CO; exact Ht|apply memE_in; exact M].
    + clear CO. revert ND EN M. induction a as [|[[y0 ny0] c0] r IH]; intros ND EN M; [discriminate|].
      cbn [bump]. cbn [keys map fst memE] in M, ND. fold (keys r) in M, ND. inversion ND as [|? ? NI ND']; subst.
      destruct (expr_eqb x y0) eqn:E.
      * apply eqb_iff in E. subst y0. intros y ny c [H|H].
        -- injection H as <- <- <-. destruct (EN x ny0 c0 (or_introl eq_refl)) as [A B]. split; [exact A|].
           rewrite cntE_snoc, kx_expr_eqb_refl, B. reflexivity.
        -- destruct (EN y ny c (or_intror H)) as [A B]. split; [exact A|]. rewrite cntE_snoc, B.
           destruct (expr_eqb x y) eqn:E2; [|ring]. apply eqb_iff in E2. subst y. exfalso. apply NI.
           change (In x (keys r)). unfold keys. apply in_map_iff. exists (x, ny, c). split; [reflexivity|exact H].
      * intros y ny c [H|H].
        -- injection H as <- <- <-. destruct (EN y0 ny0 c0 (or_introl eq_refl)) as [A B]. split; [exact A|].
           rewrite cntE_snoc, B, E. ring.
        -- apply (IH ND'); [|exact M|exact H]. intros y1 ny1 c1 H1. apply EN. right. exact H1.
  - assert (NX : ~ In x (keys a)) by (intros C; apply memE_in in C; rewrite C in M; discriminate).
    split; [|split].
    + clear EN CO M. induction (keys a) as [|k r IH]; cbn [app].
      * constructor; [intros []|constructor].
      * inversion ND as [|? ? NI ND']; subst. constructor.
        -- intros C. apply in_app_or in C. destruct C as [C|[C|[]]]; [exact (NI C)|]. subst k. apply NX. left. reflexivity.
        -- apply IH; [exact ND'|]. intros C. apply NX. right. exact C.
    + intros t Ht. apply in_app_or in Ht. apply in_or_app. destruct Ht as [Ht|[<-|[]]]; [left; apply CO; exact Ht|right; left; reflexivity].
    + assert (XD : ~ In x done) by (intros C; apply NX, CO, C).
      clear ND CO M. revert EN NX. induction a as [|[[y0 ny0] c0] r IH]; intros EN NX y ny c H.
      * destruct H as [H|[]]. injection H as <- <- <-. split; [reflexivity|]. rewrite cntE_snoc, kx_expr_eqb_refl, (cntE_notin _ _ XD). reflexivity.
      * cbn [bump] in H. cbn [keys map fst] in NX. fold (keys r) in NX.
        destruct (expr_eqb x y0) eqn:E; [apply eqb_iff in E; subst y0; exfalso; apply NX; left; reflexivity|].
        destruct H as [H|H].
        -- injection H as <- <- <-. destruct (EN y0 ny0 c0 (or_introl eq_refl)) as [A B]. split; [exact A|]. rewrite cntE_snoc, B, E. ring.
        -- apply IH; [|intros C; apply NX; right; exact C|exact H]. intros y1 ny1 c1 H1. apply EN. right. exact H1.
Qed.
Lemma counts_inv : forall (l : list expr) a done, CINV a done ->
  CINV (fold_left (fun a p => bump (fst p) (snd p) a) (map (fun t => (t, nvl t)) l) a) (done ++ l).
Proof.
  induction l as [|x r IH]; intros a done H; cbn [map fold_left fst snd]; [rewrite app_nil_r; exact H|].
  replace (done ++ x :: r) with ((done ++ [x]) ++ r) by (rewrite <- app_assoc; reflexivity).
  apply IH. apply bump_inv. exact H.
Qed.
Lemma conc_tryBF_eq : forall bc e cands,
  (forall s nvs c, In (s, nvs, c) cands -> nvs = nvl s /\ c = cntE s (subexprs e)) ->
  conc_tryBF bc e (nvl e) cands = conc_tryB bc e (keys cands).
Proof.
  intros bc e cands. induction cands as [|[[s nvs] c] rest IH]; intros H; [reflexivity|].
  cbn [conc_tryBF conc_tryB keys map fst]. fold (keys rest). rewrite sweepF_fe.
  assert (IH' : conc_tryBF bc e (nvl e) rest = conc_tryB bc e (keys rest)) by (apply IH; intros; apply H; right; assumption).
  rewrite IH'. destruct (closedb s); [reflexivity|].
  destruct (Z.eqb (c * nvs) (nvl e)) eqn:EQ; cbn [negb]; [reflexivity|].
  destruct (evalS_def s e) eqn:ED; cbn [negb]; [|reflexivity].
  exfalso. destruct (H s nvs c (or_introl eq_refl)) as [-> ->]. apply evalS_def_count in ED. rewrite ED, Z.eqb_refl in EQ. discriminate.
Qed.
Lemma concretizeBF_eq : forall bc e, concretizeBF bc e = concretizeB bc e.
Proof.
  intros bc e. unfold concretizeBF, concretizeB. destruct (closedb e); [reflexivity|]. rewrite subxN_spec.
  rewrite conc_tryBF_eq.
  - rewrite keys_counts, map_map. cbn [fst]. rewrite map_id. reflexivity.
  - assert (CI : CINV (counts (map (fun t => (t, nvl t)) (subexprs e))) ([] ++ subexprs e)).
    { unfold counts. apply counts_inv. split; [constructor|]. split; [intros t []|intros y ny c []]. }
    destruct CI as (_ & _ & EN). exact EN.
Qed.
Lemma foldKBF_eq : forall bc e, foldKBF bc e = foldKB bc e.
Proof. intros bc e. unfold foldKBF, foldKB. rewrite concretizeBF_eq. reflexivity. Qed.

Definition to_saddrKBF (bc : bctx) (e : expr) (imm : Z) : saddr :=
  match split_lit e with
  | (ELit _, _) => to_saddr e imm
  | _ => match concretizeBF bc (mkAlu ALU_ADD e (ELit imm)) with
         | Some v => SA (ELit 0) v
         | None => to_saddr e imm
         end
  end.
Lemma to_saddrKBF_eq : forall bc e imm, to_saddrKBF bc e imm = to_saddrKB bc e imm.
Proof. intros. unfold to_saddrKBF, to_saddrKB. rewrite concretizeBF_eq. reflexivity. Qed.

Definition kb_gate (s e : expr) (lo hi v : Z) : bool :=
  if Z.leb 64 (hi - lo) then if Z.leb 0 lo then if Z.ltb hi two64 then
    match KBFK.kb_const s lo hi e with Some v' => Z.eqb v' v | None => false end
  else false else false else false.
Lemma kb_gate_sound : forall s e lo hi v, kb_gate s e lo hi v = true ->
  all_eval_toS s e v lo (Z.to_nat (hi - lo + 1)) = true.
Proof.
  intros s e lo hi v G. unfold kb_gate in G.
  destruct (Z.leb_spec 64 (hi - lo)) as [H1|]; [|discriminate]. destruct (Z.leb_spec 0 lo) as [H2|]; [|discriminate].
  destruct (Z.ltb_spec hi two64) as [H3|]; [|discriminate].
  destruct (KBFK.kb_const s lo hi e) as [v'|] eqn:KM; [|discriminate]. apply Z.eqb_eq in G. subst v'.
  apply (KBFK.kb_const_sound s lo hi e v KM); [exact H2|lia|exact H3].
Qed.

Lemma bumpF_eq : forall x nx a, bumpF x nx a = bump x nx a.
Proof. intros x nx a. induction a as [|[[y ny] c] r IH]; [reflexivity|]. cbn [bumpF bump]. rewrite expr_eqbF_eq, IH. reflexivity. Qed.
Lemma countsF_eq : forall l, countsF l = counts l.
Proof.
  intros l. unfold countsF, counts. generalize (@nil (expr * Z * Z)). induction l as [|p r IH]; intros a; [reflexivity|].
  cbn [fold_left]. rewrite bumpF_eq. apply IH.
Qed.
Lemma evalS_defF_eq : forall s e, evalS_defF s e = evalS_def s e.
Proof.
  intros s e. induction e; cbn [evalS_defF evalS_def]; rewrite expr_eqbF_eq; try reflexivity;
    rewrite ?IHe1, ?IHe2, ?IHe; reflexivity.
Qed.
Lemma nvl_nonneg : forall e, 0 <= nvl e.
Proof. induction e; cbn [nvl]; lia. Qed.
Lemma closedb_nvl : forall s, closedb s = Z.eqb (nvl s) 0.
Proof.
  induction s; cbn [closedb nvl]; try reflexivity; try exact IHs;
    rewrite IHs1, IHs2; pose proof (nvl_nonneg s1); pose proof (nvl_nonneg s2);
    destruct (Z.eqb_spec (nvl s1) 0), (Z.eqb_spec (nvl s2) 0), (Z.eqb_spec (nvl s1 + nvl s2) 0); cbn [andb]; try reflexivity; lia.
Qed.

Fixpoint conc_tryBG (bc : bctx) (e : expr) (nve : Z) (cands : list (expr * Z * Z)) : option Z :=
  match cands with
  | [] => None
  | (s, nvs, c) :: rest =>
      if Z.eqb nvs 0 then conc_tryBG bc e nve rest else
      if negb (Z.eqb (c * nvs) nve) then conc_tryBG bc e nve rest else
      if negb (evalS_defF s e) then conc_tryBG bc e nve rest else
      match erangeBF bc s with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            let d := dcomp0 s e in
            match evalD s [] d (wrap64 lo) with
            | Some v =>
                if (if Z.ltb hi lo then true
                     else if probeD s d v hi then probeD s d v (lo + (hi - lo) / 2)%Z else false) then
                  if (if kb_gate s e lo hi v then true else sweepGd s e d v lo (Z.to_nat (hi - lo + 1))) then Some v
                  else conc_tryBG bc e nve rest
                else conc_tryBG bc e nve rest
            | None => conc_tryBG bc e nve rest
            end
          else conc_tryBG bc e nve rest
      | None => conc_tryBG bc e nve rest
      end
  end.
Definition concretizeBG (bc : bctx) (e : expr) : option Z :=
  if closedb e then eval_closed e else let '(l, n) := subxN e in conc_tryBG bc e n (countsF l).
Definition foldKBG (bc : bctx) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match erangeBF bc e with
         | Some (lo, hi) => if Z.eqb lo hi then ELit lo
                            else match concretizeBG bc e with Some v => ELit v | None => e end
         | None => match concretizeBG bc e with Some v => ELit v | None => e end
         end
  end.
Lemma conc_tryBG_eq : forall bc e cands,
  (forall s nvs c, In (s, nvs, c) cands -> nvs = nvl s /\ c = cntE s (subexprs e)) ->
  conc_tryBG bc e (nvl e) cands = conc_tryB bc e (keys cands).
Proof.
  intros bc e cands. induction cands as [|[[s nvs] c] rest IH]; intros H; [reflexivity|].
  cbn [conc_tryBG conc_tryB keys map fst]. fold (keys rest). rewrite erangeBF_fe, evalS_defF_eq.
  assert (IH' : conc_tryBG bc e (nvl e) rest = conc_tryB bc e (keys rest)) by (apply IH; intros; apply H; right; assumption).
  rewrite IH'. destruct (H s nvs c (or_introl eq_refl)) as [Hn _]. rewrite (closedb_nvl s), <- Hn. destruct (Z.eqb nvs 0); [reflexivity|].
  destruct (Z.eqb (c * nvs) (nvl e)) eqn:EQ; cbn [negb].
  - destruct (evalS_def s e); cbn [negb]; [|reflexivity].
    destruct (erangeB bc s) as [[lo hi]|]; [|reflexivity]. destruct (Z.leb (hi - lo) conc_limit); [|reflexivity].
    cbv zeta. rewrite dcomp0_ok. destruct (evalS s (wrap64 lo) e) as [v|] eqn:EV; [|reflexivity].
    rewrite !probeD_eq, sweepGd_eq.
    destruct (if Z.ltb hi lo then true else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2) else false) eqn:PR; [|reflexivity].
    destruct (kb_gate s e lo hi v) eqn:KG; [|reflexivity].
    rewrite (kb_gate_sound s e lo hi v KG). reflexivity.
  - destruct (evalS_def s e) eqn:ED; cbn [negb]; [|reflexivity].
    exfalso. destruct (H s nvs c (or_introl eq_refl)) as [-> ->]. apply evalS_def_count in ED. rewrite ED, Z.eqb_refl in EQ. discriminate.
Qed.
Lemma concretizeBG_eq : forall bc e, concretizeBG bc e = concretizeB bc e.
Proof.
  intros bc e. unfold concretizeBG, concretizeB. destruct (closedb e); [reflexivity|]. rewrite subxN_spec. cbv beta iota. rewrite countsF_eq.
  rewrite conc_tryBG_eq.
  - rewrite keys_counts, map_map. cbn [fst]. rewrite map_id. reflexivity.
  - assert (CI : CINV (counts (map (fun t => (t, nvl t)) (subexprs e))) ([] ++ subexprs e)).
    { unfold counts. apply counts_inv. split; [constructor|]. split; [intros t []|intros y ny c []]. }
    destruct CI as (_ & _ & EN). exact EN.
Qed.
Lemma foldKBG_eq : forall bc e, foldKBG bc e = foldKB bc e.
Proof. intros bc e. unfold foldKBG, foldKB. rewrite concretizeBG_eq, erangeBF_fe. reflexivity. Qed.

Definition to_saddrKBG (bc : bctx) (e : expr) (imm : Z) : saddr :=
  match split_lit e with
  | (ELit _, _) => to_saddr e imm
  | _ => match concretizeBG bc (mkAlu ALU_ADD e (ELit imm)) with
         | Some v => SA (ELit 0) v
         | None => to_saddr e imm
         end
  end.
Lemma to_saddrKBG_eq : forall bc e imm, to_saddrKBG bc e imm = to_saddrKB bc e imm.
Proof. intros. unfold to_saddrKBG, to_saddrKB. rewrite concretizeBG_eq. reflexivity. Qed.

Definition bigE (e : expr) : bool := negb (esize_le e 48).
Definition rmemo : Type := list (expr * option (Z * Z)).
Definition RMOK (bc : bctx) (m : rmemo) : Prop := forall e r, In (e, r) m -> r = erangeB bc e.
Lemma RMOK_nil : forall bc, RMOK bc []. Proof. intros bc e r []. Qed.
Fixpoint rm_get (m : rmemo) (e : expr) : option (option (Z * Z)) :=
  match m with
  | [] => None
  | (a, r) :: t => if expr_eqbF e a then Some r else rm_get t e
  end.
Lemma rm_get_ok : forall bc m e r, RMOK bc m -> rm_get m e = Some r -> r = erangeB bc e.
Proof.
  intros bc m e r. induction m as [|[a ra] t IH]; intros H G; [discriminate|]. cbn [rm_get] in G.
  destruct (expr_eqbF e a) eqn:E.
  - injection G as <-. apply expr_eqbF_true in E. subst a. apply H. left. reflexivity.
  - apply IH; [|exact G]. intros x rx Hx. apply H. right. exact Hx.
Qed.
Definition rangeM (bc : bctx) (m : rmemo) (e : expr) : option (Z * Z) * rmemo :=
  if bigE e then
    match rm_get m e with
    | Some r => (r, m)
    | None => let r := erangeBF bc e in (r, (e, r) :: m)
    end
  else (erangeBF bc e, m).
Lemma rangeM_ok : forall bc m e, RMOK bc m -> fst (rangeM bc m e) = erangeB bc e /\ RMOK bc (snd (rangeM bc m e)).
Proof.
  intros bc m e H. unfold rangeM. rewrite erangeBF_fe. destruct (bigE e); [|split; [reflexivity|exact H]].
  destruct (rm_get m e) as [r|] eqn:G; cbn [fst snd].
  - split; [apply (rm_get_ok bc m e r H G)|exact H].
  - split; [reflexivity|]. intros x rx [E|Hx]; [injection E as <- <-; reflexivity|apply H; exact Hx].
Qed.
Fixpoint conc_tryBM (bc : bctx) (e : expr) (nve : Z) (cands : list (expr * Z * Z)) (m : rmemo) : option Z * rmemo :=
  match cands with
  | [] => (None, m)
  | (s, nvs, c) :: rest =>
      if Z.eqb nvs 0 then conc_tryBM bc e nve rest m else
      if negb (Z.eqb (c * nvs) nve) then conc_tryBM bc e nve rest m else
      if negb (evalS_defF s e) then conc_tryBM bc e nve rest m else
      let '(r, m1) := rangeM bc m s in
      match r with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            let d := dcomp0 s e in
            match evalD s [] d (wrap64 lo) with
            | Some v =>
                if (if Z.ltb hi lo then true
                     else if probeD s d v hi then probeD s d v (lo + (hi - lo) / 2)%Z else false) then
                  if (if kb_gate s e lo hi v then true else sweepGd s e d v lo (Z.to_nat (hi - lo + 1))) then (Some v, m1)
                  else conc_tryBM bc e nve rest m1
                else conc_tryBM bc e nve rest m1
            | None => conc_tryBM bc e nve rest m1
            end
          else conc_tryBM bc e nve rest m1
      | None => conc_tryBM bc e nve rest m1
      end
  end.
Lemma conc_tryBM_ok : forall bc e nve cands m, RMOK bc m ->
  fst (conc_tryBM bc e nve cands m) = conc_tryBG bc e nve cands /\ RMOK bc (snd (conc_tryBM bc e nve cands m)).
Proof.
  intros bc e nve cands. induction cands as [|[[s nvs] c] rest IH]; intros m H; [split; [reflexivity|exact H]|].
  cbn [conc_tryBM conc_tryBG]. destruct (Z.eqb nvs 0); [apply IH; exact H|].
  destruct (negb (Z.eqb (c * nvs) nve)); [apply IH; exact H|].
  destruct (negb (evalS_defF s e)); [apply IH; exact H|].
  destruct (rangeM_ok bc m s H) as [Hr Hm1]. destruct (rangeM bc m s) as [r m1]. cbn [fst snd] in Hr, Hm1.
  rewrite erangeBF_fe, <- Hr. destruct r as [[lo hi]|]; [|apply IH; exact Hm1].
  destruct (Z.leb (hi - lo) conc_limit); [|apply IH; exact Hm1]. cbv zeta.
  destruct (evalD s [] (dcomp0 s e) (wrap64 lo)) as [v|]; [|apply IH; exact Hm1].
  destruct (if Z.ltb hi lo then true else if probeD s (dcomp0 s e) v hi then probeD s (dcomp0 s e) v (lo + (hi - lo) / 2) else false); [|apply IH; exact Hm1].
  destruct (if kb_gate s e lo hi v then true else sweepGd s e (dcomp0 s e) v lo (Z.to_nat (hi - lo + 1))); [split; [reflexivity|exact Hm1]|apply IH; exact Hm1].
Qed.
Definition concretizeBM (bc : bctx) (e : expr) (m : rmemo) : option Z * rmemo :=
  if closedb e then (eval_closed e, m) else let '(l, n) := subxN e in conc_tryBM bc e n (countsF l) m.
Lemma concretizeBM_ok : forall bc e m, RMOK bc m ->
  fst (concretizeBM bc e m) = concretizeBG bc e /\ RMOK bc (snd (concretizeBM bc e m)).
Proof.
  intros bc e m H. unfold concretizeBM, concretizeBG. destruct (closedb e); [split; [reflexivity|exact H]|].
  destruct (subxN e) as [l n]. apply conc_tryBM_ok. exact H.
Qed.
Definition foldKBM (bc : bctx) (m : rmemo) (e : expr) : expr * rmemo :=
  match e with
  | ELit _ => (e, m)
  | _ => let '(r, m1) := rangeM bc m e in
         let tail := fun (_ : unit) => let '(c, m2) := concretizeBM bc e m1 in (match c with Some v => ELit v | None => e end, m2) in
         match r with
         | Some (lo, hi) => if Z.eqb lo hi then (ELit lo, m1) else tail tt
         | None => tail tt
         end
  end.
Lemma foldKBM_ok : forall bc m e, RMOK bc m -> fst (foldKBM bc m e) = foldKBG bc e /\ RMOK bc (snd (foldKBM bc m e)).
Proof.
  intros bc m e H.
  assert (G : forall e', fst (let '(r, m1) := rangeM bc m e' in
                           let tail := fun (_ : unit) => let '(c, m2) := concretizeBM bc e' m1 in (match c with Some v => ELit v | None => e' end, m2) in
                           match r with Some (lo, hi) => if Z.eqb lo hi then (ELit lo, m1) else tail tt | None => tail tt end)
                    = match erangeBF bc e' with
                      | Some (lo, hi) => if Z.eqb lo hi then ELit lo else match concretizeBG bc e' with Some v => ELit v | None => e' end
                      | None => match concretizeBG bc e' with Some v => ELit v | None => e' end
                      end
                    /\ RMOK bc (snd (let '(r, m1) := rangeM bc m e' in
                           let tail := fun (_ : unit) => let '(c, m2) := concretizeBM bc e' m1 in (match c with Some v => ELit v | None => e' end, m2) in
                           match r with Some (lo, hi) => if Z.eqb lo hi then (ELit lo, m1) else tail tt | None => tail tt end))).
  { intros e'. destruct (rangeM_ok bc m e' H) as [Hr Hm1]. destruct (rangeM bc m e') as [r m1]. cbn [fst snd] in Hr, Hm1.
    rewrite erangeBF_fe, <- Hr. cbv zeta.
    destruct (concretizeBM_ok bc e' m1 Hm1) as [Hc Hm2]. destruct (concretizeBM bc e' m1) as [c m2]. cbn [fst snd] in Hc, Hm2. subst c.
    destruct r as [[lo hi]|]; [destruct (Z.eqb lo hi)|]; cbn [fst snd]; split; try reflexivity; assumption. }
  destruct e; try apply G. split; [reflexivity|exact H].
Qed.

Definition hask (e : expr) : bool := match e with EAlu ALU_ADD _ (ELit _) => true | _ => false end.
Lemma split_lit_shape : forall e B k, split_lit e = (B, k) -> is_lit B = None ->
  (hask e = true /\ e = EAlu ALU_ADD B (ELit k)) \/ (hask e = false /\ e = B /\ k = 0).
Proof.
  intros e B k H HL. unfold split_lit in H.
  destruct e as [z|n|op a b|op a b|op a b|op a b|sx lo n a|sx kk i n];
    try (injection H as <- <-; right; repeat split; reflexivity).
  - injection H as <- <-. discriminate.
  - destruct op; try (injection H as <- <-; right; repeat split; reflexivity).
    destruct b; try (injection H as <- <-; right; repeat split; reflexivity).
    injection H as <- <-. left. split; reflexivity.
Qed.
Lemma to_saddrKB_nolit : forall bc e imm B k, split_lit e = (B, k) -> is_lit B = None ->
  to_saddrKB bc e imm = match concretizeB bc (mkAlu ALU_ADD e (ELit imm)) with Some v => SA (ELit 0) v | None => to_saddr e imm end.
Proof. intros bc e imm B k H HL. unfold to_saddrKB. rewrite H. destruct B; try reflexivity; discriminate. Qed.

Lemma mkAlu_add_base : forall bc e imm B k, split_lit e = (B, k) -> is_lit B = None -> bi_nf (mk_binfo bc B) = true ->
  mkAlu ALU_ADD e (ELit imm) = bsum B (addc (mk_binfo bc B) (hask e) k imm).
Proof.
  intros bc e imm B k H HL NF. destruct (split_lit_shape e B k H HL) as [[HK ->]|[HK [-> ->]]]; rewrite HK.
  - apply mkAlu_add_A. exact NF.
  - apply mkAlu_add_B; assumption.
Qed.

Definition rfast (bc : bctx) (bi : binfo) (cc : Z) : option bool :=
  match bi_fa bi with
  | Some (lo63, hi63, w) =>
      if Z.eqb cc 0 then None else
      match find_rangeIF (bc_ri bc) (EAlu ALU_ADD (bi_b bi) (ELit cc)) with
      | Some _ => None
      | None =>
          let c := snorm (bi_c0 bi + snorm cc) in
          if (if Z.eqb c 0 then bi_triv bi else false) then None else
          match zb c with
          | Some c63 => if PrimInt63.leb BXIK.B62 (PrimInt63.add lo63 c63) then Some w else None
          | None => None
          end
      end
  | None => None
  end.
Lemma bi_fa_eq : forall bc B, bi_fa (mk_binfo bc B) = fa_of (bi_A (mk_binfo bc B)).
Proof. intros. unfold mk_binfo. rewrite ?erangeBF_fe, ?erange_fBF_fe. cbv zeta. destruct (nf_test _ _ _); reflexivity. Qed.
Lemma rfast_spec : forall bc B cc w, rfast bc (mk_binfo bc B) cc = Some w ->
  exists lo hi, bsum_range bc (mk_binfo bc B) cc = Some (lo, hi) /\ Z.eqb lo hi = false
                /\ bsum_noconc (mk_binfo bc B) cc (Some (lo, hi)) = (if bi_W (mk_binfo bc B) then w else false).
Proof.
  intros bc B cc w H. unfold rfast in H. rewrite bi_fa_eq in H. unfold fa_of in H.
  destruct (bi_A (mk_binfo bc B)) as [[lo0 hi0]|] eqn:EA; [|discriminate].
  destruct (Z.ltb_spec lo0 hi0) as [LT|]; [|discriminate].
  destruct (zb lo0) as [l63|] eqn:E1; [|discriminate]. destruct (zb hi0) as [h63|] eqn:E2; [|discriminate].
  destruct (Z.eqb cc 0) eqn:EC; [discriminate|].
  destruct (find_rangeIF (bc_ri bc) (EAlu ALU_ADD (bi_b (mk_binfo bc B)) (ELit cc))) eqn:EF; [discriminate|]. cbv zeta in H.
  destruct (if Z.eqb (snorm (bi_c0 (mk_binfo bc B) + snorm cc)) 0 then bi_triv (mk_binfo bc B) else false) eqn:ET; [discriminate|].
  destruct (zb (snorm (bi_c0 (mk_binfo bc B) + snorm cc))) as [c63|] eqn:E3; [|discriminate].
  destruct (PrimInt63.leb BXIK.B62 (PrimInt63.add l63 c63)) eqn:EL; [|discriminate]. injection H as <-.
  set (c := snorm (bi_c0 (mk_binfo bc B) + snorm cc)) in *.
  destruct (zb_spec _ _ E1) as [A1 B1]. destruct (zb_spec _ _ E2) as [A2 B2]. destruct (zb_spec _ _ E3) as [A3 B3].
  rewrite IMGFK.leb_b, Uint63.add_spec, A1, A3, wB63 in EL. change (Uint63.to_Z BXIK.B62) with (2 ^ 62) in EL.
  rewrite Z.mod_small in EL by lia. apply Z.leb_le in EL.
  assert (Q1 : zdiv64 (lo0 + c) = 0).
  { unfold zdiv64. destruct (Z.leb_spec 0 (lo0 + c)); [|lia]. destruct (Z.ltb_spec (lo0 + c) two64z); [reflexivity|]. unfold two64z in *. lia. }
  assert (Q2 : zdiv64 (hi0 + c) = 0).
  { unfold zdiv64. destruct (Z.leb_spec 0 (hi0 + c)); [|lia]. destruct (Z.ltb_spec (hi0 + c) two64z); [reflexivity|]. unfold two64z in *. lia. }
  exists (lo0 + c), (hi0 + c). split; [|split].
  - unfold bsum_range. rewrite EC. unfold erange_add. rewrite EF. fold c. rewrite ET, EA. cbv zeta. rewrite Q1, Q2. cbn [Z.eqb].
    f_equal. f_equal; ring.
  - apply Z.eqb_neq. lia.
  - unfold bsum_noconc. rewrite EC. destruct (bi_W (mk_binfo bc B)); [|reflexivity].
    unfold wide. replace (hi0 + c - (lo0 + c)) with (hi0 - lo0) by ring. reflexivity.
Qed.

Definition to_saddr_nl0 (bc : bctx) (c : bcache) (e : expr) (imm : Z) (B : expr) (k : Z) : saddr * bcache :=
  let '(bi, c') := bget bc c B in
  if bi_nf bi then
    let cc := addc bi (hask e) k imm in
    if bsum_noconc bi cc (bsum_range bc bi cc) then (to_saddr e imm, c') else (to_saddrKBG bc e imm, c')
  else (to_saddrKBG bc e imm, c').
Definition to_saddr_nl (bc : bctx) (c : bcache) (e : expr) (imm : Z) (B : expr) (k : Z) : saddr * bcache :=
  let '(bi, c') := bget bc c B in
  if bi_nf bi then
    let cc := addc bi (hask e) k imm in
    if (match rfast bc bi cc with Some w => if bi_W bi then w else false | None => bsum_noconc bi cc (bsum_range bc bi cc) end)
    then (to_saddr e imm, c') else (to_saddrKBG bc e imm, c')
  else (to_saddrKBG bc e imm, c').
Definition to_saddrKB_c (bc : bctx) (c : bcache) (e : expr) (imm : Z) : saddr * bcache :=
  let '(B, k) := split_lit e in
  match B with
  | ELit _ => (to_saddr e imm, c)
  | _ => to_saddr_nl bc c e imm B k
  end.
Lemma to_saddr_nl0_spec : forall bc c e imm B k, BCOK bc c -> split_lit e = (B, k) -> is_lit B = None ->
  fst (to_saddr_nl0 bc c e imm B k) = to_saddrKB bc e imm /\ BCOK bc (snd (to_saddr_nl0 bc c e imm B k)).
Proof.
  intros bc c e imm B k HC ES HL. unfold to_saddr_nl0. rewrite to_saddrKBG_eq. destruct (bget_spec bc c B HC) as [G1 G2].
  destruct (bget bc c B) as [bi c']. cbn [fst snd] in G1, G2. subst bi.
  destruct (bi_nf (mk_binfo bc B)) eqn:NF; [|split; [reflexivity|exact G2]]. cbv zeta.
  destruct (bsum_noconc _ _ _) eqn:NC; [|split; [reflexivity|exact G2]].
  split; [|exact G2]. cbn [fst]. rewrite (to_saddrKB_nolit bc e imm B k ES HL), (mkAlu_add_base bc e imm B k ES HL NF).
  rewrite bsum_range_eq in NC by exact NF. rewrite (conc_none bc B _ NF NC). reflexivity.
Qed.
Lemma to_saddr_nl_eq0 : forall bc c e imm B k, BCOK bc c -> to_saddr_nl bc c e imm B k = to_saddr_nl0 bc c e imm B k.
Proof.
  intros bc c e imm B k HC. unfold to_saddr_nl, to_saddr_nl0. destruct (bget_spec bc c B HC) as [G1 G2].
  destruct (bget bc c B) as [bi c']. cbn [fst snd] in G1, G2. subst bi.
  destruct (bi_nf (mk_binfo bc B)); [|reflexivity]. cbv zeta.
  destruct (rfast bc (mk_binfo bc B) (addc (mk_binfo bc B) (hask e) k imm)) as [w|] eqn:RF; [|reflexivity].
  destruct (rfast_spec bc B _ w RF) as (lo & hi & R1 & R2 & R3). rewrite R1, R3. reflexivity.
Qed.
Lemma to_saddr_nl_spec : forall bc c e imm B k, BCOK bc c -> split_lit e = (B, k) -> is_lit B = None ->
  fst (to_saddr_nl bc c e imm B k) = to_saddrKB bc e imm /\ BCOK bc (snd (to_saddr_nl bc c e imm B k)).
Proof. intros bc c e imm B k HC ES HL. rewrite (to_saddr_nl_eq0 bc c e imm B k HC). apply to_saddr_nl0_spec; assumption. Qed.

Lemma to_saddrKB_c_spec : forall bc c e imm, BCOK bc c ->
  fst (to_saddrKB_c bc c e imm) = to_saddrKB bc e imm /\ BCOK bc (snd (to_saddrKB_c bc c e imm)).
Proof.
  intros bc c e imm HC. unfold to_saddrKB_c. destruct (split_lit e) as [B k] eqn:ES.
  destruct B; try (apply to_saddr_nl_spec; [exact HC|exact ES|reflexivity]).
  split; [|exact HC]. cbn [fst]. unfold to_saddrKB. rewrite ES. reflexivity.
Qed.

Definition add_nl0 (bc : bctx) (c : bcache) (a : expr) (imm : Z) (B : expr) (k : Z) : expr * bcache :=
  let '(bi, c') := bget bc c B in
  if bi_nf bi then
    let cc := addc bi (hask a) k imm in
    let r := bsum_range bc bi cc in
    match r with
    | Some (lo, hi) =>
        if Z.eqb lo hi then (ELit lo, c')
        else if bsum_noconc bi cc r then (bsum B cc, c') else (foldKBG bc (mkAlu ALU_ADD a (ELit imm)), c')
    | None => if bsum_noconc bi cc r then (bsum B cc, c') else (foldKBG bc (mkAlu ALU_ADD a (ELit imm)), c')
    end
  else (foldKBG bc (mkAlu ALU_ADD a (ELit imm)), c').
Definition add_nl (bc : bctx) (c : bcache) (a : expr) (imm : Z) (B : expr) (k : Z) : expr * bcache :=
  let '(bi, c') := bget bc c B in
  if bi_nf bi then
    let cc := addc bi (hask a) k imm in
    match rfast bc bi cc with
    | Some w => if (if bi_W bi then w else false) then (bsum B cc, c') else (foldKBG bc (mkAlu ALU_ADD a (ELit imm)), c')
    | None =>
        let r := bsum_range bc bi cc in
        match r with
        | Some (lo, hi) =>
            if Z.eqb lo hi then (ELit lo, c')
            else if bsum_noconc bi cc r then (bsum B cc, c') else (foldKBG bc (mkAlu ALU_ADD a (ELit imm)), c')
        | None => if bsum_noconc bi cc r then (bsum B cc, c') else (foldKBG bc (mkAlu ALU_ADD a (ELit imm)), c')
        end
    end
  else (foldKBG bc (mkAlu ALU_ADD a (ELit imm)), c').

Definition mkAluL (op : aluop) (a b : expr) : expr :=
  match a, b with
  | ELit x, ELit y => ELit (zfast op (zmod64 x) (zmod64 y))
  | _, _ => mkAlu op a b
  end.
Lemma wrap64_zmod64 : forall z, wrap64 z = zmod64 z.
Proof.
  intros z. rewrite zmod64_eq. unfold wrap64. destruct (Z.leb_spec 0 z); cbn [andb]; [|reflexivity].
  destruct (Z.ltb_spec z two64); [|reflexivity]. symmetry. apply Z.mod_small. unfold two64 in *. lia.
Qed.
Lemma mkAluL_eq : forall op a b, mkAluL op a b = mkAlu op a b.
Proof.
  intros op a b. unfold mkAluL. destruct a; try reflexivity. destruct b; try reflexivity.
  unfold mkAlu. cbn [is_lit]. unfold zalu_l. rewrite !wrap64_zmod64. reflexivity.
Qed.
Definition mkAluKB_add_c (bc : bctx) (c : bcache) (a : expr) (imm : Z) : expr * bcache :=
  let '(B, k) := split_lit a in
  match B with
  | ELit _ => (foldKBG bc (mkAluL ALU_ADD a (ELit imm)), c)
  | _ => add_nl bc c a imm B k
  end.
Lemma foldKB_bsum : forall bc B cc, closedb B = false ->
  foldKB bc (bsum B cc) =
  match erangeB bc (bsum B cc) with
  | Some (lo, hi) => if Z.eqb lo hi then ELit lo else match concretizeB bc (bsum B cc) with Some v => ELit v | None => bsum B cc end
  | None => match concretizeB bc (bsum B cc) with Some v => ELit v | None => bsum B cc end
  end.
Proof. intros bc B cc H. unfold bsum. destruct (Z.eqb cc 0); [|reflexivity]. destruct B; try reflexivity. discriminate. Qed.
Lemma add_nl0_spec : forall bc c a imm B k, BCOK bc c -> split_lit a = (B, k) -> is_lit B = None ->
  fst (add_nl0 bc c a imm B k) = mkAluKB bc ALU_ADD a (ELit imm) /\ BCOK bc (snd (add_nl0 bc c a imm B k)).
Proof.
  intros bc c a imm B k HC ES HL. unfold add_nl0.
  replace (foldKBG bc (mkAlu ALU_ADD a (ELit imm))) with (mkAluKB bc ALU_ADD a (ELit imm)) by (rewrite foldKBG_eq; reflexivity).
  destruct (bget_spec bc c B HC) as [G1 G2].
  destruct (bget bc c B) as [bi c']. cbn [fst snd] in G1, G2. subst bi.
  destruct (bi_nf (mk_binfo bc B)) eqn:NF; [|split; [reflexivity|exact G2]]. cbv zeta.
  destruct (nf_spec bc B NF) as (_ & _ & _ & _ & CL & _).
  assert (EQ : mkAluKB bc ALU_ADD a (ELit imm) = foldKB bc (bsum B (addc (mk_binfo bc B) (hask a) k imm))).
  { unfold mkAluKB. change (mkAluK0B bc ALU_ADD a (ELit imm)) with (mkAlu ALU_ADD a (ELit imm)).
    rewrite (mkAlu_add_base bc a imm B k ES HL NF). reflexivity. }
  rewrite EQ, (foldKB_bsum bc B _ CL). rewrite <- (bsum_range_eq bc B _ NF).
  set (cc := addc (mk_binfo bc B) (hask a) k imm). set (r := bsum_range bc (mk_binfo bc B) cc).
  assert (NCE : bsum_noconc (mk_binfo bc B) cc r = true -> concretizeB bc (bsum B cc) = None).
  { intros NC. apply (conc_none bc B cc NF). rewrite <- (bsum_range_eq bc B cc NF). exact NC. }
  destruct r as [[lo hi]|].
  - destruct (Z.eqb lo hi); [split; [reflexivity|exact G2]|].
    destruct (bsum_noconc (mk_binfo bc B) cc (Some (lo, hi))) eqn:NC; [|split; [reflexivity|exact G2]].
    rewrite (NCE eq_refl). split; [reflexivity|exact G2].
  - destruct (bsum_noconc (mk_binfo bc B) cc None) eqn:NC; [|split; [reflexivity|exact G2]].
    rewrite (NCE eq_refl). split; [reflexivity|exact G2].
Qed.
Lemma add_nl_eq0 : forall bc c a imm B k, BCOK bc c -> add_nl bc c a imm B k = add_nl0 bc c a imm B k.
Proof.
  intros bc c a imm B k HC. unfold add_nl, add_nl0. destruct (bget_spec bc c B HC) as [G1 G2].
  destruct (bget bc c B) as [bi c']. cbn [fst snd] in G1, G2. subst bi.
  destruct (bi_nf (mk_binfo bc B)); [|reflexivity]. cbv zeta.
  destruct (rfast bc (mk_binfo bc B) (addc (mk_binfo bc B) (hask a) k imm)) as [w|] eqn:RF; [|reflexivity].
  destruct (rfast_spec bc B _ w RF) as (lo & hi & R1 & R2 & R3). rewrite R1, R2, R3. reflexivity.
Qed.
Lemma add_nl_spec : forall bc c a imm B k, BCOK bc c -> split_lit a = (B, k) -> is_lit B = None ->
  fst (add_nl bc c a imm B k) = mkAluKB bc ALU_ADD a (ELit imm) /\ BCOK bc (snd (add_nl bc c a imm B k)).
Proof. intros bc c a imm B k HC ES HL. rewrite (add_nl_eq0 bc c a imm B k HC). apply add_nl0_spec; assumption. Qed.

Lemma mkAluKB_add_c_spec : forall bc c a imm, BCOK bc c ->
  fst (mkAluKB_add_c bc c a imm) = mkAluKB bc ALU_ADD a (ELit imm) /\ BCOK bc (snd (mkAluKB_add_c bc c a imm)).
Proof.
  intros bc c a imm HC. unfold mkAluKB_add_c. destruct (split_lit a) as [B k] eqn:ES.
  destruct B; try (apply add_nl_spec; [exact HC|exact ES|reflexivity]).
  split; [cbn [fst]; rewrite ?foldKBG_eq, mkAluL_eq; reflexivity|exact HC].
Qed.

Definition br_nl (bc : bctx) (c : bcache) (B : expr) : option (Z * Z) * bcache :=
  let '(bi, c') := bget bc c B in (bi_er bi, c').
Definition base_range_c (bc : bctx) (c : bcache) (B : expr) : option (Z * Z) * bcache :=
  match B with
  | ELit _ => (base_rangeB bc B, c)
  | _ => br_nl bc c B
  end.
Lemma br_nl_spec : forall bc c B, BCOK bc c -> is_lit B = None ->
  fst (br_nl bc c B) = base_rangeB bc B /\ BCOK bc (snd (br_nl bc c B)).
Proof.
  intros bc c B HC HL. unfold br_nl. destruct (bget_spec bc c B HC) as [G1 G2].
  destruct (bget bc c B) as [bi c']. cbn [fst snd] in *. subst bi. split; [|exact G2].
  rewrite bi_er_eq. destruct B; try reflexivity. discriminate.
Qed.

Definition base_range63_c (bc : bctx) (c : bcache) (B : expr) : option (Z * Z) * option (PrimInt63.int * PrimInt63.int) * bcache :=
  match B with
  | ELit _ => (base_rangeB bc B, None, c)
  | _ => let '(bi, c') := bget bc c B in (bi_er bi, bi_e63 bi, c')
  end.
Lemma bi_e63_eq : forall bc B, bi_e63 (mk_binfo bc B) = rng63 (erangeB bc B).
Proof. intros. unfold mk_binfo. rewrite ?erangeBF_fe, ?erange_fBF_fe. cbv zeta. destruct (nf_test _ _ _); reflexivity. Qed.
Lemma base_range63_c_spec : forall bc c B, BCOK bc c ->
  fst (fst (base_range63_c bc c B)) = base_rangeB bc B
  /\ (snd (fst (base_range63_c bc c B)) = None \/ snd (fst (base_range63_c bc c B)) = rng63 (base_rangeB bc B))
  /\ BCOK bc (snd (base_range63_c bc c B)).
Proof.
  intros bc c B HC. unfold base_range63_c.
  assert (G : forall B', is_lit B' = None ->
            fst (fst (let '(bi, c') := bget bc c B' in (bi_er bi, bi_e63 bi, c'))) = base_rangeB bc B'
            /\ (snd (fst (let '(bi, c') := bget bc c B' in (bi_er bi, bi_e63 bi, c'))) = None
                \/ snd (fst (let '(bi, c') := bget bc c B' in (bi_er bi, bi_e63 bi, c'))) = rng63 (base_rangeB bc B'))
            /\ BCOK bc (snd (let '(bi, c') := bget bc c B' in (bi_er bi, bi_e63 bi, c')))).
  { intros B' HL. destruct (bget_spec bc c B' HC) as [G1 G2]. destruct (bget bc c B') as [bi c']. cbn [fst snd] in *. subst bi.
    rewrite bi_er_eq, bi_e63_eq. assert (E : base_rangeB bc B' = erangeB bc B') by (destruct B'; try reflexivity; discriminate).
    rewrite E. split; [reflexivity|]. split; [right; reflexivity|exact G2]. }
  destruct B; try (apply G; reflexivity).
  cbn [fst snd]. split; [reflexivity|]. split; [left; reflexivity|exact HC].
Qed.
Lemma base_range_c_spec : forall bc c B, BCOK bc c ->
  fst (base_range_c bc c B) = base_rangeB bc B /\ BCOK bc (snd (base_range_c bc c B)).
Proof.
  intros bc c B HC. unfold base_range_c.
  destruct B; try (apply br_nl_spec; [exact HC|reflexivity]).
  split; [reflexivity|exact HC].
Qed.

Definition fold_nl0 (bc : bctx) (c : bcache) (e : expr) (B : expr) (k : Z) : expr * bcache :=
  let '(bi, c') := bget bc c B in
  if bi_nf bi then
    if (if hask e then Z.eqb k 0 else false) then (foldKBG bc e, c')
    else
      let cc := if hask e then k else 0 in
      let r := bsum_range bc bi cc in
      match r with
      | Some (lo, hi) =>
          if Z.eqb lo hi then (ELit lo, c')
          else if bsum_noconc bi cc r then (e, c') else (foldKBG bc e, c')
      | None => if bsum_noconc bi cc r then (e, c') else (foldKBG bc e, c')
      end
  else (foldKBG bc e, c').
Definition fold_nl (bc : bctx) (c : bcache) (e : expr) (B : expr) (k : Z) : expr * bcache :=
  let '(bi, c') := bget bc c B in
  if bi_nf bi then
    if (if hask e then Z.eqb k 0 else false) then (foldKBG bc e, c')
    else
      let cc := if hask e then k else 0 in
      match rfast bc bi cc with
      | Some w => if (if bi_W bi then w else false) then (e, c') else (foldKBG bc e, c')
      | None =>
          let r := bsum_range bc bi cc in
          match r with
          | Some (lo, hi) =>
              if Z.eqb lo hi then (ELit lo, c')
              else if bsum_noconc bi cc r then (e, c') else (foldKBG bc e, c')
          | None => if bsum_noconc bi cc r then (e, c') else (foldKBG bc e, c')
          end
      end
  else (foldKBG bc e, c').
Definition foldKB_c (bc : bctx) (c : bcache) (e : expr) : expr * bcache :=
  match e with
  | ELit _ => (e, c)
  | _ => let '(B, k) := split_lit e in
         match B with
         | ELit _ => (foldKBG bc e, c)
         | _ => fold_nl bc c e B k
         end
  end.
Lemma fold_nl0_spec : forall bc c e B k, BCOK bc c -> split_lit e = (B, k) -> is_lit B = None ->
  fst (fold_nl0 bc c e B k) = foldKB bc e /\ BCOK bc (snd (fold_nl0 bc c e B k)).
Proof.
  intros bc c e B k HC ES HL. unfold fold_nl0. rewrite foldKBG_eq. destruct (bget_spec bc c B HC) as [G1 G2].
  destruct (bget bc c B) as [bi c']. cbn [fst snd] in G1, G2. subst bi.
  destruct (bi_nf (mk_binfo bc B)) eqn:NF; [|split; [reflexivity|exact G2]].
  destruct (nf_spec bc B NF) as (_ & _ & _ & _ & CL & _).
  destruct (if hask e then Z.eqb k 0 else false) eqn:HZ; [split; [reflexivity|exact G2]|]. cbv zeta.
  set (cc := if hask e then k else 0).
  assert (EB : e = bsum B cc).
  { unfold cc, bsum. destruct (split_lit_shape e B k ES HL) as [[HK ->]|[HK [-> ->]]]; rewrite HK in *.
    - rewrite HZ. reflexivity.
    - reflexivity. }
  assert (FE : foldKB bc e = match erangeB bc e with
                            | Some (lo, hi) => if Z.eqb lo hi then ELit lo else match concretizeB bc e with Some v => ELit v | None => e end
                            | None => match concretizeB bc e with Some v => ELit v | None => e end
                            end) by (rewrite EB; apply (foldKB_bsum bc B cc CL)).
  assert (RE : bsum_range bc (mk_binfo bc B) cc = erangeB bc e) by (rewrite EB; apply (bsum_range_eq bc B cc NF)).
  assert (NCE : bsum_noconc (mk_binfo bc B) cc (erangeB bc e) = true -> concretizeB bc e = None).
  { intros NC. rewrite EB in *. apply (conc_none bc B cc NF). exact NC. }
  rewrite FE, RE. clear FE RE EB.
  destruct (erangeB bc e) as [[lo hi]|].
  - destruct (Z.eqb lo hi); [split; [reflexivity|exact G2]|].
    destruct (bsum_noconc (mk_binfo bc B) cc (Some (lo, hi))) eqn:NC; [|split; [reflexivity|exact G2]].
    rewrite (NCE eq_refl). split; [reflexivity|exact G2].
  - destruct (bsum_noconc (mk_binfo bc B) cc None) eqn:NC; [|split; [reflexivity|exact G2]].
    rewrite (NCE eq_refl). split; [reflexivity|exact G2].
Qed.
Lemma fold_nl_eq0 : forall bc c e B k, BCOK bc c -> fold_nl bc c e B k = fold_nl0 bc c e B k.
Proof.
  intros bc c e B k HC. unfold fold_nl, fold_nl0. destruct (bget_spec bc c B HC) as [G1 G2].
  destruct (bget bc c B) as [bi c']. cbn [fst snd] in G1, G2. subst bi.
  destruct (bi_nf (mk_binfo bc B)); [|reflexivity].
  destruct (if hask e then Z.eqb k 0 else false); [reflexivity|]. cbv zeta.
  destruct (rfast bc (mk_binfo bc B) (if hask e then k else 0)) as [w|] eqn:RF; [|reflexivity].
  destruct (rfast_spec bc B _ w RF) as (lo & hi & R1 & R2 & R3). rewrite R1, R2, R3. reflexivity.
Qed.
Lemma fold_nl_spec : forall bc c e B k, BCOK bc c -> split_lit e = (B, k) -> is_lit B = None ->
  fst (fold_nl bc c e B k) = foldKB bc e /\ BCOK bc (snd (fold_nl bc c e B k)).
Proof. intros bc c e B k HC ES HL. rewrite (fold_nl_eq0 bc c e B k HC). apply fold_nl0_spec; assumption. Qed.

Lemma foldKB_c_spec : forall bc c e, BCOK bc c -> fst (foldKB_c bc c e) = foldKB bc e /\ BCOK bc (snd (foldKB_c bc c e)).
Proof.
  intros bc c e HC. unfold foldKB_c.
  destruct e; try (split; [reflexivity|exact HC]);
    (destruct (split_lit _) as [B k0] eqn:ES; destruct B; try (apply fold_nl_spec; [exact HC|exact ES|reflexivity]); split; [cbn [fst]; rewrite ?foldKBG_eq; reflexivity|exact HC]).
Qed.

Definition erange_h (bc : bctx) (c : bcache) (e : expr) : option (Z * Z) :=
  match e with
  | ELit _ => erangeBF bc e
  | _ => let '(B, k) := split_lit e in
         match B with
         | ELit _ => erangeBF bc e
         | _ => match bfind c B with
                | Some bi =>
                    if bi_nf bi then
                      if (if hask e then Z.eqb k 0 else false) then erangeBF bc e
                      else bsum_range bc bi (if hask e then k else 0)
                    else erangeBF bc e
                | None => erangeBF bc e
                end
         end
  end.
Lemma erange_h_eq : forall bc c e, BCOK bc c -> erange_h bc c e = erangeB bc e.
Proof.
  intros bc c e HC. unfold erange_h. rewrite erangeBF_fe.
  destruct e; try reflexivity;
    (destruct (split_lit _) as [B k0] eqn:ES; destruct B; try reflexivity;
     match goal with |- context [bfind c ?b] => destruct (bfind c b) as [bi|] eqn:F; [|reflexivity];
       pose proof (bfind_spec bc c b bi HC F) as EB0; subst bi;
       destruct (bi_nf (mk_binfo bc b)) eqn:NF; [|reflexivity];
       match goal with |- context [if hask ?e0 then Z.eqb k0 0 else false] =>
         destruct (if hask e0 then Z.eqb k0 0 else false) eqn:HZ; [reflexivity|];
         assert (EB : e0 = bsum b (if hask e0 then k0 else 0));
         [ unfold bsum; destruct (split_lit_shape e0 b k0 ES eq_refl) as [[HK EE]|[HK [EE1 EE2]]]; rewrite HK in *;
           [ rewrite HZ; exact EE | rewrite EE2 in *; cbn [Z.eqb]; exact EE1 ]
         | rewrite EB at 2; apply (bsum_range_eq bc b _ NF) ]
       end
     end).
Qed.
End BASFK.
