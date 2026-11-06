(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec AxSymExec3.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3B CxfLeaf CxfNat CxfStore CxfL1.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module AX2BL.
Import AX2B.
Notation "x && y" := (if x then y else false) (at level 40, left associativity) : bool_scope.
Notation "x || y" := (if x then true else y) (at level 50, left associativity) : bool_scope.
Import AX2.
Import AX2L.
Fixpoint first_var (e : expr) : option nat :=
  match e with
  | ELit _ => None
  | EVar n => Some n
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b =>
      match first_var a with Some n => Some n | None => first_var b end
  | EExt _ _ _ a => first_var a
  | EBlob _ _ _ _ => None
  end.
Lemma L_AX2BL_first_var : @first_var = @AX2B.first_var.
Proof. unfold first_var. reflexivity. Qed.

Definition vkey_of (e : expr) : option nat := first_var (fst (lit_strip e)).
Lemma L_AX2BL_vkey_of : @vkey_of = @AX2B.vkey_of.
Proof. unfold vkey_of. rewrite ?L_AX2BL_first_var, ?AX2L.L_AX2L_lit_strip. reflexivity. Qed.

Fixpoint lset {A : Type} (l : list (list A)) (n : nat) (x : A) {struct n} : list (list A) :=
  match n, l with
  | O, [] => [[x]]
  | O, b :: rest => (x :: b) :: rest
  | S m, [] => [] :: lset [] m x
  | S m, b :: rest => b :: lset rest m x
  end.
Lemma L_AX2BL_lset : @lset = @AX2B.lset.
Proof. unfold lset. reflexivity. Qed.

Definition lget {A : Type} (l : list (list A)) (n : nat) : list A := CXNAT.nthF n l [].
Lemma L_AX2BL_lget : @lget = @AX2B.lget.
Proof. unfold lget. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition ri_bucket (ri : rindex) (k : option nat) : list kentry :=
  match k with Some n => lget (ri_vars ri) n | None => ri_other ri end.
Lemma L_AX2BL_ri_bucket : @ri_bucket = @AX2B.ri_bucket.
Proof. unfold ri_bucket. rewrite ?L_AX2BL_lget. reflexivity. Qed.

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
Lemma L_AX2BL_mk_ri : @mk_ri = @AX2B.mk_ri.
Proof. unfold mk_ri. rewrite ?L_AX2BL_vkey_of, ?L_AX2BL_lset. reflexivity. Qed.

Definition find_rangeI (ri : rindex) (e : expr) : option (Z * Z) := find_range (ri_bucket ri (vkey_of e)) e.
Lemma L_AX2BL_find_rangeI : @find_rangeI = @AX2B.find_rangeI.
Proof. unfold find_rangeI. rewrite ?L_AX2BL_vkey_of, ?L_AX2BL_ri_bucket, ?AX2L.L_AX2L_find_range. reflexivity. Qed.

Definition okey_eqb (a b : option nat) : bool :=
  match a, b with Some x, Some y => CXNAT.eqbF x y | None, None => true | _, _ => false end.
Lemma L_AX2BL_okey_eqb : @okey_eqb = @AX2B.okey_eqb.
Proof. unfold okey_eqb. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition side_eqb (c : saddr) (m : expr) (t : positive * (saddr * expr)) : bool :=
  if Z.eqb (a_off (fst (snd t))) (a_off c) then if expr_eqb (snd (snd t)) m then expr_eqb (a_base (fst (snd t))) (a_base c) else false else false.
Lemma L_AX2BL_side_eqb : @side_eqb = @AX2B.side_eqb.
Proof. unfold side_eqb. rewrite ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Definition dfact : Type := (positive * positive * ((saddr * expr) * (saddr * expr)))%type.
Lemma L_AX2BL_dfact : @dfact = @AX2B.dfact.
Proof. unfold dfact. reflexivity. Qed.

Definition skey (c : saddr) (m : expr) : nat := match vkey_of (a_base c) with Some n => S n | None => O end.
Lemma L_AX2BL_skey : @skey = @AX2B.skey.
Proof. unfold skey. rewrite ?L_AX2BL_vkey_of. reflexivity. Qed.

Definition rt_empty : rtab := RT xH [] PTLeaf [] [].
Lemma L_AX2BL_rt_empty : @rt_empty = @AX2B.rt_empty.
Proof. unfold rt_empty. reflexivity. Qed.

Definition rt_bucket (rt : rtab) (k : nat) : list (positive * (saddr * expr)) := lget (rt_idx rt) k.
Lemma L_AX2BL_rt_bucket : @rt_bucket = @AX2B.rt_bucket.
Proof. unfold rt_bucket. rewrite ?L_AX2BL_lget. reflexivity. Qed.

Definition rt_lookup (rt : rtab) (c : saddr) (m : expr) : option positive :=
  match List.find (side_eqb c m) (rt_bucket rt (skey c m)) with Some t => Some (fst t) | None => None end.
Lemma L_AX2BL_rt_lookup : @rt_lookup = @AX2B.rt_lookup.
Proof. unfold rt_lookup. rewrite ?L_AX2BL_side_eqb, ?L_AX2BL_skey, ?L_AX2BL_rt_bucket. reflexivity. Qed.

Definition rt_intern (rt : rtab) (c : saddr) (m : expr) : positive * rtab :=
  match rt_lookup rt c m with
  | Some i => (i, rt)
  | None => let i := rt_n rt in let k := skey c m in
            (i, RT (Pos.succ i) ((i, (c, m)) :: rt_sides rt) (rt_part rt) (rt_facts rt) (lset (rt_idx rt) k (i, (c, m))))
  end.
Lemma L_AX2BL_rt_intern : @rt_intern = @AX2B.rt_intern.
Proof. unfold rt_intern. rewrite ?L_AX2BL_lset, ?L_AX2BL_skey, ?L_AX2BL_rt_lookup. reflexivity. Qed.

Definition rt_partners (rt : rtab) (i : positive) : list positive :=
  match pt_get (rt_part rt) i with Some l => l | None => [] end.
Lemma L_AX2BL_rt_partners : @rt_partners = @AX2B.rt_partners.
Proof. unfold rt_partners. rewrite ?AX2L.L_AX2L_pt_get. reflexivity. Qed.

Definition rt_addpair (rt : rtab) (i j : positive) : rtab :=
  RT (rt_n rt) (rt_sides rt) (pt_set i (j :: rt_partners rt i) (rt_part rt)) (rt_facts rt) (rt_idx rt).
Lemma L_AX2BL_rt_addpair : @rt_addpair = @AX2B.rt_addpair.
Proof. unfold rt_addpair. rewrite ?L_AX2BL_rt_partners, ?AX2L.L_AX2L_pt_set. reflexivity. Qed.

Definition rt_addfact (rt : rtab) (f : dfact) : rtab := RT (rt_n rt) (rt_sides rt) (rt_part rt) (f :: rt_facts rt) (rt_idx rt).
Lemma L_AX2BL_rt_addfact : @rt_addfact = @AX2B.rt_addfact.
Proof. unfold rt_addfact. rewrite ?L_AX2BL_dfact. reflexivity. Qed.

Fixpoint mk_rt (fk : list kentry) : rtab :=
  match fk with
  | [] => rt_empty
  | KDisj c1 m1 c2 m2 :: rest =>
      let rt := mk_rt rest in
      let '(i, rt1) := rt_intern rt c1 m1 in
      let '(j, rt2) := rt_intern rt1 c2 m2 in
      rt_addfact (rt_addpair (rt_addpair rt2 i j) j i) (i, j, ((c1, m1), (c2, m2)))
  | _ :: rest => mk_rt rest
  end.
Lemma L_AX2BL_mk_rt : @mk_rt = @AX2B.mk_rt.
Proof. unfold mk_rt. rewrite ?L_AX2BL_rt_empty, ?L_AX2BL_rt_intern, ?L_AX2BL_rt_addpair, ?L_AX2BL_rt_addfact. reflexivity. Qed.

Definition pmem (i : positive) (l : list positive) : bool := existsb (Pos.eqb i) l.
Lemma L_AX2BL_pmem : @pmem = @AX2B.pmem.
Proof. unfold pmem. reflexivity. Qed.

Fixpoint disj_sidesR (fs : list dfact) (RS : list positive) : list (saddr * expr) :=
  match fs with
  | [] => []
  | (i, j, (s1, s2)) :: rest =>
      let r := disj_sidesR rest RS in
      let r1 := if pmem j RS then s1 :: r else r in
      if pmem i RS then s2 :: r1 else r1
  end.
Lemma L_AX2BL_disj_sidesR : @disj_sidesR = @AX2B.disj_sidesR.
Proof. unfold disj_sidesR. rewrite ?L_AX2BL_dfact, ?L_AX2BL_pmem. reflexivity. Qed.

Definition partners_of (rt : rtab) (RS : list positive) : list positive := flat_map (rt_partners rt) RS.
Lemma L_AX2BL_partners_of : @partners_of = @AX2B.partners_of.
Proof. unfold partners_of. rewrite ?L_AX2BL_rt_partners. reflexivity. Qed.

Definition mkbc0 (fk : list kentry) (fs : list sfact) : bctx :=
  BC fk (facts_of fk) fs (mk_ri (facts_of fk)) (mk_rt fk).
Lemma L_AX2BL_mkbc0 : @mkbc0 = @AX2B.mkbc0.
Proof. unfold mkbc0. rewrite ?L_AX2BL_mk_ri, ?L_AX2BL_mk_rt, ?AX2L.L_AX2L_facts_of, ?AX2L.L_AX2L_sfact. reflexivity. Qed.

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
          
          match (match b, erange bc a with
                 | ELit m, Some (al, ah) =>
                     let m' := (CXLF.zm64 m)%Z in
                     let j := Z.log2 (m' + 1) in
                     if (Z.eqb (m' + 1) (CXLF.zpow2 j) && Z.leb (CXLF.zshr al j) (CXLF.zshr ah j) && Z.eqb (CXLF.zshr al j) (CXLF.zshr ah j))%bool
                     then Some ((CXLF.zmodp al j), (CXLF.zmodp ah j))
                     else let jh := Z.log2 (two64 - m') in
                          if (Z.eqb (two64 - m') (CXLF.zpow2 jh) && Z.ltb jh 64)%bool
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
          | Some (al, ah), Some s => Some ((CXLF.zshr al s), (CXLF.zshr ah s))
          | _, _ => None
          end
      | ALU_SRA =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              if Z.ltb ah (CXLF.p63) then Some ((CXLF.zshr al s), (CXLF.zshr ah s)) else None
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
              if (Z.ltb ah (CXLF.p63) && Z.ltb bh (CXLF.p63))%bool then
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
              if (Z.leb 0 (al + bl') && Z.ltb (ah + bh') (CXLF.p31))%bool
              then Some ((al + bl')%Z, (ah + bh')%Z) else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb bh al && Z.ltb (ah - bl) (CXLF.p31))%bool
              then Some ((al - bh)%Z, (ah - bl)%Z) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb (ah * 2 ^ s') (CXLF.p31) then Some ((al * 2 ^ s')%Z, (ah * 2 ^ s')%Z) else None
          | _, _ => None
          end
      | ALU_SRL =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if (Z.ltb ah (CXLF.p32) && (Z.ltb 0 s' || Z.ltb ah (CXLF.p31)))%bool
              then Some ((CXLF.zshr al s'), (CXLF.zshr ah s')) else None
          | _, _ => None
          end
      | ALU_SRA =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb ah (CXLF.p31) then Some ((CXLF.zshr al s'), (CXLF.zshr ah s')) else None
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
              let d' := (CXLF.zm64 d)%Z in
              if Z.ltb 0 d' then Some ((al / d')%Z, (ah / d')%Z) else None
          | _, _ => None
          end
      | M_REMU =>
          match erange bc a, b with
          | Some (al, ah), ELit d =>
              let d' := (CXLF.zm64 d)%Z in
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
            if (Z.leb 0 al && Z.ltb ah (CXLF.zhalf w))%bool then Some (al, ah)
            else if (CXNAT.lebF 1 n && CXNAT.lebF n 8 && Z.leb (CXLF.zhalf w) al && Z.ltb ah w)%bool
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
Lemma L_AX2BL_erange_fB : @erange_fB = @AX2B.erange_fB.
Proof. unfold erange_fB. rewrite ?L_AX2BL_find_rangeI, ?AX2L.L_AX2L_clampi, ?AX2L.L_AX2L_erange, ?AX2L.L_AX2L_lin_of, ?AX2L.L_AX2L_lin_range, ?AX2L.L_AX2L_lin_trivial, ?AX2L.L_AX2L_lit_shamt, ?AX2L.L_AX2L_mask_cover, ?AX2L.L_AX2L_two64, ?AX2L.L_AX2L_two64m1, ?AX2L.L_AX2L_zdiv64, ?AX2L.L_AX2L_zmod64, ?AX2L.L_AX2L_zsigned64, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition erange0B (bc : bctx) (e : expr) : option (Z * Z) := erange_fB erange_fuel bc e.
Lemma L_AX2BL_erange0B : @erange0B = @AX2B.erange0B.
Proof. unfold erange0B. rewrite ?L_AX2BL_erange_fB, ?AX2L.L_AX2L_erange_fuel. reflexivity. Qed.

Definition erangeB (bc : bctx) (e : expr) : option (Z * Z) :=
  let r := erange0B bc e in
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
Lemma L_AX2BL_erangeB : @erangeB = @AX2B.erangeB.
Proof. unfold erangeB. rewrite ?L_AX2BL_erange0B, ?AX2L.L_AX2L_deand, ?AX2L.L_AX2L_lin_of, ?AX2L.L_AX2L_unlin. reflexivity. Qed.

Definition base_rangeB (bc : bctx) (e : expr) : option (Z * Z) :=
  match e with ELit z => let v := (CXLF.zm64 z)%Z in Some (v, v) | _ => erangeB bc e end.
Lemma L_AX2BL_base_rangeB : @base_rangeB = @AX2B.base_rangeB.
Proof. unfold base_rangeB. rewrite ?L_AX2BL_erangeB, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition ealignB (bc : bctx) (e : expr) : Z := Z.max (ealign0 (bc_ffk bc) e) (pageup_align e).
Lemma L_AX2BL_ealignB : @ealignB = @AX2B.ealignB.
Proof. unfold ealignB. rewrite ?AX2L.L_AX2L_ealign0, ?AX2L.L_AX2L_pageup_align. reflexivity. Qed.

Definition lin_nowrapB (bc : bctx) (e : expr) : bool :=
  let l := lin_of e in
  match lin_range (erangeB bc) (fst l) (snd l) with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%bool
  | None => false
  end.
Lemma L_AX2BL_lin_nowrapB : @lin_nowrapB = @AX2B.lin_nowrapB.
Proof. unfold lin_nowrapB. rewrite ?L_AX2BL_erangeB, ?AX2L.L_AX2L_lin_of, ?AX2L.L_AX2L_lin_range, ?AX2L.L_AX2L_two64. reflexivity. Qed.

Fixpoint srl_expandB (bc : bctx) (ts : list (Z * expr)) : Z * list (Z * expr) :=
  match ts with
  | [] => (0%Z, [])
  | (k, a) :: rest =>
      let '(c, ts') := srl_expandB bc rest in
      let keep := (c, lins_e k a ts') in
      match a with
      | EAlu ALU_SRL e (ELit s) =>
          let m := (2 ^ ((CXLF.zm64 s) mod 64))%Z in
          if (Z.eqb (k mod m)%Z 0%Z && lin_nowrapB bc e)%bool then
            let q := (k / m)%Z in
            let le := lin_of e in
            if Z.leb ((CXLF.zm64 s) mod 64) (ealignB bc e) then   
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
                 lins_e (- k)%Z (srl_rem e (CXLF.zpow2 s)) (fold_right (fun t acc => lins_e (k * fst t)%Z (snd t) acc) ts' (snd le)))
              else keep
          | None => keep
          end
      | _ => keep
      end
  end.
Lemma L_AX2BL_srl_expandB : @srl_expandB = @AX2B.srl_expandB.
Proof. unfold srl_expandB. rewrite ?L_AX2BL_ealignB, ?L_AX2BL_lin_nowrapB, ?AX2L.L_AX2L_highmask_s, ?AX2L.L_AX2L_lin_of, ?AX2L.L_AX2L_lins_e, ?AX2L.L_AX2L_srl_rem, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition fact_nowrapB (bc : bctx) (e : expr) (hi : Z) : bool :=
  let l := lin_of e in
  match lin_range (erangeB bc) (fst l) (snd l) with
  | Some (a, b) => (Z.ltb b two64 && Z.ltb hi (a + two64))%bool
  | None => false
  end.
Lemma L_AX2BL_fact_nowrapB : @fact_nowrapB = @AX2B.fact_nowrapB.
Proof. unfold fact_nowrapB. rewrite ?L_AX2BL_erangeB, ?AX2L.L_AX2L_lin_of, ?AX2L.L_AX2L_lin_range, ?AX2L.L_AX2L_two64. reflexivity. Qed.

Definition sum_fact_xB (bc : bctx) (ts : list (Z * expr)) (lo hi : Z) : list sfact :=
  let '(c2, ts2) := srl_expandB bc ts in
  match ts2 with
  | _ :: _ => if Z.eqb c2 0 then [] else [(ts2, ((lo - c2)%Z, (hi - c2)%Z))]
  | [] => []
  end.
Lemma L_AX2BL_sum_fact_xB : @sum_fact_xB = @AX2B.sum_fact_xB.
Proof. unfold sum_fact_xB. rewrite ?L_AX2BL_srl_expandB, ?AX2L.L_AX2L_sfact. reflexivity. Qed.

Fixpoint pin_termsB (bc : bctx) (ts : list (Z * expr)) (lo hi : Z) : list (Z * expr) * (Z * Z) * bool :=
  match ts with
  | [] => ([], (lo, hi), false)
  | (k, a) :: r =>
      let '(r', lh, hit) := pin_termsB bc r lo hi in
      let '(lo', hi') := lh in
      match erangeB bc a with
      | Some (c, c') => if Z.eqb c c' then (r', ((lo' - k * c)%Z, (hi' - k * c)%Z), true) else ((k, a) :: r', (lo', hi'), hit)
      | None => ((k, a) :: r', (lo', hi'), hit)
      end
  end.
Lemma L_AX2BL_pin_termsB : @pin_termsB = @AX2B.pin_termsB.
Proof. unfold pin_termsB. rewrite ?L_AX2BL_erangeB. reflexivity. Qed.

Definition sum_fact_pinB (bc : bctx) (ts : list (Z * expr)) (lo hi : Z) : list sfact :=
  match pin_termsB bc ts lo hi with
  | ((_ :: _) as ts', lh, true) => [(ts', lh)]
  | _ => []
  end.
Lemma L_AX2BL_sum_fact_pinB : @sum_fact_pinB = @AX2B.sum_fact_pinB.
Proof. unfold sum_fact_pinB. rewrite ?L_AX2BL_pin_termsB, ?AX2L.L_AX2L_sfact. reflexivity. Qed.

Fixpoint sum_factsB (bc : bctx) (kn : list kentry) : list sfact :=
  match kn with
  | [] => []
  | KRange e lo hi :: rest =>
      match e with
      | EVar _ => sum_factsB bc rest
      | _ =>
        match lin_of e with
        | (c, (_ :: _ :: _) as ts) =>
            if fact_nowrapB bc e hi then
              let pins := sum_fact_pinB bc ts (lo - c)%Z (hi - c)%Z in
              (ts, ((lo - c)%Z, (hi - c)%Z)) :: sfact_reduce (ts, ((lo - c)%Z, (hi - c)%Z)) ++ sum_fact_xB bc ts (lo - c)%Z (hi - c)%Z
                                          ++ pins ++ List.flat_map sfact_reduce pins ++ sum_factsB bc rest
            else sum_factsB bc rest
        | _ => sum_factsB bc rest
        end
      end
  | _ :: rest => sum_factsB bc rest
  end.
Lemma L_AX2BL_sum_factsB : @sum_factsB = @AX2B.sum_factsB.
Proof. unfold sum_factsB. rewrite ?L_AX2BL_fact_nowrapB, ?L_AX2BL_sum_fact_xB, ?L_AX2BL_sum_fact_pinB, ?AX2L.L_AX2L_lin_of, ?AX2L.L_AX2L_sfact, ?AX2L.L_AX2L_sfact_reduce. reflexivity. Qed.

Definition mkbc (fk : list kentry) : bctx :=
  let ffk := facts_of fk in let ri := mk_ri ffk in let rt := mk_rt fk in
  BC fk ffk (sum_factsB (BC fk ffk [] ri rt) fk) ri rt.
Lemma L_AX2BL_mkbc : @mkbc = @AX2B.mkbc.
Proof. unfold mkbc. rewrite ?AX2L.L_AX2L_facts_of, ?L_AX2BL_mk_ri, ?L_AX2BL_mk_rt, ?L_AX2BL_sum_factsB. reflexivity. Qed.

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
Lemma L_AX2BL_lin_test_relB : @lin_test_relB = @AX2B.lin_test_relB.
Proof. unfold lin_test_relB. rewrite ?L_AX2BL_erangeB, ?AX2L.L_AX2L_lin_range, ?AX2L.L_AX2L_sum_subst. reflexivity. Qed.

Definition lin_testB (bc : bctx) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match lin_range (erangeB bc) c ts with
  | Some (lo, hi) => if test lo hi then true else lin_test_relB bc c ts test
  | None => lin_test_relB bc c ts test
  end.
Lemma L_AX2BL_lin_testB : @lin_testB = @AX2B.lin_testB.
Proof. unfold lin_testB. rewrite ?L_AX2BL_erangeB, ?L_AX2BL_lin_test_relB, ?AX2L.L_AX2L_lin_range. reflexivity. Qed.

Definition lin_srangeB (bc : bctx) (e : expr) : option (Z * Z) :=
  let l := lin_of e in
  let j := srl_scale_need (snd l) in
  if (if Z.leb 0 j then Z.leb j 24 else false) then   
    let sc := (CXLF.zpow2 j) in
    let ts := List.map (fun t => ((sc * fst t)%Z, snd t)) (snd l) in
    let '(c2, t2) := srl_expandB bc ts in
    let '(c3, t3) := (if has_round t2 then srl_expandB bc t2 else (0%Z, t2)) in
    match lin_range (erangeB bc) (sc * fst l + c2 + c3)%Z t3 with
    | Some (lo', hi') =>
        let lo := zcdiv lo' sc in let hi := (hi' / sc)%Z in
        if (if Z.leb 0 lo then (if Z.leb lo hi then Z.ltb hi two64 else false) else false) then Some (lo, hi) else None
    | None => None
    end
  else None.
Lemma L_AX2BL_lin_srangeB : @lin_srangeB = @AX2B.lin_srangeB.
Proof. unfold lin_srangeB. rewrite ?L_AX2BL_erangeB, ?L_AX2BL_srl_expandB, ?AX2L.L_AX2L_has_round, ?AX2L.L_AX2L_lin_of, ?AX2L.L_AX2L_lin_range, ?AX2L.L_AX2L_srl_scale_need, ?AX2L.L_AX2L_two64, ?AX2L.L_AX2L_zcdiv, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition lin_nowrapRB (bc : bctx) (e : expr) : bool :=
  let l := lin_of e in
  let '(c2, t2) := srl_expandB bc (snd l) in            
  if lin_testB bc (fst l + c2)%Z t2 (fun lo hi => (Z.leb 0 lo && Z.ltb hi two64)%bool) then true
  else 
    match lin_srangeB bc e with Some _ => true | None => false end.
Lemma L_AX2BL_lin_nowrapRB : @lin_nowrapRB = @AX2B.lin_nowrapRB.
Proof. unfold lin_nowrapRB. rewrite ?L_AX2BL_srl_expandB, ?L_AX2BL_lin_testB, ?L_AX2BL_lin_srangeB, ?AX2L.L_AX2L_lin_of, ?AX2L.L_AX2L_two64. reflexivity. Qed.

Definition lin_apart0B (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  (lin_nowrapRB bc b1 && lin_nowrapRB bc b2 &&
   let l1 := lin_of b1 in let l2 := lin_of b2 in
   lin_testB bc (fst l2 + k2 - fst l1 - k1)%Z (lsub_e (snd l2) (snd l1))
            (fun lo hi => (Z.leb n1 lo || Z.leb hi (- n2))%bool))%bool.
Lemma L_AX2BL_lin_apart0B : @lin_apart0B = @AX2B.lin_apart0B.
Proof. unfold lin_apart0B. rewrite ?L_AX2BL_lin_testB, ?L_AX2BL_lin_nowrapRB, ?AX2L.L_AX2L_lin_of, ?AX2L.L_AX2L_lsub_e. reflexivity. Qed.

Definition lin_apart0BF (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  let l1 := lin_of b1 in let l2 := lin_of b2 in
  if lin_testB bc (fst l2 + k2 - fst l1 - k1)%Z (lsub_e (snd l2) (snd l1)) (fun lo hi => (Z.leb n1 lo || Z.leb hi (- n2))%bool)
  then (if lin_nowrapRB bc b1 then lin_nowrapRB bc b2 else false) else false.
Lemma L_AX2BL_lin_apart0BF : @lin_apart0BF = @AX2B.lin_apart0BF.
Proof. unfold lin_apart0BF. rewrite ?L_AX2BL_lin_testB, ?L_AX2BL_lin_nowrapRB, ?AX2L.L_AX2L_lin_of, ?AX2L.L_AX2L_lsub_e. reflexivity. Qed.

Definition lin_apartB (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if shares_var b1 b2 then lin_apart0BF bc b1 k1 n1 b2 k2 n2 else false.
Lemma L_AX2BL_lin_apartB : @lin_apartB = @AX2B.lin_apartB.
Proof. unfold lin_apartB. rewrite ?L_AX2BL_lin_apart0BF, ?AX2L.L_AX2L_shares_var. reflexivity. Qed.

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
Lemma L_AX2BL_lin_brangeB : @lin_brangeB = @AX2B.lin_brangeB.
Proof. unfold lin_brangeB. rewrite ?L_AX2BL_erangeB, ?AX2L.L_AX2L_lin_of, ?AX2L.L_AX2L_lin_range, ?AX2L.L_AX2L_sum_subst, ?AX2L.L_AX2L_two64. reflexivity. Qed.

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
Lemma L_AX2BL_xloB : @xloB = @AX2B.xloB.
Proof. unfold xloB. rewrite ?L_AX2BL_erangeB, ?L_AX2BL_lin_srangeB, ?L_AX2BL_lin_brangeB, ?AX2L.L_AX2L_zlit64. reflexivity. Qed.

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
Lemma L_AX2BL_xhiB : @xhiB = @AX2B.xhiB.
Proof. unfold xhiB. rewrite ?L_AX2BL_erangeB, ?L_AX2BL_lin_srangeB, ?L_AX2BL_lin_brangeB, ?AX2L.L_AX2L_zlit64. reflexivity. Qed.

Fixpoint xt_nowrapB (bc : bctx) (ts : xterms) : bool :=
  match ts with [] => true | (e, _) :: r => lin_nowrapRB bc e && xt_nowrapB bc r end.
Lemma L_AX2BL_xt_nowrapB : @xt_nowrapB = @AX2B.xt_nowrapB.
Proof. unfold xt_nowrapB. rewrite ?L_AX2BL_lin_nowrapRB, ?AX2L.L_AX2L_xterms. reflexivity. Qed.

Definition lin_ge0_scaledB (bc : bctx) (c : Z) (ts : list (Z * expr)) : bool :=
  let j := srl_scale_need ts in
  if (if Z.ltb 0 j then Z.leb j 24 else false) then
    let sc := (CXLF.zpow2 j) in
    let ts' := List.map (fun t => ((sc * fst t)%Z, snd t)) ts in
    let '(c2, t2) := srl_expandB bc ts' in
    let '(c3, t3) := (if has_round t2 then srl_expandB bc t2 else (0%Z, t2)) in
    lin_testB bc (sc * c + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
  else false.
Lemma L_AX2BL_lin_ge0_scaledB : @lin_ge0_scaledB = @AX2B.lin_ge0_scaledB.
Proof. unfold lin_ge0_scaledB. rewrite ?L_AX2BL_srl_expandB, ?L_AX2BL_lin_testB, ?AX2L.L_AX2L_has_round, ?AX2L.L_AX2L_srl_scale_need, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition lin_test_rB (bc : bctx) (r : option (Z * Z)) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match r with
  | Some (lo, hi) => if test lo hi then true else lin_test_relB bc c ts test
  | None => lin_test_relB bc c ts test
  end.
Lemma L_AX2BL_lin_test_rB : @lin_test_rB = @AX2B.lin_test_rB.
Proof. unfold lin_test_rB. rewrite ?L_AX2BL_lin_test_relB. reflexivity. Qed.

Definition lin_ge0_coreB (bc : bctx) (pos neg : xterms) : bool :=
  if negb (xt_nowrapB bc pos) then false else if negb (xt_nowrapB bc neg) then false else
  let r0 := lin_range (erangeB bc) (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) in
  if lin_hopeless r0 then false else
   
   (if lin_test_rB bc r0 (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) (fun lo _ => Z.leb 0 lo) then true
    else let '(c2, t2) := srl_expandB bc (lsub_e (xt_lin pos) (xt_lin neg)) in
         if lin_testB bc (xt_const pos - xt_const neg + c2)%Z t2 (fun lo _ => Z.leb 0 lo) then true
         else 
         if (if has_round t2 then
               let '(c3, t3) := srl_expandB bc t2 in
               lin_testB bc (xt_const pos - xt_const neg + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
             else false) then true
         else 
         if lin_ge0_scaledB bc (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) then true
         else 
           (has_round t2 && lin_ge0_scaledB bc (xt_const pos - xt_const neg + c2)%Z t2))%bool.
Lemma L_AX2BL_lin_ge0_coreB : @lin_ge0_coreB = @AX2B.lin_ge0_coreB.
Proof. unfold lin_ge0_coreB. rewrite ?L_AX2BL_erangeB, ?L_AX2BL_srl_expandB, ?L_AX2BL_lin_testB, ?L_AX2BL_xt_nowrapB, ?L_AX2BL_lin_ge0_scaledB, ?L_AX2BL_lin_test_rB, ?AX2L.L_AX2L_has_round, ?AX2L.L_AX2L_lin_hopeless, ?AX2L.L_AX2L_lin_range, ?AX2L.L_AX2L_lsub_e, ?AX2L.L_AX2L_xt_const, ?AX2L.L_AX2L_xt_lin, ?AX2L.L_AX2L_xterms. reflexivity. Qed.

Fixpoint terms_alignB (bc : bctx) (ts : list (Z * expr)) : Z :=
  match ts with
  | [] => 64%Z
  | (k, a) :: rest => Z.min (Z.min (ctz64 (Z.abs k) + ealignB bc a) 64)%Z (terms_alignB bc rest)
  end.
Lemma L_AX2BL_terms_alignB : @terms_alignB = @AX2B.terms_alignB.
Proof. unfold terms_alignB. rewrite ?L_AX2BL_ealignB, ?AX2L.L_AX2L_ctz64. reflexivity. Qed.

Definition form_alignB (bc : bctx) (c : Z) (ts : list (Z * expr)) : Z :=
  Z.max 0 (Z.min (if Z.eqb c 0 then 64%Z else ctz64 (Z.abs c)) (terms_alignB bc ts)).
Lemma L_AX2BL_form_alignB : @form_alignB = @AX2B.form_alignB.
Proof. unfold form_alignB. rewrite ?L_AX2BL_terms_alignB, ?AX2L.L_AX2L_ctz64. reflexivity. Qed.

Definition lin_ge0B (bc : bctx) (pos neg : xterms) : bool :=
  if lin_ge0_coreB bc pos neg then true
  else
    let ts := lsub_e (xt_lin pos) (xt_lin neg) in
    if (has_round ts && xt_nowrapB bc pos && xt_nowrapB bc neg)%bool then
      let j := Z.min (form_alignB bc (xt_const pos - xt_const neg)%Z ts) 16 in
      if Z.ltb 0 j then lin_ge0_coreB bc ((ELit 0, (2 ^ j - 1)%Z) :: pos) neg else false
    else false.
Lemma L_AX2BL_lin_ge0B : @lin_ge0B = @AX2B.lin_ge0B.
Proof. unfold lin_ge0B. rewrite ?L_AX2BL_xt_nowrapB, ?L_AX2BL_lin_ge0_coreB, ?L_AX2BL_form_alignB, ?AX2L.L_AX2L_has_round, ?AX2L.L_AX2L_lsub_e, ?AX2L.L_AX2L_xt_const, ?AX2L.L_AX2L_xt_lin, ?AX2L.L_AX2L_xterms. reflexivity. Qed.

Definition lin_ge0_coreBX (bc : bctx) (np nn : bool) (pos neg : xterms) : bool :=
  let r0 := lin_range (erangeB bc) (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) in
  if lin_hopeless r0 then false else
  if negb np then false else if negb nn then false else
   (if lin_test_rB bc r0 (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) (fun lo _ => Z.leb 0 lo) then true
    else let '(c2, t2) := srl_expandB bc (lsub_e (xt_lin pos) (xt_lin neg)) in
         if lin_testB bc (xt_const pos - xt_const neg + c2)%Z t2 (fun lo _ => Z.leb 0 lo) then true
         else
         if (if has_round t2 then
               let '(c3, t3) := srl_expandB bc t2 in
               lin_testB bc (xt_const pos - xt_const neg + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
             else false) then true
         else
         if lin_ge0_scaledB bc (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) then true
         else (has_round t2 && lin_ge0_scaledB bc (xt_const pos - xt_const neg + c2)%Z t2))%bool.
Lemma L_AX2BL_lin_ge0_coreBX : @lin_ge0_coreBX = @AX2B.lin_ge0_coreBX.
Proof. unfold lin_ge0_coreBX. rewrite ?L_AX2BL_erangeB, ?L_AX2BL_srl_expandB, ?L_AX2BL_lin_testB, ?L_AX2BL_lin_ge0_scaledB, ?L_AX2BL_lin_test_rB, ?AX2L.L_AX2L_has_round, ?AX2L.L_AX2L_lin_hopeless, ?AX2L.L_AX2L_lin_range, ?AX2L.L_AX2L_lsub_e, ?AX2L.L_AX2L_xt_const, ?AX2L.L_AX2L_xt_lin, ?AX2L.L_AX2L_xterms. reflexivity. Qed.

Definition lin_ge0BF (bc : bctx) (pos neg : xterms) : bool :=
  let ts := lsub_e (xt_lin pos) (xt_lin neg) in
  let hop := lin_hopeless (lin_range (erangeB bc) (xt_const pos - xt_const neg)%Z ts) in
  let hr := has_round ts in
  if (if hop then negb hr else false) then false
  else
    let np := xt_nowrapB bc pos in
    let nn := xt_nowrapB bc neg in
    if (if hop then false else lin_ge0_coreBX bc np nn pos neg) then true
    else if hr then if np then if nn then
           let j := Z.min (form_alignB bc (xt_const pos - xt_const neg)%Z ts) 16 in
           if Z.ltb 0 j then lin_ge0_coreBX bc (lin_nowrapRB bc (ELit 0%Z) && np)%bool nn ((ELit 0%Z, (2 ^ j - 1)%Z) :: pos) neg else false
         else false else false else false.
Lemma L_AX2BL_lin_ge0BF : @lin_ge0BF = @AX2B.lin_ge0BF.
Proof. unfold lin_ge0BF. rewrite ?L_AX2BL_erangeB, ?L_AX2BL_lin_nowrapRB, ?L_AX2BL_xt_nowrapB, ?L_AX2BL_form_alignB, ?L_AX2BL_lin_ge0_coreBX, ?AX2L.L_AX2L_has_round, ?AX2L.L_AX2L_lin_hopeless, ?AX2L.L_AX2L_lin_range, ?AX2L.L_AX2L_lsub_e, ?AX2L.L_AX2L_xt_const, ?AX2L.L_AX2L_xt_lin, ?AX2L.L_AX2L_xterms. reflexivity. Qed.

Definition xinside0B (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if lin_ge0BF bc [(b1, k1)] [(b2, k2)] then lin_ge0BF bc [(b2, k2); (n2, 0%Z)] [(b1, k1); (n1, 0%Z)] else false.
Lemma L_AX2BL_xinside0B : @xinside0B = @AX2B.xinside0B.
Proof. unfold xinside0B. rewrite ?L_AX2BL_lin_ge0BF. reflexivity. Qed.

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
Lemma L_AX2BL_xinside_numB : @xinside_numB = @AX2B.xinside_numB.
Proof. unfold xinside_numB. rewrite ?L_AX2BL_base_rangeB, ?L_AX2BL_xloB, ?L_AX2BL_xhiB. reflexivity. Qed.

Definition end_hiB (bc : bctx) (b : expr) (k : Z) (n : expr) (lo1 hi1 h1 : Z) : option Z :=
  match n with
  | ELit _ => None
  | _ => if (if Z.leb 0 (lo1 + k) then Z.ltb (hi1 + k + h1) two64 else false)
         then match lsum3 b k n with
              | ELit z => Some (CXLF.zm64 z)%Z
              | e => match find_rangeI (bc_ri bc) e with
                     | Some (_, ehi) => Some ehi
                     | None => None
                     end
              end
         else None
  end.
Lemma L_AX2BL_end_hiB : @end_hiB = @AX2B.end_hiB.
Proof. unfold end_hiB. rewrite ?L_AX2BL_find_rangeI, ?AX2L.L_AX2L_lsum3, ?AX2L.L_AX2L_two64, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition xinside_jtB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match xloB bc b2, xhiB bc b2 with
  | Some lo2, Some hi2 =>
      if Z.eqb lo2 hi2 then
        match base_rangeB bc b1, xhiB bc n1, xloB bc n2 with
        | Some (lo1, hi1), Some h1, Some l2 =>
            if Z.leb (lo2 + k2) (lo1 + k1)
            then match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some eh => Z.leb eh (lo2 + k2 + l2) | None => false end
            else false
        | _, _, _ => false
        end
      else false
  | _, _ => false
  end.
Lemma L_AX2BL_xinside_jtB : @xinside_jtB = @AX2B.xinside_jtB.
Proof. unfold xinside_jtB. rewrite ?L_AX2BL_base_rangeB, ?L_AX2BL_xloB, ?L_AX2BL_xhiB, ?L_AX2BL_end_hiB. reflexivity. Qed.

Definition xinsideB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if shares_var b1 b2 then xinside0B bc b1 k1 n1 b2 k2 n2
  else if novars b2 then (if xinside_numB bc b1 k1 n1 b2 k2 n2 then true else xinside_jtB bc b1 k1 n1 b2 k2 n2) else false.
Lemma L_AX2BL_xinsideB : @xinsideB = @AX2B.xinsideB.
Proof. unfold xinsideB. rewrite ?L_AX2BL_xinside0B, ?L_AX2BL_xinside_numB, ?L_AX2BL_xinside_jtB, ?AX2L.L_AX2L_novars, ?AX2L.L_AX2L_shares_var. reflexivity. Qed.

Definition is_lit0 (e : expr) : bool := match e with ELit 0 => true | _ => false end.
Lemma L_AX2BL_is_lit0 : @is_lit0 = @AX2B.is_lit0.
Proof. unfold is_lit0. reflexivity. Qed.

Definition mkqp (bc : bctx) (b1 : expr) (n1 : expr) : qprep :=
  QP (base_rangeB bc b1) (xloB bc (ELit 0%Z)) (xhiB bc (ELit 0%Z)) (xhiB bc n1).
Lemma L_AX2BL_mkqp : @mkqp = @AX2B.mkqp.
Proof. unfold mkqp. rewrite ?L_AX2BL_base_rangeB, ?L_AX2BL_xloB, ?L_AX2BL_xhiB. reflexivity. Qed.

Definition xinside_numBQ (bc : bctx) (qp : qprep) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match (if is_lit0 b2 then qp_z0lo qp else xloB bc b2), (if is_lit0 b2 then qp_z0hi qp else xhiB bc b2) with
  | Some lo2, Some hi2 =>
      if Z.eqb lo2 hi2 then
        match qp_r qp, qp_h1 qp, xloB bc n2 with
        | Some (lo1, hi1), Some h1, Some l2 => Z.leb (lo2 + k2) (lo1 + k1) && Z.leb (hi1 + k1 + h1) (lo2 + k2 + l2)
        | _, _, _ => false
        end
      else false
  | _, _ => false
  end.
Lemma L_AX2BL_xinside_numBQ : @xinside_numBQ = @AX2B.xinside_numBQ.
Proof. unfold xinside_numBQ. rewrite ?L_AX2BL_xloB, ?L_AX2BL_xhiB, ?L_AX2BL_is_lit0. reflexivity. Qed.

Definition xinside_jtBQ (bc : bctx) (qp : qprep) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match (if is_lit0 b2 then qp_z0lo qp else xloB bc b2), (if is_lit0 b2 then qp_z0hi qp else xhiB bc b2) with
  | Some lo2, Some hi2 =>
      if Z.eqb lo2 hi2 then
        match qp_r qp, qp_h1 qp, xloB bc n2 with
        | Some (lo1, hi1), Some h1, Some l2 =>
            if Z.leb (lo2 + k2) (lo1 + k1)
            then match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some eh => Z.leb eh (lo2 + k2 + l2) | None => false end
            else false
        | _, _, _ => false
        end
      else false
  | _, _ => false
  end.
Lemma L_AX2BL_xinside_jtBQ : @xinside_jtBQ = @AX2B.xinside_jtBQ.
Proof. unfold xinside_jtBQ. rewrite ?L_AX2BL_xloB, ?L_AX2BL_xhiB, ?L_AX2BL_end_hiB, ?L_AX2BL_is_lit0. reflexivity. Qed.

Definition xinsideBQ (bc : bctx) (qp : qprep) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if shares_var b1 b2 then xinside0B bc b1 k1 n1 b2 k2 n2
  else if novars b2 then (if xinside_numBQ bc qp b1 k1 n1 b2 k2 n2 then true else xinside_jtBQ bc qp b1 k1 n1 b2 k2 n2) else false.
Lemma L_AX2BL_xinsideBQ : @xinsideBQ = @AX2B.xinsideBQ.
Proof. unfold xinsideBQ. rewrite ?L_AX2BL_xinside0B, ?L_AX2BL_xinside_numBQ, ?L_AX2BL_xinside_jtBQ, ?AX2L.L_AX2L_novars, ?AX2L.L_AX2L_shares_var. reflexivity. Qed.

Definition sub_itvB (bc : bctx) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
  if (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
        match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
      else false)
  then true
  else 
    if (Z.leb 0 n && Z.ltb n two64)%bool then xinsideB bc b k (ELit n) (a_base c) (a_off c) m else false.
Lemma L_AX2BL_sub_itvB : @sub_itvB = @AX2B.sub_itvB.
Proof. unfold sub_itvB. rewrite ?L_AX2BL_xloB, ?L_AX2BL_xinsideB, ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_two64. reflexivity. Qed.

Fixpoint kdisj_apartB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itvB bc b1 k1 n1 c1 m1 then sub_itvB bc b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itvB bc b1 k1 n1 c2 m2 then sub_itvB bc b2 k2 n2 c1 m1 else false) then true
      else kdisj_apartB bc rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apartB bc rest b1 k1 n1 b2 k2 n2
  end.
Lemma L_AX2BL_kdisj_apartB : @kdisj_apartB = @AX2B.kdisj_apartB.
Proof. unfold kdisj_apartB. rewrite ?L_AX2BL_sub_itvB. reflexivity. Qed.

Definition ranges_apartB (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match base_rangeB bc b1, base_rangeB bc b2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
      | _, _ => false
      end) then true
  else if kdisj_apartB bc (bc_fk bc) b1 k1 n1 b2 k2 n2 then true
  else lin_apartB bc b1 k1 n1 b2 k2 n2.
Lemma L_AX2BL_ranges_apartB : @ranges_apartB = @AX2B.ranges_apartB.
Proof. unfold ranges_apartB. rewrite ?L_AX2BL_base_rangeB, ?L_AX2BL_lin_apartB, ?L_AX2BL_kdisj_apartB. reflexivity. Qed.

Definition regs (bc : bctx) (b : expr) (k n : Z) : list positive :=
  List.map fst (List.filter (fun t : positive * (saddr * expr) => sub_itvB bc b k n (fst (snd t)) (snd (snd t))) (rt_sides (bc_rt bc))).
Lemma L_AX2BL_regs : @regs = @AX2B.regs.
Proof. unfold regs. rewrite ?L_AX2BL_sub_itvB. reflexivity. Qed.

Definition kdisj_apartR (bc : bctx) (RQ RS : list positive) : bool :=
  existsb (fun i => existsb (fun j => existsb (Pos.eqb j) RS) (rt_partners (bc_rt bc) i)) RQ.
Lemma L_AX2BL_kdisj_apartR : @kdisj_apartR = @AX2B.kdisj_apartR.
Proof. unfold kdisj_apartR. rewrite ?L_AX2BL_rt_partners. reflexivity. Qed.

Definition ranges_apartQ (bc : bctx) (r1 : option (Z * Z)) (RQ : list positive)
           (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match r1, base_rangeB bc b2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
      | _, _ => false
      end) then true
  else if kdisj_apartR bc RQ (regs bc b2 k2 n2) then true
  else lin_apartB bc b1 k1 n1 b2 k2 n2.
Lemma L_AX2BL_ranges_apartQ : @ranges_apartQ = @AX2B.ranges_apartQ.
Proof. unfold ranges_apartQ. rewrite ?L_AX2BL_base_rangeB, ?L_AX2BL_lin_apartB, ?L_AX2BL_regs, ?L_AX2BL_kdisj_apartR. reflexivity. Qed.

Definition rt_In (rt : rtab) (i : positive) (c : saddr) (m : expr) : Prop := In (i, (c, m)) (rt_sides rt).
Lemma L_AX2BL_rt_In : @rt_In = @AX2B.rt_In.
Proof. unfold rt_In. reflexivity. Qed.

Fixpoint dfacts_of (fk : list kentry) : list ((saddr * expr) * (saddr * expr)) :=
  match fk with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest => ((c1, m1), (c2, m2)) :: dfacts_of rest
  | _ :: rest => dfacts_of rest
  end.
Lemma L_AX2BL_dfacts_of : @dfacts_of = @AX2B.dfacts_of.
Proof. unfold dfacts_of. reflexivity. Qed.

Definition sub_itv_xB (bc : bctx) (b : expr) (k : Z) (n : expr) (c : saddr) (m : expr) : bool :=
  match n with
  | ELit z => sub_itvB bc b k (zlit64 z) c m
  | _ => xinsideB bc b k n (a_base c) (a_off c) m
  end.
Lemma L_AX2BL_sub_itv_xB : @sub_itv_xB = @AX2B.sub_itv_xB.
Proof. unfold sub_itv_xB. rewrite ?L_AX2BL_xinsideB, ?L_AX2BL_sub_itvB, ?AX2L.L_AX2L_zlit64. reflexivity. Qed.

Fixpoint kdisj_apart_xB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itv_xB bc b1 k1 n1 c1 m1 then sub_itv_xB bc b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itv_xB bc b1 k1 n1 c2 m2 then sub_itv_xB bc b2 k2 n2 c1 m1 else false) then true
      else kdisj_apart_xB bc rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apart_xB bc rest b1 k1 n1 b2 k2 n2
  end.
Lemma L_AX2BL_kdisj_apart_xB : @kdisj_apart_xB = @AX2B.kdisj_apart_xB.
Proof. unfold kdisj_apart_xB. rewrite ?L_AX2BL_sub_itv_xB. reflexivity. Qed.

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
    else if kdisj_apart_xB bc (bc_fk bc) b1 k1 n1 b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0BF bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0BF bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.
Lemma L_AX2BL_ranges_apart_xB : @ranges_apart_xB = @AX2B.ranges_apart_xB.
Proof. unfold ranges_apart_xB. rewrite ?L_AX2BL_base_rangeB, ?L_AX2BL_xhiB, ?L_AX2BL_lin_ge0BF, ?L_AX2BL_end_hiB, ?L_AX2BL_ranges_apartB, ?L_AX2BL_kdisj_apart_xB, ?AX2L.L_AX2L_shares_var, ?AX2L.L_AX2L_zlit64. reflexivity. Qed.

Fixpoint disj_sidesB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sidesB bc rest b1 k1 n1 in
      let r1 := if sub_itvB bc b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itvB bc b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sidesB bc rest b1 k1 n1
  end.
Lemma L_AX2BL_disj_sidesB : @disj_sidesB = @AX2B.disj_sidesB.
Proof. unfold disj_sidesB. rewrite ?L_AX2BL_sub_itvB. reflexivity. Qed.

Fixpoint disj_sides_xB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sides_xB bc rest b1 k1 n1 in
      let r1 := if sub_itv_xB bc b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itv_xB bc b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sides_xB bc rest b1 k1 n1
  end.
Lemma L_AX2BL_disj_sides_xB : @disj_sides_xB = @AX2B.disj_sides_xB.
Proof. unfold disj_sides_xB. rewrite ?L_AX2BL_sub_itv_xB. reflexivity. Qed.

Fixpoint in_sidesB (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itvB bc b2 k2 n2 c m then true else in_sidesB bc r b2 k2 n2
  end.
Lemma L_AX2BL_in_sidesB : @in_sidesB = @AX2B.in_sidesB.
Proof. unfold in_sidesB. rewrite ?L_AX2BL_sub_itvB. reflexivity. Qed.

Fixpoint in_sides_xB (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv_xB bc b2 k2 n2 c m then true else in_sides_xB bc r b2 k2 n2
  end.
Lemma L_AX2BL_in_sides_xB : @in_sides_xB = @AX2B.in_sides_xB.
Proof. unfold in_sides_xB. rewrite ?L_AX2BL_sub_itv_xB. reflexivity. Qed.

Definition dmemo : Type := ptree (list (saddr * expr * bool)).
Lemma L_AX2BL_dmemo : @dmemo = @AX2B.dmemo.
Proof. unfold dmemo. reflexivity. Qed.

Definition dside_key (c : saddr) (l : expr) : positive :=
  let o := a_off c in
  let z := match l with ELit z => z | _ => 0%Z end in
  Z.to_pos (1 + (if Z.leb 0 o then 2 * o else 1 - 2 * o) + 4 * Z.abs z)%Z.
Lemma L_AX2BL_dside_key : @dside_key = @AX2B.dside_key.
Proof. unfold dside_key. reflexivity. Qed.

Fixpoint dmemo_getl (m : list (saddr * expr * bool)) (c : saddr) (l : expr) : option bool :=
  match m with
  | [] => None
  | (c', l', b) :: r => if (if saddr_eqb c c' then expr_eqb l l' else false) then Some b else dmemo_getl r c l
  end.
Lemma L_AX2BL_dmemo_getl : @dmemo_getl = @AX2B.dmemo_getl.
Proof. unfold dmemo_getl. rewrite ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_saddr_eqb. reflexivity. Qed.

Definition dmemo_bucket (m : dmemo) (p : positive) : list (saddr * expr * bool) :=
  match pt_get m p with Some l => l | None => [] end.
Lemma L_AX2BL_dmemo_bucket : @dmemo_bucket = @AX2B.dmemo_bucket.
Proof. unfold dmemo_bucket. rewrite ?L_AX2BL_dmemo, ?AX2L.L_AX2L_pt_get. reflexivity. Qed.

Definition dmemo_get (m : dmemo) (c : saddr) (l : expr) : option bool := dmemo_getl (dmemo_bucket m (dside_key c l)) c l.
Lemma L_AX2BL_dmemo_get : @dmemo_get = @AX2B.dmemo_get.
Proof. unfold dmemo_get. rewrite ?L_AX2BL_dmemo, ?L_AX2BL_dside_key, ?L_AX2BL_dmemo_getl, ?L_AX2BL_dmemo_bucket. reflexivity. Qed.

Definition dmemo_add (m : dmemo) (c : saddr) (l : expr) (b : bool) : dmemo :=
  let p := dside_key c l in pt_set p ((c, l, b) :: dmemo_bucket m p) m.
Lemma L_AX2BL_dmemo_add : @dmemo_add = @AX2B.dmemo_add.
Proof. unfold dmemo_add. rewrite ?L_AX2BL_dmemo, ?L_AX2BL_dside_key, ?L_AX2BL_dmemo_bucket, ?AX2L.L_AX2L_pt_set. reflexivity. Qed.

Definition sub_itvBM (bc : bctx) (b1 : expr) (k1 n1 : Z) (c : saddr) (l : expr) (m : dmemo) : bool * dmemo :=
  match dmemo_get m c l with
  | Some b => (b, m)
  | None => let b := sub_itvB bc b1 k1 n1 c l in (b, dmemo_add m c l b)
  end.
Lemma L_AX2BL_sub_itvBM : @sub_itvBM = @AX2B.sub_itvBM.
Proof. unfold sub_itvBM. rewrite ?L_AX2BL_sub_itvB, ?L_AX2BL_dmemo, ?L_AX2BL_dmemo_get, ?L_AX2BL_dmemo_add. reflexivity. Qed.

Fixpoint disj_sidesBM (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) (m : dmemo) : list (saddr * expr) * dmemo :=
  match kn with
  | [] => ([], m)
  | KDisj c1 m1 c2 m2 :: rest =>
      let '(r, mm) := disj_sidesBM bc rest b1 k1 n1 m in
      let '(t2, mm1) := sub_itvBM bc b1 k1 n1 c2 m2 mm in
      let r1 := if t2 then (c1, m1) :: r else r in
      let '(t1, mm2) := sub_itvBM bc b1 k1 n1 c1 m1 mm1 in
      ((if t1 then (c2, m2) :: r1 else r1), mm2)
  | _ :: rest => disj_sidesBM bc rest b1 k1 n1 m
  end.
Lemma L_AX2BL_disj_sidesBM : @disj_sidesBM = @AX2B.disj_sidesBM.
Proof. unfold disj_sidesBM. rewrite ?L_AX2BL_dmemo, ?L_AX2BL_sub_itvBM. reflexivity. Qed.

Definition sub_itv_xBM (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (c : saddr) (l : expr) (m : dmemo) : bool * dmemo :=
  match dmemo_get m c l with
  | Some b => (b, m)
  | None => let b := sub_itv_xB bc b1 k1 n1 c l in (b, dmemo_add m c l b)
  end.
Lemma L_AX2BL_sub_itv_xBM : @sub_itv_xBM = @AX2B.sub_itv_xBM.
Proof. unfold sub_itv_xBM. rewrite ?L_AX2BL_sub_itv_xB, ?L_AX2BL_dmemo, ?L_AX2BL_dmemo_get, ?L_AX2BL_dmemo_add. reflexivity. Qed.

Fixpoint disj_sides_xBM (bc : bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (m : dmemo) : list (saddr * expr) * dmemo :=
  match kn with
  | [] => ([], m)
  | KDisj c1 m1 c2 m2 :: rest =>
      let '(r, mm) := disj_sides_xBM bc rest b1 k1 n1 m in
      let '(t2, mm1) := sub_itv_xBM bc b1 k1 n1 c2 m2 mm in
      let r1 := if t2 then (c1, m1) :: r else r in
      let '(t1, mm2) := sub_itv_xBM bc b1 k1 n1 c1 m1 mm1 in
      ((if t1 then (c2, m2) :: r1 else r1), mm2)
  | _ :: rest => disj_sides_xBM bc rest b1 k1 n1 m
  end.
Lemma L_AX2BL_disj_sides_xBM : @disj_sides_xBM = @AX2B.disj_sides_xBM.
Proof. unfold disj_sides_xBM. rewrite ?L_AX2BL_dmemo, ?L_AX2BL_sub_itv_xBM. reflexivity. Qed.

Section DMemo.
Variable f : saddr -> expr -> bool.
Definition dmemo_ok (m : dmemo) : Prop := forall p c l b, In (c, l, b) (dmemo_bucket m p) -> f c l = b.
End DMemo.
Lemma L_AX2BL_dmemo_ok : @dmemo_ok = @AX2B.dmemo_ok.
Proof. unfold dmemo_ok. rewrite ?L_AX2BL_dmemo, ?L_AX2BL_dmemo_bucket. reflexivity. Qed.

Definition mk_sprepB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) : sprep :=
  match n1 with
  | ELit z1 => let D := fst (disj_sidesBM bc (bc_fk bc) b1 k1 (zlit64 z1) PTLeaf) in
               SPrep (base_rangeB bc b1) (xhiB bc n1) D D      
  | _ => SPrep (base_rangeB bc b1) (xhiB bc n1) [] (fst (disj_sides_xBM bc (bc_fk bc) b1 k1 n1 PTLeaf))
  end.
Lemma L_AX2BL_mk_sprepB : @mk_sprepB = @AX2B.mk_sprepB.
Proof. unfold mk_sprepB. rewrite ?L_AX2BL_base_rangeB, ?L_AX2BL_xhiB, ?L_AX2BL_disj_sidesBM, ?L_AX2BL_disj_sides_xBM, ?AX2L.L_AX2L_zlit64. reflexivity. Qed.

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
            else 
            if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_xB bc (sp_Dx sp) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0BF bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0BF bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.
Lemma L_AX2BL_ranges_apart_pB : @ranges_apart_pB = @AX2B.ranges_apart_pB.
Proof. unfold ranges_apart_pB. rewrite ?L_AX2BL_base_rangeB, ?L_AX2BL_lin_apartB, ?L_AX2BL_xhiB, ?L_AX2BL_lin_ge0BF, ?L_AX2BL_end_hiB, ?L_AX2BL_in_sidesB, ?L_AX2BL_in_sides_xB, ?AX2L.L_AX2L_shares_var, ?AX2L.L_AX2L_zlit64. reflexivity. Qed.

Definition ranges_apart_pBF (bc : bctx) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
           (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, base_rangeB bc b2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then true
      else if shares_var b1 b2 then (if lin_apart0BF bc b1 k1 m1 b2 k2 m2 then true else in_sidesB bc (sp_D sp) b2 k2 m2)
      else in_sidesB bc (sp_D sp) b2 k2 m2
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
    else if negb (shares_var b1 b2) then false
    else if lin_ge0BF bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0BF bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.
Lemma L_AX2BL_ranges_apart_pBF : @ranges_apart_pBF = @AX2B.ranges_apart_pBF.
Proof. unfold ranges_apart_pBF. rewrite ?L_AX2BL_base_rangeB, ?L_AX2BL_lin_apart0BF, ?L_AX2BL_xhiB, ?L_AX2BL_lin_ge0BF, ?L_AX2BL_end_hiB, ?L_AX2BL_in_sidesB, ?L_AX2BL_in_sides_xB, ?AX2L.L_AX2L_shares_var, ?AX2L.L_AX2L_zlit64. reflexivity. Qed.

Fixpoint coeffs_divkB (bc : bctx) (m : Z) (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => true
  | (k, a) :: rest => ((Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealignB bc a) mod m) 0) && coeffs_divkB bc m rest)%bool
  end.
Lemma L_AX2BL_coeffs_divkB : @coeffs_divkB = @AX2B.coeffs_divkB.
Proof. unfold coeffs_divkB. rewrite ?L_AX2BL_ealignB. reflexivity. Qed.

Definition lin_lowbits_knB (bc : bctx) (e : expr) (k : Z) : option Z :=
  let l := lin_of e in
  if coeffs_divkB bc (CXLF.zpow2 k) (snd l) then Some ((fst l) mod 2 ^ k)%Z
  else pageup_low e (CXLF.zpow2 k).
Lemma L_AX2BL_lin_lowbits_knB : @lin_lowbits_knB = @AX2B.lin_lowbits_knB.
Proof. unfold lin_lowbits_knB. rewrite ?L_AX2BL_coeffs_divkB, ?AX2L.L_AX2L_lin_of, ?AX2L.L_AX2L_pageup_low, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition lin_nowrap_lB (bc : bctx) (c : Z) (ts : list (Z * expr)) : bool :=
  match lin_range (erangeB bc) c ts with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%bool
  | None => false
  end.
Lemma L_AX2BL_lin_nowrap_lB : @lin_nowrap_lB = @AX2B.lin_nowrap_lB.
Proof. unfold lin_nowrap_lB. rewrite ?L_AX2BL_erangeB, ?AX2L.L_AX2L_lin_range, ?AX2L.L_AX2L_two64. reflexivity. Qed.

Definition mkSrlB (bc : bctx) (a : expr) (s : Z) : expr :=
  let l := lin_of a in
  let m := (CXLF.zpow2 s) in
  if (negb (lin_trivial l) && coeffs_div m (snd l) && lin_nowrapB bc a)%bool
  then unlin ((fst l / m)%Z, ldiv_terms m (snd l))     
  else
    
    match (if (negb (lin_trivial l) && lin_nowrapB bc a)%bool then lsplit_divc m (snd l) else ([], [])) with
    | ((_ :: _) as dts, (_ :: _) as rts) =>
        match (if lin_nowrap_lB bc (fst l) rts then erangeB bc (unlin (fst l, rts)) else None) with
        | Some (lo, hi) =>
            if Z.eqb (lo / m) (hi / m) then unlin ((lo / m)%Z, ldiv_terms m dts)
            else if Z.leb (hi / m - lo / m) srl_split_span
            then unlin (ladd (0%Z, ldiv_terms m dts) (0%Z, [(1%Z, EAlu ALU_SRL (unlin (fst l, rts)) (ELit s))]))
            else mkAlu ALU_SRL a (ELit s)
        | None => mkAlu ALU_SRL a (ELit s)
        end
    | _ => mkAlu ALU_SRL a (ELit s)
    end.
Lemma L_AX2BL_mkSrlB : @mkSrlB = @AX2B.mkSrlB.
Proof. unfold mkSrlB. rewrite ?L_AX2BL_erangeB, ?L_AX2BL_lin_nowrapB, ?L_AX2BL_lin_nowrap_lB, ?AX2L.L_AX2L_coeffs_div, ?AX2L.L_AX2L_ladd, ?AX2L.L_AX2L_ldiv_terms, ?AX2L.L_AX2L_lin_of, ?AX2L.L_AX2L_lin_trivial, ?AX2L.L_AX2L_lsplit_divc, ?AX2L.L_AX2L_mkAlu, ?AX2L.L_AX2L_srl_split_span, ?AX2L.L_AX2L_unlin, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Fixpoint lowbitsB (bc : bctx) (e : expr) (j : Z) {struct e} : option Z :=
  let m := (CXLF.zpow2 j) in
  let dflt := if Z.leb j (ealignB bc e) then Some 0%Z else lin_lowbits_knB bc e j in
  match e with
  | ELit z => Some ((CXLF.zm64 z) mod m)%Z
  | EAlu ALU_AND a (ELit c) =>
      if Z.eqb ((CXLF.zm64 c) mod m) 0 then Some 0%Z else
      match lowbitsB bc a j with Some v => Some (Z.land v ((CXLF.zm64 c) mod m)) | None => dflt end
  | EAlu ALU_OR a (ELit c) =>
      match lowbitsB bc a j with Some v => Some (Z.lor v ((CXLF.zm64 c) mod m)) | None => dflt end
  | EAlu ALU_XOR a (ELit c) =>
      match lowbitsB bc a j with Some v => Some (Z.lxor v ((CXLF.zm64 c) mod m)) | None => dflt end
  | EAlu ALU_ADD a b =>
      match lowbitsB bc a j, lowbitsB bc b j with Some x, Some y => Some ((x + y) mod m)%Z | _, _ => dflt end
  | EAlu ALU_SUB a b =>
      match lowbitsB bc a j, lowbitsB bc b j with Some x, Some y => Some ((x - y) mod m)%Z | _, _ => dflt end
  | EMd M_MUL (ELit c) a =>
      if Z.eqb ((CXLF.zm64 c) mod m) 0 then Some 0%Z else
      match lowbitsB bc a j with Some v => Some ((c * v) mod m)%Z | None => dflt end
  | _ => dflt
  end.
Lemma L_AX2BL_lowbitsB : @lowbitsB = @AX2B.lowbitsB.
Proof. unfold lowbitsB. rewrite ?L_AX2BL_ealignB, ?L_AX2BL_lin_lowbits_knB, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Fixpoint lsplit_divB (bc : bctx) (m : Z) (ts : list (Z * expr)) : list (Z * expr) * list (Z * expr) :=
  match ts with
  | [] => ([], [])
  | (k, a) :: rest =>
      let (d, r) := lsplit_divB bc m rest in
      if (Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealignB bc a) mod m) 0)%bool then ((k, a) :: d, r) else (d, (k, a) :: r)
  end.
Lemma L_AX2BL_lsplit_divB : @lsplit_divB = @AX2B.lsplit_divB.
Proof. unfold lsplit_divB. rewrite ?L_AX2BL_ealignB. reflexivity. Qed.

Definition and_high_splitB (bc : bctx) (bk : expr) (j c : Z) (dts rts : list (Z * expr)) : expr :=
  let m := (CXLF.zpow2 j) in
  let cA := (c - c mod m)%Z in
  let r := unlin ((c mod m)%Z, rts) in
  match erangeB bc r with
  | Some (lo, hi) =>
      if Z.eqb (lo / m) (hi / m) then unlin ((cA + (lo / m) * m)%Z, dts)
      else mkAlu ALU_ADD (unlin (cA, dts)) (mkAlu ALU_AND r bk)
  | None => mkAlu ALU_ADD (unlin (cA, dts)) (mkAlu ALU_AND r bk)
  end.
Lemma L_AX2BL_and_high_splitB : @and_high_splitB = @AX2B.and_high_splitB.
Proof. unfold and_high_splitB. rewrite ?L_AX2BL_erangeB, ?AX2L.L_AX2L_mkAlu, ?AX2L.L_AX2L_unlin, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition and_low_splitB (bc : bctx) (bk : expr) (j c : Z) (rts : list (Z * expr)) : expr :=
  let m := (CXLF.zpow2 j) in
  let r := unlin ((c mod m)%Z, rts) in
  match erangeB bc r with
  | Some (lo, hi) =>
      if Z.eqb (lo / m) (hi / m) then unlin ((c mod m - (lo / m) * m)%Z, rts)
      else mkAlu ALU_AND r bk
  | None => mkAlu ALU_AND r bk
  end.
Lemma L_AX2BL_and_low_splitB : @and_low_splitB = @AX2B.and_low_splitB.
Proof. unfold and_low_splitB. rewrite ?L_AX2BL_erangeB, ?AX2L.L_AX2L_mkAlu, ?AX2L.L_AX2L_unlin, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition narrow_maskB (bc : bctx) (a : expr) (k' : Z) : option Z :=
  let i := ctz64 k' in
  let m := (k' + 2 ^ i)%Z in
  let j := Z.log2 m in
  if (Z.ltb 0 k' && Z.eqb m (CXLF.zpow2 j) && Z.ltb j 64)%bool then
    match xhiB bc a with
    | Some h => if Z.ltb h (CXLF.zpow2 j) then Some (two64 - 2 ^ i)%Z else None
    | None => None
    end
  else None.
Lemma L_AX2BL_narrow_maskB : @narrow_maskB = @AX2B.narrow_maskB.
Proof. unfold narrow_maskB. rewrite ?L_AX2BL_xhiB, ?AX2L.L_AX2L_ctz64, ?AX2L.L_AX2L_two64, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition mkAnd0B (bc : bctx) (a b : expr) : expr :=
  match b with
  | ELit k =>
      let k' := (CXLF.zm64 k)%Z in
      let j := Z.log2 (two64 - k') in
      if (Z.eqb (two64 - k') (CXLF.zpow2 j) && Z.ltb j 64)%bool then
        
        (if Z.leb j (ealignB bc a) then a
         else let l := lin_of a in
              if (negb (lin_trivial l) && coeffs_divkB bc (CXLF.zpow2 j) (snd l))%bool
              then unlin ((fst l - (fst l) mod 2 ^ j)%Z, snd l)
              else 
                match (if lin_trivial l then ([], snd l) else lsplit_divB bc (CXLF.zpow2 j) (snd l)) with
                | ((_ :: _) as dts, (_ :: _) as rts) => and_high_splitB bc b j (fst l) dts rts
                | _ => 
                       mkMd M_MUL (ELit (CXLF.zpow2 j)) (mkSrlB bc a j)
                end)
      else
        let j2 := Z.log2 (k' + 1) in
        if (Z.eqb (k' + 1) (CXLF.zpow2 j2) && Z.ltb j2 64)%bool then
          
          (if Z.leb j2 (ealignB bc a) then ELit 0
           else match lowbitsB bc a j2 with        
           | Some v => ELit v
           | None =>
           if lin_trivial (lin_of a) then mkAlu ALU_AND a b
           else match lin_lowbits_knB bc a j2 with
                | Some v => ELit v
                | None => 
                    match lsplit_divB bc (CXLF.zpow2 j2) (snd (lin_of a)) with
                    | (_ :: _, (_ :: _) as rts) => and_low_splitB bc b j2 (fst (lin_of a)) rts
                    | _ => mkAlu ALU_AND a b
                    end
                end
           end)
        else 
          let j3 := (Z.log2 k' + 1)%Z in
          if (Z.ltb 0 k' && Z.leb j3 64 && negb (lin_trivial (lin_of a)))%bool then
            match lin_lowbits_knB bc a j3 with
            | Some v => ELit (Z.land v k')
            | None => mkAlu ALU_AND a b
            end
          else mkAlu ALU_AND a b
  | _ => mkAlu ALU_AND a b
  end.
Lemma L_AX2BL_mkAnd0B : @mkAnd0B = @AX2B.mkAnd0B.
Proof. unfold mkAnd0B. rewrite ?L_AX2BL_ealignB, ?L_AX2BL_coeffs_divkB, ?L_AX2BL_lin_lowbits_knB, ?L_AX2BL_mkSrlB, ?L_AX2BL_lowbitsB, ?L_AX2BL_lsplit_divB, ?L_AX2BL_and_high_splitB, ?L_AX2BL_and_low_splitB, ?AX2L.L_AX2L_lin_of, ?AX2L.L_AX2L_lin_trivial, ?AX2L.L_AX2L_mkAlu, ?AX2L.L_AX2L_mkMd, ?AX2L.L_AX2L_two64, ?AX2L.L_AX2L_unlin, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition mkAndB (bc : bctx) (a b : expr) : expr :=
  match b with
  | ELit k =>
      match narrow_maskB bc a (CXLF.zm64 k)%Z with
      | Some m => mkAnd0B bc a (ELit m)
      | None => mkAnd0B bc a b
      end
  | _ => mkAnd0B bc a b
  end.
Lemma L_AX2BL_mkAndB : @mkAndB = @AX2B.mkAndB.
Proof. unfold mkAndB. rewrite ?L_AX2BL_narrow_maskB, ?L_AX2BL_mkAnd0B, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition mkAndKB (bc : bctx) (a b : expr) : expr :=
  match a, b with
  | EAlu ALU_AND x (ELit m1), ELit k => mkAndB bc x (ELit (Z.land (CXLF.zm64 m1) (CXLF.zm64 k))%Z)
  | EMd M_MUL (ELit m) (EAlu ALU_SRL x (ELit i)), ELit k =>
      
      let i' := ((CXLF.zm64 i) mod 64)%Z in
      if Z.eqb (CXLF.zm64 m) (CXLF.zpow2 i') then mkAndB bc x (ELit (Z.land (two64 - 2 ^ i') (CXLF.zm64 k))%Z)
      else mkAndB bc a b
  | _, _ => mkAndB bc a b
  end.
Lemma L_AX2BL_mkAndKB : @mkAndKB = @AX2B.mkAndKB.
Proof. unfold mkAndKB. rewrite ?L_AX2BL_mkAndB, ?AX2L.L_AX2L_two64, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition or_disjointB (bc : bctx) (a b : expr) : bool :=
  match erangeB bc b with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi (2 ^ (ealignB bc a)))%bool
  | None => false
  end.
Lemma L_AX2BL_or_disjointB : @or_disjointB = @AX2B.or_disjointB.
Proof. unfold or_disjointB. rewrite ?L_AX2BL_erangeB, ?L_AX2BL_ealignB. reflexivity. Qed.

Definition mkOrB (bc : bctx) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (zalu ALU_OR x y)
  | _, _ =>
      if or_disjointB bc a b then mkAlu ALU_ADD a b
      else if or_disjointB bc b a then mkAlu ALU_ADD a b
      else 
           match b with
           | ELit c => mkAlu ALU_ADD (mkAndKB bc a (ELit (Z.lnot (CXLF.zm64 c)))) (ELit c)
           | _ => match a with
                  | ELit c => mkAlu ALU_ADD (mkAndKB bc b (ELit (Z.lnot (CXLF.zm64 c)))) (ELit c)
                  | _ => EAlu ALU_OR a b
                  end
           end
  end.
Lemma L_AX2BL_mkOrB : @mkOrB = @AX2B.mkOrB.
Proof. unfold mkOrB. rewrite ?L_AX2BL_mkAndKB, ?L_AX2BL_or_disjointB, ?AX2L.L_AX2L_is_lit, ?AX2L.L_AX2L_mkAlu, ?AX2L.L_AX2L_zalu, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

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
Lemma L_AX2BL_conc_tryB : @conc_tryB = @AX2B.conc_tryB.
Proof. unfold conc_tryB. rewrite ?L_AX2BL_erangeB, ?AX2L.L_AX2L_all_eval_toS, ?AX2L.L_AX2L_closedb, ?AX2L.L_AX2L_conc_limit, ?AX2L.L_AX2L_evalS, ?AX2L.L_AX2L_evalS_def, ?AX2L.L_AX2L_probeS, ?AX2L.L_AX2L_wrap64. reflexivity. Qed.

Definition concretizeB (bc : bctx) (e : expr) : option Z :=
  if closedb e then eval_closed e else conc_tryB bc e (nubE (subexprs e)).
Lemma L_AX2BL_concretizeB : @concretizeB = @AX2B.concretizeB.
Proof. unfold concretizeB. rewrite ?L_AX2BL_conc_tryB, ?AX2L.L_AX2L_closedb, ?AX2L.L_AX2L_eval_closed, ?AX2L.L_AX2L_nubE, ?AX2L.L_AX2L_subexprs. reflexivity. Qed.

Definition foldKB (bc : bctx) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match erangeB bc e with
         | Some (lo, hi) => if Z.eqb lo hi then ELit lo
                            else match concretizeB bc e with Some v => ELit v | None => e end
         | None => match concretizeB bc e with Some v => ELit v | None => e end   
         end
  end.
Lemma L_AX2BL_foldKB : @foldKB = @AX2B.foldKB.
Proof. unfold foldKB. rewrite ?L_AX2BL_erangeB, ?L_AX2BL_concretizeB. reflexivity. Qed.

Definition lowbits_widthB (bc : bctx) (e : expr) : Z :=
  Z.max (lin_ctz (snd (lin_of e))) (ealignB bc e).
Lemma L_AX2BL_lowbits_widthB : @lowbits_widthB = @AX2B.lowbits_widthB.
Proof. unfold lowbits_widthB. rewrite ?L_AX2BL_ealignB, ?AX2L.L_AX2L_lin_ctz, ?AX2L.L_AX2L_lin_of. reflexivity. Qed.

Definition lowbits_neqB (bc : bctx) (a b : expr) : bool :=
  let j := Z.min (Z.min (lowbits_widthB bc a) (lowbits_widthB bc b)) 64 in
  if Z.ltb 0 j then
    match lowbitsB bc a j, lowbitsB bc b j with
    | Some x, Some y => negb (Z.eqb x y)
    | _, _ => false
    end
  else false.
Lemma L_AX2BL_lowbits_neqB : @lowbits_neqB = @AX2B.lowbits_neqB.
Proof. unfold lowbits_neqB. rewrite ?L_AX2BL_lowbitsB, ?L_AX2BL_lowbits_widthB. reflexivity. Qed.

Definition lowbits_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
  match c with
  | BC_EQ => if lowbits_neqB bc a b then Some false else None
  | BC_NE => if lowbits_neqB bc a b then Some true else None
  | _ => None
  end.
Lemma L_AX2BL_lowbits_branchB : @lowbits_branchB = @AX2B.lowbits_branchB.
Proof. unfold lowbits_branchB. rewrite ?L_AX2BL_lowbits_neqB. reflexivity. Qed.

Definition lin_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
  let ltu := if lin_ge0BF bc [(b, (-1)%Z)] [(a, 0%Z)] then Some true
             else if lin_ge0BF bc [(a, 0%Z)] [(b, 0%Z)] then Some false else None in
  match c with
  | BC_LTU => ltu
  | BC_GEU => option_map negb ltu
  | BC_LT | BC_GE =>
      match erangeB bc a, erangeB bc b with
      | Some (_, ah), Some (_, bh) =>
          if (Z.ltb ah (CXLF.p63) && Z.ltb bh (CXLF.p63))%bool
          then match c with BC_LT => ltu | _ => option_map negb ltu end
          else None
      | _, _ => None
      end
  | BC_EQ | BC_NE =>
      
      if (lin_ge0BF bc [(b, (-1)%Z)] [(a, 0%Z)] || lin_ge0BF bc [(a, (-1)%Z)] [(b, 0%Z)])%bool
      then Some (match c with BC_EQ => false | _ => true end)
      else
      
      if (if lin_ge0BF bc [(a, 0%Z)] [(b, 0%Z)] then lin_ge0BF bc [(b, 0%Z)] [(a, 0%Z)] else false)
      then Some (match c with BC_EQ => true | _ => false end)
      else None
  end.
Lemma L_AX2BL_lin_branchB : @lin_branchB = @AX2B.lin_branchB.
Proof. unfold lin_branchB. rewrite ?L_AX2BL_erangeB, ?L_AX2BL_lin_ge0BF, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

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
             | None => match lowbits_branchB bc c a b with   
                       | Some t => Some t
                       | None => lin_branchB bc c a b      
                       end
             end
           end
  end.
Lemma L_AX2BL_decide_branchB : @decide_branchB = @AX2B.decide_branchB.
Proof. unfold decide_branchB. rewrite ?L_AX2BL_erangeB, ?L_AX2BL_lowbits_branchB, ?L_AX2BL_lin_branchB, ?AX2L.L_AX2L_cond_on_eq, ?AX2L.L_AX2L_diff_branch, ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_lit_branch, ?AX2L.L_AX2L_range_branch. reflexivity. Qed.

Definition mkSltB (bc : bctx) (c : branch_cond) (op : aluop) (a b : expr) : expr :=
  match a, b with
  | ELit _, ELit _ => mkAlu op a b
  | _, _ => match decide_branchB bc c a b with
            | Some true => ELit 1
            | Some false => ELit 0
            | None => mkAlu op a b
            end
  end.
Lemma L_AX2BL_mkSltB : @mkSltB = @AX2B.mkSltB.
Proof. unfold mkSltB. rewrite ?L_AX2BL_decide_branchB, ?AX2L.L_AX2L_mkAlu. reflexivity. Qed.

Definition mkAluK0B (bc : bctx) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_SLTU => mkSltB bc BC_LTU ALU_SLTU a b
  | ALU_SLT => mkSltB bc BC_LT ALU_SLT a b
  | ALU_AND => match a, b with
               | ELit _, ELit _ => mkAndB bc a b
               | ELit _, _ => mkAndKB bc b a      
               | _, _ => mkAndKB bc a b
               end
  | ALU_OR => if expr_eqb a b then a else mkOrB bc a b
  | ALU_XOR => if expr_eqb a b then ELit 0 else match is_lit a, b with
               | None, ELit k => if Z.eqb (CXLF.zm64 k) (two64 - 1) then mkAlu ALU_SUB (ELit (two64 - 1)) a
                                else mkAlu op a b
               | _, _ => mkAlu op a b
               end
  | ALU_SRL => match is_lit a, shamt_of b 6 with
               | None, Some s => mkSrlB bc a s
               | _, _ => mkAlu op a b
               end
  | _ => mkAlu op a b
  end.
Lemma L_AX2BL_mkAluK0B : @mkAluK0B = @AX2B.mkAluK0B.
Proof. unfold mkAluK0B. rewrite ?L_AX2BL_mkSrlB, ?L_AX2BL_mkAndB, ?L_AX2BL_mkAndKB, ?L_AX2BL_mkOrB, ?L_AX2BL_mkSltB, ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_is_lit, ?AX2L.L_AX2L_mkAlu, ?AX2L.L_AX2L_shamt_of, ?AX2L.L_AX2L_two64, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition mkAluKB (bc : bctx) (op : aluop) (a b : expr) : expr :=
  foldKB bc (mkAluK0B bc op a b).
Lemma L_AX2BL_mkAluKB : @mkAluKB = @AX2B.mkAluKB.
Proof. unfold mkAluKB. rewrite ?L_AX2BL_foldKB, ?L_AX2BL_mkAluK0B. reflexivity. Qed.

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
Lemma L_AX2BL_mkMdKB : @mkMdKB = @AX2B.mkMdKB.
Proof. unfold mkMdKB. rewrite ?L_AX2BL_mkAluKB, ?AX2L.L_AX2L_is_lit, ?AX2L.L_AX2L_mkMd, ?AX2L.L_AX2L_pow2_log. reflexivity. Qed.

Definition zband32B (bc : bctx) (d : expr) : bool :=
  let l := lin_of d in
  match lin_range (erangeB bc) (fst l) (snd l) with
  | Some (lo, hi) => (Z.ltb (- CXLF.p31) lo && Z.ltb hi (CXLF.p31))%bool
  | None => false
  end.
Lemma L_AX2BL_zband32B : @zband32B = @AX2B.zband32B.
Proof. unfold zband32B. rewrite ?L_AX2BL_erangeB, ?AX2L.L_AX2L_lin_of, ?AX2L.L_AX2L_lin_range, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

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
Lemma L_AX2BL_mkAluwK0B : @mkAluwK0B = @AX2B.mkAluwK0B.
Proof. unfold mkAluwK0B. rewrite ?L_AX2BL_erangeB, ?L_AX2BL_zband32B, ?AX2L.L_AX2L_is_lit, ?AX2L.L_AX2L_mkAlu, ?AX2L.L_AX2L_mkAluw, ?AX2L.L_AX2L_sx32_stable, ?AX2L.L_AX2L_zsx32. reflexivity. Qed.

Definition mkAluwKB (bc : bctx) (op : aluop) (a b : expr) : expr :=
  foldKB bc (mkAluwK0B bc op a b).
Lemma L_AX2BL_mkAluwKB : @mkAluwKB = @AX2B.mkAluwKB.
Proof. unfold mkAluwKB. rewrite ?L_AX2BL_foldKB, ?L_AX2BL_mkAluwK0B. reflexivity. Qed.

Definition extK0B (bc : bctx) (v : expr) : expr :=
  match v with
  | EExt sx O n e =>
      if CXNAT.lebF n 7 then
        match erangeB bc e with
        | Some (lo, hi) => if Z.ltb hi (if sx then 2 ^ (8 * Z.of_nat n) / 2 else 2 ^ (8 * Z.of_nat n)) then e else v
        | None => v
        end
      else v
  | _ => v
  end.
Lemma L_AX2BL_extK0B : @extK0B = @AX2B.extK0B.
Proof. unfold extK0B. rewrite ?L_AX2BL_erangeB, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition extKB (bc : bctx) (v : expr) : expr := foldKB bc (extK0B bc v).
Lemma L_AX2BL_extKB : @extKB = @AX2B.extKB.
Proof. unfold extKB. rewrite ?L_AX2BL_foldKB, ?L_AX2BL_extK0B. reflexivity. Qed.

Definition flat_scB (bc : bctx) (a : saddr) (n : nat) : list sidecond :=
  match base_rangeB bc (a_base a) with
  | Some (lo, hi) =>
      if (Z.leb 0 (lo + a_off a) && Z.leb (hi + a_off a + Z.of_nat n) (CXLF.p64))%bool
      then [] else [SCFlat a (elen n)]
  | None => [SCFlat a (elen n)]
  end.
Lemma L_AX2BL_flat_scB : @flat_scB = @AX2B.flat_scB.
Proof. unfold flat_scB. rewrite ?L_AX2BL_base_rangeB, ?AX2L.L_AX2L_elen, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

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
Lemma L_AX2BL_wr_coveredB : @wr_coveredB = @AX2B.wr_coveredB.
Proof. unfold wr_coveredB. rewrite ?L_AX2BL_xloB, ?L_AX2BL_xinsideB, ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Fixpoint wr_cheap (bc : bctx) (kn : list kentry) (a : saddr) (n : nat) : bool :=
  match kn with
  | [] => false
  | KWr (SA kb kk) len :: rest =>
      if (if Z.leb kk (a_off a)
          then if expr_eqb (a_base a) kb
               then match xloB bc len with Some l => Z.leb (a_off a + Z.of_nat n) (kk + l) | None => false end
               else false
          else false)
      then true
      else wr_cheap bc rest a n
  | _ :: rest => wr_cheap bc rest a n
  end.
Lemma L_AX2BL_wr_cheap : @wr_cheap = @CXFS.wr_cheap.
Proof. unfold wr_cheap. rewrite ?L_AX2BL_xloB, ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Definition storeok_scF (bc : bctx) (a : saddr) (n : nat) : list sidecond :=
  if wr_cheap bc (bc_fk bc) a n then [] else if wr_coveredB bc (bc_fk bc) a n then [] else [SCStoreOk a n].
Lemma L_AX2BL_storeok_scF : @storeok_scF = @CXFS.storeok_scF.
Proof. unfold storeok_scF. rewrite ?L_AX2BL_wr_coveredB, ?L_AX2BL_wr_cheap. reflexivity. Qed.

Definition storeok_scB := storeok_scF.
Lemma L_AX2BL_storeok_scB : @storeok_scB = @AX2B.storeok_scB.
Proof. unfold storeok_scB. rewrite L_AX2BL_storeok_scF. exact CXFS.storeok_scF_eqf. Qed.

Definition conc_exprB (bc : bctx) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match concretizeB bc e with Some v => ELit v | None => e end
  end.
Lemma L_AX2BL_conc_exprB : @conc_exprB = @AX2B.conc_exprB.
Proof. unfold conc_exprB. rewrite ?L_AX2BL_concretizeB. reflexivity. Qed.

Definition enum_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
  let '(e, pos) := cond_probe c a b in
  match concretizeB bc e with
  | Some v => let z := Z.eqb (CXLF.zm64 v) 0 in Some (if pos then negb z else z)
  | None => None
  end.
Lemma L_AX2BL_enum_branchB : @enum_branchB = @AX2B.enum_branchB.
Proof. unfold enum_branchB. rewrite ?L_AX2BL_concretizeB, ?AX2L.L_AX2L_cond_probe, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition to_saddrKB (bc : bctx) (e : expr) (imm : Z) : saddr :=
  match split_lit e with
  | (ELit _, _) => to_saddr e imm
  | _ => match concretizeB bc (mkAlu ALU_ADD e (ELit imm)) with
         | Some v => SA (ELit 0) v
         | None => to_saddr e imm
         end
  end.
Lemma L_AX2BL_to_saddrKB : @to_saddrKB = @AX2B.to_saddrKB.
Proof. unfold to_saddrKB. rewrite ?L_AX2BL_concretizeB, ?AX2L.L_AX2L_mkAlu, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_to_saddr. reflexivity. Qed.

Definition amo_alignedbB (bc : bctx) (e : expr) (wd : awidth) : bool :=
  match lin_lowbits_knB bc e (match wd with AW => 2 | AD => 3 end) with
  | Some r => Z.eqb r 0
  | None => false
  end.
Lemma L_AX2BL_amo_alignedbB : @amo_alignedbB = @AX2B.amo_alignedbB.
Proof. unfold amo_alignedbB. rewrite ?L_AX2BL_lin_lowbits_knB. reflexivity. Qed.

Definition amo_newvalB (bc : bctx) (wd : awidth) (aop : option aluop) (old src : expr) : expr :=
  match aop with
  | None => src
  | Some o => match wd with AW => mkAluwKB bc o old src | AD => mkAluKB bc o old src end
  end.
Lemma L_AX2BL_amo_newvalB : @amo_newvalB = @AX2B.amo_newvalB.
Proof. unfold amo_newvalB. rewrite ?L_AX2BL_mkAluKB, ?L_AX2BL_mkAluwKB. reflexivity. Qed.

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
Lemma L_AX2BL_log_lookupB : @log_lookupB = @AX2B.log_lookupB.
Proof. unfold log_lookupB. rewrite ?L_AX2BL_ranges_apartB, ?AX2L.L_AX2L_elen, ?AX2L.L_AX2L_lit_of_bytes, ?AX2L.L_AX2L_log_bytes_lit, ?AX2L.L_AX2L_mkExt, ?AX2L.L_AX2L_rel_lit. reflexivity. Qed.

Fixpoint log_lookupQ (bc : bctx) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) (q : option (option (Z * Z) * list positive)) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupQ bc rest rb rk n sx hints acc q
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          let q' := match q with Some x => x | None => (base_rangeB bc rb, regs bc rb rk (Z.of_nat n)) end in
          if ranges_apartQ bc (fst q') (snd q') rb rk (Z.of_nat n) kb kk (Z.of_nat w)
          then log_lookupQ bc rest rb rk n sx hints acc (Some q')
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupQ bc rest rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc) (Some q')
          end
      end
  end.
Lemma L_AX2BL_log_lookupQ : @log_lookupQ = @AX2B.log_lookupQ.
Proof. unfold log_lookupQ. rewrite ?L_AX2BL_base_rangeB, ?L_AX2BL_regs, ?L_AX2BL_ranges_apartQ, ?AX2L.L_AX2L_elen, ?AX2L.L_AX2L_lit_of_bytes, ?AX2L.L_AX2L_log_bytes_lit, ?AX2L.L_AX2L_mkExt, ?AX2L.L_AX2L_rel_lit. reflexivity. Qed.

Definition regsE (bc : bctx) (e : sentry) : list positive :=
  match e with SE (SA kb kk) w _ => regs bc kb kk (Z.of_nat w) end.
Lemma L_AX2BL_regsE : @regsE = @AX2B.regsE.
Proof. unfold regsE. rewrite ?L_AX2BL_regs. reflexivity. Qed.

Definition ranges_apartQR (bc : bctx) (r1 : option (Z * Z)) (RQ RS : list positive)
           (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match r1, base_rangeB bc b2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
      | _, _ => false
      end) then true
  else if kdisj_apartR bc RQ RS then true
  else lin_apartB bc b1 k1 n1 b2 k2 n2.
Lemma L_AX2BL_ranges_apartQR : @ranges_apartQR = @AX2B.ranges_apartQR.
Proof. unfold ranges_apartQR. rewrite ?L_AX2BL_base_rangeB, ?L_AX2BL_lin_apartB, ?L_AX2BL_kdisj_apartR. reflexivity. Qed.

Fixpoint log_lookupQL (bc : bctx) (log : list sentry) (lrs : list (list positive)) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) (q : option (option (Z * Z) * list positive)) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      let lrs' := match lrs with _ :: t => t | [] => [] end in
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupQL bc rest lrs' rb rk n sx hints acc q
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          let q' := match q with Some x => x | None => (base_rangeB bc rb, regs bc rb rk (Z.of_nat n)) end in
          let rs := match lrs with r :: _ => r | [] => regs bc kb kk (Z.of_nat w) end in
          if ranges_apartQR bc (fst q') (snd q') rs rb rk (Z.of_nat n) kb kk (Z.of_nat w)
          then log_lookupQL bc rest lrs' rb rk n sx hints acc (Some q')
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupQL bc rest lrs' rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc) (Some q')
          end
      end
  end.
Lemma L_AX2BL_log_lookupQL : @log_lookupQL = @AX2B.log_lookupQL.
Proof. unfold log_lookupQL. rewrite ?L_AX2BL_base_rangeB, ?L_AX2BL_regs, ?L_AX2BL_ranges_apartQR, ?AX2L.L_AX2L_elen, ?AX2L.L_AX2L_lit_of_bytes, ?AX2L.L_AX2L_log_bytes_lit, ?AX2L.L_AX2L_mkExt, ?AX2L.L_AX2L_rel_lit. reflexivity. Qed.

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
              match rel_lit rb rk (Z.of_nat n) kb kk (CXLF.zm64 l0)%Z with
              | RInside _ => LHit (ELit 0) acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  
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
          
          let hit := fill_lit sx n c in
          match len with
          | ELit l0 =>
              match rel_lit rb rk (Z.of_nat n) kb kk (CXLF.zm64 l0)%Z with
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
      | KUnk _ _ => know_lookup segs rest rb rk n sx hints acc   
      | KBlob (SA kb kk) len k =>
          if expr_eqb rb kb then
            
            if Z.leb kk rk then
              match len with
              | ELit l0 =>
                  if Z.leb (rk + Z.of_nat n) (kk + (CXLF.zm64 l0)%Z)
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else if Z.leb (kk + (CXLF.zm64 l0)%Z) rk then know_lookup segs rest rb rk n sx hints acc
                  else LStuck
              | _ =>
                  
                  if match erangeB bc len with   
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
Lemma L_AX2BL_know_lookupA0B : @know_lookupA0B = @AX2B.know_lookupA0B.
Proof. unfold know_lookupA0B. rewrite ?L_AX2BL_erangeB, ?L_AX2BL_xinsideB, ?AX2L.L_AX2L_elen, ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_fill_lit, ?AX2L.L_AX2L_img_bytes, ?AX2L.L_AX2L_know_lookup, ?AX2L.L_AX2L_lit_of_bytes, ?AX2L.L_AX2L_mkExt, ?AX2L.L_AX2L_rel_lit, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition qfast (qp : qprep) (hints : list bool) (rb kb len : expr) : option (Z * Z * Z * Z) :=
  match hints, kb, len, qp_r qp, qp_h1 qp with
  | [], ELit Z0, ELit l0, Some (lo1, hi1), Some h1 => if is_lit0 rb then None else Some (lo1, hi1, h1, zlit64 l0)
  | _, _, _, _, _ => None
  end.
Lemma L_AX2BL_qfast : @qfast = @AX2B.qfast.
Proof. unfold qfast. rewrite ?L_AX2BL_is_lit0, ?AX2L.L_AX2L_zlit64. reflexivity. Qed.

Fixpoint know_lookupA0BQ (bc : bctx) (qp : qprep) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  let know_lookup := know_lookupA0BQ bc qp in
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
          
          match qfast qp hints rb kb len with
          | Some (lo1, hi1, h1, l2) =>
              if (Z.leb kk (lo1 + rk) && Z.leb (hi1 + rk + h1) (kk + l2))%bool then LHit (ELit 0) acc hints
              else know_lookup segs rest rb rk n sx hints acc
          | None =>
          match len with
          | ELit l0 =>
              match rel_lit rb rk (Z.of_nat n) kb kk (CXLF.zm64 l0)%Z with
              | RInside _ => LHit (ELit 0) acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  
                  if xinsideBQ bc qp rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
                  match hints with
                  | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinsideBQ bc qp rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
              match hints with
              | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | [] => know_lookup segs rest rb rk n sx [] acc
              end
          end
          end
      | KFill (SA kb kk) len c =>
          
          let hit := fill_lit sx n c in
          match qfast qp hints rb kb len with
          | Some (lo1, hi1, h1, l2) =>
              if (Z.leb kk (lo1 + rk) && Z.leb (hi1 + rk + h1) (kk + l2))%bool then LHit hit acc hints
              else know_lookup segs rest rb rk n sx hints acc
          | None =>
          match len with
          | ELit l0 =>
              match rel_lit rb rk (Z.of_nat n) kb kk (CXLF.zm64 l0)%Z with
              | RInside _ => LHit hit acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  if xinsideBQ bc qp rb rk (elen n) kb kk len then LHit hit acc hints else
                  match hints with
                  | true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinsideBQ bc qp rb rk (elen n) kb kk len then LHit hit acc hints else
              match hints with
              | true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | [] => know_lookup segs rest rb rk n sx [] acc
              end
          end
          end
      | KUnk _ _ => know_lookup segs rest rb rk n sx hints acc   
      | KBlob (SA kb kk) len k =>
          if expr_eqb rb kb then
            
            if Z.leb kk rk then
              match len with
              | ELit l0 =>
                  if Z.leb (rk + Z.of_nat n) (kk + (CXLF.zm64 l0)%Z)
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else if Z.leb (kk + (CXLF.zm64 l0)%Z) rk then know_lookup segs rest rb rk n sx hints acc
                  else LStuck
              | _ =>
                  
                  if match erangeB bc len with   
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
Lemma L_AX2BL_know_lookupA0BQ : @know_lookupA0BQ = @AX2B.know_lookupA0BQ.
Proof. unfold know_lookupA0BQ. rewrite ?L_AX2BL_erangeB, ?L_AX2BL_xinsideBQ, ?L_AX2BL_qfast, ?AX2L.L_AX2L_elen, ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_fill_lit, ?AX2L.L_AX2L_img_bytes, ?AX2L.L_AX2L_know_lookup, ?AX2L.L_AX2L_lit_of_bytes, ?AX2L.L_AX2L_mkExt, ?AX2L.L_AX2L_rel_lit, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

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
Lemma L_AX2BL_know_lookupAB : @know_lookupAB = @AX2B.know_lookupAB.
Proof. unfold know_lookupAB. rewrite ?L_AX2BL_know_lookupA0B, ?AX2L.L_AX2L_know_bytes_lit, ?AX2L.L_AX2L_lit_of_bytes. reflexivity. Qed.

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
          
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
      end
  end.
Lemma L_AX2BL_sym_readB : @sym_readB = @AX2B.sym_readB.
Proof. unfold sym_readB. rewrite ?L_AX2BL_extKB, ?L_AX2BL_flat_scB, ?L_AX2BL_log_lookupB, ?L_AX2BL_know_lookupAB. reflexivity. Qed.

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
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod CXLF.p64)) [] scr
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
            else SStop   
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
Lemma L_AX2BL_sym_stepB : @sym_stepB = @AX2B.sym_stepB.
Proof. unfold sym_stepB. rewrite ?L_AX2BL_decide_branchB, ?L_AX2BL_mkAluKB, ?L_AX2BL_mkMdKB, ?L_AX2BL_mkAluwKB, ?L_AX2BL_flat_scB, ?L_AX2BL_storeok_scB, ?L_AX2BL_conc_exprB, ?L_AX2BL_enum_branchB, ?L_AX2BL_to_saddrKB, ?L_AX2BL_amo_alignedbB, ?L_AX2BL_amo_newvalB, ?L_AX2BL_sym_readB, ?AX2L.L_AX2L_amo_aluop, ?AX2L.L_AX2L_amo_sx, ?AX2L.L_AX2L_amo_sz, ?AX2L.L_AX2L_mkAluw, ?AX2L.L_AX2L_mkMdw, ?AX2L.L_AX2L_msize_bytes, ?AX2L.L_AX2L_resv_inval, ?AX2L.L_AX2L_ridx, ?AX2L.L_AX2L_saddr_eqb, ?AX2L.L_AX2L_sjump, ?AX2L.L_AX2L_sr_get, ?AX2L.L_AX2L_sr_upd, ?AX2L.L_AX2L_sset, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition know_lookupB (segs : list Segment) (bc : bctx) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  know_lookupAB bc segs (bc_fk bc) rb rk n sx hints acc.
Lemma L_AX2BL_know_lookupB : @know_lookupB = @AX2B.know_lookupB.
Proof. unfold know_lookupB. rewrite ?L_AX2BL_know_lookupAB. reflexivity. Qed.

Local Open Scope Z_scope.
Definition gran (a : Z) : Z := Z.shiftr a 12.
Lemma L_AX2BL_gran : @gran = @AX2B.gran.
Proof. unfold gran. reflexivity. Qed.

Definition lit0_extent (K : kentry) : option (Z * Z) :=
  match K with
  | KWord (SA (ELit 0) kk) w _ => Some (kk, kk + Z.of_nat w)
  | KZero (SA (ELit 0) kk) (ELit l0) => Some (kk, kk + zmod64 l0)
  | KFill (SA (ELit 0) kk) (ELit l0) _ => Some (kk, kk + zmod64 l0)
  | KBlob (SA (ELit 0) kk) (ELit l0) _ => Some (kk, kk + zmod64 l0)
  | KImg lo hi => Some (lo, hi)
  | _ => None
  end.
Lemma L_AX2BL_lit0_extent : @lit0_extent = @AX2B.lit0_extent.
Proof. unfold lit0_extent. rewrite ?AX2L.L_AX2L_zmod64. reflexivity. Qed.

Definition ext_fits (s e : Z) : bool := if Z.ltb s e then Z.leb (gran (e - 1) - gran s) 1 else false.
Lemma L_AX2BL_ext_fits : @ext_fits = @AX2B.ext_fits.
Proof. unfold ext_fits. rewrite ?L_AX2BL_gran. reflexivity. Qed.

Definition ext_has (s e g : Z) : bool := if Z.eqb g (gran s) then true else Z.eqb g (gran (e - 1)).
Lemma L_AX2BL_ext_has : @ext_has = @AX2B.ext_has.
Proof. unfold ext_has. rewrite ?L_AX2BL_gran. reflexivity. Qed.

Definition kx_wide0 (K : kentry) : bool :=
  match lit0_extent K with
  | Some (s, e) => negb (ext_fits s e)
  | None =>
      match K with
      | KZero (SA kb _) _ | KFill (SA kb _) _ _ => true      
      | KBlob (SA kb _) _ _ => is_lit0 kb                    
      | _ => false
      end
  end.
Lemma L_AX2BL_kx_wide0 : @kx_wide0 = @AX2B.kx_wide0.
Proof. unfold kx_wide0. rewrite ?L_AX2BL_is_lit0, ?L_AX2BL_lit0_extent, ?L_AX2BL_ext_fits. reflexivity. Qed.

Definition kx_cand0 (g : Z) (K : kentry) : bool :=
  match lit0_extent K with
  | Some (s, e) => if ext_fits s e then ext_has s e g else true
  | None => kx_wide0 K
  end.
Lemma L_AX2BL_kx_cand0 : @kx_cand0 = @AX2B.kx_cand0.
Proof. unfold kx_cand0. rewrite ?L_AX2BL_lit0_extent, ?L_AX2BL_ext_fits, ?L_AX2BL_ext_has, ?L_AX2BL_kx_wide0. reflexivity. Qed.

Definition kx_candf (K : kentry) : bool :=
  match K with
  | KWord (SA kb _) _ _ | KBlob (SA kb _) _ _ => negb (is_lit0 kb)
  | KZero _ _ | KFill _ _ _ => true
  | _ => false
  end.
Lemma L_AX2BL_kx_candf : @kx_candf = @AX2B.kx_candf.
Proof. unfold kx_candf. rewrite ?L_AX2BL_is_lit0. reflexivity. Qed.

Definition kx_gkey (g : Z) : positive := match g with Z0 => xH | Zpos p => xO p | Zneg p => xI p end.
Lemma L_AX2BL_kx_gkey : @kx_gkey = @AX2B.kx_gkey.
Proof. unfold kx_gkey. reflexivity. Qed.

Definition kx_bucket (t : ptree (list (positive * kentry))) (g : Z) : list (positive * kentry) :=
  match pt_get t (kx_gkey g) with Some b => b | None => [] end.
Lemma L_AX2BL_kx_bucket : @kx_bucket = @AX2B.kx_bucket.
Proof. unfold kx_bucket. rewrite ?L_AX2BL_kx_gkey, ?AX2L.L_AX2L_pt_get. reflexivity. Qed.

Definition kx_add (g : Z) (x : positive * kentry) (t : ptree (list (positive * kentry))) : ptree (list (positive * kentry)) :=
  pt_set (kx_gkey g) (x :: kx_bucket t g) t.
Lemma L_AX2BL_kx_add : @kx_add = @AX2B.kx_add.
Proof. unfold kx_add. rewrite ?L_AX2BL_kx_gkey, ?L_AX2BL_kx_bucket, ?AX2L.L_AX2L_pt_set. reflexivity. Qed.

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
Lemma L_AX2BL_kx_build : @kx_build = @AX2B.kx_build.
Proof. unfold kx_build. rewrite ?L_AX2BL_gran, ?L_AX2BL_lit0_extent, ?L_AX2BL_ext_fits, ?L_AX2BL_kx_wide0, ?L_AX2BL_kx_candf, ?L_AX2BL_kx_add. reflexivity. Qed.

Definition mk_kix (kn : list kentry) : kix :=
  let r := kx_build kn xH in KX kn (fst (fst r)) (snd (fst r)) (snd r).
Lemma L_AX2BL_mk_kix : @mk_kix = @AX2B.mk_kix.
Proof. unfold mk_kix. rewrite ?L_AX2BL_kx_build. reflexivity. Qed.

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
Lemma L_AX2BL_kx_merge : @kx_merge = @AX2B.kx_merge.
Proof. unfold kx_merge. reflexivity. Qed.

Definition kx_select (kx : kix) (rb : expr) (rk : Z) : list kentry :=
  if is_lit0 rb then kx_merge (kx_bucket (kx_gran kx) (gran rk)) (kx_w0 kx)
  else kx_wf kx.
Lemma L_AX2BL_kx_select : @kx_select = @AX2B.kx_select.
Proof. unfold kx_select. rewrite ?L_AX2BL_is_lit0, ?L_AX2BL_gran, ?L_AX2BL_kx_bucket, ?L_AX2BL_kx_merge. reflexivity. Qed.

Definition know_lookupA0I (bc : bctx) (kx : kix) (segs : list Segment) (rb : expr) (rk : Z)
           (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match hints, n with
  | [], S _ => know_lookupA0BQ bc (mkqp bc rb (elen n)) segs (kx_select kx rb rk) rb rk n sx [] acc   
  | _, _ => know_lookupA0B bc segs (kx_kn kx) rb rk n sx hints acc
  end.
Lemma L_AX2BL_know_lookupA0I : @know_lookupA0I = @AX2B.know_lookupA0I.
Proof. unfold know_lookupA0I. rewrite ?L_AX2BL_mkqp, ?L_AX2BL_know_lookupA0B, ?L_AX2BL_know_lookupA0BQ, ?L_AX2BL_kx_select, ?AX2L.L_AX2L_elen. reflexivity. Qed.

Fixpoint tagged (kn : list kentry) (i : positive) : list (positive * kentry) :=
  match kn with [] => [] | K :: rest => (i, K) :: tagged rest (Pos.succ i) end.
Lemma L_AX2BL_tagged : @tagged = @AX2B.tagged.
Proof. unfold tagged. reflexivity. Qed.

Definition all_gt (i : positive) (l : list (positive * kentry)) : Prop := Forall (fun t => (i < fst t)%positive) l.
Lemma L_AX2BL_all_gt : @all_gt = @AX2B.all_gt.
Proof. unfold all_gt. reflexivity. Qed.

Definition narrow_in (g : Z) (K : kentry) : bool :=
  match lit0_extent K with
  | Some (s, e) => if ext_fits s e then ext_has s e g else false
  | None => false
  end.
Lemma L_AX2BL_narrow_in : @narrow_in = @AX2B.narrow_in.
Proof. unfold narrow_in. rewrite ?L_AX2BL_lit0_extent, ?L_AX2BL_ext_fits, ?L_AX2BL_ext_has. reflexivity. Qed.

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
Lemma L_AX2BL_know_lookupABI : @know_lookupABI = @AX2B.know_lookupABI.
Proof. unfold know_lookupABI. rewrite ?L_AX2BL_know_lookupA0I, ?AX2L.L_AX2L_know_bytes_lit, ?AX2L.L_AX2L_lit_of_bytes. reflexivity. Qed.

Local Close Scope Z_scope.
Definition sym_readBI (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (lrs : list (list positive)) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match log_lookupQL bc (s_log ss) lrs (a_base a) (a_off a) n sx' (sc_hints scr) [] None with   
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
          Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
      end
  end.
Lemma L_AX2BL_sym_readBI : @sym_readBI = @AX2B.sym_readBI.
Proof. unfold sym_readBI. rewrite ?L_AX2BL_extKB, ?L_AX2BL_flat_scB, ?L_AX2BL_log_lookupQL, ?L_AX2BL_know_lookupABI. reflexivity. Qed.

Definition sym_stepBI (bc : bctx) (kx : kix) (lrs : list (list positive)) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
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
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod CXLF.p64)) [] scr
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
      
      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrKB bc (g rs) (bv_signed imm) in
      match sym_readBI segs ss bc kx lrs scr a n sx' with
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
  
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match sym_readBI segs ss bc kx lrs scr a n (amo_sx wd) with
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
            else SStop   
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
                match sym_readBI segs ss bc kx lrs scr a n (amo_sx wd) with
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
Lemma L_AX2BL_sym_stepBI : @sym_stepBI = @AX2B.sym_stepBI.
Proof. unfold sym_stepBI. rewrite ?L_AX2BL_decide_branchB, ?L_AX2BL_mkAluKB, ?L_AX2BL_mkMdKB, ?L_AX2BL_mkAluwKB, ?L_AX2BL_flat_scB, ?L_AX2BL_storeok_scB, ?L_AX2BL_conc_exprB, ?L_AX2BL_enum_branchB, ?L_AX2BL_to_saddrKB, ?L_AX2BL_amo_alignedbB, ?L_AX2BL_amo_newvalB, ?L_AX2BL_sym_readBI, ?AX2L.L_AX2L_amo_aluop, ?AX2L.L_AX2L_amo_sx, ?AX2L.L_AX2L_amo_sz, ?AX2L.L_AX2L_mkAluw, ?AX2L.L_AX2L_mkMdw, ?AX2L.L_AX2L_msize_bytes, ?AX2L.L_AX2L_resv_inval, ?AX2L.L_AX2L_ridx, ?AX2L.L_AX2L_saddr_eqb, ?AX2L.L_AX2L_sjump, ?AX2L.L_AX2L_sr_get, ?AX2L.L_AX2L_sr_upd, ?AX2L.L_AX2L_sset, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.
Definition zf_coversB (bc : bctx) (rb : expr) (rk : Z) (n : nat) (kb : expr) (kk : Z) (len : expr) : bool :=
  (match len with
   | ELit l0 => match rel_lit rb rk (Z.of_nat n) kb kk (CXLF.zm64 l0)%Z with RInside _ => true | _ => false end
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
       | Some (a', n', sx') => saddr_eqb a' a && CXNAT.eqbF n' n && Bool.eqb sx' sx
       | None => false
       end)
      && CXNAT.eqbF j (s_next ss) && CXNAT.ltbF j (s_next ss') && evars_lt (s_next ss) (a_base a)
      && CXNAT.lebF 1 n && CXNAT.lebF n 8 && kn_readable segs (bc_fk bc) kn (a_base a) (a_off a) n
  | SCFlat a (ELit z) =>
      Z.leb 1 z && Z.leb z 8 && kn_readable segs (bc_fk bc) kn (a_base a) (a_off a) (Z.to_nat z)
  | SCStoreOk a n => CXNAT.lebF 1 n && CXNAT.lebF n 8 && kn_overlay segs (bc_fk bc) kn (a_base a) (a_off a) n
  | _ => false
  end%bool.
Definition x_filterB (bc : bctx) (ss ss' : sym_state) (scs : list sidecond) : list sidecond :=
  match scs with
  | [] => []          
  | _ => let rb := find_readbase (s_next ss) scs in
         List.filter (fun sc => negb (x_dischargeableB bc ss ss' rb sc)) scs
  end.
Definition sym_stepXB (bc : bctx) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match sym_stepB bc segs i ss scr with
  | SOk ss' scs scr' =>
      if CXNAT.lebF (s_next ss) (s_next ss')            
      then SOk (cap_rd K i ss') (x_filterB bc ss ss' scs) scr'
      else SStop
  | SStop => SStop
  end.
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
Definition sym_stepXBI (bc : bctx) (kx : kix) (lrs : list (list positive)) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match sym_stepBI bc kx lrs segs i ss scr with
  | SOk ss' scs scr' =>
      if CXNAT.lebF (s_next ss) (s_next ss')
      then SOk (cap_rd K i ss') (x_filterB bc ss ss' scs) scr'
      else SStop
  | SStop => SStop
  end.
Definition lrs_step (bc : bctx) (ss ss' : sym_state) (lrs : list (list positive)) : list (list positive) :=
  if CXNAT.eqbF (length (s_log ss')) (length (s_log ss)) then lrs
  else match s_log ss' with e :: _ => regsE bc e :: lrs | [] => lrs end.
Fixpoint sym_execTXBI_go (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
         (lrs : list (list positive)) : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_stepXBI bc kx lrs K i ss scr_nil with
          | SOk ss' [] _ => sym_execTXBI_go bc kx t K f false stops ss' (if s_clean ss' then ss' else ck) (lrs_step bc ss ss' lrs)
          | _ => if s_clean ss then ss else ck
          end
      end
  end.
Definition sym_execTXBI (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  sym_execTXBI_go bc kx t K fuel first stops (clr ss) (clr ss) (List.map (regsE bc) (s_log ss)).
End WithSegs.
Lemma L_AX2BL_zf_coversB : @zf_coversB = @AX2B.zf_coversB.
Proof. unfold zf_coversB. rewrite ?L_AX2BL_xinsideB, ?AX2L.L_AX2L_elen, ?AX2L.L_AX2L_rel_lit, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_AX2BL_kentry_overlayB : @kentry_overlayB = @AX2B.kentry_overlayB.
Proof. unfold kentry_overlayB. rewrite ?L_AX2BL_zf_coversB. reflexivity. Qed.

Lemma L_AX2BL_kentry_readableB : @kentry_readableB = @AX2B.kentry_readableB.
Proof. unfold kentry_readableB. rewrite ?L_AX2BL_kentry_overlayB, ?AX2L.L_AX2L_rel_lit. reflexivity. Qed.

Lemma L_AX2BL_kn_readableB : @kn_readableB = @AX2B.kn_readableB.
Proof. unfold kn_readableB. rewrite ?L_AX2BL_kentry_readableB, ?AX2L.L_AX2L_know_bytes_cov. reflexivity. Qed.

Lemma L_AX2BL_kn_overlayB : @kn_overlayB = @AX2B.kn_overlayB.
Proof. unfold kn_overlayB. rewrite ?L_AX2BL_kentry_overlayB, ?AX2L.L_AX2L_know_bytes_cov. reflexivity. Qed.

Lemma L_AX2BL_x_dischargeableB : @x_dischargeableB = @AX2B.x_dischargeableB.
Proof. unfold x_dischargeableB. rewrite ?AX2L.L_AX2L_evars_lt, ?AX2L.L_AX2L_kn_overlay, ?AX2L.L_AX2L_kn_readable, ?AX2L.L_AX2L_saddr_eqb, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_AX2BL_x_filterB : @x_filterB = @AX2B.x_filterB.
Proof. unfold x_filterB. rewrite ?L_AX2BL_x_dischargeableB, ?AX2L.L_AX2L_find_readbase. reflexivity. Qed.

Lemma L_AX2BL_sym_stepXB : @sym_stepXB = @AX2B.sym_stepXB.
Proof. unfold sym_stepXB. rewrite ?L_AX2BL_sym_stepB, ?L_AX2BL_x_filterB, ?AX2L.L_AX2L_cap_rd, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_AX2BL_sym_execTXB_go : @sym_execTXB_go = @AX2B.sym_execTXB_go.
Proof. unfold sym_execTXB_go. rewrite ?L_AX2BL_sym_stepXB, ?AX2L.L_AX2L_itab, ?AX2L.L_AX2L_itab_lookup, ?AX2L.L_AX2L_s_clean, ?AX2L.L_AX2L_scr_nil. reflexivity. Qed.

Lemma L_AX2BL_sym_execTXB : @sym_execTXB = @AX2B.sym_execTXB.
Proof. unfold sym_execTXB. rewrite ?L_AX2BL_sym_execTXB_go, ?AX2L.L_AX2L_clr, ?AX2L.L_AX2L_itab. reflexivity. Qed.

Lemma L_AX2BL_sym_stepXBI : @sym_stepXBI = @AX2B.sym_stepXBI.
Proof. unfold sym_stepXBI. rewrite ?L_AX2BL_sym_stepBI, ?L_AX2BL_x_filterB, ?AX2L.L_AX2L_cap_rd, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_AX2BL_lrs_step : @lrs_step = @AX2B.lrs_step.
Proof. unfold lrs_step. rewrite ?L_AX2BL_regsE, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_AX2BL_sym_execTXBI_go : @sym_execTXBI_go = @AX2B.sym_execTXBI_go.
Proof. unfold sym_execTXBI_go. rewrite ?L_AX2BL_sym_stepXBI, ?L_AX2BL_lrs_step, ?AX2L.L_AX2L_itab, ?AX2L.L_AX2L_itab_lookup, ?AX2L.L_AX2L_s_clean, ?AX2L.L_AX2L_scr_nil. reflexivity. Qed.

Lemma L_AX2BL_sym_execTXBI : @sym_execTXBI = @AX2B.sym_execTXBI.
Proof. unfold sym_execTXBI. rewrite ?L_AX2BL_regsE, ?L_AX2BL_sym_execTXBI_go, ?AX2L.L_AX2L_clr, ?AX2L.L_AX2L_itab. reflexivity. Qed.

Definition kcutB (bc : bctx) (mk : saddr -> expr -> kentry) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry :=
  let ws := mkAlu ALU_ADD wb (ELit wk) in
  let ks := mkAlu ALU_ADD kb (ELit kk) in
  
  let low :=
    if (if lin_ge0BF bc [(kb, kk)] [(wb, wk)] then false   
        else if lin_ge0BF bc [(wb, wk)] [(kb, kk)] then lin_ge0BF bc [(kb, kk); (len, 0%Z)] [(wb, wk)] else false)
    then [mk (SA kb kk) (mkAlu ALU_SUB ws ks)] else [] in
  let high :=
    if (if lin_ge0BF bc [(kb, kk); (len, 0%Z)] [(wb, wk); (wn, 0%Z)]            
        then if lin_ge0BF bc [(wb, wk); (wn, 0%Z)] [(kb, kk)]                    
             then lin_ge0BF bc [(ELit 0, (two64 - 1)%Z)] [(kb, kk); (len, 0%Z)]  
             else false
        else false)
    then let we := mkAlu ALU_ADD ws wn in
         let '(hb, ho) := split_lit we in
         let ha := if (lin_ge0BF bc [(hb, ho)] [(wb, wk); (wn, 0%Z)] && lin_ge0BF bc [(wb, wk); (wn, 0%Z)] [(hb, ho)])%bool
                   then SA hb ho else SA we 0%Z in
         [mk ha (mkAlu ALU_SUB (mkAlu ALU_ADD ks len) we)]
    else [] in
  low ++ high.
Lemma L_AX2BL_kcutB : @kcutB = @AX2B.kcutB.
Proof. unfold kcutB. rewrite ?L_AX2BL_lin_ge0BF, ?AX2L.L_AX2L_mkAlu, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_two64. reflexivity. Qed.

Definition kzero_cutB (bc : bctx) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := kcutB bc KZero wb wk wn kb kk len.
Lemma L_AX2BL_kzero_cutB : @kzero_cutB = @AX2B.kzero_cutB.
Proof. unfold kzero_cutB. rewrite ?L_AX2BL_kcutB. reflexivity. Qed.

Definition kfill_cutB (bc : bctx) (c : Z) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := kcutB bc (fun a n => KFill a n c) wb wk wn kb kk len.
Lemma L_AX2BL_kfill_cutB : @kfill_cutB = @AX2B.kfill_cutB.
Proof. unfold kfill_cutB. rewrite ?L_AX2BL_kcutB. reflexivity. Qed.

Definition kunk_cutB (bc : bctx) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := kcutB bc KUnk wb wk wn kb kk len.
Lemma L_AX2BL_kunk_cutB : @kunk_cutB = @AX2B.kunk_cutB.
Proof. unfold kunk_cutB. rewrite ?L_AX2BL_kcutB. reflexivity. Qed.

Definition prune_zfB (bc : bctx) (mk : saddr -> expr -> kentry) (wb : expr) (k : Z) (w : nat)
           (K : kentry) (kb : expr) (kk : Z) (len : expr) (apart : unit -> bool) (hints : list bool)
           (diffbase : unit -> list kentry * list sidecond * list bool)
  : list kentry * list sidecond * list bool :=
  
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
Lemma L_AX2BL_prune_zfB : @prune_zfB = @AX2B.prune_zfB.
Proof. unfold prune_zfB. rewrite ?L_AX2BL_kcutB, ?AX2L.L_AX2L_elen, ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_ktrim. reflexivity. Qed.

Definition prune1pB (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  let k := a_off wa in
  let diffbase (ka : saddr) (kl : expr) :=
    let apart := ranges_apart_pBF bc sp (a_base wa) k (elen w) (a_base ka) (a_off ka) kl in
    if apart then ([K], [], hints) else
    match hints with
    | true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)   
    | false :: hs => ([], [], hs)                          
    | [] => ([], [], [])                                   
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
      | _ => if Z.ltb (hi - lo) (CXLF.p64) then diffbase (SA (ELit 0) lo) (ELit (hi - lo))
             else ([], [], hints)
      end
  | KZero (SA kb kk) len =>
      prune_zfB bc KZero (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_pBF bc sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KFill (SA kb kk) len c =>
      prune_zfB bc (fun a n => KFill a n c) (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_pBF bc sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KUnk (SA kb kk) len =>
      prune_zfB bc KUnk (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_pBF bc sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then
        (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool
         then ([K], [], hints) else (kword_cut kb kk w' v k w, [], hints))   
      else if ranges_apart_pBF bc sp (a_base wa) k (elen w) kb kk (elen w') then ([K], [], hints)
      else if (CXNAT.eqbF w 1 && CXNAT.eqbF w' 1 && expr_eqb wv v)%bool
      then ([K], [], hints)   
      else diffbase (SA kb kk) (elen w')
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then
        match len with
        | ELit l0 =>
            let l := (CXLF.zm64 l0)%Z in
            (if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool
             then ([K], [], hints) else ([], [], hints))
        | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints) else ([], [], hints)
        end
      else diffbase (SA kb kk) len
  end.
Lemma L_AX2BL_prune1pB : @prune1pB = @AX2B.prune1pB.
Proof. unfold prune1pB. rewrite ?L_AX2BL_ranges_apart_pBF, ?L_AX2BL_prune_zfB, ?AX2L.L_AX2L_elen, ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_kword_cut, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

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
            else 
            if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_xB bc (sp_Dx sp) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0BF bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0BF bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.
Lemma L_AX2BL_ranges_apart_pcB : @ranges_apart_pcB = @AX2B.ranges_apart_pcB.
Proof. unfold ranges_apart_pcB. rewrite ?L_AX2BL_lin_apartB, ?L_AX2BL_xhiB, ?L_AX2BL_lin_ge0BF, ?L_AX2BL_end_hiB, ?L_AX2BL_in_sidesB, ?L_AX2BL_in_sides_xB, ?AX2L.L_AX2L_shares_var, ?AX2L.L_AX2L_zlit64. reflexivity. Qed.

Definition ranges_apart_pcBF (bc : bctx) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
           (br2 : option (Z * Z)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, br2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then true
      else if shares_var b1 b2 then (if lin_apart0BF bc b1 k1 m1 b2 k2 m2 then true else in_sidesB bc (sp_D sp) b2 k2 m2)
      else in_sidesB bc (sp_D sp) b2 k2 m2
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
    else if negb (shares_var b1 b2) then false
    else if lin_ge0BF bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0BF bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.
Lemma L_AX2BL_ranges_apart_pcBF : @ranges_apart_pcBF = @AX2B.ranges_apart_pcBF.
Proof. unfold ranges_apart_pcBF. rewrite ?L_AX2BL_lin_apart0BF, ?L_AX2BL_xhiB, ?L_AX2BL_lin_ge0BF, ?L_AX2BL_end_hiB, ?L_AX2BL_in_sidesB, ?L_AX2BL_in_sides_xB, ?AX2L.L_AX2L_shares_var, ?AX2L.L_AX2L_zlit64. reflexivity. Qed.

Definition prune1pcB (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
  (br2 : option (Z * Z)) : list kentry * list sidecond * list bool :=
  let k := a_off wa in
  let diffbase (ka : saddr) (kl : expr) :=
    let apart := ranges_apart_pcBF bc sp (a_base wa) k (elen w) br2 (a_base ka) (a_off ka) kl in
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
      else if ranges_apart_pcBF bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kzero_cutB bc (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KFill (SA kb kk) len c =>
      if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
      else if ranges_apart_pcBF bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kfill_cutB bc c (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KUnk (SA kb kk) len =>
      if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
      else if ranges_apart_pcBF bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kunk_cutB bc (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
      else if ranges_apart_pcBF bc sp (a_base wa) k (elen w) br2 kb kk (elen w') then ([K], [], hints)
      else if (CXNAT.eqbF w 1 && CXNAT.eqbF w' 1 && expr_eqb wv v)%bool
      then ([K], [], hints)
      else diffbase (SA kb kk) (elen w')
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
      else diffbase (SA kb kk) len
  end.
Lemma L_AX2BL_prune1pcB : @prune1pcB = @AX2B.prune1pcB.
Proof. unfold prune1pcB. rewrite ?L_AX2BL_kzero_cutB, ?L_AX2BL_kfill_cutB, ?L_AX2BL_kunk_cutB, ?L_AX2BL_prune1pB, ?L_AX2BL_ranges_apart_pcBF, ?AX2L.L_AX2L_elen, ?AX2L.L_AX2L_expr_eqb, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

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
Lemma L_AX2BL_prunepcB : @prunepcB = @AX2B.prunepcB.
Proof. unfold prunepcB. rewrite ?L_AX2BL_base_rangeB, ?L_AX2BL_prune1pcB, ?AX2L.L_AX2L_br_lookup, ?AX2L.L_AX2L_kbase. reflexivity. Qed.

Fixpoint carryB (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log with
  | [] => (kn, [], hints)
  | SE a w v :: older =>
      let '(kn1, scs1, hs1) := carryB bc older kn hints in
      let '(kn2, scs2, hs2) := prunepcB bc (mk_sprepB bc (a_base a) (a_off a) (elen w)) a w v kn1 hs1 [] in
      (KWord a w v :: kn2, scs1 ++ scs2, hs2)
  end.
Lemma L_AX2BL_carryB : @carryB = @AX2B.carryB.
Proof. unfold carryB. rewrite ?L_AX2BL_mk_sprepB, ?L_AX2BL_prunepcB, ?AX2L.L_AX2L_elen. reflexivity. Qed.

Definition p_br_cache_ok (allkn : list kentry) (c : list (expr * option (Z * Z))) : Prop :=
  Forall (fun p => snd p = base_range allkn (fst p)) c.
Lemma L_AX2BL_p_br_cache_ok : @p_br_cache_ok = @AX2B.p_br_cache_ok.
Proof. unfold p_br_cache_ok. rewrite ?AX2L.L_AX2L_base_range. reflexivity. Qed.

Definition g1 (fk : list kentry) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) : list kentry :=
  fst (fst (prune1p fk sp wa w wv K [])).
Lemma L_AX2BL_g1 : @g1 = @AX2B.g1.
Proof. unfold g1. rewrite ?AX2L.L_AX2L_prune1p. reflexivity. Qed.

Definition pk_list (K : kentry) (r : pk_res) : list kentry := match r with PKeep => [K] | PRepl l => l end.
Lemma L_AX2BL_pk_list : @pk_list = @AX2B.pk_list.
Proof. unfold pk_list. reflexivity. Qed.

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
    else if ranges_apart_pcBF bc sp wb k (elen w) br2 kb kk len then PKeep
    else match kcutB bc mk wb k (elen w) kb kk len with
         | [] => if ranges_apart_pcBF bc sp wb k (elen w) br2 kb kk len then PKeep else PRepl []
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
      | _ => if Z.ltb (hi - lo) (CXLF.p64) then
               (if ranges_apart_pBF bc sp wb k (elen w) (ELit 0) lo (ELit (hi - lo)) then PKeep else PRepl [])
             else PRepl []
      end
  | KZero (SA kb kk) len => zfK KZero kb kk len
  | KFill (SA kb kk) len c => zfK (fun a n => KFill a n c) kb kk len
  | KUnk (SA kb kk) len => zfK KUnk kb kk len
  | KWord (SA kb kk) w' v =>
      if same then (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool then PKeep else PRepl (kword_cut kb kk w' v k w))
      else if ranges_apart_pcBF bc sp wb k (elen w) br2 kb kk (elen w') then PKeep
      else if (CXNAT.eqbF w 1 && CXNAT.eqbF w' 1 && expr_eqb wv v)%bool then PKeep
      else if ranges_apart_pcBF bc sp wb k (elen w) br2 kb kk (elen w') then PKeep else PRepl []
  | KBlob (SA kb kk) len bk =>
      if same then
        match len with
        | ELit l0 => let l := (CXLF.zm64 l0)%Z in
                     if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool then PKeep else PRepl []
        | _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl []
        end
      else if ranges_apart_pcBF bc sp wb k (elen w) br2 kb kk len then PKeep else PRepl []
  end.
Lemma L_AX2BL_prune1pcK : @prune1pcK = @AX2B.prune1pcK.
Proof. unfold prune1pcK. rewrite ?L_AX2BL_ranges_apart_pBF, ?L_AX2BL_kcutB, ?L_AX2BL_ranges_apart_pcBF, ?AX2L.L_AX2L_elen, ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_ktrim, ?AX2L.L_AX2L_kword_cut, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition bkey (e : expr) : option nat := first_var e.
Lemma L_AX2BL_bkey : @bkey = @AX2B.bkey.
Proof. unfold bkey. rewrite ?L_AX2BL_first_var. reflexivity. Qed.

Definition nt_empty : ntab := NT [] [] xH PTLeaf.
Lemma L_AX2BL_nt_empty : @nt_empty = @AX2B.nt_empty.
Proof. unfold nt_empty. reflexivity. Qed.

Fixpoint alookupE (l : list (expr * positive)) (b : expr) : option positive :=
  match l with
  | [] => None
  | (b', id) :: rest => if expr_eqb b b' then Some id else alookupE rest b
  end.
Lemma L_AX2BL_alookupE : @alookupE = @AX2B.alookupE.
Proof. unfold alookupE. rewrite ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Definition nt_bucket (t : ntab) (k : option nat) : list (expr * positive) :=
  match k with Some n => lget (nt_vars t) n | None => nt_other t end.
Lemma L_AX2BL_nt_bucket : @nt_bucket = @AX2B.nt_bucket.
Proof. unfold nt_bucket. rewrite ?L_AX2BL_lget. reflexivity. Qed.

Definition nt_add (t : ntab) (k : option nat) (p : expr * positive) (bi : binfo) : ntab :=
  match k with
  | Some n => NT (lset (nt_vars t) n p) (nt_other t) (Pos.succ (nt_next t)) (pt_set (nt_next t) bi (nt_info t))
  | None => NT (nt_vars t) (p :: nt_other t) (Pos.succ (nt_next t)) (pt_set (nt_next t) bi (nt_info t))
  end.
Lemma L_AX2BL_nt_add : @nt_add = @AX2B.nt_add.
Proof. unfold nt_add. rewrite ?L_AX2BL_lset, ?AX2L.L_AX2L_pt_set. reflexivity. Qed.

Definition intern (bc : bctx) (t : ntab) (b : expr) : positive * binfo * ntab :=
  let k := bkey b in
  match alookupE (nt_bucket t k) b with
  | Some id => (id, match pt_get (nt_info t) id with Some bi => bi | None => BI b (base_rangeB bc b) end, t)
  | None => let id := nt_next t in
            let bi := BI b (base_rangeB bc b) in
            (id, bi, nt_add t k (b, id) bi)
  end.
Lemma L_AX2BL_intern : @intern = @AX2B.intern.
Proof. unfold intern. rewrite ?L_AX2BL_base_rangeB, ?L_AX2BL_bkey, ?L_AX2BL_alookupE, ?L_AX2BL_nt_bucket, ?L_AX2BL_nt_add, ?AX2L.L_AX2L_pt_get. reflexivity. Qed.

Definition NTI (bc : bctx) (t : ntab) : Prop :=
  (forall k b id, In (b, id) (nt_bucket t k) ->
     k = bkey b /\ pt_get (nt_info t) id = Some (BI b (base_rangeB bc b)) /\ (id < nt_next t)%positive)
  /\ (forall k b id id', In (b, id) (nt_bucket t k) -> In (b, id') (nt_bucket t k) -> id = id').
Lemma L_AX2BL_NTI : @NTI = @AX2B.NTI.
Proof. unfold NTI. rewrite ?L_AX2BL_base_rangeB, ?L_AX2BL_bkey, ?L_AX2BL_nt_bucket, ?AX2L.L_AX2L_pt_get. reflexivity. Qed.

Definition mk_sprepR (bc : bctx) (RS : list positive) (b1 : expr) (w : nat) : sprep :=
  let D := disj_sidesR (rt_facts (bc_rt bc)) RS in
  SPrep (base_rangeB bc b1) (xhiB bc (elen w)) D D.
Lemma L_AX2BL_mk_sprepR : @mk_sprepR = @AX2B.mk_sprepR.
Proof. unfold mk_sprepR. rewrite ?L_AX2BL_disj_sidesR, ?L_AX2BL_base_rangeB, ?L_AX2BL_xhiB, ?AX2L.L_AX2L_elen. reflexivity. Qed.

Definition regs_w (bc : bctx) (a : saddr) (w : nat) : list positive :=
  regs bc (a_base a) (a_off a) (zlit64 (Z.of_nat w)).
Lemma L_AX2BL_regs_w : @regs_w = @AX2B.regs_w.
Proof. unfold regs_w. rewrite ?L_AX2BL_regs, ?AX2L.L_AX2L_zlit64. reflexivity. Qed.

Fixpoint mk_stxs (bc : bctx) (log : list sentry) (t : ntab) : list stx * ntab :=   
  match log with
  | [] => ([], t)
  | SE a w v :: older =>
      let '(sxs, t1) := mk_stxs bc older t in
      let '(r, t2) := intern bc t1 (a_base a) in
      let '(bid, bi) := r in
      let RS := regs_w bc a w in
      (sxs ++ [STX a w v (mk_sprepR bc RS (a_base a) w) bid (bi_br bi) (partners_of (bc_rt bc) RS)], t2)
  end.
Lemma L_AX2BL_mk_stxs : @mk_stxs = @AX2B.mk_stxs.
Proof. unfold mk_stxs. rewrite ?L_AX2BL_partners_of, ?L_AX2BL_intern, ?L_AX2BL_mk_sprepR, ?L_AX2BL_regs_w. reflexivity. Qed.

Definition obrB (bc : bctx) (K : kentry) : option (Z * Z) :=
  match kbase K with Some kb => base_rangeB bc kb | None => None end.
Lemma L_AX2BL_obrB : @obrB = @AX2B.obrB.
Proof. unfold obrB. rewrite ?L_AX2BL_base_rangeB, ?AX2L.L_AX2L_kbase. reflexivity. Qed.

Definition g1cB (bc : bctx) (sx : stx) (K : kentry) : list kentry :=
  fst (fst (prune1pcB bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K [] (obrB bc K))).
Lemma L_AX2BL_g1cB : @g1cB = @AX2B.g1cB.
Proof. unfold g1cB. rewrite ?L_AX2BL_prune1pcB, ?L_AX2BL_obrB. reflexivity. Qed.

Fixpoint chain_slow (bc : bctx) (sxs : list stx) (l : list kentry) : list kentry :=
  match sxs with
  | [] => l
  | sx :: rest => chain_slow bc rest (flat_map (g1cB bc sx) l)
  end.
Lemma L_AX2BL_chain_slow : @chain_slow = @AX2B.chain_slow.
Proof. unfold chain_slow. rewrite ?L_AX2BL_g1cB. reflexivity. Qed.

Fixpoint chainK (bc : bctx) (sxs : list stx) (K : kentry) (same_of : positive -> bool) (br2 : option (Z * Z)) : list kentry :=
  match sxs with
  | [] => [K]
  | sx :: rest =>
      match prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
      | PKeep => chainK bc rest K same_of br2
      | PRepl l => chain_slow bc rest l
      end
  end.
Lemma L_AX2BL_chainK : @chainK = @AX2B.chainK.
Proof. unfold chainK. rewrite ?L_AX2BL_prune1pcK, ?L_AX2BL_chain_slow. reflexivity. Qed.

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
Lemma L_AX2BL_chainK2 : @chainK2 = @AX2B.chainK2.
Proof. unfold chainK2. rewrite ?L_AX2BL_prune1pcK, ?L_AX2BL_chain_slow, ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_kbase. reflexivity. Qed.

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
Lemma L_AX2BL_entriesV : @entriesV = @AX2B.entriesV.
Proof. unfold entriesV. rewrite ?L_AX2BL_intern, ?L_AX2BL_chainK2, ?AX2L.L_AX2L_kbase. reflexivity. Qed.

Fixpoint stores_part (bc : bctx) (sxs : list stx) : list kentry :=   
  match sxs with
  | [] => []
  | sx :: newer => stores_part bc newer ++ chainK2 bc newer (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx)
  end.
Lemma L_AX2BL_stores_part : @stores_part = @AX2B.stores_part.
Proof. unfold stores_part. rewrite ?L_AX2BL_chainK2. reflexivity. Qed.

Definition carryV (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t) := mk_stxs bc log nt_empty in
  stores_part bc sxs ++ entriesV bc sxs kn t.
Lemma L_AX2BL_carryV : @carryV = @AX2B.carryV.
Proof. unfold carryV. rewrite ?L_AX2BL_nt_empty, ?L_AX2BL_mk_stxs, ?L_AX2BL_entriesV, ?L_AX2BL_stores_part. reflexivity. Qed.

Definition carryK0 (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryV bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma L_AX2BL_carryK0 : @carryK0 = @AX2B.carryK0.
Proof. unfold carryK0. rewrite ?L_AX2BL_carryB, ?L_AX2BL_carryV. reflexivity. Qed.

Definition FM (fk : list kentry) (s : sentry) (l : list kentry) : list kentry :=
  match s with SE a w v => flat_map (g1 fk (mk_sprep fk (a_base a) (a_off a) (elen w)) a w v) l end.
Lemma L_AX2BL_FM : @FM = @AX2B.FM.
Proof. unfold FM. rewrite ?L_AX2BL_g1, ?AX2L.L_AX2L_elen, ?AX2L.L_AX2L_mk_sprep. reflexivity. Qed.

Fixpoint chainRo (fk : list kentry) (sxo : list sentry) (l : list kentry) : list kentry :=
  match sxo with [] => l | s :: newer => chainRo fk newer (FM fk s l) end.
Lemma L_AX2BL_chainRo : @chainRo = @AX2B.chainRo.
Proof. unfold chainRo. rewrite ?L_AX2BL_FM. reflexivity. Qed.

Definition kw (s : sentry) : kentry := match s with SE a w v => KWord a w v end.
Lemma L_AX2BL_kw : @kw = @AX2B.kw.
Proof. unfold kw. reflexivity. Qed.

Fixpoint SPRo (fk : list kentry) (sxo : list sentry) : list kentry :=
  match sxo with [] => [] | s :: newer => SPRo fk newer ++ chainRo fk newer [kw s] end.
Lemma L_AX2BL_SPRo : @SPRo = @AX2B.SPRo.
Proof. unfold SPRo. rewrite ?L_AX2BL_chainRo, ?L_AX2BL_kw. reflexivity. Qed.

Definition strip (sx : stx) : sentry := SE (sx_a sx) (sx_w sx) (sx_v sx).
Lemma L_AX2BL_strip : @strip = @AX2B.strip.
Proof. unfold strip. reflexivity. Qed.

Definition SX_OK (bc : bctx) (t : ntab) (sx : stx) : Prop :=
  In (a_base (sx_a sx), sx_bid sx) (nt_bucket t (bkey (a_base (sx_a sx))))
  /\ sx_br sx = base_rangeB bc (a_base (sx_a sx))
  /\ sx_sp sx = mk_sprepB bc (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))
  /\ sx_ps sx = partners_of (bc_rt bc) (regs_w bc (sx_a sx) (sx_w sx)).
Lemma L_AX2BL_SX_OK : @SX_OK = @AX2B.SX_OK.
Proof. unfold SX_OK. rewrite ?L_AX2BL_partners_of, ?L_AX2BL_base_rangeB, ?L_AX2BL_mk_sprepB, ?L_AX2BL_bkey, ?L_AX2BL_nt_bucket, ?L_AX2BL_regs_w, ?AX2L.L_AX2L_elen. reflexivity. Qed.

Fixpoint pt_map {A B : Type} (f : A -> B) (t : ptree A) : ptree B :=
  match t with
  | PTLeaf => PTLeaf
  | PTNode l o r => PTNode (pt_map f l) (match o with Some a => Some (f a) | None => None end) (pt_map f r)
  end.
Lemma L_AX2BL_pt_map : @pt_map = @AX2B.pt_map.
Proof. unfold pt_map. reflexivity. Qed.

Definition kdescr (K : kentry) : option (expr * Z * option Z) :=
  match K with
  | KWord (SA kb kk) w _ => Some (kb, kk, Some (zlit64 (Z.of_nat w)))
  | KZero (SA kb kk) len | KUnk (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
      Some (kb, kk, match len with ELit z => Some (zlit64 z) | _ => None end)
  | KImg lo hi => Some (ELit 0%Z, lo, if Z.ltb (hi - lo) (CXLF.p64) then Some (zlit64 (hi - lo)) else None)
  | _ => None
  end.
Lemma L_AX2BL_kdescr : @kdescr = @AX2B.kdescr.
Proof. unfold kdescr. rewrite ?AX2L.L_AX2L_zlit64, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition gval : Type := (positive * expr * option (Z * Z) * (Z * Z))%type.
Lemma L_AX2BL_gval : @gval = @AX2B.gval.
Proof. unfold gval. reflexivity. Qed.

Definition gtab := ptree gval.
Lemma L_AX2BL_gtab : @gtab = @AX2B.gtab.
Proof. unfold gtab. rewrite ?L_AX2BL_gval. reflexivity. Qed.

Definition gst_empty : gst := GST PTLeaf xH PTLeaf.
Lemma L_AX2BL_gst_empty : @gst_empty = @AX2B.gst_empty.
Proof. unfold gst_empty. reflexivity. Qed.

Definition gkey (kk : Z) : positive :=
  let g := Z.shiftr kk 16 in Z.to_pos (if Z.leb 0 g then 2 * g + 1 else - (2 * g))%Z.
Lemma L_AX2BL_gkey : @gkey = @AX2B.gkey.
Proof. unfold gkey. reflexivity. Qed.

Definition ggroup (gs : gst) (bid : positive) (kk : Z) : positive * gst :=
  let gk := gkey kk in
  let inner := match pt_get (gs_gid gs) bid with Some i => i | None => PTLeaf end in
  match pt_get inner gk with
  | Some gid => (gid, gs)
  | None => let gid := gs_next gs in
            (gid, GST (pt_set bid (pt_set gk gid inner) (gs_gid gs)) (Pos.succ gid) (gs_bnds gs))
  end.
Lemma L_AX2BL_ggroup : @ggroup = @AX2B.ggroup.
Proof. unfold ggroup. rewrite ?L_AX2BL_gkey, ?AX2L.L_AX2L_pt_get, ?AX2L.L_AX2L_pt_set. reflexivity. Qed.

Definition bnd_add (gs : gst) (gid bid : positive) (kb : expr) (obr : option (Z * Z)) (lo hi : Z) : gst :=
  GST (gs_gid gs) (gs_next gs)
      (match pt_get (gs_bnds gs) gid with
       | Some (b, e, o, (l, h)) => pt_set gid (b, e, o, (Z.min l lo, Z.max h hi)) (gs_bnds gs)
       | None => pt_set gid (bid, kb, obr, (lo, hi)) (gs_bnds gs)
       end).
Lemma L_AX2BL_bnd_add : @bnd_add = @AX2B.bnd_add.
Proof. unfold bnd_add. rewrite ?AX2L.L_AX2L_pt_get, ?AX2L.L_AX2L_pt_set. reflexivity. Qed.

Fixpoint scan_entries (bc : bctx) (kn : list kentry) (t : ntab) (gs : gst) : list (option einfo) * ntab * gst :=
  match kn with
  | [] => ([], t, gs)
  | K :: rest =>
      match kdescr K with
      | Some (kb, kk, om) =>
          let '(r, t1) := intern bc t kb in
          let '(bid, bi) := r in
          let '(gid, gs1) := match om with
                             | Some m => let '(gid, gs0) := ggroup gs bid kk in (gid, bnd_add gs0 gid bid kb (bi_br bi) kk (kk + m)%Z)
                             | None => (xH, gs)
                             end in
          let '(infos, t2, gs2) := scan_entries bc rest t1 gs1 in
          (Some (EI bid gid kb (bi_br bi) kk om) :: infos, t2, gs2)
      | None =>
          let '(infos, t2, gs2) := scan_entries bc rest t gs in
          (None :: infos, t2, gs2)
      end
  end.
Lemma L_AX2BL_scan_entries : @scan_entries = @AX2B.scan_entries.
Proof. unfold scan_entries. rewrite ?L_AX2BL_intern, ?L_AX2BL_kdescr, ?L_AX2BL_ggroup, ?L_AX2BL_bnd_add. reflexivity. Qed.

Definition sx_m1 (sx : stx) : Z := zlit64 (Z.of_nat (sx_w sx)).
Lemma L_AX2BL_sx_m1 : @sx_m1 = @AX2B.sx_m1.
Proof. unfold sx_m1. rewrite ?AX2L.L_AX2L_zlit64. reflexivity. Qed.

Definition verdict (sx : stx) (g : gval) : bool :=
  match g with
  | (b, _, obr, (glo, ghi)) =>
      if Pos.eqb b (sx_bid sx) then false else
      match sp_rng (sx_sp sx), obr with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + a_off (sx_a sx) + sx_m1 sx - lo2) glo || Z.leb ghi (lo1 + a_off (sx_a sx) - hi2))%bool
      | _, _ => false
      end
  end.
Lemma L_AX2BL_verdict : @verdict = @AX2B.verdict.
Proof. unfold verdict. rewrite ?L_AX2BL_gval, ?L_AX2BL_sx_m1. reflexivity. Qed.

Definition verdict_disj (bc : bctx) (sx : stx) (g : gval) : bool :=
  match g with
  | (b, gkb, _, (glo, ghi)) =>
      if Pos.eqb b (sx_bid sx) then false else
      existsb (fun cm : saddr * expr =>
                 let '(c, ml) := cm in
                 (expr_eqb gkb (a_base c) && Z.leb (a_off c) glo
                  && match xloB bc ml with Some l => Z.leb ghi (a_off c + l) | None => false end)%bool)
              (sp_D (sx_sp sx))
  end.
Lemma L_AX2BL_verdict_disj : @verdict_disj = @AX2B.verdict_disj.
Proof. unfold verdict_disj. rewrite ?L_AX2BL_xloB, ?L_AX2BL_gval, ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Definition verdict2 (bc : bctx) (sx : stx) (g : gval) : bool :=
  if verdict sx g then true else verdict_disj bc sx g.
Lemma L_AX2BL_verdict2 : @verdict2 = @AX2B.verdict2.
Proof. unfold verdict2. rewrite ?L_AX2BL_gval, ?L_AX2BL_verdict, ?L_AX2BL_verdict_disj. reflexivity. Qed.

Definition cg_of (bc : bctx) (g : gval) : list positive :=
  match g with
  | (_, gkb, _, (glo, ghi)) =>
      List.map fst (List.filter (fun t : positive * (saddr * expr) =>
                      let '(c, ml) := snd t in
                      (expr_eqb gkb (a_base c) && Z.leb (a_off c) glo
                       && match xloB bc ml with Some l => Z.leb ghi (a_off c + l) | None => false end)%bool)
                   (rt_sides (bc_rt bc)))
  end.
Lemma L_AX2BL_cg_of : @cg_of = @AX2B.cg_of.
Proof. unfold cg_of. rewrite ?L_AX2BL_xloB, ?L_AX2BL_gval, ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Definition verdict_disjR (cg : list positive) (sx : stx) (g : gval) : bool :=
  match g with
  | (b, _, _, _) => if Pos.eqb b (sx_bid sx) then false else existsb (fun j => pmem j (sx_ps sx)) cg
  end.
Lemma L_AX2BL_verdict_disjR : @verdict_disjR = @AX2B.verdict_disjR.
Proof. unfold verdict_disjR. rewrite ?L_AX2BL_pmem, ?L_AX2BL_gval. reflexivity. Qed.

Definition verdict2R (cg : list positive) (sx : stx) (g : gval) : bool :=
  if verdict sx g then true else verdict_disjR cg sx g.
Lemma L_AX2BL_verdict2R : @verdict2R = @AX2B.verdict2R.
Proof. unfold verdict2R. rewrite ?L_AX2BL_gval, ?L_AX2BL_verdict, ?L_AX2BL_verdict_disjR. reflexivity. Qed.

Fixpoint mk_fl (cg : list positive) (g : gval) (sxs : list stx) : list (stx * list stx) :=
  match sxs with
  | [] => []
  | sx :: rest => if verdict2R cg sx g then mk_fl cg g rest else (sx, rest) :: mk_fl cg g rest
  end.
Lemma L_AX2BL_mk_fl : @mk_fl = @AX2B.mk_fl.
Proof. unfold mk_fl. rewrite ?L_AX2BL_gval, ?L_AX2BL_verdict2R. reflexivity. Qed.

Definition gfl : Type := (gval * list (stx * list stx))%type.
Lemma L_AX2BL_gfl : @gfl = @AX2B.gfl.
Proof. unfold gfl. rewrite ?L_AX2BL_gval. reflexivity. Qed.

Definition mk_gl (bc : bctx) (bnds : gtab) (sxs : list stx) : ptree gfl := pt_map (fun g => (g, mk_fl (cg_of bc g) g sxs)) bnds.
Lemma L_AX2BL_mk_gl : @mk_gl = @AX2B.mk_gl.
Proof. unfold mk_gl. rewrite ?L_AX2BL_pt_map, ?L_AX2BL_gtab, ?L_AX2BL_cg_of, ?L_AX2BL_mk_fl, ?L_AX2BL_gfl. reflexivity. Qed.

Definition obr_eqb (a b : option (Z * Z)) : bool :=
  match a, b with
  | Some (x1, y1), Some (x2, y2) => Z.eqb x1 x2 && Z.eqb y1 y2
  | None, None => true
  | _, _ => false
  end%bool.
Lemma L_AX2BL_obr_eqb : @obr_eqb = @AX2B.obr_eqb.
Proof. unfold obr_eqb. reflexivity. Qed.

Definition inb (g : gval) (ei : einfo) : bool :=
  match ei_m ei, g with
  | Some m, (b, gkb, obr, (lo, hi)) =>
      Pos.eqb b (ei_bid ei) && expr_eqb gkb (ei_kb ei) && obr_eqb obr (ei_br ei) && Z.leb lo (ei_k ei) && Z.leb (ei_k ei + m) hi
  | _, _ => false
  end%bool.
Lemma L_AX2BL_inb : @inb = @AX2B.inb.
Proof. unfold inb. rewrite ?L_AX2BL_gval, ?L_AX2BL_obr_eqb, ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

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
Lemma L_AX2BL_chainKF : @chainKF = @AX2B.chainKF.
Proof. unfold chainKF. rewrite ?L_AX2BL_prune1pcK, ?L_AX2BL_chain_slow, ?L_AX2BL_chainK2, ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_kbase. reflexivity. Qed.

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
Lemma L_AX2BL_entriesG : @entriesG = @AX2B.entriesG.
Proof. unfold entriesG. rewrite ?L_AX2BL_chainK2, ?L_AX2BL_gfl, ?L_AX2BL_inb, ?L_AX2BL_chainKF, ?AX2L.L_AX2L_kbase, ?AX2L.L_AX2L_pt_get. reflexivity. Qed.

Definition carryG (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxs bc log nt_empty in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, _) := r in
  stores_part bc sxs ++ entriesG bc sxs (mk_gl bc (gs_bnds gs) sxs) kn infos.
Lemma L_AX2BL_carryG : @carryG = @AX2B.carryG.
Proof. unfold carryG. rewrite ?L_AX2BL_nt_empty, ?L_AX2BL_mk_stxs, ?L_AX2BL_stores_part, ?L_AX2BL_gst_empty, ?L_AX2BL_scan_entries, ?L_AX2BL_mk_gl, ?L_AX2BL_entriesG. reflexivity. Qed.

Definition EINF (bc : bctx) (t : ntab) (K : kentry) (oi : option einfo) : Prop :=
  match oi with
  | None => kdescr K = None
  | Some ei => kdescr K = Some (ei_kb ei, ei_k ei, ei_m ei)
               /\ In (ei_kb ei, ei_bid ei) (nt_bucket t (bkey (ei_kb ei)))
               /\ ei_br ei = base_rangeB bc (ei_kb ei)
  end.
Lemma L_AX2BL_EINF : @EINF = @AX2B.EINF.
Proof. unfold EINF. rewrite ?L_AX2BL_base_rangeB, ?L_AX2BL_bkey, ?L_AX2BL_nt_bucket, ?L_AX2BL_kdescr. reflexivity. Qed.

Definition carryK (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryG bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma L_AX2BL_carryK : @carryK = @AX2B.carryK.
Proof. unfold carryK. rewrite ?L_AX2BL_carryB, ?L_AX2BL_carryG. reflexivity. Qed.

End AX2BL.
