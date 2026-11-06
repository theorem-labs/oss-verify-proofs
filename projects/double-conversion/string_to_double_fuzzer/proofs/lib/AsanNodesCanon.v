(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3B AsanPlanCore AsanPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2B. Import APC. Import AP. Import Instr.
Open Scope Z_scope.

Module CAN.
Section WithA.
  Variable A : atable.

  (* [comment removed for export] *)
  Definition rs_sa (B : expr) (lo hi : Z) (B' : expr) (d : Z) (a : saddr) : saddr :=
    match a with SA b o => if (expr_eqb b B && Z.leb lo o && Z.ltb o hi)%bool then SA B' (o - d) else a end.
  Definition rs_k (B : expr) (lo hi : Z) (B' : expr) (d : Z) (K : kentry) : kentry :=
    let f := rs_sa B lo hi B' d in
    match K with
    | KWord a w v => KWord (f a) w v
    | KZero a n => KZero (f a) n
    | KBlob a n j => KBlob (f a) n j
    | KWr a n => KWr (f a) n
    | KDisj a1 n1 a2 n2 => KDisj (f a1) n1 (f a2) n2
    | KFill a n c => KFill (f a) n c
    | KUnk a n => KUnk (f a) n
    | _ => K
    end.
  Definition node_rsbase (cs : acs) (B : expr) (lo hi : Z) (B' : expr) (d : Z) : option acs :=
    let k := kn cs in
    match xlo k B, xhi k B with
    | Some blo, Some bhi =>
        if (Z.leb 0 (blo + d) && Z.ltb (bhi + d) two64 && expr_vars_lt (nxt cs) B' && respell_ok k (eaddz B d) B')%bool
        then Some (set_kn cs (map (rs_k B lo hi B' d) k))
        else None
    | _, _ => None
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition node_addzero (cs : acs) (b : expr) (o : Z) (n : expr) : option acs :=
    let k := kn cs in
    if (expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n && flat_x k b o n && kzero_x k k b o n)%bool
    then Some (set_kn cs (KZero (SA b o) n :: k)) else None.
  Definition node_addwr (cs : acs) (b : expr) (o : Z) (n : expr) : option acs :=
    let k := kn cs in
    if (expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n && flat_x k b o n && kwritable_x A k k b o n)%bool
    then Some (set_kn cs (KWr (SA b o) n :: k)) else None.

  (* [comment removed for export] *)
  Fixpoint upd_nth {T : Type} (l : list T) (i : nat) (x : T) : list T :=
    match l, i with
    | [], _ => []
    | _ :: r, O => x :: r
    | y :: r, S i' => y :: upd_nth r i' x
    end.
  Definition node_rsvis (cs : acs) (i : nat) (e' : expr) : option acs :=
    match nth_error (a_vis cs) i with
    | Some (b, n) =>
        if (expr_vars_lt (nxt cs) e' && respell_ok (kn cs) b e')%bool
        then Some (ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                       (upd_nth (a_vis cs) i (e', n)) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
        else None
    | None => None
    end.


  (* [comment removed for export] *)
  Fixpoint rep (a x : expr) (t : expr) : expr :=
    if expr_eqb t a then x else
    match t with
    | EAlu op p q => EAlu op (rep a x p) (rep a x q)
    | EAluw op p q => EAluw op (rep a x p) (rep a x q)
    | EMd op p q => EMd op (rep a x p) (rep a x q)
    | EMdw op p q => EMdw op (rep a x p) (rep a x q)
    | EExt sx lo n p => EExt sx lo n (rep a x p)
    | _ => t
    end.
  Definition node_rscase (cs : acs) (r : nat) (e a : expr) : option acs :=
    let k := kn cs in
    match xlo k a, xhi k a with
    | Some alo, Some ahi =>
        if (Nat.ltb 0 r && Nat.ltb r 32 && expr_vars_lt (nxt cs) e && Z.leb 0 alo && Z.leb (ahi - alo) 64
            && forallb (fun i => let x := ELit (alo + Z.of_nat i) in respell_ok k (rep a x (reg cs r)) (rep a x e))
                       (seq 0 (Z.to_nat (ahi - alo + 1))))%bool
        then Some (set_reg cs r e) else None
    | _, _ => None
    end.

  (* [comment removed for export] *)
  Definition low3 (x : expr) : expr := mkAlu ALU_SUB x (EMd M_MUL (ELit 8) (EAlu ALU_SRL x (ELit 3))).

  (* [comment removed for export] *)
  Definition rup3 (x : expr) : expr := mkAlu ALU_SUB (EMd M_MUL (ELit 8) (EAlu ALU_SRL (mkAlu ALU_ADD x (ELit 7)) (ELit 3))) x.

  (* [comment removed for export] *)
  Fixpoint find_byte (k allk : list kentry) (ab : expr) (off : Z) : option expr :=
    match k with
    | [] => None
    | KWord (SA b o) 1%nat w :: rest =>
        if (expr_eqb b ab && Z.eqb o off)%bool then Some w else find_byte rest allk ab off
    | KFill (SA b o) L c :: rest =>
        if (expr_eqb b ab && Z.leb o off
            && match xlo allk L with Some lo => Z.ltb (off - o) lo | None => false end)%bool
        then Some (ELit c) else find_byte rest allk ab off
    | _ :: rest => find_byte rest allk ab off
    end.
  Definition node_bytespell (cs : acs) (a : expr) (off : Z) (V : expr) : option acs :=
    let k := kn cs in
    let '(ab, ao) := split_lit (eaddz a off) in    (* [comment removed for export] *)
    match find_byte k k ab ao with
    | Some w =>
        let w' := extK k w in
        if (flat_x k ab ao (ELit 1) && lin_ge0 k [(w', 0)] [(V, 0)] && lin_ge0 k [(V, 0)] [(w', 0)])%bool
        then Some (set_kn cs (KWord (SA ab ao) 1 V :: k)) else None
    | None => None
    end.
  
  
  (* [comment removed for export] *)
  Definition node_bytecase (cs : acs) (a : expr) (off : Z) (V atom : expr) : option acs :=
    let k := kn cs in
    let '(ab, ao) := split_lit (eaddz a off) in
    match find_byte k k ab ao, xlo k atom, xhi k atom with
    | Some w, Some alo, Some ahi =>
        let w' := extK k w in
        if (flat_x k ab ao (ELit 1) && expr_vars_lt (nxt cs) V && Z.leb 0 alo && Z.leb (ahi - alo) 64
            && forallb (fun i => let x := ELit (alo + Z.of_nat i) in respell_ok k (rep atom x w') (rep atom x V))
                       (seq 0 (Z.to_nat (ahi - alo + 1))))%bool
        then Some (set_kn cs (KWord (SA ab ao) 1 V :: k)) else None
    | _, _, _ => None
    end.

  (* [comment removed for export] *)
  Definition rs_val (b : expr) (o : Z) (e : expr) (K : kentry) : kentry :=
    match K with
    | KWord (SA b' o') w v => if (expr_eqb b' b && Z.eqb o' o)%bool then KWord (SA b' o') w e else K
    | _ => K
    end.
  Definition node_rsval (cs : acs) (b : expr) (o : Z) (e : expr) : option acs :=
    let k := kn cs in
    if (expr_vars_lt (nxt cs) e
        && forallb (fun K => match K with
                             | KWord (SA b' o') w v => if (expr_eqb b' b && Z.eqb o' o)%bool then respell_ok k v e else true
                             | _ => true
                             end) k)%bool
    then Some (set_kn cs (map (rs_val b o e) k)) else None.

  (* [comment removed for export] *)
  Definition node_addzero0 (cs : acs) (b : expr) (o : Z) (n : expr) : option acs :=
    match xhi (kn cs) n, base_range (kn cs) b with
    | Some 0, Some (blo, bhi) =>
        if (expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n && Z.leb 0 (blo + o) && Z.ltb (bhi + o) two64)%bool
        then Some (set_kn cs (KZero (SA b o) n :: kn cs)) else None
    | _, _ => None
    end.
  Definition node_rup3 (cs : acs) (x : expr) : option acs :=
    match xhi (kn cs) x with
    | Some h => if (expr_vars_lt (nxt cs) x && Z.ltb h (two64 - 8))%bool then Some (set_kn cs (KRange (rup3 x) 0 7 :: kn cs)) else None
    | None => None
    end.
  Definition node_low3 (cs : acs) (x : expr) : option acs :=
    if expr_vars_lt (nxt cs) x then
      match erange (kn cs) (EAlu ALU_AND x (ELit 7)) with
      | Some (lo, hi) => Some (set_kn cs (KRange (low3 x) (Z.max lo 0) (Z.min hi 7) :: kn cs))
      | None => Some (set_kn cs (KRange (low3 x) 0 7 :: kn cs))
      end
    else None.
  (* [comment removed for export] *)
  Definition probe_raw (x : expr) : expr := EAlu ALU_SLTU (EAlu ALU_SUB x (EMd M_MUL (ELit 8) (EAlu ALU_SRL x (ELit 3)))) (ELit 1).
  Definition probe_low3 (x : expr) : expr := EAlu ALU_SLTU (low3 x) (ELit 1).
  Definition lowp_fact (x : expr) (r : option (Z * Z)) : option kentry :=
    match r with
    | Some (lo, hi) => if Z.eqb hi 0 then Some (KRange (EAlu ALU_AND x (ELit 7)) 1 7)
                       else if Z.eqb lo 1 then Some (KRange (EAlu ALU_AND x (ELit 7)) 0 0) else None
    | None => None
    end.
  Definition node_lowp (cs : acs) (x : expr) : option acs :=
    if expr_vars_lt (nxt cs) x then
      match lowp_fact x (match erange (kn cs) (probe_raw x) with Some r => Some r | None => erange (kn cs) (probe_low3 x) end) with
      | Some K => Some (set_kn cs (K :: kn cs))
      | None => None
      end
    else None.
  (* [comment removed for export] *)
  Definition sr3diff (x : expr) : expr := mkAlu ALU_SUB (EAlu ALU_SRL (mkAlu ALU_ADD x (ELit 7)) (ELit 3)) (EAlu ALU_SRL x (ELit 3)).
  Definition low3z_facts (x : expr) (r : option (Z * Z)) : option (list kentry) :=
    match r with
    | Some (lo, hi) => if Z.eqb hi 0 then Some [KRange (sr3diff x) 0 0; KRange (low3 x) 0 0]
                       else if Z.leb 1 lo then Some [KRange (sr3diff x) 1 1] else None
    | None => None
    end.
  Definition node_low3z (cs : acs) (x : expr) : option acs :=
    match xhi (kn cs) x with
    | Some h => if (expr_vars_lt (nxt cs) x && Z.ltb h (two64 - 8))%bool then
                  match low3z_facts x (erange (kn cs) (EAlu ALU_AND x (ELit 7))) with
                  | Some Ks => Some (set_kn cs (Ks ++ kn cs))
                  | None => None
                  end
                else None
    | None => None
    end.
  Definition xn_ref (args : list expr) (cs : acs) : option acs :=
    match args with
    | ELit op :: rest =>
        if Z.eqb op 0 then match rest with [B; ELit lo; ELit hi; B'; ELit d] => node_rsbase cs B lo hi B' d | _ => None end
        else if Z.eqb op 1 then match rest with [b; ELit o; n] => node_addzero cs b o n | _ => None end
        else if Z.eqb op 2 then match rest with [b; ELit o; n] => node_addwr cs b o n | _ => None end
        else if Z.eqb op 4 then match rest with [ELit i; e'] => node_rsvis cs (Z.to_nat i) e' | _ => None end
        else if Z.eqb op 5 then match rest with [ELit r; e; a] => node_rscase cs (Z.to_nat r) e a | _ => None end
        else if Z.eqb op 6 then match rest with [ELit a; ELit n] => Some (set_kn cs (kimg_cut (kn cs) a n)) | _ => None end
        else if Z.eqb op 7 then match rest with [x] => node_low3 cs x | _ => None end
        else if Z.eqb op 8 then match rest with [x] => node_rup3 cs x | _ => None end
        else if Z.eqb op 9 then match rest with [a; ELit off; V; atom] => node_bytecase cs a off V atom | _ => None end
        else if Z.eqb op 10 then match rest with [b; ELit o; n] => node_addzero0 cs b o n | _ => None end
        else if Z.eqb op 11 then match rest with [b; ELit o; e] => node_rsval cs b o e | _ => None end
        else if Z.eqb op 12 then match rest with [x] => node_lowp cs x | _ => None end
        else if Z.eqb op 13 then match rest with [x] => node_low3z cs x | _ => None end
        else if Z.eqb op 34 then match rest with [a; ELit off; V] => node_bytespell cs a off V | _ => None end
        else None
    | _ => None
    end.

  (* [comment removed for export] *)
  Definition node_rsbaseB (bc : bctx) (cs : acs) (B : expr) (lo hi : Z) (B' : expr) (d : Z) : option acs :=
    let k := kn cs in
    match xloB bc B, xhiB bc B with
    | Some blo, Some bhi =>
        if (Z.leb 0 (blo + d) && Z.ltb (bhi + d) two64 && expr_vars_lt (nxt cs) B' && respell_okB bc (eaddz B d) B')%bool
        then Some (set_kn cs (map (rs_k B lo hi B' d) k))
        else None
    | _, _ => None
    end.
  Definition node_addzeroB (bc : bctx) (cs : acs) (b : expr) (o : Z) (n : expr) : option acs :=
    let k := kn cs in
    if (expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n && flat_xB bc b o n && kzero_xB bc k b o n)%bool
    then Some (set_kn cs (KZero (SA b o) n :: k)) else None.
  Definition node_addwrB (bc : bctx) (cs : acs) (b : expr) (o : Z) (n : expr) : option acs :=
    let k := kn cs in
    if (expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n && flat_xB bc b o n && kwritable_xB A bc k b o n)%bool
    then Some (set_kn cs (KWr (SA b o) n :: k)) else None.
  Definition node_rsvisB (bc : bctx) (cs : acs) (i : nat) (e' : expr) : option acs :=
    match nth_error (a_vis cs) i with
    | Some (b, n) =>
        if (expr_vars_lt (nxt cs) e' && respell_okB bc b e')%bool
        then Some (ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                       (upd_nth (a_vis cs) i (e', n)) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
        else None
    | None => None
    end.
  Definition node_rscaseB (bc : bctx) (cs : acs) (r : nat) (e a : expr) : option acs :=
    let k := kn cs in
    match xloB bc a, xhiB bc a with
    | Some alo, Some ahi =>
        if (Nat.ltb 0 r && Nat.ltb r 32 && expr_vars_lt (nxt cs) e && Z.leb 0 alo && Z.leb (ahi - alo) 64
            && forallb (fun i => let x := ELit (alo + Z.of_nat i) in respell_okB bc (rep a x (reg cs r)) (rep a x e))
                       (seq 0 (Z.to_nat (ahi - alo + 1))))%bool
        then Some (set_reg cs r e) else None
    | _, _ => None
    end.
  Fixpoint find_byteB (bc : bctx) (k : list kentry) (ab : expr) (off : Z) : option expr :=
    match k with
    | [] => None
    | KWord (SA b o) 1%nat w :: rest =>
        if (expr_eqb b ab && Z.eqb o off)%bool then Some w else find_byteB bc rest ab off
    | KFill (SA b o) L c :: rest =>
        if (expr_eqb b ab && Z.leb o off
            && match xloB bc L with Some lo => Z.ltb (off - o) lo | None => false end)%bool
        then Some (ELit c) else find_byteB bc rest ab off
    | _ :: rest => find_byteB bc rest ab off
    end.
  Definition node_bytespellB (bc : bctx) (cs : acs) (a : expr) (off : Z) (V : expr) : option acs :=
    let k := kn cs in
    let '(ab, ao) := split_lit (eaddz a off) in    (* [comment removed for export] *)
    match find_byteB bc k ab ao with
    | Some w =>
        let w' := extKB bc w in
        if (flat_xB bc ab ao (ELit 1) && lin_ge0B bc [(w', 0)] [(V, 0)] && lin_ge0B bc [(V, 0)] [(w', 0)])%bool
        then Some (set_kn cs (KWord (SA ab ao) 1 V :: k)) else None
    | None => None
    end.
  Definition node_bytecaseB (bc : bctx) (cs : acs) (a : expr) (off : Z) (V atom : expr) : option acs :=
    let k := kn cs in
    let '(ab, ao) := split_lit (eaddz a off) in
    match find_byteB bc k ab ao, xloB bc atom, xhiB bc atom with
    | Some w, Some alo, Some ahi =>
        let w' := extKB bc w in
        if (flat_xB bc ab ao (ELit 1) && expr_vars_lt (nxt cs) V && Z.leb 0 alo && Z.leb (ahi - alo) 64
            && forallb (fun i => let x := ELit (alo + Z.of_nat i) in respell_okB bc (rep atom x w') (rep atom x V))
                       (seq 0 (Z.to_nat (ahi - alo + 1))))%bool
        then Some (set_kn cs (KWord (SA ab ao) 1 V :: k)) else None
    | _, _, _ => None
    end.
  Definition node_rsvalB (bc : bctx) (cs : acs) (b : expr) (o : Z) (e : expr) : option acs :=
    let k := kn cs in
    if (expr_vars_lt (nxt cs) e
        && forallb (fun K => match K with
                             | KWord (SA b' o') w v => if (expr_eqb b' b && Z.eqb o' o)%bool then respell_okB bc v e else true
                             | _ => true
                             end) k)%bool
    then Some (set_kn cs (map (rs_val b o e) k)) else None.
  Definition node_addzero0B (bc : bctx) (cs : acs) (b : expr) (o : Z) (n : expr) : option acs :=
    match xhiB bc n, base_rangeB bc b with
    | Some 0, Some (blo, bhi) =>
        if (expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n && Z.leb 0 (blo + o) && Z.ltb (bhi + o) two64)%bool
        then Some (set_kn cs (KZero (SA b o) n :: kn cs)) else None
    | _, _ => None
    end.
  Definition node_rup3B (bc : bctx) (cs : acs) (x : expr) : option acs :=
    match xhiB bc x with
    | Some h => if (expr_vars_lt (nxt cs) x && Z.ltb h (two64 - 8))%bool then Some (set_kn cs (KRange (rup3 x) 0 7 :: kn cs)) else None
    | None => None
    end.
  Definition node_low3B (bc : bctx) (cs : acs) (x : expr) : option acs :=
    if expr_vars_lt (nxt cs) x then
      match erangeB bc (EAlu ALU_AND x (ELit 7)) with
      | Some (lo, hi) => Some (set_kn cs (KRange (low3 x) (Z.max lo 0) (Z.min hi 7) :: kn cs))
      | None => Some (set_kn cs (KRange (low3 x) 0 7 :: kn cs))
      end
    else None.

  Definition node_lowpB (bc : bctx) (cs : acs) (x : expr) : option acs :=
    if expr_vars_lt (nxt cs) x then
      match lowp_fact x (match erangeB bc (probe_raw x) with Some r => Some r | None => erangeB bc (probe_low3 x) end) with
      | Some K => Some (set_kn cs (K :: kn cs))
      | None => None
      end
    else None.
  Definition node_low3zB (bc : bctx) (cs : acs) (x : expr) : option acs :=
    match xhiB bc x with
    | Some h => if (expr_vars_lt (nxt cs) x && Z.ltb h (two64 - 8))%bool then
                  match low3z_facts x (erangeB bc (EAlu ALU_AND x (ELit 7))) with
                  | Some Ks => Some (set_kn cs (Ks ++ kn cs))
                  | None => None
                  end
                else None
    | None => None
    end.
  Lemma find_byteB_eq : forall allk k ab off, find_byteB (mkbc allk) k ab off = find_byte k allk ab off.
  Proof.
    intros allk k ab off. induction k as [|K rest IH]; [reflexivity|]. cbn [find_byteB find_byte]. rewrite IH, xloB_eqf. reflexivity.
  Qed.
  Lemma find_byteB_feq : forall allk, find_byteB (mkbc allk) = (fun k ab off => find_byte k allk ab off).
  Proof. intros allk. apply functional_extensionality; intros k. apply functional_extensionality; intros ab. apply functional_extensionality; intros off. apply find_byteB_eq. Qed.
  Definition xn (args : list expr) (cs : acs) : option acs :=
    let bc := mkbc (kn cs) in   (* [comment removed for export] *)
    match args with
    | ELit op :: rest =>
        if Z.eqb op 0 then match rest with [B; ELit lo; ELit hi; B'; ELit d] => node_rsbaseB bc cs B lo hi B' d | _ => None end
        else if Z.eqb op 1 then match rest with [b; ELit o; n] => node_addzeroB bc cs b o n | _ => None end
        else if Z.eqb op 2 then match rest with [b; ELit o; n] => node_addwrB bc cs b o n | _ => None end
        else if Z.eqb op 4 then match rest with [ELit i; e'] => node_rsvisB bc cs (Z.to_nat i) e' | _ => None end
        else if Z.eqb op 5 then match rest with [ELit r; e; a] => node_rscaseB bc cs (Z.to_nat r) e a | _ => None end
        else if Z.eqb op 6 then match rest with [ELit a; ELit n] => Some (set_kn cs (kimg_cut (kn cs) a n)) | _ => None end
        else if Z.eqb op 7 then match rest with [x] => node_low3B bc cs x | _ => None end
        else if Z.eqb op 8 then match rest with [x] => node_rup3B bc cs x | _ => None end
        else if Z.eqb op 9 then match rest with [a; ELit off; V; atom] => node_bytecaseB bc cs a off V atom | _ => None end
        else if Z.eqb op 10 then match rest with [b; ELit o; n] => node_addzero0B bc cs b o n | _ => None end
        else if Z.eqb op 11 then match rest with [b; ELit o; e] => node_rsvalB bc cs b o e | _ => None end
        else if Z.eqb op 12 then match rest with [x] => node_lowpB bc cs x | _ => None end
        else if Z.eqb op 13 then match rest with [x] => node_low3zB bc cs x | _ => None end
        else if Z.eqb op 34 then match rest with [a; ELit off; V] => node_bytespellB bc cs a off V | _ => None end
        else None
    | _ => None
    end.

  Lemma xn_eq : forall args cs, xn args cs = xn_ref args cs.
  Proof.
    intros args cs. unfold xn, xn_ref. cbv zeta.
    unfold node_rsbaseB, node_addzeroB, node_addwrB, node_rsvisB, node_rscaseB, node_bytespellB, node_bytecaseB, node_rsvalB, node_addzero0B, node_rup3B, node_low3B, node_lowpB, node_lowp, node_low3zB, node_low3z,
           node_rsbase, node_addzero, node_addwr, node_rsvis, node_rscase, node_bytespell, node_bytecase, node_rsval, node_addzero0, node_rup3, node_low3.
    rewrite ?respell_okB_eqf, ?xloB_eqf, ?xhiB_eqf, ?flat_xB_eqf, ?kzero_xB_eqf, ?kwritable_xB_eqf, ?extKB_eqf, ?lin_ge0B_eqf, ?base_rangeB_eqf, ?erangeB_eqf.
    rewrite ?find_byteB_feq. reflexivity.
  Qed.
End WithA.
End CAN.
