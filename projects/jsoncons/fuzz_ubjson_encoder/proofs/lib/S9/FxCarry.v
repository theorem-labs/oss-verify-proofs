(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From Stdlib Require Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import FxBlock.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Module CARF.
Import AX2. Import AX2B.

Notation expr_eqbF := BLKF.expr_eqbF.
Ltac eF := rewrite ?BLKF.expr_eqbF_eq in *.

Definition is_kdisjb (K : kentry) : bool := match K with KDisj _ _ _ _ => true | _ => false end.
Definition is_kwrb (K : kentry) : bool := match K with KWr _ _ => true | _ => false end.
Record bext := BE { be_kd : list kentry; be_kw : list kentry }.
Definition mk_bext (bc : bctx) : bext := BE (List.filter is_kdisjb (bc_fk bc)) (List.filter is_kwrb (bc_fk bc)).

Local Open Scope Z_scope.

Fixpoint existsbF {T : Type} (f : T -> bool) (l : list T) : bool :=
  match l with [] => false | x :: r => if f x then true else existsbF f r end.

Record bx := BX { bx_b : expr; bx_l : lin; bx_nw : bool }.
Definition mk_bx (bc : bctx) (b : expr) : bx := BX b (lin_of b) (lin_nowrapRB bc b).
Definition bx_get (bc : bctx) (o : option bx) (b : expr) : lin * bool :=
  match o with
  | Some x => if expr_eqbF (bx_b x) b then (bx_l x, bx_nw x) else (lin_of b, lin_nowrapRB bc b)
  | None => (lin_of b, lin_nowrapRB bc b)
  end.

Definition lin_apartF (bc : bctx) (i1 i2 : option bx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if shares_var b1 b2 then
    let '(l1, nw1) := bx_get bc i1 b1 in
    if nw1 then
      let '(l2, nw2) := bx_get bc i2 b2 in
      if nw2 then lin_testB bc (fst l2 + k2 - fst l1 - k1) (lsub_e (snd l2) (snd l1)) (fun lo hi => if Z.leb n1 lo then true else Z.leb hi (- n2))
      else false
    else false
  else false.

Definition ranges_apart_pcF (bc : bctx) (i1 i2 : option bx) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
           (br2 : option (Z * Z)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, br2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              if Z.leb (hi1 + k1 + m1) (lo2 + k2) then true else Z.leb (hi2 + k2 + m2) (lo1 + k1)
          | _, _ => false
          end) then true
      else if lin_apartF bc i1 i2 b1 k1 m1 b2 k2 m2 then true
      else in_sidesB bc (sp_D sp) b2 k2 m2
  | _, _ => ranges_apart_pcB bc sp b1 k1 n1 br2 b2 k2 n2
  end.

Definition prune1pcKF (bc : bctx) (i1 i2 : option bx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
  (br2 : option (Z * Z)) : pk_res :=
  let k := a_off wa in
  let wb := a_base wa in
  let zfK (mk : saddr -> expr -> kentry) (kb : expr) (kk : Z) (len : expr) :=
    if same then
      match len with
      | ELit l0 => PRepl (ktrim mk kb kk l0 k w)
      | _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl (kcutB bc mk wb k (elen w) kb kk len)
      end
    else if ranges_apart_pcF bc i1 i2 sp wb k (elen w) br2 kb kk len then PKeep
    else PRepl (kcutB bc mk wb k (elen w) kb kk len) in
  match K with
  | KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ => PKeep
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
      if same then (if Z.leb (kk + Z.of_nat w') k then PKeep else if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl (kword_cut kb kk w' v k w))
      else if ranges_apart_pcF bc i1 i2 sp wb k (elen w) br2 kb kk (elen w') then PKeep
      else if (if Nat.eqb w 1 then if Nat.eqb w' 1 then expr_eqb wv v else false else false) then PKeep
      else PRepl []
  | KBlob (SA kb kk) len bk =>
      if same then
        match len with
        | ELit l0 => let l := zmod64 l0 in
                     if Z.leb (kk + l) k then PKeep else if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl []
        | _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl []
        end
      else if ranges_apart_pcF bc i1 i2 sp wb k (elen w) br2 kb kk len then PKeep else PRepl []
  end.

Definition prune1pBF (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  let k := a_off wa in
  let diffbase (ka : saddr) (kl : expr) :=
    let apart := ranges_apart_pB bc sp (a_base wa) k (elen w) (a_base ka) (a_off ka) kl in
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
         then ([K], [], hints) else (kword_cut kb kk w' v k w, [], hints))
      else if ranges_apart_pB bc sp (a_base wa) k (elen w) kb kk (elen w') then ([K], [], hints)
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool
      then ([K], [], hints)
      else diffbase (SA kb kk) (elen w')
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then
        match len with
        | ELit l0 =>
            let l := zmod64 l0 in
            (if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool
             then ([K], [], hints) else ([], [], hints))
        | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints) else ([], [], hints)
        end
      else diffbase (SA kb kk) len
  end.

Definition prune1pcBF (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
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
  | KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ | KImg _ _ => prune1pBF bc sp wa w wv K hints
  | KZero (SA kb kk) len =>
      if expr_eqb kb (a_base wa) then prune1pBF bc sp wa w wv K hints
      else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kzero_cutB bc (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KFill (SA kb kk) len c =>
      if expr_eqb kb (a_base wa) then prune1pBF bc sp wa w wv K hints
      else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kfill_cutB bc c (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KUnk (SA kb kk) len =>
      if expr_eqb kb (a_base wa) then prune1pBF bc sp wa w wv K hints
      else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kunk_cutB bc (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then prune1pBF bc sp wa w wv K hints
      else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk (elen w') then ([K], [], hints)
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool
      then ([K], [], hints)
      else diffbase (SA kb kk) (elen w')
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then prune1pBF bc sp wa w wv K hints
      else diffbase (SA kb kk) len
  end.

Definition g1cBF (bc : bctx) (sx : stx) (K : kentry) : list kentry :=
  fst (fst (prune1pcBF bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K [] (obrB bc K))).

Definition i0 : PrimInt63.int := Uint63.of_Z 0.
Definition i1 : PrimInt63.int := Uint63.of_Z 1.
Definition m61 : PrimInt63.int := Uint63.of_Z (2 ^ 61).
Definition B59 : PrimInt63.int := Uint63.of_Z (2 ^ 59).

Fixpoint p2iS (p : positive) (acc pw : PrimInt63.int) : option PrimInt63.int :=
  if PrimInt63.ltb m61 pw then None else
  match p with
  | xH => Some (PrimInt63.add acc pw)
  | xO q => p2iS q acc (PrimInt63.add pw pw)
  | xI q => p2iS q (PrimInt63.add acc pw) (PrimInt63.add pw pw)
  end.

Module P2Q.
Import PrimInt63.
Local Notation toZ := Uint63Axioms.to_Z.
Lemma m61_val : toZ m61 = 2 ^ 61. Proof. reflexivity. Qed.
Lemma wB_val : Uint63Axioms.wB = 2 ^ 63. Proof. reflexivity. Qed.
Definition pfin (pw r : PrimInt63.int) : option PrimInt63.int :=
  if PrimInt63.ltb 0%uint63 pw then (if PrimInt63.leb pw m61 then Some r else None) else None.
Fixpoint p2iQ4 (p : positive) (acc pw : PrimInt63.int) : option PrimInt63.int :=
  match p with
  | xH => pfin pw (PrimInt63.add acc pw)
  | xO q1 =>
      match q1 with
      | xH => pfin (PrimInt63.lsl pw 1%uint63) (PrimInt63.add acc (PrimInt63.mul pw 2%uint63))
      | xO q2 =>
          match q2 with
          | xH => pfin (PrimInt63.lsl pw 2%uint63) (PrimInt63.add acc (PrimInt63.mul pw 4%uint63))
          | xO q3 =>
              match q3 with
              | xH => pfin (PrimInt63.lsl pw 3%uint63) (PrimInt63.add acc (PrimInt63.mul pw 8%uint63))
              | xO q4 =>
                  p2iQ4 q4 acc (PrimInt63.lsl pw 4%uint63)
              | xI q4 =>
                  p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 8%uint63)) (PrimInt63.lsl pw 4%uint63)
              end
          | xI q3 =>
              match q3 with
              | xH => pfin (PrimInt63.lsl pw 3%uint63) (PrimInt63.add acc (PrimInt63.mul pw 12%uint63))
              | xO q4 =>
                  p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 4%uint63)) (PrimInt63.lsl pw 4%uint63)
              | xI q4 =>
                  p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 12%uint63)) (PrimInt63.lsl pw 4%uint63)
              end
          end
      | xI q2 =>
          match q2 with
          | xH => pfin (PrimInt63.lsl pw 2%uint63) (PrimInt63.add acc (PrimInt63.mul pw 6%uint63))
          | xO q3 =>
              match q3 with
              | xH => pfin (PrimInt63.lsl pw 3%uint63) (PrimInt63.add acc (PrimInt63.mul pw 10%uint63))
              | xO q4 =>
                  p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 2%uint63)) (PrimInt63.lsl pw 4%uint63)
              | xI q4 =>
                  p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 10%uint63)) (PrimInt63.lsl pw 4%uint63)
              end
          | xI q3 =>
              match q3 with
              | xH => pfin (PrimInt63.lsl pw 3%uint63) (PrimInt63.add acc (PrimInt63.mul pw 14%uint63))
              | xO q4 =>
                  p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 6%uint63)) (PrimInt63.lsl pw 4%uint63)
              | xI q4 =>
                  p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 14%uint63)) (PrimInt63.lsl pw 4%uint63)
              end
          end
      end
  | xI q1 =>
      match q1 with
      | xH => pfin (PrimInt63.lsl pw 1%uint63) (PrimInt63.add acc (PrimInt63.mul pw 3%uint63))
      | xO q2 =>
          match q2 with
          | xH => pfin (PrimInt63.lsl pw 2%uint63) (PrimInt63.add acc (PrimInt63.mul pw 5%uint63))
          | xO q3 =>
              match q3 with
              | xH => pfin (PrimInt63.lsl pw 3%uint63) (PrimInt63.add acc (PrimInt63.mul pw 9%uint63))
              | xO q4 =>
                  p2iQ4 q4 (PrimInt63.add acc pw) (PrimInt63.lsl pw 4%uint63)
              | xI q4 =>
                  p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 9%uint63)) (PrimInt63.lsl pw 4%uint63)
              end
          | xI q3 =>
              match q3 with
              | xH => pfin (PrimInt63.lsl pw 3%uint63) (PrimInt63.add acc (PrimInt63.mul pw 13%uint63))
              | xO q4 =>
                  p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 5%uint63)) (PrimInt63.lsl pw 4%uint63)
              | xI q4 =>
                  p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 13%uint63)) (PrimInt63.lsl pw 4%uint63)
              end
          end
      | xI q2 =>
          match q2 with
          | xH => pfin (PrimInt63.lsl pw 2%uint63) (PrimInt63.add acc (PrimInt63.mul pw 7%uint63))
          | xO q3 =>
              match q3 with
              | xH => pfin (PrimInt63.lsl pw 3%uint63) (PrimInt63.add acc (PrimInt63.mul pw 11%uint63))
              | xO q4 =>
                  p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 3%uint63)) (PrimInt63.lsl pw 4%uint63)
              | xI q4 =>
                  p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 11%uint63)) (PrimInt63.lsl pw 4%uint63)
              end
          | xI q3 =>
              match q3 with
              | xH => pfin (PrimInt63.lsl pw 3%uint63) (PrimInt63.add acc (PrimInt63.mul pw 15%uint63))
              | xO q4 =>
                  p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 7%uint63)) (PrimInt63.lsl pw 4%uint63)
              | xI q4 =>
                  p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 15%uint63)) (PrimInt63.lsl pw 4%uint63)
              end
          end
      end
  end.

Lemma pow2_mod_pos : forall t, 0 <= t -> 0 < 2 ^ t mod 2 ^ 63 -> t < 63.
Proof.
  intros t Ht H. destruct (Z.lt_ge_cases t 63) as [L|G]; [exact L|exfalso].
  replace t with (63 + (t - 63)) in H by lia. rewrite Z.pow_add_r in H by lia.
  rewrite Z.mul_comm, Z.mod_mul in H by lia. lia.
Qed.
Lemma pfin_spec : forall pw r x s A, 0 <= s -> toZ pw = 2 ^ s mod 2 ^ 63 -> toZ r = A mod 2 ^ 63 -> 0 <= A < 2 ^ (s + 1) ->
  pfin pw r = Some x -> toZ x = A /\ A < 2 ^ 62.
Proof.
  intros pw r x s A Hs Hpw Hr HA H. unfold pfin in H.
  destruct (PrimInt63.ltb _ pw) eqn:E1; [|discriminate]. destruct (PrimInt63.leb pw m61) eqn:E2; [|discriminate].
  injection H as <-. apply Uint63Axioms.ltb_spec in E1. apply Uint63Axioms.leb_spec in E2. rewrite m61_val in E2.
  change (toZ 0%uint63) with 0 in E1. rewrite Hpw in E1, E2.
  pose proof (pow2_mod_pos s Hs E1) as L. rewrite Z.mod_small in E2 by (split; [apply Z.pow_nonneg; lia|apply Z.pow_lt_mono_r; lia]).
  assert (s <= 61) by (apply (Z.pow_le_mono_r_iff 2); lia).
  assert (2 ^ (s + 1) <= 2 ^ 62) by (apply Z.pow_le_mono_r; lia).
  rewrite Hr, Z.mod_small by lia. lia.
Qed.
Lemma lsl_inv : forall pw s j J, 0 <= s -> toZ pw = 2 ^ s mod 2 ^ 63 -> toZ j = J -> 0 <= J ->
  toZ (PrimInt63.lsl pw j) = 2 ^ (s + J) mod 2 ^ 63.
Proof.
  intros pw s j J Hs Hpw Hj HJ. rewrite Uint63Axioms.lsl_spec, wB_val, Hpw, Hj, Z.mul_mod_idemp_l by lia.
  rewrite Z.pow_add_r by lia. reflexivity.
Qed.
Lemma addmul_inv : forall acc pw c s A C, toZ pw = 2 ^ s mod 2 ^ 63 -> toZ acc = A mod 2 ^ 63 -> toZ c = C ->
  toZ (PrimInt63.add acc (PrimInt63.mul pw c)) = (A + 2 ^ s * C) mod 2 ^ 63.
Proof.
  intros acc pw c s A C Hpw Ha Hc. rewrite Uint63Axioms.add_spec, Uint63Axioms.mul_spec, wB_val, Hpw, Ha, Hc.
  rewrite Z.mul_mod_idemp_l, Z.add_mod_idemp_l, Z.add_mod_idemp_r by lia. reflexivity.
Qed.
Lemma add_inv : forall acc pw s A, toZ pw = 2 ^ s mod 2 ^ 63 -> toZ acc = A mod 2 ^ 63 ->
  toZ (PrimInt63.add acc pw) = (A + 2 ^ s * 1) mod 2 ^ 63.
Proof.
  intros acc pw s A Hpw Ha. rewrite Uint63Axioms.add_spec, wB_val, Hpw, Ha.
  rewrite Z.add_mod_idemp_l, Z.add_mod_idemp_r, Z.mul_1_r by lia. reflexivity.
Qed.
Lemma acc_inv0 : forall acc s A, toZ acc = A mod 2 ^ 63 -> toZ acc = (A + 2 ^ s * 0) mod 2 ^ 63.
Proof. intros acc s A H. rewrite Z.mul_0_r, Z.add_0_r. exact H. Qed.
Ltac posfacts p := lazymatch p with
  | xI ?q => pose proof (Pos2Z.inj_xI q); posfacts q
  | xO ?q => pose proof (Pos2Z.inj_xO q); posfacts q
  | _ => idtac end.
Lemma p2iQ4_spec : forall n p acc pw r s A, (Pos.size_nat p <= n)%nat -> 0 <= s -> toZ pw = 2 ^ s mod 2 ^ 63 -> toZ acc = A mod 2 ^ 63 -> 0 <= A < 2 ^ s ->
  p2iQ4 p acc pw = Some r -> toZ r = A + 2 ^ s * Zpos p /\ A + 2 ^ s * Zpos p < 2 ^ 62.
Proof.
  induction n as [|n IH]; intros p acc pw r s A Hn Hs Hpw Ha HA H; [destruct p; cbn in Hn; lia|].
  assert (P0 : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  destruct p as [[[[q|q|]|[q|q|]|]|[[q|q|]|[q|q|]|]|]|[[[q|q|]|[q|q|]|]|[[q|q|]|[q|q|]|]|]|]; cbn [p2iQ4] in H;
  lazymatch type of H with
  | p2iQ4 ?q ?acc' (PrimInt63.lsl _ ?j) = _ =>

       let C := lazymatch acc' with
                | PrimInt63.add _ (PrimInt63.mul _ ?c) => eval vm_compute in (toZ c)
                | PrimInt63.add _ _ => constr:(1)
                | _ => constr:(0)
                end in
       let Hacc := lazymatch acc' with
                | PrimInt63.add _ (PrimInt63.mul _ ?c) => constr:(addmul_inv acc pw c s A C Hpw Ha eq_refl)
                | PrimInt63.add _ _ => constr:(add_inv acc pw s A Hpw Ha)
                | _ => constr:(acc_inv0 acc s A Ha)
                end in
       assert (Hn' : (Pos.size_nat q <= n)%nat) by (cbn [Pos.size_nat] in Hn; lia);
       pose proof (IH q acc' _ r (s + 4) (A + 2 ^ s * C) Hn' ltac:(lia) (lsl_inv pw s j 4 Hs Hpw eq_refl ltac:(lia)) Hacc) as R;
       rewrite Z.pow_add_r in R by lia; change (2 ^ 4) with 16 in R;
       assert (HA' : 0 <= A + 2 ^ s * C < 2 ^ s * 16) by lia;
       specialize (R HA' H); destruct R as [R1 R2];
       lazymatch goal with |- _ = _ + _ * Z.pos ?p /\ _ =>
         posfacts p;
         assert (E : Z.pos p = 16 * Z.pos q + C) by lia; rewrite E
       end;
       (split; [rewrite R1; ring|eapply Z.le_lt_trans; [|exact R2]; apply Z.eq_le_incl; ring])
  | pfin pw (PrimInt63.add acc pw) = _ =>
       exact (pfin_spec pw _ r s (A + 2 ^ s * 1) Hs Hpw (add_inv acc pw s A Hpw Ha) ltac:(rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia) H)
  | pfin (PrimInt63.lsl pw ?j) (PrimInt63.add acc (PrimInt63.mul pw ?c)) = _ =>
       let J := eval vm_compute in (toZ j) in
       let C := eval vm_compute in (toZ c) in
       let T := eval vm_compute in (2 ^ (J + 1)) in
       lazymatch goal with |- _ = _ + _ * Z.pos ?p /\ _ => change (Z.pos p) with C end;
       refine (pfin_spec (PrimInt63.lsl pw j) _ r (s + J) (A + 2 ^ s * C) ltac:(lia) (lsl_inv pw s j J Hs Hpw eq_refl ltac:(lia)) (addmul_inv acc pw c s A C Hpw Ha eq_refl) _ H);
       replace (s + J + 1) with (s + (J + 1)) by ring; rewrite Z.pow_add_r by lia; change (2 ^ (J + 1)) with T; lia
  end.
Qed.
Lemma p2iQ4_val : forall p r, p2iQ4 p i0 i1 = Some r -> toZ r = Zpos p /\ Zpos p < 2 ^ 62.
Proof.
  intros p r H. pose proof (p2iQ4_spec (Pos.size_nat p) p i0 i1 r 0 0 (le_n _) (Z.le_refl 0) eq_refl eq_refl ltac:(lia) H) as R.
  rewrite Z.pow_0_r in R. lia.
Qed.
End P2Q.

Definition z2l (z : Z) : option PrimInt63.int :=
  match z with
  | Z0 => Some i0
  | Zpos p => match P2Q.p2iQ4 p i0 i1 with Some r => if PrimInt63.ltb r B59 then Some r else None | None => None end
  | Zneg _ => None
  end.

Definition z2b (z : Z) : option PrimInt63.int :=
  match z with
  | Z0 => Some B59
  | Zpos p => match P2Q.p2iQ4 p i0 i1 with Some r => if PrimInt63.ltb r B59 then Some (PrimInt63.add B59 r) else None | None => None end
  | Zneg p => match P2Q.p2iQ4 p i0 i1 with Some r => if PrimInt63.leb r B59 then Some (PrimInt63.sub B59 r) else None | None => None end
  end.
Definition iv_of (k m : Z) : option (PrimInt63.int * PrimInt63.int) :=
  match z2b k with Some a => match z2l m with Some l => Some (a, PrimInt63.add a l) | None => None end | None => None end.

Definition ent_iv (K : kentry) : option (PrimInt63.int * PrimInt63.int) :=
  match K with
  | KWord (SA _ kk) w' _ => iv_of kk (Z.of_nat w')
  | KZero (SA _ kk) (ELit l0) | KFill (SA _ kk) (ELit l0) _ | KUnk (SA _ kk) (ELit l0) =>
      match l0 with Zpos _ => iv_of kk l0 | _ => None end
  | KBlob (SA _ kk) (ELit l0) _ => iv_of kk l0
  | KImg lo hi => if Z.ltb lo hi then match z2b lo, z2b hi with Some a, Some b => Some (a, b) | _, _ => None end else None
  | _ => None
  end.

Lemma wB_val : Uint63Axioms.wB = 2 ^ 63. Proof. reflexivity. Qed.
Lemma add_nov : forall x y, Uint63Axioms.to_Z x + Uint63Axioms.to_Z y < 2 ^ 63 ->
  Uint63Axioms.to_Z (PrimInt63.add x y) = Uint63Axioms.to_Z x + Uint63Axioms.to_Z y.
Proof.
  intros x y H. rewrite Uint63Axioms.add_spec, wB_val.
  pose proof (Uint63.to_Z_bounded x). pose proof (Uint63.to_Z_bounded y). rewrite wB_val in *.
  apply Z.mod_small. lia.
Qed.
Lemma sub_nov : forall x y, Uint63Axioms.to_Z y <= Uint63Axioms.to_Z x ->
  Uint63Axioms.to_Z (PrimInt63.sub x y) = Uint63Axioms.to_Z x - Uint63Axioms.to_Z y.
Proof.
  intros x y H. rewrite Uint63Axioms.sub_spec, wB_val.
  pose proof (Uint63.to_Z_bounded x). pose proof (Uint63.to_Z_bounded y). rewrite wB_val in *.
  apply Z.mod_small. lia.
Qed.
Lemma i0_val : Uint63Axioms.to_Z i0 = 0. Proof. reflexivity. Qed.
Lemma i1_val : Uint63Axioms.to_Z i1 = 1. Proof. reflexivity. Qed.
Lemma m61_val : Uint63Axioms.to_Z m61 = 2 ^ 61. Proof. reflexivity. Qed.
Lemma B59_val : Uint63Axioms.to_Z B59 = 2 ^ 59. Proof. reflexivity. Qed.
Lemma ileb_le : forall x y, PrimInt63.leb x y = true -> Uint63Axioms.to_Z x <= Uint63Axioms.to_Z y.
Proof. intros x y H. apply Uint63Axioms.leb_spec. exact H. Qed.
Lemma iltb_lt : forall x y, PrimInt63.ltb x y = true -> Uint63Axioms.to_Z x < Uint63Axioms.to_Z y.
Proof. intros x y H. apply Uint63Axioms.ltb_spec. exact H. Qed.
Lemma p2iS_spec : forall p acc pw r,
  0 <= Uint63Axioms.to_Z acc < Uint63Axioms.to_Z pw ->
  p2iS p acc pw = Some r -> Uint63Axioms.to_Z r = Uint63Axioms.to_Z acc + Uint63Axioms.to_Z pw * Zpos p.
Proof.
  induction p as [q IH|q IH|]; intros acc pw r Ha H; cbn [p2iS] in H;
    (destruct (PrimInt63.ltb m61 pw) eqn:El; [discriminate|]);
    (assert (Q : Uint63Axioms.to_Z pw <= 2 ^ 61) by (rewrite <- m61_val; destruct (Z.le_gt_cases (Uint63Axioms.to_Z pw) (Uint63Axioms.to_Z m61)) as [X|X]; [exact X|];
        apply Uint63Axioms.ltb_spec in X; congruence));
    (assert (E2 : Uint63Axioms.to_Z (PrimInt63.add pw pw) = Uint63Axioms.to_Z pw + Uint63Axioms.to_Z pw) by (apply add_nov; lia)).
  - assert (E1 : Uint63Axioms.to_Z (PrimInt63.add acc pw) = Uint63Axioms.to_Z acc + Uint63Axioms.to_Z pw) by (apply add_nov; lia).
    apply IH in H; [|rewrite E1, E2; lia]. rewrite H, E1, E2, Pos2Z.inj_xI. ring.
  - apply IH in H; [|rewrite E2; lia]. rewrite H, E2, Pos2Z.inj_xO. ring.
  - injection H as <-. rewrite add_nov by lia. lia.
Qed.
Lemma p2iS_val : forall p r, p2iS p i0 i1 = Some r -> Uint63Axioms.to_Z r = Zpos p.
Proof. intros p r H. rewrite (p2iS_spec p i0 i1 r); [rewrite i0_val, i1_val; lia|rewrite i0_val, i1_val; lia|exact H]. Qed.
Lemma z2l_val : forall z l, z2l z = Some l -> Uint63Axioms.to_Z l = z /\ 0 <= z < 2 ^ 59.
Proof.
  intros z l H. destruct z as [|p|p]; cbn [z2l] in H; [injection H as <-; rewrite i0_val; lia| |discriminate].
  destruct (P2Q.p2iQ4 p i0 i1) as [r|] eqn:E; [|discriminate]. destruct (PrimInt63.ltb r B59) eqn:EB; [|discriminate].
  injection H as <-. apply P2Q.p2iQ4_val in E. destruct E as [E _]. apply iltb_lt in EB. rewrite B59_val in EB. lia.
Qed.
Lemma z2b_val : forall z a, z2b z = Some a -> Uint63Axioms.to_Z a = z + 2 ^ 59 /\ - 2 ^ 59 <= z < 2 ^ 59.
Proof.
  intros z a H. destruct z as [|p|p]; cbn [z2b] in H.
  - injection H as <-. rewrite B59_val. lia.
  - destruct (P2Q.p2iQ4 p i0 i1) as [r|] eqn:E; [|discriminate]. destruct (PrimInt63.ltb r B59) eqn:EB; [|discriminate].
    injection H as <-. apply P2Q.p2iQ4_val in E. destruct E as [E _]. apply iltb_lt in EB. rewrite B59_val in EB.
    rewrite add_nov by (rewrite B59_val; lia). rewrite B59_val. lia.
  - destruct (P2Q.p2iQ4 p i0 i1) as [r|] eqn:E; [|discriminate]. destruct (PrimInt63.leb r B59) eqn:EB; [|discriminate].
    injection H as <-. apply P2Q.p2iQ4_val in E. destruct E as [E _]. apply ileb_le in EB. rewrite B59_val in EB.
    rewrite sub_nov by (rewrite B59_val; lia). rewrite B59_val. lia.
Qed.
Lemma iv_of_val : forall k m a e, iv_of k m = Some (a, e) ->
  Uint63Axioms.to_Z a = k + 2 ^ 59 /\ Uint63Axioms.to_Z e = k + m + 2 ^ 59 /\ 0 <= m < 2 ^ 59.
Proof.
  intros k m a e H. unfold iv_of in H. destruct (z2b k) as [a'|] eqn:Ea; [|discriminate]. destruct (z2l m) as [l|] eqn:El; [|discriminate].
  injection H as <- <-. apply z2b_val in Ea. apply z2l_val in El. destruct Ea as [Ea1 Ea2]. destruct El as [El1 El2].
  split; [exact Ea1|]. split; [|exact El2]. rewrite add_nov by lia. lia.
Qed.
Lemma iv_of_kb : forall k m a e, iv_of k m = Some (a, e) -> - 2 ^ 59 <= k < 2 ^ 59.
Proof.
  intros k m a e H. unfold iv_of in H. destruct (z2b k) as [a'|] eqn:Ea; [|discriminate]. apply z2b_val in Ea. apply Ea.
Qed.

Definition two62 : Z := 2 ^ 62.
Definition z2i (z : Z) : option PrimInt63.int :=
  match z with Z0 => Some i0 | Zpos p => P2Q.p2iQ4 p i0 i1 | Zneg _ => None end.
Definition ab2i (o : option (Z * Z)) : option (PrimInt63.int * PrimInt63.int) :=
  match o with Some (A, B) => match z2i A, z2i B with Some a, Some b => Some (a, b) | _, _ => None end | None => None end.
Definition rng2l (o : option (Z * Z)) : option (PrimInt63.int * PrimInt63.int) :=
  match o with
  | Some (lo, hi) => match z2l lo with Some a => match z2l hi with Some b => Some (a, b) | None => None end | None => None end
  | None => None
  end.

Definition mk_abj (rng : option (Z * Z)) (iv : option (PrimInt63.int * PrimInt63.int)) : option (PrimInt63.int * PrimInt63.int) :=
  match iv with
  | Some (c, d) => match rng2l rng with Some (lo1, hi1) => Some (PrimInt63.add hi1 d, PrimInt63.add lo1 c) | None => None end
  | None => None
  end.
Record sxi := SXI { si_sx : stx; si_ab : option (Z * Z); si_bx : option bx; si_ke : Z;
                    si_iv : option (PrimInt63.int * PrimInt63.int);
                    si_abj : option (PrimInt63.int * PrimInt63.int); si_eabj : option (PrimInt63.int * PrimInt63.int); si_a2j : option (PrimInt63.int * PrimInt63.int) }.
Definition xget (X : ptree (option bx)) (bid : positive) : option bx :=
  match pt_get X bid with Some o => o | None => None end.
Definition mk_sxi (X : ptree (option bx)) (sx : stx) : sxi :=
  let ab := match sp_rng (sx_sp sx) with
            | Some (lo1, hi1) => Some (hi1 + a_off (sx_a sx) + sx_m1 sx, lo1 + a_off (sx_a sx))
            | None => None
            end in
  let iv := iv_of (a_off (sx_a sx)) (Z.of_nat (sx_w sx)) in
  let abj := mk_abj (sp_rng (sx_sp sx)) iv in
  SXI sx ab (xget X (sx_bid sx)) (a_off (sx_a sx) + Z.of_nat (sx_w sx)) iv abj
      (if obr_eqb (sx_br sx) (sp_rng (sx_sp sx)) then match abj with Some (A, B) => Some (B, A) | None => None end else None)
      (match sp_h1 (sx_sp sx) with
       | Some h1 => if Z.eqb h1 (Z.of_nat (sx_w sx)) then abj else None
       | None => None
       end).

Definition gq_of (g : gval) : option (Z * Z) :=
  match g with (b, obr, (glo, ghi)) => match obr with Some (lo2, hi2) => Some (glo + lo2, ghi + hi2) | None => None end end.
Definition verdictF (si : sxi) (b : positive) (gq : option (Z * Z)) : bool :=
  if Pos.eqb b (sx_bid (si_sx si)) then false else
  match si_ab si, gq with
  | Some (A, B), Some (GL, GH) => if Z.leb A GL then true else Z.leb GH B
  | _, _ => false
  end.

Record gxi := GXI { gx_b : expr; gx_bx : option bx }.
Definition linV (bc : bctx) (si : sxi) (b : positive) (obr : option (Z * Z)) (glo ghi : Z) (gx : option gxi) : bool :=
  match gx with
  | Some x =>
      if Pos.eqb b (sx_bid (si_sx si)) then false else
      if (if Z.leb 0 (ghi - glo) then Z.ltb (ghi - glo) two63z else false) then
        let sx := si_sx si in
        ranges_apart_pcF bc (si_bx si) (gx_bx x) (sx_sp sx) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx)) obr (gx_b x) glo (ELit (ghi - glo))
      else false
  | None => false
  end.
Fixpoint mk_flF (bc : bctx) (b : positive) (gq : option (Z * Z)) (obr : option (Z * Z)) (glo ghi : Z) (gx : option gxi) (sis : list sxi) : list (sxi * list sxi) :=
  match sis with
  | si :: srest => if verdictF si b gq then mk_flF bc b gq obr glo ghi gx srest
                   else if linV bc si b obr glo ghi gx then mk_flF bc b gq obr glo ghi gx srest
                   else (si, srest) :: mk_flF bc b gq obr glo ghi gx srest
  | [] => []
  end.
Definition is_litb (e : expr) : bool := match e with ELit _ => true | _ => false end.
Definition gflF : Type := (gval * option gxi * list (sxi * list sxi))%type.
Definition mk_glF (bc : bctx) (info : ptree binfo) (X : ptree (option bx)) (bnds : gtab) (sis : list sxi) : ptree gflF :=
  pt_map (fun g : gval =>
            match g with
            | (b, obr, (glo, ghi)) =>
                let gx := match pt_get info b with
                          | Some bi => if is_litb (bi_base bi) then None else Some (GXI (bi_base bi) (xget X b))
                          | None => None
                          end in
                (g, gx, mk_flF bc b (gq_of g) obr glo ghi gx sis)
            end) bnds.

Definition member_ok (K : kentry) (g : gval) (gx : option gxi) : bool :=
  match gx with
  | None => true
  | Some x =>
      match g, kdescr K with
      | (_, _, (glo, ghi)), Some (kb, kk, Some m) =>
          if expr_eqb kb (gx_b x) then (if Z.leb glo kk then Z.leb (kk + m) ghi else false) else false
      | _, _ => false
      end
  end.

Definition g1cF (bc : bctx) (si : sxi) (K : kentry) : list kentry :=
  match K with
  | KImg lo hi =>
      match a_base (sx_a (si_sx si)), si_ab si with
      | ELit 0, _ => g1cBF bc (si_sx si) K
      | _, Some (A, B) =>
          if (if (let d := hi - lo in if Z.leb 0 d then Z.ltb d two64 else false) then (if Z.leb A lo then true else Z.leb hi B) else false)
          then [K] else g1cBF bc (si_sx si) K
      | _, None => g1cBF bc (si_sx si) K
      end
  | _ => g1cBF bc (si_sx si) K
  end.
Fixpoint chain_slowF (bc : bctx) (sis : list sxi) (l : list kentry) : list kentry :=
  match sis with
  | [] => l
  | si :: rest => chain_slowF bc rest (flat_map (g1cF bc si) l)
  end.
Fixpoint chainK2F (bc : bctx) (xo : option bx) (sis : list sxi) (K : kentry) (okb : option expr) (same_of : positive -> bool)
         (br2 : option (Z * Z)) : list kentry :=
  match sis with
  | [] => [K]
  | si :: rest =>
      let sx := si_sx si in
      match prune1pcKF bc (si_bx si) xo (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
      | PKeep => chainK2F bc xo rest K okb same_of br2
      | PRepl l =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2F bc xo rest K' okb same_of br2 else chain_slowF bc rest [K']
                                  | None => chain_slowF bc rest [K']
                                  end) l
          | None => chain_slowF bc rest l
          end
      end
  end.

Fixpoint chainKFF (bc : bctx) (xo : option bx) (fl : list (sxi * list sxi)) (K : kentry) (okb : option expr) (same_of : positive -> bool)
         (br2 : option (Z * Z)) : list kentry :=
  match fl with
  | [] => [K]
  | (si, rest) :: fl' =>
      let sx := si_sx si in
      match prune1pcKF bc (si_bx si) xo (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
      | PKeep => chainKFF bc xo fl' K okb same_of br2
      | PRepl l =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2F bc xo rest K' okb same_of br2 else chain_slowF bc rest [K']
                                  | None => chain_slowF bc rest [K']
                                  end) l
          | None => chain_slowF bc rest l
          end
      end
  end.

Definition is_fact_entry (K : kentry) : bool :=
  match K with KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ => true | _ => false end.

Fixpoint entriesGF (bc : bctx) (X : ptree (option bx)) (sis : list sxi) (gl : ptree gflF) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | Some ei =>
           let okb := kbase K in
           let same_of := match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end in
           let br2 := match okb with Some _ => ei_br ei | None => None end in
           match pt_get gl (ei_gid ei) with
           | Some (g, gx, fl) =>
               if inb g ei then
                 (if member_ok K g gx then chainKFF bc (xget X (ei_bid ei)) fl K okb same_of br2
                  else match g with
                       | (b, obr, (glo, ghi)) => chainKFF bc (xget X (ei_bid ei)) (mk_flF bc b (gq_of g) obr glo ghi None sis) K okb same_of br2
                       end)
               else chainK2F bc (xget X (ei_bid ei)) sis K okb same_of br2
           | None => chainK2F bc (xget X (ei_bid ei)) sis K okb same_of br2
           end
       | None => if is_fact_entry K then [K] else chainK2F bc None sis K None (fun _ => false) None
       end) ++ entriesGF bc X sis gl rest irest
  | _, _ => []
  end.

Fixpoint store_bases (sxs : list stx) (seen : ptree unit) : list expr :=
  match sxs with
  | [] => []
  | sx :: rest => match pt_get seen (sx_bid sx) with
                  | Some _ => store_bases rest seen
                  | None => a_base (sx_a sx) :: store_bases rest (pt_set (sx_bid sx) tt seen)
                  end
  end.

Fixpoint stores_partF (bc : bctx) (sis : list sxi) : list kentry :=
  match sis with
  | [] => []
  | si :: newer => let sx := si_sx si in
                   stores_partF bc newer ++ chainK2F bc (si_bx si) newer (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx)
  end.

Definition num_sub (bc : bctx) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
  if (if expr_eqb b (a_base c) then Z.leb (a_off c) k else false) then
    match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
  else false.
Fixpoint disj_both (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) * list (saddr * expr) :=
  match kn with
  | [] => ([], [])
  | KDisj c1 m1 c2 m2 :: rest =>
      let '(r, rx) := disj_both bc rest b1 k1 n1 in
      let x2 := xinsideB bc b1 k1 (ELit n1) (a_base c2) (a_off c2) m2 in
      let x1 := xinsideB bc b1 k1 (ELit n1) (a_base c1) (a_off c1) m1 in
      let r1 := if (if num_sub bc b1 k1 n1 c2 m2 then true else x2) then (c1, m1) :: r else r in
      let rx1 := if x2 then (c1, m1) :: rx else rx in
      ((if (if num_sub bc b1 k1 n1 c1 m1 then true else x1) then (c2, m2) :: r1 else r1),
       (if x1 then (c2, m2) :: rx1 else rx1))
  | _ :: rest => disj_both bc rest b1 k1 n1
  end.
Definition mk_sprepF (bc : bctx) (kd : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) : sprep :=
  match n1 with
  | ELit z1 =>
      if Z.eqb (zlit64 z1) z1 then
        let '(D, Dx) := disj_both bc kd b1 k1 z1 in SPrep (base_rangeB bc b1) (xhiB bc n1) D Dx
      else SPrep (base_rangeB bc b1) (xhiB bc n1) (disj_sidesB bc kd b1 k1 (zlit64 z1)) (disj_sides_xB bc kd b1 k1 n1)
  | _ => SPrep (base_rangeB bc b1) (xhiB bc n1) [] (disj_sides_xB bc kd b1 k1 n1)
  end.
Fixpoint mk_stxsF (bc : bctx) (kd : list kentry) (log : list sentry) (t : ntab) : list stx * ntab :=
  match log with
  | [] => ([], t)
  | SE a w v :: older =>
      let '(sxs, t1) := mk_stxsF bc kd older t in
      let '(r, t2) := intern bc t1 (a_base a) in
      let '(bid, bi) := r in
      (sxs ++ [STX a w v (mk_sprepF bc kd (a_base a) (a_off a) (elen w)) bid (bi_br bi)], t2)
  end.

Definition carryGF (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxsF bc (be_kd (mk_bext bc)) log nt_empty in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, t1) := r in
  let sbs := store_bases sxs PTLeaf in
  let X := pt_map (fun bi => if existsbF (fun sb => shares_var sb (bi_base bi)) sbs then Some (mk_bx bc (bi_base bi)) else None) (nt_info t1) in
  let sis := map (mk_sxi X) sxs in
  stores_partF bc sis ++ entriesGF bc X sis (mk_glF bc (nt_info t1) X (gs_bnds gs) sis) kn infos.

Definition carryKF1 (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryGF bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.

Ltac fe := repeat (apply functional_extensionality; intros ?).
Lemma zmod64_fe : zmod64 = fun z => (z mod 2 ^ 64)%Z.
Proof. fe. apply zmod64_eq. Qed.

Lemma lin_range_shift : forall rng c ts,
  lin_range rng c ts = match lin_range rng 0 ts with Some (lo, hi) => Some (lo + c, hi + c) | None => None end.
Proof.
  intros rng c ts. induction ts as [|[k a] rest IH]; cbn [lin_range].
  - reflexivity.
  - rewrite IH. destruct (rng a) as [[al ah]|]; [|reflexivity].
    destruct (lin_range rng 0 rest) as [[lo hi]|]; [|reflexivity].
    destruct (Z.leb 0 k); f_equal; f_equal; lia.
Qed.

Lemma lin_testB_mono : forall bc c d ts (T1 T2 : Z -> Z -> bool),
  (forall x y, T1 x y = true -> T2 (x + d) (y + d) = true) ->
  lin_testB bc c ts T1 = true -> lin_testB bc (c + d) ts T2 = true.
Proof.
  intros bc c d ts T1 T2 HT. unfold lin_testB, lin_test_relB.
  rewrite (lin_range_shift _ c ts), (lin_range_shift _ (c + d) ts).
  destruct (lin_range (erangeB bc) 0 ts) as [[lo hi]|] eqn:E0.
  - destruct (T1 (lo + c) (hi + c)) eqn:E1.
    + intros _. replace (lo + (c + d)) with (lo + c + d) by lia. replace (hi + (c + d)) with (hi + c + d) by lia.
      rewrite (HT _ _ E1). reflexivity.
    + intros H. destruct (T2 (lo + (c + d)) (hi + (c + d))); [reflexivity|].
      destruct (bc_fs bc) as [|f fs]; [discriminate|].
      destruct (sum_subst (f :: fs) ts 0 0 false) as [[ts' [lo0 hi0]] [|]]; [|discriminate].
      rewrite (lin_range_shift _ c ts') in H. rewrite (lin_range_shift _ (c + d) ts').
      destruct (lin_range (erangeB bc) 0 ts') as [[a b]|]; [|discriminate].
      replace (a + (c + d) + lo0) with (a + c + lo0 + d) by lia. replace (b + (c + d) + hi0) with (b + c + hi0 + d) by lia.
      apply HT. exact H.
  - intros H.
    destruct (bc_fs bc) as [|f fs]; [discriminate|].
    destruct (sum_subst (f :: fs) ts 0 0 false) as [[ts' [lo0 hi0]] [|]]; [|discriminate].
    rewrite (lin_range_shift _ c ts') in H. rewrite (lin_range_shift _ (c + d) ts').
    destruct (lin_range (erangeB bc) 0 ts') as [[a b]|]; [|discriminate].
    replace (a + (c + d) + lo0) with (a + c + lo0 + d) by lia. replace (b + (c + d) + hi0) with (b + c + hi0 + d) by lia.
    apply HT. exact H.
Qed.

Lemma T0_mono : forall d, 0 <= d -> forall x y : Z, (fun lo _ : Z => Z.leb 0 lo) x y = true -> (fun lo _ : Z => Z.leb 0 lo) (x + d) (y + d) = true.
Proof. intros d Hd x y H. cbv beta in *. apply Z.leb_le in H. apply Z.leb_le. lia. Qed.

Lemma lin_ge0_scaledB_mono : forall bc C d ts, 0 <= d -> lin_ge0_scaledB bc C ts = true -> lin_ge0_scaledB bc (C + d) ts = true.
Proof.
  intros bc C d ts Hd H. unfold lin_ge0_scaledB in *.
  destruct (if Z.ltb 0 (srl_scale_need ts) then Z.leb (srl_scale_need ts) 24 else false) eqn:Ej; [|discriminate].
  assert (Hj : 0 < srl_scale_need ts) by (destruct (Z.ltb_spec 0 (srl_scale_need ts)); [lia|discriminate]).
  destruct (srl_expandB bc (List.map (fun t => (2 ^ srl_scale_need ts * fst t, snd t)) ts)) as [c2 t2].
  destruct (if has_srl t2 then srl_expandB bc t2 else (0, t2)) as [c3 t3].
  replace (2 ^ srl_scale_need ts * (C + d) + c2 + c3) with ((2 ^ srl_scale_need ts * C + c2 + c3) + 2 ^ srl_scale_need ts * d) by ring.
  assert (Hsd : 0 <= 2 ^ srl_scale_need ts * d) by (apply Z.mul_nonneg_nonneg; [apply Z.pow_nonneg; lia|exact Hd]).
  apply (lin_testB_mono _ _ _ _ _ _ (T0_mono _ Hsd)). exact H.
Qed.

Lemma lin_ge0B_mono : forall bc pos neg pos' neg',
  xt_nowrapB bc pos' = xt_nowrapB bc pos -> xt_nowrapB bc neg' = xt_nowrapB bc neg ->
  xt_lin pos' = xt_lin pos -> xt_lin neg' = xt_lin neg ->
  xt_const pos - xt_const neg <= xt_const pos' - xt_const neg' ->
  lin_ge0B bc pos neg = true -> lin_ge0B bc pos' neg' = true.
Proof.
  intros bc pos neg pos' neg' Hnp Hnn Hlp Hln Hc H. unfold lin_ge0B in *. rewrite Hnp, Hnn, Hlp, Hln.
  set (ts := lsub_e (xt_lin pos) (xt_lin neg)) in *.
  set (C := xt_const pos - xt_const neg) in *.
  replace (xt_const pos' - xt_const neg') with (C + (xt_const pos' - xt_const neg' - C)) by lia.
  set (d := xt_const pos' - xt_const neg' - C).
  assert (Hd : 0 <= d) by (unfold d; lia).
  pose proof (T0_mono d Hd) as HT.
  destruct (xt_nowrapB bc pos), (xt_nowrapB bc neg); cbn [andb] in *; try discriminate.
  destruct (lin_testB bc C ts (fun lo _ => Z.leb 0 lo)) eqn:E1.
  { rewrite (lin_testB_mono bc C d ts _ _ HT E1). reflexivity. }
  destruct (lin_testB bc (C + d) ts (fun lo _ => Z.leb 0 lo)); [reflexivity|].
  destruct (srl_expandB bc ts) as [c2 t2].
  destruct (lin_testB bc (C + c2) t2 (fun lo _ => Z.leb 0 lo)) eqn:E2.
  { replace (C + d + c2) with (C + c2 + d) by lia. rewrite (lin_testB_mono bc _ d t2 _ _ HT E2). reflexivity. }
  destruct (lin_testB bc (C + d + c2) t2 (fun lo _ => Z.leb 0 lo)); [reflexivity|].
  destruct (has_srl t2).
  - destruct (srl_expandB bc t2) as [c3 t3].
    destruct (lin_testB bc (C + c2 + c3) t3 (fun lo _ => Z.leb 0 lo)) eqn:E3.
    { replace (C + d + c2 + c3) with (C + c2 + c3 + d) by lia. rewrite (lin_testB_mono bc _ d t3 _ _ HT E3). reflexivity. }
    destruct (lin_testB bc (C + d + c2 + c3) t3 (fun lo _ => Z.leb 0 lo)); [reflexivity|].
    apply lin_ge0_scaledB_mono; assumption.
  - apply lin_ge0_scaledB_mono; assumption.
Qed.

Lemma snorm_small : forall k, mtwo63z <= k < two63z -> snorm k = k.
Proof.
  intros k [H1 H2]. unfold snorm. destruct (Z.leb_spec mtwo63z k); [|lia]. destruct (Z.ltb_spec k two63z); [|lia]. reflexivity.
Qed.
Lemma two63z_val : two63z = 9223372036854775808. Proof. reflexivity. Qed.
Lemma mtwo63z_val : mtwo63z = -9223372036854775808. Proof. reflexivity. Qed.
Lemma two64_val : two64 = 18446744073709551616. Proof. reflexivity. Qed.

Lemma lin_nowrapRB_lit : forall bc z, 0 <= z < two63z -> lin_nowrapRB bc (ELit z) = true.
Proof.
  intros bc z Hz. unfold lin_nowrapRB. cbn [lin_of fst snd srl_expandB].
  rewrite snorm_small by (rewrite ?mtwo63z_val, ?two63z_val in *; lia).
  unfold lin_testB. cbn [lin_range]. rewrite ?two63z_val in Hz.
  destruct (Z.leb_spec 0 (z + 0)); [|lia]. destruct (Z.ltb_spec (z + 0) two64); [reflexivity|]. rewrite two64_val in *. lia.
Qed.

Lemma xinside0B_mono : forall bc b k n cb co m k' n',
  0 <= n' -> n < two63z -> 0 <= n -> k <= k' -> k' + n' <= k + n ->
  xinside0B bc b k (ELit n) cb co m = true -> xinside0B bc b k' (ELit n') cb co m = true.
Proof.
  intros bc b k n cb co m k' n' Hn' Hn Hn0 Hk Hkn H. unfold xinside0B in *.
  destruct (lin_ge0B bc [(b, k)] [(cb, co)]) eqn:E1; [|discriminate].
  rewrite (lin_ge0B_mono bc [(b, k)] [(cb, co)] [(b, k')] [(cb, co)]); try reflexivity; [|cbn [xt_const]; lia|exact E1].
  revert H. apply lin_ge0B_mono; try reflexivity.
  - cbn [xt_nowrapB]. rewrite !lin_nowrapRB_lit by (rewrite ?two63z_val in *; lia). reflexivity.
  - cbn [xt_const lin_of fst]. rewrite !snorm_small by (rewrite ?mtwo63z_val, ?two63z_val in *; lia). lia.
Qed.

Lemma xinside_numB_mono : forall bc b k n cb co m k' n',
  0 <= n' -> n < two64 -> 0 <= n -> k <= k' -> k' + n' <= k + n -> n' < two64 ->
  xinside_numB bc b k (ELit n) cb co m = true -> xinside_numB bc b k' (ELit n') cb co m = true.
Proof.
  intros bc b k n cb co m k' n' Hn' Hn Hn0 Hk Hkn Hn2 H. unfold xinside_numB in *.
  destruct (xloB bc cb) as [lo2|]; [|discriminate]. destruct (xhiB bc cb) as [hi2|]; [|discriminate].
  destruct (Z.eqb lo2 hi2); [|discriminate].
  destruct (base_rangeB bc b) as [[lo1 hi1]|]; [|discriminate].
  cbn [xhiB] in *. unfold zlit64 in *.
  destruct (Z.leb_spec 0 n), (Z.ltb_spec n two64); try lia. destruct (Z.leb_spec 0 n'), (Z.ltb_spec n' two64); try lia.
  cbn [andb] in *. destruct (xloB bc m) as [l2|]; [|discriminate].
  apply andb_prop in H as [A1 A2]. apply Z.leb_le in A1. apply Z.leb_le in A2.
  apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Lemma xinsideB_mono : forall bc b k n cb co m k' n',
  0 <= n' -> n < two63z -> 0 <= n -> k <= k' -> k' + n' <= k + n ->
  xinsideB bc b k (ELit n) cb co m = true -> xinsideB bc b k' (ELit n') cb co m = true.
Proof.
  intros bc b k n cb co m k' n' Hn' Hn Hn0 Hk Hkn H. unfold xinsideB in *. rewrite two63z_val in Hn.
  destruct (shares_var b cb).
  - apply (xinside0B_mono bc b k n); try assumption; rewrite ?two63z_val; lia.
  - destruct (novars cb); [|discriminate]. apply (xinside_numB_mono bc b k n); try assumption; rewrite ?two64_val; lia.
Qed.

Lemma sub_itvB_mono : forall bc b k n c m k' n',
  0 <= n' -> n < two63z -> 0 <= n -> k <= k' -> k' + n' <= k + n ->
  sub_itvB bc b k n c m = true -> sub_itvB bc b k' n' c m = true.
Proof.
  intros bc b k n c m k' n' Hn' Hn Hn0 Hk Hkn H. unfold sub_itvB in *.
  assert (NUM : (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
                   match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end else false) = true ->
                (if (expr_eqb b (a_base c) && Z.leb (a_off c) k')%bool then
                   match xloB bc m with Some ml => Z.leb (k' + n') (a_off c + ml) | None => false end else false) = true).
  { destruct (expr_eqb b (a_base c)); cbn [andb]; [|discriminate].
    destruct (Z.leb_spec (a_off c) k); [|discriminate]. destruct (Z.leb_spec (a_off c) k'); [|lia].
    destruct (xloB bc m) as [ml|]; [|discriminate]. intros X. apply Z.leb_le in X. apply Z.leb_le. lia. }
  assert (RNG : (Z.leb 0 n' && Z.ltb n' two64)%bool = true)
    by (apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; rewrite ?two64_val, ?two63z_val in *; lia).
  destruct (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
              match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end else false) eqn:E1.
  - rewrite (NUM eq_refl). reflexivity.
  - destruct (if (expr_eqb b (a_base c) && Z.leb (a_off c) k')%bool then
                match xloB bc m with Some ml => Z.leb (k' + n') (a_off c + ml) | None => false end else false); [reflexivity|].
    rewrite RNG. destruct (Z.leb 0 n && Z.ltb n two64)%bool; [|discriminate].
    apply (xinsideB_mono bc b k n); assumption.
Qed.

Lemma in_sidesB_mono : forall bc D b k n k' n',
  0 <= n' -> n < two63z -> 0 <= n -> k <= k' -> k' + n' <= k + n ->
  in_sidesB bc D b k n = true -> in_sidesB bc D b k' n' = true.
Proof.
  intros bc D b k n k' n' Hn' Hn Hn0 Hk Hkn. induction D as [|[c m] r IH]; cbn [in_sidesB]; [discriminate|].
  destruct (sub_itvB bc b k n c m) eqn:E.
  - rewrite (sub_itvB_mono bc b k n c m k' n' Hn' Hn Hn0 Hk Hkn E). reflexivity.
  - intros H. destruct (sub_itvB bc b k' n' c m); [reflexivity|]. apply IH. exact H.
Qed.

Lemma lin_apartB_mono : forall bc b1 k1 n1 b2 k2 n2 k2' n2',
  k2 <= k2' -> k2' + n2' <= k2 + n2 ->
  lin_apartB bc b1 k1 n1 b2 k2 n2 = true -> lin_apartB bc b1 k1 n1 b2 k2' n2' = true.
Proof.
  intros bc b1 k1 n1 b2 k2 n2 k2' n2' Hk Hkn H. unfold lin_apartB, lin_apart0B in *.
  destruct (shares_var b1 b2); [|discriminate].
  destruct (lin_nowrapRB bc b1), (lin_nowrapRB bc b2); cbn [andb] in *; try discriminate.
  replace (fst (lin_of b2) + k2' - fst (lin_of b1) - k1) with ((fst (lin_of b2) + k2 - fst (lin_of b1) - k1) + (k2' - k2)) by lia.
  revert H. apply lin_testB_mono. intros x y HT.
  apply Bool.orb_true_iff in HT. apply Bool.orb_true_iff. destruct HT as [HT|HT]; apply Z.leb_le in HT; [left|right]; apply Z.leb_le; lia.
Qed.

Lemma zlit64_bounds : forall z, 0 <= zlit64 z < two64.
Proof.
  intros z. pose proof (Z.mod_pos_bound z two64 ltac:(rewrite two64_val; lia)) as B. unfold zlit64.
  destruct (Z.leb_spec 0 z), (Z.ltb_spec z two64); cbn [andb]; lia.
Qed.

Lemma ranges_apart_pcB_mono : forall bc sp b1 k1 z1 br2 b2 k2 zh k2' z2',
  0 <= zh < two63z -> k2 <= k2' -> k2' + zlit64 z2' <= k2 + zh ->
  ranges_apart_pcB bc sp b1 k1 (ELit z1) br2 b2 k2 (ELit zh) = true ->
  ranges_apart_pcB bc sp b1 k1 (ELit z1) br2 b2 k2' (ELit z2') = true.
Proof.
  intros bc sp b1 k1 z1 br2 b2 k2 zh k2' z2' Hzh Hk Hkn H. unfold ranges_apart_pcB in *. cbv zeta in *.
  assert (Ezh : zlit64 zh = zh).
  { unfold zlit64. rewrite two63z_val in Hzh. destruct (Z.leb_spec 0 zh), (Z.ltb_spec zh two64); cbn [andb]; try reflexivity; rewrite two64_val in *; lia. }
  rewrite Ezh in H. pose proof (zlit64_bounds z2') as B2. set (m2' := zlit64 z2') in *.
  destruct (match sp_rng sp with Some (lo1, hi1) => match br2 with Some (lo2, hi2) => ((hi1 + k1 + zlit64 z1 <=? lo2 + k2') || (hi2 + k2' + m2' <=? lo1 + k1))%bool | None => false end | None => false end) eqn:EN; [reflexivity|].
  destruct (match sp_rng sp with Some (lo1, hi1) => match br2 with Some (lo2, hi2) => ((hi1 + k1 + zlit64 z1 <=? lo2 + k2) || (hi2 + k2 + zh <=? lo1 + k1))%bool | None => false end | None => false end) eqn:EH.
  { exfalso. destruct (sp_rng sp) as [[lo1 hi1]|]; [|discriminate]. destruct br2 as [[lo2 hi2]|]; [|discriminate].
    apply Bool.orb_true_iff in EH. apply Bool.orb_false_iff in EN. destruct EN as [N1 N2].
    apply Z.leb_gt in N1. apply Z.leb_gt in N2. destruct EH as [X|X]; apply Z.leb_le in X; lia. }
  destruct (in_sidesB bc (sp_D sp) b2 k2 zh) eqn:ES.
  { rewrite (in_sidesB_mono bc (sp_D sp) b2 k2 zh k2' m2'); [reflexivity|lia|apply Hzh|apply Hzh|exact Hk|exact Hkn|exact ES]. }
  destruct (in_sidesB bc (sp_D sp) b2 k2' m2'); [reflexivity|].
  apply (lin_apartB_mono bc b1 k1 (zlit64 z1) b2 k2 zh); assumption.
Qed.

Lemma prune1pcK_keep_lin : forall bc sp wa w wv K kb kk m br2 glo ghi,
  kdescr K = Some (kb, kk, Some m) -> (forall z, kb <> ELit z) ->
  0 <= ghi - glo < two63z -> glo <= kk -> kk + m <= ghi ->
  ranges_apart_pcB bc sp (a_base wa) (a_off wa) (elen w) br2 kb glo (ELit (ghi - glo)) = true ->
  prune1pcK bc sp wa w wv K false br2 = PKeep.
Proof.
  intros bc sp wa w wv K kb kk m br2 glo ghi HD Hkb Hg Hk Hkm H. unfold elen in H.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[b k] len fc|[b k] len];
    cbn [kdescr] in HD; try discriminate.
  - injection HD as <- <- <-. unfold prune1pcK, elen. cbv zeta beta iota.
    rewrite (ranges_apart_pcB_mono bc sp (a_base wa) (a_off wa) (Z.of_nat w) br2 b glo (ghi - glo) k (Z.of_nat w')); first [reflexivity | assumption | lia].
  - destruct len as [z| | | | | | |]; try discriminate. injection HD as <- <- <-. unfold prune1pcK, elen. cbv zeta beta iota.
    rewrite (ranges_apart_pcB_mono bc sp (a_base wa) (a_off wa) (Z.of_nat w) br2 b glo (ghi - glo) k z); first [reflexivity | assumption | lia].
  - destruct len as [z| | | | | | |]; try discriminate. injection HD as <- <- <-. unfold prune1pcK, elen. cbv zeta beta iota.
    rewrite (ranges_apart_pcB_mono bc sp (a_base wa) (a_off wa) (Z.of_nat w) br2 b glo (ghi - glo) k z); first [reflexivity | assumption | lia].
  - injection HD as <- _ _. exfalso. apply (Hkb 0). reflexivity.
  - destruct len as [z| | | | | | |]; try discriminate. injection HD as <- <- <-. unfold prune1pcK, elen. cbv zeta beta iota.
    rewrite (ranges_apart_pcB_mono bc sp (a_base wa) (a_off wa) (Z.of_nat w) br2 b glo (ghi - glo) k z); first [reflexivity | assumption | lia].
  - destruct len as [z| | | | | | |]; try discriminate. injection HD as <- <- <-. unfold prune1pcK, elen. cbv zeta beta iota.
    rewrite (ranges_apart_pcB_mono bc sp (a_base wa) (a_off wa) (Z.of_nat w) br2 b glo (ghi - glo) k z); first [reflexivity | assumption | lia].
Qed.

Definition BXOK (bc : bctx) (o : option bx) : Prop := forall x, o = Some x -> x = mk_bx bc (bx_b x).
Lemma bx_get_ok : forall bc o b, BXOK bc o -> bx_get bc o b = (lin_of b, lin_nowrapRB bc b).
Proof.
  intros bc [x|] b H; [|reflexivity]. cbn [bx_get]. eF.
  destruct (expr_eqb (bx_b x) b) eqn:E; [|reflexivity].
  apply p_expr_eqb_eq in E. rewrite (H x eq_refl). subst b. reflexivity.
Qed.
Lemma lin_apartF_eq : forall bc i1 i2, BXOK bc i1 -> BXOK bc i2 -> lin_apartF bc i1 i2 = lin_apartB bc.
Proof.
  intros bc i1 i2 H1 H2. fe. rename x into b1, x0 into k1, x1 into n1, x2 into b2, x3 into k2, x4 into n2.
  unfold lin_apartF, lin_apartB, lin_apart0B. destruct (shares_var b1 b2); [|reflexivity].
  rewrite (bx_get_ok _ _ _ H1), (bx_get_ok _ _ _ H2).
  destruct (lin_nowrapRB bc b1), (lin_nowrapRB bc b2); reflexivity.
Qed.
Lemma ranges_apart_pcF_eq : forall bc i1 i2, BXOK bc i1 -> BXOK bc i2 -> ranges_apart_pcF bc i1 i2 = ranges_apart_pcB bc.
Proof.
  intros bc i1 i2 H1 H2. apply functional_extensionality; intros sp. apply functional_extensionality; intros b1.
  apply functional_extensionality; intros k1. apply functional_extensionality; intros n1.
  apply functional_extensionality; intros br2. apply functional_extensionality; intros b2.
  apply functional_extensionality; intros k2. apply functional_extensionality; intros n2.
  unfold ranges_apart_pcF, ranges_apart_pcB. rewrite (lin_apartF_eq _ _ _ H1 H2).
  destruct n1 as [z1| | | | | | |]; try reflexivity. destruct n2 as [z2| | | | | | |]; try reflexivity. cbv zeta.
  destruct (match sp_rng sp with Some (lo1, hi1) => _ | None => false end); [reflexivity|].
  destruct (in_sidesB bc (sp_D sp) b2 k2 (zlit64 z2)), (lin_apartB bc b1 k1 (zlit64 z1) b2 k2 (zlit64 z2)); reflexivity.
Qed.
Ltac crush :=
  repeat (first [ reflexivity
                | match goal with
                  | |- context [if ?c then _ else _] =>
                      lazymatch c with context [if _ then _ else _] => fail | _ => destruct c end
                  | |- context [match ?x with nil => _ | cons _ _ => _ end] =>
                      lazymatch x with context [if _ then _ else _] => fail | _ => destruct x end
                  | |- context [match ?x with ELit _ => _ | _ => _ end] => is_var x; destruct x
                  end ]).
Lemma prune1pcKF_eq : forall bc i1 i2, BXOK bc i1 -> BXOK bc i2 -> prune1pcKF bc i1 i2 = prune1pcK bc.
Proof.
  intros bc i1 i2 H1 H2. fe. rename x into sp, x0 into wa, x1 into w, x2 into wv, x3 into K, x4 into same, x5 into br2.
  unfold prune1pcKF, prune1pcK. rewrite (ranges_apart_pcF_eq _ _ _ H1 H2), zmod64_fe. cbv [orb andb]. cbv zeta.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    try reflexivity; crush.
Qed.

Definition XOK (bc : bctx) (X : ptree (option bx)) : Prop := forall bid, BXOK bc (xget X bid).
Lemma verdictF_eq : forall X sx b obr glo ghi,
  verdictF (mk_sxi X sx) b (gq_of (b, obr, (glo, ghi))) = verdict sx (b, obr, (glo, ghi)).
Proof.
  intros X sx b obr glo ghi. unfold verdictF, verdict, mk_sxi, gq_of. cbn [si_sx si_ab].
  destruct (Pos.eqb b (sx_bid sx)); [reflexivity|].
  destruct (sp_rng (sx_sp sx)) as [[lo1 hi1]|]; [|reflexivity].
  destruct obr as [[lo2 hi2]|]; [|reflexivity].
  destruct (Z.leb_spec (hi1 + a_off (sx_a sx) + sx_m1 sx) (glo + lo2));
  destruct (Z.leb_spec (hi1 + a_off (sx_a sx) + sx_m1 sx - lo2) glo); try lia;
  destruct (Z.leb_spec (ghi + hi2) (lo1 + a_off (sx_a sx)));
  destruct (Z.leb_spec ghi (lo1 + a_off (sx_a sx) - hi2)); try lia; reflexivity.
Qed.
Lemma prune1pBF_eq : prune1pBF = prune1pB.
Proof. fe. unfold prune1pBF, prune1pB. rewrite zmod64_fe. reflexivity. Qed.
Lemma prune1pcBF_eq : prune1pcBF = prune1pcB.
Proof. fe. unfold prune1pcBF, prune1pcB. rewrite prune1pBF_eq. reflexivity. Qed.
Lemma g1cBF_eq : g1cBF = g1cB.
Proof. fe. unfold g1cBF, g1cB. rewrite prune1pcBF_eq. reflexivity. Qed.
Lemma match_nz : forall (T : Type) (e : expr) (X Y : T),
  match e with ELit 0 => false | _ => true end = true -> match e with ELit 0 => X | _ => Y end = Y.
Proof. intros T e X Y H. destruct e as [z| | | | | | |]; try reflexivity. destruct z; [discriminate|reflexivity|reflexivity]. Qed.
Lemma g1cBF_img_keep : forall bc sx lo hi lo1 hi1,
  sp_rng (sx_sp sx) = Some (lo1, hi1) -> match a_base (sx_a sx) with ELit 0 => false | _ => true end = true ->
  (if (if Z.leb 0 (hi - lo) then Z.ltb (hi - lo) two64 else false)
   then (if Z.leb (hi1 + a_off (sx_a sx) + sx_m1 sx) lo then true else Z.leb hi (lo1 + a_off (sx_a sx))) else false) = true ->
  g1cBF bc sx (KImg lo hi) = [KImg lo hi].
Proof.
  intros bc sx lo hi lo1 hi1 Hsp Hnz HC.
  destruct (Z.leb_spec 0 (hi - lo)) as [H0|H0]; [|discriminate]. destruct (Z.ltb_spec (hi - lo) two64) as [H1|H1]; [|discriminate].
  assert (Hz : zlit64 (hi - lo) = hi - lo)
    by (unfold zlit64; destruct (Z.leb_spec 0 (hi - lo)), (Z.ltb_spec (hi - lo) two64); cbn [andb]; first [reflexivity | lia]).
  assert (HAP : ranges_apart_pB bc (sx_sp sx) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx)) (ELit 0) lo (ELit (hi - lo)) = true).
  { unfold ranges_apart_pB. cbn [elen base_rangeB]. rewrite Hsp. change (0 mod two64) with 0. cbv zeta. rewrite Hz. unfold sx_m1 in HC.
    rewrite ?Z.add_0_l. replace (lo + (hi - lo)) with hi by lia.
    destruct (Z.leb (hi1 + a_off (sx_a sx) + zlit64 (Z.of_nat (sx_w sx))) lo) eqn:EA; cbn [orb]; [reflexivity|].
    rewrite HC. reflexivity. }
  unfold g1cBF, prune1pcBF, prune1pBF. cbn [obrB kbase]. rewrite (match_nz _ _ _ _ Hnz).
  replace (Z.ltb (hi - lo) two64) with true by (symmetry; apply Z.ltb_lt; exact H1). cbv zeta. cbn [a_base a_off]. rewrite HAP. reflexivity.
Qed.
Lemma g1cF_eq : forall bc X sx, g1cF bc (mk_sxi X sx) = g1cBF bc sx.
Proof.
  intros bc X sx. fe. rename x into K. unfold g1cF. cbn [si_sx si_ab mk_sxi].
  destruct K as [a w' v|a len|a len bk|lo hi|e' m'|e' lo' hi'|a en|c1 m1 c2 m2|a len fc|a len]; try reflexivity.
  destruct (sp_rng (sx_sp sx)) as [[lo1 hi1]|] eqn:Hsp; cbv beta iota.
  - destruct (match a_base (sx_a sx) with ELit 0 => false | _ => true end) eqn:Hnz.
    + set (C := if (if Z.leb 0 (hi - lo) then Z.ltb (hi - lo) two64 else false)
                then (if Z.leb (hi1 + a_off (sx_a sx) + sx_m1 sx) lo then true else Z.leb hi (lo1 + a_off (sx_a sx))) else false).
      assert (HK : (if C then [KImg lo hi] else g1cBF bc sx (KImg lo hi)) = g1cBF bc sx (KImg lo hi)).
      { destruct C eqn:EC; [|reflexivity]. symmetry. apply (g1cBF_img_keep bc sx lo hi lo1 hi1 Hsp Hnz EC). }
      destruct (a_base (sx_a sx)) as [z| | | | | | |]; try exact HK. destruct z; [discriminate|exact HK|exact HK].
    + destruct (a_base (sx_a sx)) as [z| | | | | | |]; try discriminate. destruct z; [reflexivity|discriminate|discriminate].
  - destruct (a_base (sx_a sx)) as [z| | | | | | |]; try reflexivity. destruct z; reflexivity.
Qed.
Lemma chain_slowF_eq : forall bc X sxs, chain_slowF bc (map (mk_sxi X) sxs) = chain_slow bc sxs.
Proof.
  intros bc X sxs. induction sxs as [|sx rest IH]; fe; [reflexivity|].
  cbn [map chain_slowF chain_slow]. rewrite g1cF_eq, g1cBF_eq, IH. reflexivity.
Qed.
Lemma chainK2F_eq : forall bc X xo sxs, XOK bc X -> BXOK bc xo ->
  chainK2F bc xo (map (mk_sxi X) sxs) = chainK2 bc sxs.
Proof.
  intros bc X xo sxs HX Hxo. induction sxs as [|sx rest IH]; fe; [reflexivity|].
  rename x into K, x0 into okb, x1 into same_of, x2 into br2.
  cbn [map chainK2F chainK2 si_sx si_bx mk_sxi]. rewrite (prune1pcKF_eq bc (xget X (sx_bid sx)) xo (HX (sx_bid sx)) Hxo).
  rewrite IH, chain_slowF_eq. reflexivity.
Qed.
Lemma chainKFF_eq : forall bc X xo b obr glo ghi gx sxs K okb same_of br2,
  XOK bc X -> BXOK bc xo ->
  (forall sx, linV bc (mk_sxi X sx) b obr glo ghi gx = true ->
     prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 = PKeep) ->
  chainKFF bc xo (mk_flF bc b (gq_of (b, obr, (glo, ghi))) obr glo ghi gx (map (mk_sxi X) sxs)) K okb same_of br2
  = chainKF bc (mk_fl (b, obr, (glo, ghi)) sxs) K okb same_of br2.
Proof.
  intros bc X xo b obr glo ghi gx sxs K okb same_of br2 HX Hxo HS.
  induction sxs as [|sx rest IH]; [reflexivity|].
  cbn [map mk_flF mk_fl]. rewrite verdictF_eq.
  destruct (verdict sx (b, obr, (glo, ghi))); [exact IH|].
  destruct (linV bc (mk_sxi X sx) b obr glo ghi gx) eqn:EL.
  - cbn [chainKF]. rewrite (HS sx EL). exact IH.
  - cbn [chainKFF chainKF si_sx si_bx mk_sxi]. rewrite (prune1pcKF_eq bc (xget X (sx_bid sx)) xo (HX (sx_bid sx)) Hxo).
    rewrite (chainK2F_eq bc X xo rest HX Hxo), chain_slowF_eq.
    destruct (prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2); [exact IH|reflexivity].
Qed.
Lemma obr_eqb_eq : forall a b, obr_eqb a b = true -> a = b.
Proof.
  intros [[x1 y1]|] [[x2 y2]|]; cbn [obr_eqb]; try discriminate; [|reflexivity].
  intros H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

Lemma linV_keep : forall bc X sx b obr glo ghi x K ei,
  XOK bc X -> BXOK bc (gx_bx x) -> is_litb (gx_b x) = false ->
  member_ok K (b, obr, (glo, ghi)) (Some x) = true -> inb (b, obr, (glo, ghi)) ei = true ->
  linV bc (mk_sxi X sx) b obr glo ghi (Some x) = true ->
  prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K
    (match kbase K with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end (sx_bid sx))
    (match kbase K with Some _ => ei_br ei | None => None end) = PKeep.
Proof.
  intros bc X sx b obr glo ghi x K ei HX Hx Hlit HM Hinb HL.
  unfold member_ok in HM. destruct (kdescr K) as [[[kb kk] [m|]]|] eqn:HD; try discriminate.
  destruct (expr_eqb kb (gx_b x)) eqn:Eb; [|discriminate]. apply p_expr_eqb_eq in Eb. subst kb.
  destruct (Z.leb_spec glo kk); [|discriminate]. apply Z.leb_le in HM.
  unfold inb in Hinb. cbn [ei_m] in Hinb. destruct (ei_m ei) as [m'|]; [|discriminate].
  apply andb_prop in Hinb as [Hinb _]. apply andb_prop in Hinb as [Hinb _]. apply andb_prop in Hinb as [Hb Hbr].
  apply Pos.eqb_eq in Hb. apply obr_eqb_eq in Hbr. subst b obr.
  unfold linV in HL. cbn [si_sx si_bx mk_sxi] in HL.
  destruct (Pos.eqb (ei_bid ei) (sx_bid sx)) eqn:Ebid; [discriminate|].
  destruct (if Z.leb 0 (ghi - glo) then Z.ltb (ghi - glo) two63z else false) eqn:Eg; [|discriminate].
  assert (Hg : 0 <= ghi - glo < two63z) by (destruct (Z.leb_spec 0 (ghi - glo)); [destruct (Z.ltb_spec (ghi - glo) two63z); [lia|discriminate]|discriminate]).
  rewrite (ranges_apart_pcF_eq bc _ _ (HX (sx_bid sx)) Hx) in HL.
  assert (Hkb : forall z, gx_b x <> ELit z) by (intros z E; rewrite E in Hlit; discriminate).
  destruct (kbase K) as [kb'|] eqn:HK.
  - rewrite Ebid. apply (prune1pcK_keep_lin bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (gx_b x) kk m (ei_br ei) glo ghi); assumption.
  - exfalso. destruct (kdescr_kbase K (gx_b x) kk (Some m) HD) as [HK'|(lo & hi & _ & E & _)]; [rewrite HK in HK'; discriminate|].
    exact (Hkb 0 E).
Qed.
Lemma chainK2_fact : forall bc sxs K okb same_of br2, is_fact_entry K = true -> chainK2 bc sxs K okb same_of br2 = [K].
Proof.
  intros bc sxs K okb same_of br2 HK. induction sxs as [|sx rest IH]; [reflexivity|].
  cbn [chainK2]. replace (prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2) with PKeep; [exact IH|].
  destruct K; try discriminate; reflexivity.
Qed.
Lemma entriesGF_eq : forall bc X sxs info bnds kn infos, XOK bc X ->
  entriesGF bc X (map (mk_sxi X) sxs) (mk_glF bc info X bnds (map (mk_sxi X) sxs)) kn infos = entriesG bc sxs (mk_gl bnds sxs) kn infos.
Proof.
  intros bc X sxs info bnds kn. induction kn as [|K rest IH]; intros infos HX; [reflexivity|].
  destruct infos as [|oi irest]; [reflexivity|].
  cbn [entriesGF entriesG]. rewrite (IH irest HX). f_equal.
  assert (HN : BXOK bc None) by (intros x H; discriminate).
  destruct oi as [ei|].
  - rewrite (chainK2F_eq bc X (xget X (ei_bid ei)) sxs HX (HX (ei_bid ei))).
    unfold mk_glF, mk_gl. rewrite !pt_get_map.
    destruct (pt_get bnds (ei_gid ei)) as [[[b obr] [glo ghi]]|]; [|reflexivity].
    destruct (inb (b, obr, (glo, ghi)) ei) eqn:Hinb; [|reflexivity].
    set (gx := match pt_get info b with
               | Some bi => if is_litb (bi_base bi) then None else Some (GXI (bi_base bi) (xget X b))
               | None => None
               end).
    assert (GX : match gx with Some x => BXOK bc (gx_bx x) /\ is_litb (gx_b x) = false | None => True end).
    { unfold gx. destruct (pt_get info b) as [bi|]; [|exact I]. destruct (is_litb (bi_base bi)) eqn:E; [exact I|].
      split; [apply HX|exact E]. }
    destruct (member_ok K (b, obr, (glo, ghi)) gx) eqn:HM.
    + apply chainKFF_eq; [exact HX|apply HX|].
      intros sx HL. destruct gx as [x|]; [|discriminate]. destruct GX as [GX1 GX2].
      exact (linV_keep bc X sx b obr glo ghi x K ei HX GX1 GX2 HM Hinb HL).
    + apply chainKFF_eq; [exact HX|apply HX|]. intros sx HL. discriminate.
  - rewrite (chainK2F_eq bc X None sxs HX HN).
    destruct (is_fact_entry K) eqn:HK; [|reflexivity]. symmetry. apply chainK2_fact. exact HK.
Qed.
Lemma stores_partF_eq : forall bc X sxs, XOK bc X -> stores_partF bc (map (mk_sxi X) sxs) = stores_part bc sxs.
Proof.
  intros bc X sxs HX. induction sxs as [|sx rest IH]; [reflexivity|].
  cbn [map stores_partF stores_part si_sx si_bx mk_sxi]. rewrite IH, (chainK2F_eq bc X (xget X (sx_bid sx)) rest HX (HX (sx_bid sx))).
  reflexivity.
Qed.
Lemma XOK_map : forall bc (P : binfo -> bool) t,
  XOK bc (pt_map (fun bi => if P bi then Some (mk_bx bc (bi_base bi)) else None) t).
Proof.
  intros bc P t bid x. unfold xget. rewrite pt_get_map.
  destruct (pt_get t bid) as [bi|]; [|discriminate].
  destruct (P bi); [|discriminate]. intros H. injection H as <-. reflexivity.
Qed.
Lemma disj_sidesB_filter : forall bc kn b1 k1 n1, disj_sidesB bc (List.filter is_kdisjb kn) b1 k1 n1 = disj_sidesB bc kn b1 k1 n1.
Proof. intros bc kn b1 k1 n1. induction kn as [|K rest IH]; [reflexivity|]. destruct K; cbn [List.filter is_kdisjb disj_sidesB]; rewrite ?IH; reflexivity. Qed.
Lemma disj_sides_xB_filter : forall bc kn b1 k1 n1, disj_sides_xB bc (List.filter is_kdisjb kn) b1 k1 n1 = disj_sides_xB bc kn b1 k1 n1.
Proof. intros bc kn b1 k1 n1. induction kn as [|K rest IH]; [reflexivity|]. destruct K; cbn [List.filter is_kdisjb disj_sides_xB]; rewrite ?IH; reflexivity. Qed.
Lemma disj_both_eq : forall bc kn b1 k1 n1, (Z.leb 0 n1 && Z.ltb n1 two64)%bool = true ->
  disj_both bc kn b1 k1 n1 = (disj_sidesB bc kn b1 k1 n1, disj_sides_xB bc kn b1 k1 (ELit n1)).
Proof.
  intros bc kn b1 k1 n1 Hn. induction kn as [|K rest IH]; [reflexivity|].
  destruct K; cbn [disj_both disj_sidesB disj_sides_xB]; rewrite ?IH; try reflexivity.
  unfold sub_itvB, sub_itv_xB, num_sub. rewrite Hn. cbv [andb]. reflexivity.
Qed.
Lemma zlit64_range : forall z, (Z.leb 0 (zlit64 z) && Z.ltb (zlit64 z) two64)%bool = true.
Proof.
  intros z. pose proof (Z.mod_pos_bound z two64 ltac:(unfold two64; lia)) as B. unfold zlit64.
  destruct (Z.leb_spec 0 z); destruct (Z.ltb_spec z two64); cbn [andb];
    apply andb_true_intro; split; first [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma mk_sprepF_eq : forall bc b1 k1 n1, mk_sprepF bc (be_kd (mk_bext bc)) b1 k1 n1 = mk_sprepB bc b1 k1 n1.
Proof.
  intros bc b1 k1 n1. unfold mk_sprepF, mk_sprepB. cbn [be_kd mk_bext].
  destruct n1; rewrite ?disj_sides_xB_filter; try reflexivity.
  rewrite disj_sidesB_filter. destruct (Z.eqb (zlit64 z) z) eqn:E; [|reflexivity].
  apply Z.eqb_eq in E. rewrite disj_both_eq by (rewrite <- E; apply zlit64_range).
  rewrite disj_sidesB_filter, disj_sides_xB_filter, E. reflexivity.
Qed.
Lemma mk_stxsF_eq : forall bc log t, mk_stxsF bc (be_kd (mk_bext bc)) log t = mk_stxs bc log t.
Proof.
  intros bc log t. induction log as [|[a w v] older IH]; [reflexivity|].
  cbn [mk_stxsF mk_stxs]. rewrite IH. destruct (mk_stxs bc older t) as [sxs t1].
  destruct (intern bc t1 (a_base a)) as [[bid bi] t2]. rewrite mk_sprepF_eq. reflexivity.
Qed.
Lemma carryGF_eq : carryGF = carryG.
Proof.
  fe. rename x into bc, x0 into log, x1 into kn. unfold carryGF, carryG. rewrite mk_stxsF_eq.
  destruct (mk_stxs bc log nt_empty) as [sxs t0].
  destruct (scan_entries bc kn t0 gst_empty) as [[infos t1] gs].
  rewrite stores_partF_eq, entriesGF_eq; [reflexivity| apply XOK_map | apply XOK_map].
Qed.
Lemma carryKF1_eq : carryKF1 = carryK.
Proof. fe. unfold carryKF1, carryK. rewrite carryGF_eq. reflexivity. Qed.

Definition nov (kk l0 k : Z) (w : nat) : bool :=
  if Z.ltb 0 l0 then if Z.ltb l0 two64 then (if Z.leb (kk + l0) k then true else Z.leb (k + Z.of_nat w) kk) else false else false.
Definition img_nov (lo hi k : Z) (w : nat) : bool :=
  if Z.ltb lo hi then (if Z.leb hi k then true else Z.leb (k + Z.of_nat w) lo) else false.

Definition ranges_apart_pcS (bc : bctx) (sp : sprep) (b1 : expr) (k1 : Z) (z1 : Z)
           (br2 : option (Z * Z)) (b2 : expr) (k2 : Z) (n2 : expr) (h2o e2o : option Z) : bool :=
  if (match sp_rng sp, br2, sp_h1 sp, h2o with
      | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
          if Z.leb (hi1 + k1 + h1) (lo2 + k2) then true else if Z.leb (hi2 + k2 + h2) (lo1 + k1) then true
          else match e2o with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
      | _, _, _, _ => false
      end) then true
  else if in_sides_xB bc (sp_Dx sp) b2 k2 n2 then true
  else if shares_var b1 b2 then
    (if lin_ge0B bc [(b2, k2)] [(b1, k1); (ELit z1, 0)] then true else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0)])
  else false.

Definition mk_pre (bc : bctx) (K : kentry) (br2 : option (Z * Z)) : option Z * option Z :=
  match K with
  | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KUnk (SA kb kk) len | KBlob (SA kb kk) len _ =>
      let h2o := xhiB bc len in
      (h2o, match br2, h2o with Some (lo2, hi2), Some h2 => end_hiB bc kb kk len lo2 hi2 h2 | _, _ => None end)
  | _ => (None, None)
  end.

Definition fastkeep (K : kentry) (wa : saddr) (w : nat) (same : bool) : bool :=
  match K with
  | KZero (SA _ kk) (ELit l0) | KFill (SA _ kk) (ELit l0) _ | KUnk (SA _ kk) (ELit l0) => if same then nov kk l0 (a_off wa) w else false
  | KImg lo hi => match a_base wa with ELit 0 => img_nov lo hi (a_off wa) w | _ => false end
  | _ => false
  end.

Definition prune1pcKS (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
  (br2 : option (Z * Z)) (h2o e2o : option Z) : pk_res :=
  let wb := a_base wa in let k := a_off wa in
  if same then prune1pcKF bc None None sp wa w wv K same br2 else
  match K with
  | KZero (SA kb kk) len =>
      match len with
      | ELit _ => prune1pcKF bc None None sp wa w wv K same br2
      | _ => if ranges_apart_pcS bc sp wb k (Z.of_nat w) br2 kb kk len h2o e2o then PKeep else PRepl (kcutB bc KZero wb k (elen w) kb kk len)
      end
  | KFill (SA kb kk) len c =>
      match len with
      | ELit _ => prune1pcKF bc None None sp wa w wv K same br2
      | _ => if ranges_apart_pcS bc sp wb k (Z.of_nat w) br2 kb kk len h2o e2o then PKeep else PRepl (kcutB bc (fun a n => KFill a n c) wb k (elen w) kb kk len)
      end
  | KUnk (SA kb kk) len =>
      match len with
      | ELit _ => prune1pcKF bc None None sp wa w wv K same br2
      | _ => if ranges_apart_pcS bc sp wb k (Z.of_nat w) br2 kb kk len h2o e2o then PKeep else PRepl (kcutB bc KUnk wb k (elen w) kb kk len)
      end
  | KBlob (SA kb kk) len _ =>
      match len with
      | ELit _ => prune1pcKF bc None None sp wa w wv K same br2
      | _ => if ranges_apart_pcS bc sp wb k (Z.of_nat w) br2 kb kk len h2o e2o then PKeep else PRepl []
      end
  | _ => prune1pcKF bc None None sp wa w wv K same br2
  end.
Definition prune1pcKF2 (bc : bctx) (i1 i2 : option bx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
  (br2 : option (Z * Z)) (pre : option (option Z * option Z)) : pk_res :=
  if fastkeep K wa w same then PKeep else
  match pre with
  | Some (h2o, e2o) => prune1pcKS bc sp wa w wv K same br2 h2o e2o
  | None => prune1pcKF bc i1 i2 sp wa w wv K same br2
  end.

Definition zlit64F (z : Z) : Z := if Z.leb 0 z then (if Z.ltb z two64 then z else zmod64 z) else zmod64 z.

Definition wlenF (w : nat) : Z :=
  match w with
  | 1%nat => 1 | 2%nat => 2 | 4%nat => 4 | 8%nat => 8
  | _ => zlit64F (Z.of_nat w)
  end.
Definition kdescrF (K : kentry) : option (expr * Z * option Z) :=
  match K with
  | KWord (SA kb kk) w _ => Some (kb, kk, Some (wlenF w))
  | KZero (SA kb kk) len | KUnk (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
      Some (kb, kk, match len with ELit z => Some (zlit64F z) | _ => None end)
  | KImg lo hi => let d := hi - lo in Some (ELit 0%Z, lo, if Z.ltb d two64 then Some (zlit64F d) else None)
  | _ => None
  end.
Fixpoint shrn (n : nat) (p : positive) : positive :=
  match n with O => p | S n' => match p with xH => xH | xO q => shrn n' q | xI q => shrn n' q end end.
Definition gkeyF (kk : Z) : positive :=
  match kk with Z0 => xH | Zpos p => xI (shrn 16 p) | Zneg p => xO (shrn 16 p) end.
Definition ggroupK (gs : gst) (bid gk : positive) : positive * gst :=
  let inner := match pt_get (gs_gid gs) bid with Some i => i | None => PTLeaf end in
  match pt_get inner gk with
  | Some gid => (gid, gs)
  | None => let gid := gs_next gs in
            (gid, GST (pt_set bid (pt_set gk gid inner) (gs_gid gs)) (Pos.succ gid) (gs_bnds gs))
  end.
Definition ggroupF (gs : gst) (bid : positive) (kk : Z) : positive * gst := ggroupK gs bid (gkeyF kk).
Definition bnd_addF (gs : gst) (gid bid : positive) (obr : option (Z * Z)) (lo hi : Z) : gst :=
  match pt_get (gs_bnds gs) gid with
  | Some (b, o, (l, h)) =>
      if Z.leb l lo then (if Z.leb hi h then gs else GST (gs_gid gs) (gs_next gs) (pt_set gid (b, o, (l, hi)) (gs_bnds gs)))
      else GST (gs_gid gs) (gs_next gs) (pt_set gid (b, o, (lo, if Z.leb hi h then h else hi)) (gs_bnds gs))
  | None => GST (gs_gid gs) (gs_next gs) (pt_set gid (bid, obr, (lo, hi)) (gs_bnds gs))
  end.

Record einfoF := EF { ef_bid : positive; ef_gid : positive; ef_kb : expr; ef_br : option (Z * Z); ef_k : Z; ef_m : option Z; ef_end : Z }.
Definition ef_ei (e : einfoF) : einfo := EI (ef_bid e) (ef_gid e) (ef_kb e) (ef_br e) (ef_k e) (ef_m e).
Fixpoint scanF (bc : bctx) (kn : list kentry) (t : ntab) (gs : gst) : list (option einfoF) * ntab * gst :=
  match kn with
  | [] => ([], t, gs)
  | K :: rest =>
      match kdescrF K with
      | Some (kb, kk, om) =>
          let '(r, t1) := intern bc t kb in
          let '(bid, bi) := r in
          match om with
          | Some m =>
              let ke := kk + m in
              let '(gid, gs0) := ggroupF gs bid kk in
              let '(infos, t2, gs2) := scanF bc rest t1 (bnd_addF gs0 gid bid (bi_br bi) kk ke) in
              (Some (EF bid gid kb (bi_br bi) kk om ke) :: infos, t2, gs2)
          | None =>
              let '(infos, t2, gs2) := scanF bc rest t1 gs in
              (Some (EF bid xH kb (bi_br bi) kk om kk) :: infos, t2, gs2)
          end
      | None =>
          let '(infos, t2, gs2) := scanF bc rest t gs in
          (None :: infos, t2, gs2)
      end
  end.

Fixpoint alookupEF (l : list (expr * positive)) (b : expr) : option positive :=
  match l with
  | [] => None
  | (b', id) :: rest => if expr_eqbF b b' then Some id else alookupEF rest b
  end.
Lemma alookupEF_eq : forall l b, alookupEF l b = alookupE l b.
Proof. induction l as [|[b' id] rest IH]; intros b; [reflexivity|]. cbn [alookupEF alookupE]. rewrite BLKF.expr_eqbF_eq, IH. reflexivity. Qed.
Fixpoint nth4 {A : Type} (n : nat) (l : list A) (d : A) {struct n} : A :=
  match n with
  | S (S (S (S m))) => match l with _ :: _ :: _ :: _ :: r => nth4 m r d | _ => nth n l d end
  | _ => nth n l d
  end.
Lemma nth4_eq : forall (A : Type) n (l : list A) d, nth4 n l d = nth n l d.
Proof.
  intros A n. induction n as [n IH] using (well_founded_induction Wf_nat.lt_wf). intros l d.
  destruct n as [|[|[|[|m]]]]; try reflexivity.
  cbn [nth4]. destruct l as [|a [|b [|c [|e r]]]]; try reflexivity.
  cbn [nth]. apply IH. repeat constructor.
Qed.
Definition internF (bc : bctx) (t : ntab) (b : expr) : positive * binfo * ntab :=
  let k := bkey b in
  match alookupEF (match k with Some n => nth4 n (nt_vars t) [] | None => nt_other t end) b with
  | Some id => (id, match pt_get (nt_info t) id with Some bi => bi | None => BI b (base_rangeB bc b) end, t)
  | None => let id := nt_next t in
            let bi := BI b (base_rangeB bc b) in
            (id, bi, nt_add t k (b, id) bi)
  end.
Lemma internF_eq : forall bc t b, internF bc t b = intern bc t b.
Proof.
  intros bc t b. unfold internF, intern, nt_bucket, lget. rewrite alookupEF_eq. destruct (bkey b); [rewrite nth4_eq|]; reflexivity.
Qed.
Definition intern_c (bc : bctx) (t : ntab) (lb : option (expr * positive * binfo)) (b : expr) : positive * binfo * ntab :=
  match lb with
  | Some (b', id, bi) => if expr_eqbF b b' then (id, bi, t) else internF bc t b
  | None => internF bc t b
  end.
Definition ggroup_c (gs : gst) (lg : option (positive * positive * positive)) (bid gk : positive) : positive * gst :=
  match lg with
  | Some (b', gk', gid) => if Pos.eqb bid b' then (if Pos.eqb gk gk' then (gid, gs) else ggroupK gs bid gk) else ggroupK gs bid gk
  | None => ggroupK gs bid gk
  end.
Fixpoint scanF2 (bc : bctx) (kn : list kentry) (t : ntab) (gs : gst) (lb : option (expr * positive * binfo))
         (lg : option (positive * positive * positive)) : list (option einfoF) * ntab * gst :=
  match kn with
  | [] => ([], t, gs)
  | K :: rest =>
      match kdescrF K with
      | Some (kb, kk, om) =>
          let '(r, t1) := intern_c bc t lb kb in
          let '(bid, bi) := r in
          match om with
          | Some m =>
              let ke := kk + m in
              let gk := gkeyF kk in
              let '(gid, gs0) := ggroup_c gs lg bid gk in
              let '(infos, t2, gs2) := scanF2 bc rest t1 (bnd_addF gs0 gid bid (bi_br bi) kk ke) (Some (kb, bid, bi)) (Some (bid, gk, gid)) in
              (Some (EF bid gid kb (bi_br bi) kk om ke) :: infos, t2, gs2)
          | None =>
              let '(infos, t2, gs2) := scanF2 bc rest t1 gs (Some (kb, bid, bi)) lg in
              (Some (EF bid xH kb (bi_br bi) kk om kk) :: infos, t2, gs2)
          end
      | None =>
          let '(infos, t2, gs2) := scanF2 bc rest t gs lb lg in
          (None :: infos, t2, gs2)
      end
  end.

Definition zfKF (bc : bctx) (i1 i2 : option bx) (sp : sprep) (wa : saddr) (w : nat) (same : bool) (br2 : option (Z * Z))
  (mk : saddr -> expr -> kentry) (kb : expr) (kk : Z) (len : expr) : pk_res :=
  let k := a_off wa in
  let wb := a_base wa in
  if same then
    match len with
    | ELit l0 => PRepl (ktrim mk kb kk l0 k w)
    | _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl (kcutB bc mk wb k (elen w) kb kk len)
    end
  else if ranges_apart_pcF bc i1 i2 sp wb k (elen w) br2 kb kk len then PKeep
  else PRepl (kcutB bc mk wb k (elen w) kb kk len).
Definition prune1pcKF3 (bc : bctx) (i1 i2 : option bx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
  (br2 : option (Z * Z)) : pk_res :=
  match K with
  | KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ => PKeep
  | KImg lo hi =>
      let k := a_off wa in
      match a_base wa with
      | ELit 0 =>
          let r1 := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
          let lo2 := Z.max lo (k + Z.of_nat w) in
          let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
          PRepl (r1 ++ r2)
      | wb => if Z.ltb (hi - lo) two64 then
               (if ranges_apart_pB bc sp wb k (elen w) (ELit 0) lo (ELit (hi - lo)) then PKeep else PRepl [])
             else PRepl []
      end
  | KZero (SA kb kk) len => zfKF bc i1 i2 sp wa w same br2 KZero kb kk len
  | KFill (SA kb kk) len c => zfKF bc i1 i2 sp wa w same br2 (fun a n => KFill a n c) kb kk len
  | KUnk (SA kb kk) len => zfKF bc i1 i2 sp wa w same br2 KUnk kb kk len
  | KWord (SA kb kk) w' v =>
      let k := a_off wa in
      if same then (if Z.leb (kk + Z.of_nat w') k then PKeep else if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl (kword_cut kb kk w' v k w))
      else if ranges_apart_pcF bc i1 i2 sp (a_base wa) k (elen w) br2 kb kk (elen w') then PKeep
      else if (if Nat.eqb w 1 then if Nat.eqb w' 1 then expr_eqb wv v else false else false) then PKeep
      else PRepl []
  | KBlob (SA kb kk) len bk =>
      let k := a_off wa in
      if same then
        match len with
        | ELit l0 => let l := zmod64 l0 in
                     if Z.leb (kk + l) k then PKeep else if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl []
        | _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl []
        end
      else if ranges_apart_pcF bc i1 i2 sp (a_base wa) k (elen w) br2 kb kk len then PKeep else PRepl []
  end.

Definition nov2 (kk l0 k ke : Z) : bool :=
  if Z.ltb 0 l0 then if Z.ltb l0 two64 then (if Z.leb (kk + l0) k then true else Z.leb ke kk) else false else false.
Definition prune1pcKF2' (bc : bctx) (i1 i2 : option bx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
  (br2 : option (Z * Z)) (pre : option (option Z * option Z)) : pk_res :=
  if fastkeep K wa w same then PKeep else
  match pre with
  | Some (h2o, e2o) => prune1pcKS bc sp wa w wv K same br2 h2o e2o
  | None => prune1pcKF3 bc i1 i2 sp wa w wv K same br2
  end.
Definition prune1pcKX (bc : bctx) (si : sxi) (i2 : option bx) (K : kentry) (same : bool)
  (br2 : option (Z * Z)) (pre : option (option Z * option Z)) : pk_res :=
  let sx := si_sx si in
  match K with
  | KWord (SA kb kk) w' v =>
      if same then (let k := a_off (sx_a sx) in if Z.leb (kk + Z.of_nat w') k then PKeep else if Z.leb (si_ke si) kk then PKeep else PRepl (kword_cut kb kk w' v k (sx_w sx)))
      else prune1pcKF2' bc (si_bx si) i2 (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K same br2 pre
  | KZero (SA kb kk) (ELit l0) | KFill (SA kb kk) (ELit l0) _ | KUnk (SA kb kk) (ELit l0) =>
      if same then (if nov2 kk l0 (a_off (sx_a sx)) (si_ke si) then PKeep else prune1pcKF2' bc (si_bx si) i2 (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K same br2 pre)
      else prune1pcKF2' bc (si_bx si) i2 (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K same br2 pre
  | KImg lo hi =>
      match a_base (sx_a sx) with
      | ELit 0 => if (if Z.ltb lo hi then (if Z.leb hi (a_off (sx_a sx)) then true else Z.leb (si_ke si) lo) else false) then PKeep
                  else prune1pcKF2' bc (si_bx si) i2 (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K same br2 pre
      | _ => prune1pcKF2' bc (si_bx si) i2 (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K same br2 pre
      end
  | _ => prune1pcKF2' bc (si_bx si) i2 (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K same br2 pre
  end.

Fixpoint chainK2F2 (bc : bctx) (xo : option bx) (sis : list sxi) (K : kentry) (okb : option expr) (same_of : positive -> bool)
         (br2 : option (Z * Z)) (pre : option (option Z * option Z)) : list kentry :=
  match sis with
  | [] => [K]
  | si :: rest =>
      let sx := si_sx si in
      match prune1pcKX bc si xo K (same_of (sx_bid sx)) br2 pre with
      | PKeep => chainK2F2 bc xo rest K okb same_of br2 pre
      | PRepl l =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2F2 bc xo rest K' okb same_of br2 None else chain_slowF bc rest [K']
                                  | None => chain_slowF bc rest [K']
                                  end) l
          | None => chain_slowF bc rest l
          end
      end
  end.

Fixpoint chainKFF2 (bc : bctx) (xo : option bx) (fl : list (sxi * list sxi)) (K : kentry) (okb : option expr) (same_of : positive -> bool)
         (br2 : option (Z * Z)) (pre : option (option Z * option Z)) : list kentry :=
  match fl with
  | [] => [K]
  | (si, rest) :: fl' =>
      let sx := si_sx si in
      match prune1pcKX bc si xo K (same_of (sx_bid sx)) br2 pre with
      | PKeep => chainKFF2 bc xo fl' K okb same_of br2 pre
      | PRepl l =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2F2 bc xo rest K' okb same_of br2 None else chain_slowF bc rest [K']
                                  | None => chain_slowF bc rest [K']
                                  end) l
          | None => chain_slowF bc rest l
          end
      end
  end.

Fixpoint mk_flG (skip : sxi -> bool) (sis : list sxi) : list (sxi * list sxi) :=
  match sis with
  | si :: srest => if skip si then mk_flG skip srest else (si, srest) :: mk_flG skip srest
  | [] => []
  end.

Fixpoint in_sides_num (bc : bctx) (D : list (saddr * expr)) (b : expr) (k n : Z) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if num_sub bc b k n c m then true else in_sides_num bc r b k n
  end.

Definition linV2 (bc : bctx) (si : sxi) (b : positive) (glo ghi : Z) (gx : option gxi) : bool :=
  match gx with
  | Some x =>
      if Pos.eqb b (sx_bid (si_sx si)) then false else
      if (if Z.leb 0 (ghi - glo) then Z.ltb (ghi - glo) two63z else false) then
        let sx := si_sx si in
        if in_sides_num bc (sp_D (sx_sp sx)) (gx_b x) glo (ghi - glo) then true
        else if lin_apartF bc (si_bx si) (gx_bx x) (a_base (sx_a sx)) (a_off (sx_a sx)) (zlit64F (Z.of_nat (sx_w sx))) (gx_b x) glo (ghi - glo) then true
        else in_sidesB bc (sp_D (sx_sp sx)) (gx_b x) glo (ghi - glo)
      else false
  | None => false
  end.

Definition gflF2 : Type := (positive * Z * Z * list (sxi * list sxi))%type.

Definition eni_of2 (K : kentry) (br2 : option (Z * Z)) (h2o e2o : option Z) : option (PrimInt63.int * PrimInt63.int * option PrimInt63.int) :=
  match K with
  | KZero (SA _ kk) len | KFill (SA _ kk) len _ | KUnk (SA _ kk) len | KBlob (SA _ kk) len _ =>
      match len with
      | ELit _ => None
      | _ =>
          match br2, h2o with
          | Some (lo2, hi2), Some h2 =>
              match z2i (lo2 + kk), z2i (hi2 + kk + h2) with
              | Some el, Some eh =>
                  match e2o with
                  | None => Some (el, eh, None)
                  | Some e2 => match z2i e2 with Some i => Some (el, eh, Some i) | None => None end
                  end
              | _, _ => None
              end
          | _, _ => None
          end
      end
  | _ => None
  end.
Fixpoint stores_partF2 (bc : bctx) (sis : list sxi) : list kentry :=
  match sis with
  | [] => []
  | si :: newer => let sx := si_sx si in
                   stores_partF2 bc newer ++ chainK2F2 bc (si_bx si) newer (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx) None
  end.

Definition mk_sctx (bc : bctx) (ex : bext) (s : sentry) : sprep :=
  match s with SE a w v => mk_sprepF bc (be_kd ex) (a_base a) (a_off a) (elen w) end.

Definition intern_r (t : ntab) (b : expr) (br : option (Z * Z)) : positive * binfo * ntab :=
  let k := bkey b in
  match alookupEF (match k with Some n => nth4 n (nt_vars t) [] | None => nt_other t end) b with
  | Some id => (id, match pt_get (nt_info t) id with Some bi => bi | None => BI b br end, t)
  | None => let id := nt_next t in
            let bi := BI b br in
            (id, bi, nt_add t k (b, id) bi)
  end.
Lemma intern_r_eq : forall bc t b, intern_r t b (base_rangeB bc b) = intern bc t b.
Proof.
  intros bc t b. unfold intern_r, intern, nt_bucket, lget. rewrite alookupEF_eq. destruct (bkey b); [rewrite nth4_eq|]; reflexivity.
Qed.
Fixpoint mk_stxsC2 (log : list sentry) (scs : list sprep) (t : ntab) : list stx * ntab :=
  match log, scs with
  | SE a w v :: older, sp :: scs' =>
      let '(sxs, t1) := mk_stxsC2 older scs' t in
      let '(r, t2) := intern_r t1 (a_base a) (sp_rng sp) in
      let '(bid, bi) := r in
      (sxs ++ [STX a w v sp bid (bi_br bi)], t2)
  | _, _ => ([], t)
  end.

Lemma mk_stxs_okG : forall bc log t sxs t',
  NTI bc t -> mk_stxs bc log t = (sxs, t') ->
  NTI bc t' /\ Forall (SX_OK bc t') sxs /\ (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k)).
Proof.
  intros bc log. induction log as [|[a w v] older IH]; intros t sxs t' HT H.
  - cbn in H. injection H as <- <-. split; [exact HT|]. split; [constructor|]. intros; assumption.
  - cbn [mk_stxs] in H. destruct (mk_stxs bc older t) as [sxs0 t1] eqn:E0.
    destruct (intern bc t1 (a_base a)) as [[bid bi] t2] eqn:EI.
    injection H as <- <-.
    destruct (IH t sxs0 t1 HT E0) as (HT1 & HS & Hm1).
    destruct (intern_ok _ _ _ _ _ _ HT1 EI) as (HT2 & -> & HIn & Hm2).
    split; [exact HT2|]. split.
    + apply Forall_app. split.
      * apply Forall_impl with (P := SX_OK bc t1); [|exact HS]. intros sx. apply SX_OK_mono. exact Hm2.
      * constructor; [|constructor]. split; [exact HIn|]. split; reflexivity.
    + intros k p Hp. apply Hm2. apply Hm1. exact Hp.
Qed.

Lemma scan_entries_okG : forall bc kn t gs infos t' gs',
  NTI bc t -> scan_entries bc kn t gs = (infos, t', gs') ->
  NTI bc t' /\ (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k)) /\ Forall2 (EINF bc t') kn infos.
Proof.
  intros bc kn. induction kn as [|K rest IH]; intros t gs infos t' gs' HT H.
  - cbn in H. injection H as <- <- <-. split; [exact HT|]. split; [intros; assumption|]. constructor.
  - cbn [scan_entries] in H.
    destruct (kdescr K) as [[[kb kk] om]|] eqn:HD.
    + destruct (intern bc t kb) as [[bid bi] t1] eqn:EI.
      destruct (intern_ok _ _ _ _ _ _ HT EI) as (HT1 & Hbi & HIn & Hm1).
      lazymatch type of H with (let '(_, _) := ?X in _) = _ => destruct X as [gid gs1] end.
      destruct (scan_entries bc rest t1 _) as [[infos2 t2] gs2] eqn:ES.
      injection H as <- <- <-.
      destruct (IH _ _ _ _ _ HT1 ES) as (HT2 & Hm2 & HF).
      split; [exact HT2|]. split; [intros k p Hp; apply Hm2; apply Hm1; exact Hp|].
      constructor; [|exact HF]. cbn [EINF ei_kb ei_k ei_m ei_bid ei_br].
      split; [exact HD|]. split; [apply Hm2; exact HIn|]. rewrite Hbi. reflexivity.
    + destruct (scan_entries bc rest t gs) as [[infos2 t2] gs2] eqn:ES.
      injection H as <- <- <-.
      destruct (IH _ _ _ _ _ HT ES) as (HT2 & Hm2 & HF).
      split; [exact HT2|]. split; [exact Hm2|]. constructor; [exact HD | exact HF].
Qed.

Lemma verdict_keepG : forall bc t sx g ei K,
  NTI bc t -> SX_OK bc t sx -> EINF bc t K (Some ei) -> inb g ei = true -> verdict sx g = true ->
  prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K
     (match kbase K with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end (sx_bid sx))
     (match kbase K with Some _ => ei_br ei | None => None end) = PKeep.
Proof.
  intros bc t sx g ei K HT HSX HK Hinb Hv. cbn [EINF] in HK. destruct HK as (HD & HIn & Hbr).
  assert (Hm : exists m, ei_m ei = Some m).
  { unfold inb in Hinb. destruct (ei_m ei) as [m|]; [exists m; reflexivity|discriminate]. }
  destruct Hm as [m Hm].
  destruct (verdict_inb_num _ _ _ _ Hv Hinb Hm) as (Hne & lo1 & hi1 & lo2 & hi2 & Hsp & Hbr2 & Hnum).
  destruct HSX as (SXin & SXbr & SXsp).
  rewrite Hm in HD.
  destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
  - rewrite HB. rewrite Hne. rewrite Hbr. eapply prune1pcK_keep_based; [exact HB|exact HD|exact Hsp| | exact Hnum].
    rewrite <- Hbr. exact Hbr2.
  - cbn [kbase]. rewrite Hkb, Hk in *.
    eapply prune1pcK_keep_img; [exact HD| |exact Hsp| rewrite <- Hbr; exact Hbr2 | exact Hnum].
    rewrite <- (nt_same_eq _ _ _ _ _ _ HT HIn SXin). exact Hne.
Qed.

Lemma two64_pow : (2 ^ 64)%Z = two64. Proof. reflexivity. Qed.
Lemma ktrim_nov : forall (mk : saddr -> expr -> kentry) kb kk l0 k w, nov kk l0 k w = true -> ktrim mk kb kk l0 k w = [mk (SA kb kk) (ELit l0)].
Proof.
  intros mk kb kk l0 k w H. unfold nov in H. unfold ktrim. rewrite two64_pow.
  destruct (Z.ltb_spec 0 l0); [|discriminate]. destruct (Z.ltb_spec l0 two64); [|discriminate].
  rewrite (Z.mod_small l0 two64) by lia.
  destruct (Z.leb_spec (kk + l0) k).
  - rewrite (Z.min_r k (kk + l0)) by lia. destruct (Z.ltb_spec kk (kk + l0)); [|lia].
    destruct (Z.ltb_spec (Z.max kk (k + Z.of_nat w)) (kk + l0)); [lia|].
    replace (kk + l0 - kk) with l0 by lia. reflexivity.
  - apply Z.leb_le in H. rewrite (Z.min_l k (kk + l0)) by lia. destruct (Z.ltb_spec kk k); [lia|].
    rewrite (Z.max_l kk (k + Z.of_nat w)) by lia. destruct (Z.ltb_spec kk (kk + l0)); [|lia].
    replace (kk + l0 - kk) with l0 by lia. reflexivity.
Qed.
Lemma img_nov_eq : forall lo hi k w, img_nov lo hi k w = true ->
  (if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else []) ++
  (if Z.ltb (Z.max lo (k + Z.of_nat w)) hi then [KImg (Z.max lo (k + Z.of_nat w)) hi] else []) = [KImg lo hi].
Proof.
  intros lo hi k w H. unfold img_nov in H. destruct (Z.ltb_spec lo hi); [|discriminate].
  destruct (Z.leb_spec hi k).
  - rewrite (Z.min_r k hi) by lia. destruct (Z.ltb_spec lo hi); [|lia].
    destruct (Z.ltb_spec (Z.max lo (k + Z.of_nat w)) hi); [lia|]. reflexivity.
  - apply Z.leb_le in H. destruct (Z.ltb_spec lo (Z.min k hi)); [lia|].
    rewrite (Z.max_l lo (k + Z.of_nat w)) by lia. destruct (Z.ltb_spec lo hi); [|lia]. reflexivity.
Qed.
Lemma fastkeep_rel : forall bc sp wa w wv K same br2, fastkeep K wa w same = true ->
  prune1pcK bc sp wa w wv K same br2 = PRepl [K].
Proof.
  intros bc sp wa w wv K same br2 H.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    cbn [fastkeep] in H; try discriminate.
  - destruct len as [l0| | | | | | |]; try discriminate. destruct same; [|discriminate].
    unfold prune1pcK. cbv zeta. rewrite (ktrim_nov _ _ _ _ _ _ H). reflexivity.
  - unfold prune1pcK. cbv zeta. destruct wa as [wb k]. cbn [a_base a_off] in *.
    destruct wb as [z| | | | | | |]; try discriminate. destruct z; try discriminate.
    rewrite (img_nov_eq _ _ _ _ H). reflexivity.
  - destruct len as [l0| | | | | | |]; try discriminate. destruct same; [|discriminate].
    unfold prune1pcK. cbv zeta. rewrite (ktrim_nov _ _ _ _ _ _ H). reflexivity.
  - destruct len as [l0| | | | | | |]; try discriminate. destruct same; [|discriminate].
    unfold prune1pcK. cbv zeta. rewrite (ktrim_nov _ _ _ _ _ _ H). reflexivity.
Qed.

Lemma ranges_apart_pcS_eq : forall bc sp b1 k1 z1 br2 b2 k2 n2, (forall z, n2 <> ELit z) ->
  ranges_apart_pcS bc sp b1 k1 z1 br2 b2 k2 n2 (xhiB bc n2)
     (match br2, xhiB bc n2 with Some (lo2, hi2), Some h2 => end_hiB bc b2 k2 n2 lo2 hi2 h2 | _, _ => None end)
  = ranges_apart_pcB bc sp b1 k1 (ELit z1) br2 b2 k2 n2.
Proof.
  intros bc sp b1 k1 z1 br2 b2 k2 n2 Hn.
  assert (E : ranges_apart_pcB bc sp b1 k1 (ELit z1) br2 b2 k2 n2 =
    if (match sp_rng sp, br2, sp_h1 sp, xhiB bc n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else if match end_hiB bc b1 k1 (ELit z1) lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_xB bc (sp_Dx sp) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0B bc [(b2, k2)] [(b1, k1); (ELit z1, 0%Z)] then true
    else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]).
  { unfold ranges_apart_pcB. destruct n2 as [z| | | | | | |]; [exfalso; exact (Hn z eq_refl)| ..]; reflexivity. }
  rewrite E. unfold ranges_apart_pcS. cbv [orb negb].
  destruct (shares_var b1 b2);
  (destruct (sp_rng sp) as [[lo1 hi1]|]; [|reflexivity]);
  (destruct br2 as [[lo2 hi2]|]; [|destruct (sp_h1 sp); destruct (xhiB bc n2); reflexivity]);
  (destruct (sp_h1 sp) as [h1|]; [|destruct (xhiB bc n2); reflexivity]);
  (destruct (xhiB bc n2) as [h2|]; [|reflexivity]);
  change (end_hiB bc b1 k1 (ELit z1) lo1 hi1 h1) with (@None Z);
  (destruct (hi1 + k1 + h1 <=? lo2 + k2); [reflexivity|]);
  (destruct (hi2 + k2 + h2 <=? lo1 + k1); reflexivity).
Qed.

Lemma BXOK_None : forall bc, BXOK bc None.
Proof. intros bc x H. discriminate. Qed.
Lemma prune1pcKS_eq : forall bc sp wa w wv K same br2,
  prune1pcKS bc sp wa w wv K same br2 (fst (mk_pre bc K br2)) (snd (mk_pre bc K br2)) = prune1pcK bc sp wa w wv K same br2.
Proof.
  intros bc sp wa w wv K same br2. unfold prune1pcKS.
  rewrite (prune1pcKF_eq bc None None (BXOK_None bc) (BXOK_None bc)).
  destruct same; [reflexivity|].
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    try reflexivity;
    (destruct len as [l0| | | | | | |]; [reflexivity| ..]);
    cbn [mk_pre fst snd]; unfold prune1pcK; cbv zeta; cbn [a_base a_off];
    (rewrite ranges_apart_pcS_eq by discriminate);
    (destruct (ranges_apart_pcB _ _ _ _ _ _ _ _ _); [reflexivity|]);
    try reflexivity;
    (destruct (kcutB _ _ _ _ _ _ _ _); reflexivity).
Qed.

Definition pk_rel (K : kentry) (r' r : pk_res) : Prop := r' = r \/ (r' = PKeep /\ r = PRepl [K]).
Definition PRE_OK (bc : bctx) (K : kentry) (br2 : option (Z * Z)) (pre : option (option Z * option Z)) : Prop :=
  match pre with None => True | Some p => p = mk_pre bc K br2 end.
Lemma prune1pcKF2_rel : forall bc i1 i2 sp wa w wv K same br2 pre, BXOK bc i1 -> BXOK bc i2 -> PRE_OK bc K br2 pre ->
  pk_rel K (prune1pcKF2 bc i1 i2 sp wa w wv K same br2 pre) (prune1pcK bc sp wa w wv K same br2).
Proof.
  intros bc i1 i2 sp wa w wv K same br2 pre H1 H2 HP. unfold prune1pcKF2.
  destruct (fastkeep K wa w same) eqn:E.
  - right. split; [reflexivity|]. apply fastkeep_rel. exact E.
  - left. destruct pre as [[h2o e2o]|].
    + cbn [PRE_OK] in HP. rewrite (surjective_pairing (mk_pre bc K br2)) in HP. injection HP as -> ->. apply prune1pcKS_eq.
    + rewrite (prune1pcKF_eq bc i1 i2 H1 H2). reflexivity.
Qed.

Lemma g1cB_nobase : forall bc sx K same br2, kbase K = None ->
  g1cB bc sx K = pk_list K (prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K same br2).
Proof.
  intros bc sx K same br2 HK. unfold g1cB, obrB. rewrite HK.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    cbn [kbase] in HK; try discriminate; try reflexivity.
  unfold prune1pcB, prune1pB, prune1pcK. cbv zeta. destruct (sx_a sx) as [wb k]. cbn [a_base a_off].
  destruct wb as [z| | | | | | |];
    try (destruct (Z.ltb (hi - lo) (2 ^ 64)); [destruct (ranges_apart_pB _ _ _ _ _ _ _ _); reflexivity|reflexivity]).
  destruct z; try reflexivity;
    (destruct (Z.ltb (hi - lo) (2 ^ 64)); [destruct (ranges_apart_pB _ _ _ _ _ _ _ _); reflexivity|reflexivity]).
Qed.
Lemma chain_slow_nobase : forall bc sxs K same_of br2, kbase K = None ->
  chain_slow bc sxs [K] = chainK2 bc sxs K None same_of br2.
Proof.
  intros bc sxs K same_of br2 HK. induction sxs as [|sx rest IH]; [reflexivity|].
  cbn [chain_slow chainK2 flat_map]. rewrite app_nil_r, (g1cB_nobase bc sx K (same_of (sx_bid sx)) br2 HK).
  destruct (prune1pcK _ _ _ _ _ K _ br2); [exact IH|reflexivity].
Qed.
Lemma flat_map_ext_in : forall (A B : Type) (f g : A -> list B) l, (forall x, In x l -> f x = g x) -> flat_map f l = flat_map g l.
Proof. intros A B f g l H. induction l as [|x r IH]; [reflexivity|]. cbn. rewrite H by (left; reflexivity). rewrite IH by (intros; apply H; right; assumption). reflexivity. Qed.

Lemma prune1pcKF3_eq : prune1pcKF3 = prune1pcKF.
Proof.
  fe. rename x into bc, x0 into i1, x1 into i2, x2 into sp, x3 into wa, x4 into w, x5 into wv, x6 into K, x7 into same, x8 into br2.
  unfold prune1pcKF3, prune1pcKF, zfKF. cbv zeta.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    try reflexivity.
Qed.
Lemma prune1pcKF2'_eq : prune1pcKF2' = prune1pcKF2.
Proof. fe. unfold prune1pcKF2', prune1pcKF2. rewrite prune1pcKF3_eq. reflexivity. Qed.
Lemma prune1pcKX_eq : forall bc X sx i2 K same br2 pre,
  prune1pcKX bc (mk_sxi X sx) i2 K same br2 pre = prune1pcKF2 bc (xget X (sx_bid sx)) i2 (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K same br2 pre.
Proof.
  intros bc X sx i2 K same br2 pre. unfold prune1pcKX. rewrite prune1pcKF2'_eq. cbn [si_sx si_bx si_ke mk_sxi]. cbv zeta beta.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    try reflexivity.
  - destruct same; [|reflexivity]. unfold prune1pcKF2. cbn [fastkeep].
    destruct pre as [[h2o e2o]|]; unfold prune1pcKS, prune1pcKF; cbv zeta; reflexivity.
  - destruct len as [l0| | | | | | |]; try reflexivity. destruct same; [|reflexivity].
    unfold prune1pcKF2, nov2. cbn [fastkeep]. unfold nov. destruct (Z.ltb 0 l0), (Z.ltb l0 two64), (Z.leb (kk + l0) (a_off (sx_a sx))), (Z.leb (a_off (sx_a sx) + Z.of_nat (sx_w sx)) kk); reflexivity.
  - unfold prune1pcKF2. cbn [fastkeep]. destruct (sx_a sx) as [wb k]. cbn [a_base a_off].
    destruct wb as [z| | | | | | |]; try reflexivity. destruct z; try reflexivity.
    unfold img_nov. destruct (Z.ltb lo hi), (Z.leb hi k), (Z.leb (k + Z.of_nat (sx_w sx)) lo); reflexivity.
  - destruct len as [l0| | | | | | |]; try reflexivity. destruct same; [|reflexivity].
    unfold prune1pcKF2, nov2. cbn [fastkeep]. unfold nov. destruct (Z.ltb 0 l0), (Z.ltb l0 two64), (Z.leb (kk + l0) (a_off (sx_a sx))), (Z.leb (a_off (sx_a sx) + Z.of_nat (sx_w sx)) kk); reflexivity.
  - destruct len as [l0| | | | | | |]; try reflexivity. destruct same; [|reflexivity].
    unfold prune1pcKF2, nov2. cbn [fastkeep]. unfold nov. destruct (Z.ltb 0 l0), (Z.ltb l0 two64), (Z.leb (kk + l0) (a_off (sx_a sx))), (Z.leb (a_off (sx_a sx) + Z.of_nat (sx_w sx)) kk); reflexivity.
Qed.

Lemma chainK2F2_eq : forall bc X xo sxs K okb same_of br2 pre, XOK bc X -> BXOK bc xo -> okb = kbase K -> PRE_OK bc K br2 pre ->
  chainK2F2 bc xo (map (mk_sxi X) sxs) K okb same_of br2 pre = chainK2 bc sxs K okb same_of br2.
Proof.
  intros bc X xo sxs. induction sxs as [|sx rest IH]; intros K okb same_of br2 pre HX Hxo Hokb HP; [reflexivity|].
  cbn [map chainK2F2 chainK2]. rewrite prune1pcKX_eq. cbn [si_sx si_bx mk_sxi].
  destruct (prune1pcKF2_rel bc (xget X (sx_bid sx)) xo (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 pre (HX (sx_bid sx)) Hxo HP)
    as [E|[E1 E2]].
  - rewrite E. destruct (prune1pcK _ _ _ _ _ K _ br2) as [|l]; [apply IH; assumption|].
    destruct okb as [kb|]; [|(rewrite chain_slowF_eq; reflexivity)].
    apply flat_map_ext_in. intros K' _. destruct (kbase K') as [kb'|] eqn:HB; [|(rewrite chain_slowF_eq; reflexivity)].
    destruct (expr_eqb kb' kb) eqn:EQ; [|(rewrite chain_slowF_eq; reflexivity)].
    apply p_expr_eqb_eq in EQ. subst kb'. apply IH; [exact HX|exact Hxo|symmetry; exact HB|exact I].
  - rewrite E1, E2. rewrite (IH K okb same_of br2 pre HX Hxo Hokb HP).
    destruct okb as [kb|].
    + cbn [flat_map]. rewrite <- Hokb, p_expr_eqb_refl, app_nil_r. reflexivity.
    + symmetry. apply chain_slow_nobase. symmetry. exact Hokb.
Qed.

Lemma chainKFF2_eqG : forall bc X xo skip sxs K okb same_of br2 pre,
  XOK bc X -> BXOK bc xo -> okb = kbase K -> PRE_OK bc K br2 pre ->
  (forall sx, In sx sxs -> skip (mk_sxi X sx) = true ->
     prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 = PKeep) ->
  chainKFF2 bc xo (mk_flG skip (map (mk_sxi X) sxs)) K okb same_of br2 pre = chainK2 bc sxs K okb same_of br2.
Proof.
  intros bc X xo skip sxs K okb same_of br2 pre HX Hxo Hokb HP. induction sxs as [|sx rest IH]; intros HS; [reflexivity|].
  assert (IH' : chainKFF2 bc xo (mk_flG skip (map (mk_sxi X) rest)) K okb same_of br2 pre = chainK2 bc rest K okb same_of br2)
    by (apply IH; intros sx' Hin; apply HS; right; exact Hin).
  cbn [map mk_flG chainK2].
  destruct (skip (mk_sxi X sx)) eqn:EV.
  { rewrite (HS sx (or_introl eq_refl) EV). exact IH'. }
  cbn [chainKFF2]. rewrite prune1pcKX_eq. cbn [si_sx si_bx mk_sxi].
  destruct (prune1pcKF2_rel bc (xget X (sx_bid sx)) xo (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 pre (HX (sx_bid sx)) Hxo HP)
    as [E|[E1 E2]].
  - rewrite E. destruct (prune1pcK _ _ _ _ _ K _ br2) as [|l]; [exact IH'|].
    destruct okb as [kb|]; [|(rewrite chain_slowF_eq; reflexivity)].
    apply flat_map_ext_in. intros K' _. destruct (kbase K') as [kb'|] eqn:HB; [|(rewrite chain_slowF_eq; reflexivity)].
    destruct (expr_eqb kb' kb) eqn:EQ; [|(rewrite chain_slowF_eq; reflexivity)].
    apply p_expr_eqb_eq in EQ. subst kb'. apply chainK2F2_eq; [exact HX|exact Hxo|symmetry; exact HB|exact I].
  - rewrite E1, E2, IH'.
    destruct okb as [kb|].
    + cbn [flat_map]. rewrite <- Hokb, p_expr_eqb_refl, app_nil_r. reflexivity.
    + symmetry. apply chain_slow_nobase. symmetry. exact Hokb.
Qed.

Fixpoint entC (bc : bctx) (sxs : list stx) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | Some ei => chainK2 bc sxs K (kbase K) (match kbase K with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end)
                            (match kbase K with Some _ => ei_br ei | None => None end)
       | None => chainK2 bc sxs K None (fun _ => false) None
       end) ++ entC bc sxs rest irest
  | _, _ => []
  end.
Definition ei_strip (oi : option einfo) : option (positive * option (Z * Z)) :=
  match oi with Some ei => Some (ei_bid ei, ei_br ei) | None => None end.
Lemma entC_strip : forall bc sxs kn infos1 infos2, map ei_strip infos1 = map ei_strip infos2 -> entC bc sxs kn infos1 = entC bc sxs kn infos2.
Proof.
  intros bc sxs kn. induction kn as [|K rest IH]; intros infos1 infos2 H; [reflexivity|].
  destruct infos1 as [|o1 r1]; destruct infos2 as [|o2 r2]; cbn [map] in H; try discriminate; [reflexivity|].
  injection H as H1 H2. cbn [entC]. rewrite (IH r1 r2 H2). f_equal.
  destruct o1 as [e1|]; destruct o2 as [e2|]; cbn [ei_strip] in H1; try discriminate; [|reflexivity].
  injection H1 as -> ->. reflexivity.
Qed.

Lemma entriesG_C : forall bc t sxs bnds kn infos, NTI bc t -> Forall (SX_OK bc t) sxs -> Forall2 (EINF bc t) kn infos ->
  entriesG bc sxs (mk_gl bnds sxs) kn infos = entC bc sxs kn infos.
Proof.
  intros bc t sxs bnds kn infos HT HS HF. induction HF as [|K oi rest irest HK HF IH]; [reflexivity|].
  cbn [entriesG entC]. rewrite IH. f_equal.
  destruct oi as [ei|]; [|reflexivity].
  unfold mk_gl. rewrite pt_get_map.
  destruct (pt_get bnds (ei_gid ei)) as [g|]; [|reflexivity].
  destruct (inb g ei) eqn:Hinb; [|reflexivity].
  apply chainKF_eq. intros sx Hsx Hv.
  exact (verdict_keepG bc t sx g ei K HT (proj1 (Forall_forall _ _) HS sx Hsx) HK Hinb Hv).
Qed.

Definition EINFF (bc : bctx) (t : ntab) (K : kentry) (oi : option einfoF) : Prop :=
  match oi with
  | None => kdescr K = None
  | Some e => EINF bc t K (Some (ef_ei e)) /\ (forall m, ef_m e = Some m -> ef_end e = ef_k e + m)
  end.
Lemma obr_eqb_refl : forall o, obr_eqb o o = true.
Proof. intros [[x y]|]; cbn [obr_eqb]; [rewrite !Z.eqb_refl|]; reflexivity. Qed.
Lemma nti_info : forall bc t b id, NTI bc t -> In (b, id) (nt_bucket t (bkey b)) -> pt_get (nt_info t) id = Some (BI b (base_rangeB bc b)).
Proof. intros bc t b id [HA _] H. exact (proj1 (proj2 (HA _ _ _ H))). Qed.
Lemma zlit64F_eq : forall z, zlit64F z = zlit64 z.
Proof.
  intros z. unfold zlit64F, zlit64. rewrite zmod64_eq2.
  destruct (Z.leb 0 z); [|reflexivity]. destruct (Z.ltb z two64); reflexivity.
Qed.
Lemma in_sides_num_in : forall bc D b k n, in_sides_num bc D b k n = true -> in_sidesB bc D b k n = true.
Proof.
  intros bc D b k n. induction D as [|[c m] r IH]; cbn [in_sides_num in_sidesB]; [discriminate|].
  unfold num_sub, sub_itvB. cbv [andb].
  intros H. destruct (if expr_eqb b (a_base c) then Z.leb (a_off c) k else false).
  - destruct (match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end); [reflexivity|].
    destruct (if if 0 <=? n then n <? two64 else false then xinsideB bc b k (ELit n) (a_base c) (a_off c) m else false); [reflexivity|exact (IH H)].
  - destruct (if if 0 <=? n then n <? two64 else false then xinsideB bc b k (ELit n) (a_base c) (a_off c) m else false); [reflexivity|exact (IH H)].
Qed.
Lemma linV2_linV : forall bc si b obr glo ghi gx, linV2 bc si b glo ghi gx = true -> linV bc si b obr glo ghi gx = true.
Proof.
  intros bc si b obr glo ghi gx H. unfold linV2 in H. unfold linV.
  destruct gx as [x|]; [|discriminate]. destruct (Pos.eqb b (sx_bid (si_sx si))); [discriminate|].
  destruct (if Z.leb 0 (ghi - glo) then Z.ltb (ghi - glo) two63z else false) eqn:Eg; [|discriminate].
  assert (Hz : zlit64 (ghi - glo) = ghi - glo).
  { unfold zlit64. rewrite two63z_val in Eg. destruct (Z.leb_spec 0 (ghi - glo)); [|discriminate].
    destruct (Z.ltb_spec (ghi - glo) 9223372036854775808); [|discriminate].
    destruct (Z.leb_spec 0 (ghi - glo)), (Z.ltb_spec (ghi - glo) two64); cbn [andb]; first [reflexivity | rewrite two64_val in *; lia]. }
  unfold ranges_apart_pcF, elen. cbv zeta. rewrite Hz, <- zlit64F_eq.
  destruct (match sp_rng (sx_sp (si_sx si)) with Some (lo1, hi1) => _ | None => false end); [reflexivity|].
  destruct (in_sides_num bc (sp_D (sx_sp (si_sx si))) (gx_b x) glo (ghi - glo)) eqn:EN.
  - destruct (lin_apartF _ _ _ _ _ _ _ _ _); [reflexivity|]. apply in_sides_num_in. exact EN.
  - destruct (lin_apartF _ _ _ _ _ _ _ _ _); [reflexivity|]. exact H.
Qed.

Lemma z2i_val : forall z i, z2i z = Some i -> Uint63Axioms.to_Z i = z.
Proof.
  intros z i H. destruct z as [|p|p]; cbn [z2i] in H; [injection H as <-; exact i0_val|exact (proj1 (P2Q.p2iQ4_val p i H))|discriminate].
Qed.
Lemma z2i_leb : forall a b ai bi, z2i a = Some ai -> z2i b = Some bi -> PrimInt63.leb ai bi = Z.leb a b.
Proof.
  intros a b ai bi Ha Hb. apply z2i_val in Ha. apply z2i_val in Hb.
  destruct (PrimInt63.leb ai bi) eqn:E; symmetry.
  - apply Uint63Axioms.leb_spec in E. apply Z.leb_le. lia.
  - apply Z.leb_gt. destruct (Z.le_gt_cases a b) as [H|H]; [|exact H].
    exfalso. assert (X : PrimInt63.leb ai bi = true) by (apply Uint63Axioms.leb_spec; lia). congruence.
Qed.
Lemma rap_num : forall bc sp b1 k1 z1 br2 b2 k2 n2 lo1 hi1 h1 lo2 hi2 h2,
  (forall z, n2 <> ELit z) -> sp_rng sp = Some (lo1, hi1) -> sp_h1 sp = Some h1 -> br2 = Some (lo2, hi2) -> xhiB bc n2 = Some h2 ->
  (if Z.leb (hi1 + k1 + h1) (lo2 + k2) then true else if Z.leb (hi2 + k2 + h2) (lo1 + k1) then true
   else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end) = true ->
  ranges_apart_pcB bc sp b1 k1 (ELit z1) br2 b2 k2 n2 = true.
Proof.
  intros bc sp b1 k1 z1 br2 b2 k2 n2 lo1 hi1 h1 lo2 hi2 h2 Hn H1 H2 H3 H4 H. subst br2.
  assert (E : ranges_apart_pcB bc sp b1 k1 (ELit z1) (Some (lo2, hi2)) b2 k2 n2 =
    if (match sp_rng sp, Some (lo2, hi2), sp_h1 sp, xhiB bc n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else if match end_hiB bc b1 k1 (ELit z1) lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_xB bc (sp_Dx sp) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0B bc [(b2, k2)] [(b1, k1); (ELit z1, 0%Z)] then true
    else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]).
  { unfold ranges_apart_pcB. destruct n2 as [z| | | | | | |]; [exfalso; exact (Hn z eq_refl)| ..]; reflexivity. }
  rewrite E, H1, H2, H4. change (end_hiB bc b1 k1 (ELit z1) lo1 hi1 h1) with (@None Z). cbv [orb].
  destruct (hi1 + k1 + h1 <=? lo2 + k2); [reflexivity|]. destruct (hi2 + k2 + h2 <=? lo1 + k1); [reflexivity|].
  rewrite H. reflexivity.
Qed.

Lemma wlenF_eq : forall w, wlenF w = zlit64F (Z.of_nat w).
Proof. intros w. do 9 (destruct w as [|w]; [reflexivity|]). reflexivity. Qed.
Lemma kdescrF_eq : forall K, kdescrF K = kdescr K.
Proof.
  intros K. unfold kdescrF, kdescr.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    cbv zeta; rewrite ?wlenF_eq, ?two64_pow; try reflexivity; try (rewrite zlit64F_eq; reflexivity); destruct len; rewrite ?zlit64F_eq; reflexivity.
Qed.
Lemma scanF_sim : forall bc kn t gs gs' infos1 t1 gs1 infos2 t2 gs2,
  scanF bc kn t gs = (infos1, t1, gs1) -> scan_entries bc kn t gs' = (infos2, t2, gs2) ->
  t1 = t2 /\ map ei_strip (map (option_map ef_ei) infos1) = map ei_strip infos2.
Proof.
  intros bc kn. induction kn as [|K rest IH]; intros t gs gs' infos1 t1 gs1 infos2 t2 gs2 H1 H2.
  - cbn in H1, H2. injection H1 as <- <- <-. injection H2 as <- <- <-. split; reflexivity.
  - cbn [scanF scan_entries] in H1, H2. rewrite kdescrF_eq in H1.
    destruct (kdescr K) as [[[kb kk] om]|].
    + destruct (intern bc t kb) as [[bid bi] t3].
      lazymatch type of H2 with (let '(_, _) := ?X in _) = _ => destruct X as [gid' gs3'] end.
      destruct (scan_entries bc rest t3 gs3') as [[i2 t5] g5] eqn:E2. injection H2 as <- <- <-.
      destruct om as [m|].
      * lazymatch type of H1 with (let '(_, _) := ?X in _) = _ => destruct X as [gid gs3] end.
        destruct (scanF bc rest t3 _) as [[i1 t4] g4] eqn:E1. injection H1 as <- <- <-.
        destruct (IH _ _ _ _ _ _ _ _ _ E1 E2) as [-> HI]. split; [reflexivity|]. cbn [map option_map ei_strip ef_ei ei_bid ei_br]. rewrite HI. reflexivity.
      * destruct (scanF bc rest t3 gs) as [[i1 t4] g4] eqn:E1. injection H1 as <- <- <-.
        destruct (IH _ _ _ _ _ _ _ _ _ E1 E2) as [-> HI]. split; [reflexivity|]. cbn [map option_map ei_strip ef_ei ei_bid ei_br]. rewrite HI. reflexivity.
    + destruct (scanF bc rest t gs) as [[i1 t4] g4] eqn:E1.
      destruct (scan_entries bc rest t gs') as [[i2 t5] g5] eqn:E2.
      injection H1 as <- <- <-. injection H2 as <- <- <-.
      destruct (IH _ _ _ _ _ _ _ _ _ E1 E2) as [-> HI]. split; [reflexivity|]. cbn [map option_map ei_strip]. rewrite HI. reflexivity.
Qed.
Lemma scanF_okG : forall bc kn t gs infos t' gs',
  NTI bc t -> scanF bc kn t gs = (infos, t', gs') ->
  NTI bc t' /\ (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k)) /\ Forall2 (EINFF bc t') kn infos.
Proof.
  intros bc kn. induction kn as [|K rest IH]; intros t gs infos t' gs' HT H.
  - cbn in H. injection H as <- <- <-. split; [exact HT|]. split; [intros; assumption|]. constructor.
  - cbn [scanF] in H. rewrite kdescrF_eq in H.
    destruct (kdescr K) as [[[kb kk] om]|] eqn:HD.
    + destruct (intern bc t kb) as [[bid bi] t1] eqn:EI.
      destruct (intern_ok _ _ _ _ _ _ HT EI) as (HT1 & Hbi & HIn & Hm1).
      assert (STEP : forall infos2 t2 gid ke, Forall2 (EINFF bc t2) rest infos2 -> (forall k p, In p (nt_bucket t1 k) -> In p (nt_bucket t2 k)) ->
                (forall m, om = Some m -> ke = kk + m) ->
                Forall2 (EINFF bc t2) (K :: rest) (Some (EF bid gid kb (bi_br bi) kk om ke) :: infos2)).
      { intros infos2 t2 gid ke HF Hm2 Hke. constructor; [|exact HF]. cbn [EINFF EINF ef_ei ei_kb ei_k ei_m ei_bid ei_br ef_end ef_k ef_m].
        split; [|exact Hke]. split; [exact HD|]. split; [apply Hm2; exact HIn|]. rewrite Hbi. reflexivity. }
      destruct om as [m|].
      * lazymatch type of H with (let '(_, _) := ?X in _) = _ => destruct X as [gid gs0] end.
        destruct (scanF bc rest t1 _) as [[infos2 t2] gs2] eqn:ES.
        injection H as <- <- <-.
        destruct (IH _ _ _ _ _ HT1 ES) as (HT2 & Hm2 & HF).
        split; [exact HT2|]. split; [intros k p Hp; apply Hm2; apply Hm1; exact Hp|].
        apply STEP; [exact HF|exact Hm2|intros m' E; injection E as <-; reflexivity].
      * destruct (scanF bc rest t1 gs) as [[infos2 t2] gs2] eqn:ES.
        injection H as <- <- <-.
        destruct (IH _ _ _ _ _ HT1 ES) as (HT2 & Hm2 & HF).
        split; [exact HT2|]. split; [intros k p Hp; apply Hm2; apply Hm1; exact Hp|].
        apply STEP; [exact HF|exact Hm2|intros m' E; discriminate].
    + destruct (scanF bc rest t gs) as [[infos2 t2] gs2] eqn:ES.
      injection H as <- <- <-.
      destruct (IH _ _ _ _ _ HT ES) as (HT2 & Hm2 & HF).
      split; [exact HT2|]. split; [exact Hm2|]. constructor; [exact HD | exact HF].
Qed.

Lemma stores_partF2_eq : forall bc X sxs, XOK bc X -> stores_partF2 bc (map (mk_sxi X) sxs) = stores_part bc sxs.
Proof.
  intros bc X sxs HX. induction sxs as [|sx rest IH]; [reflexivity|].
  cbn [map stores_partF2 stores_part si_sx si_bx mk_sxi]. rewrite IH.
  rewrite (chainK2F2_eq bc X (xget X (sx_bid sx)) rest); [reflexivity|exact HX|apply HX| |exact I].
  destruct (sx_a sx); reflexivity.
Qed.

Lemma mk_sctx_rng : forall bc ex a w v, sp_rng (mk_sctx bc ex (SE a w v)) = base_rangeB bc (a_base a).
Proof.
  intros bc ex a w v. unfold mk_sctx, mk_sprepF, elen.
  destruct (Z.eqb (zlit64 (Z.of_nat w)) (Z.of_nat w)); [|reflexivity].
  destruct (disj_both bc (be_kd ex) (a_base a) (a_off a) (Z.of_nat w)); reflexivity.
Qed.
Lemma mk_sctx_D : forall bc a w v, sp_D (mk_sctx bc (mk_bext bc) (SE a w v)) = disj_sidesB bc (bc_fk bc) (a_base a) (a_off a) (zlit64 (Z.of_nat w)).
Proof. intros bc a w v. unfold mk_sctx. rewrite mk_sprepF_eq. reflexivity. Qed.
Lemma mk_sctx_eq : forall bc a w v, mk_sctx bc (mk_bext bc) (SE a w v) = mk_sprepB bc (a_base a) (a_off a) (elen w).
Proof. intros bc a w v. unfold mk_sctx. apply mk_sprepF_eq. Qed.
Lemma mk_stxsC2_eq : forall bc log t, mk_stxsC2 log (map (mk_sctx bc (mk_bext bc)) log) t = mk_stxs bc log t.
Proof.
  intros bc log t. induction log as [|[a w v] older IH]; [reflexivity|].
  cbn [map mk_stxsC2 mk_stxs]. rewrite IH, mk_sctx_rng, mk_sctx_eq. destruct (mk_stxs bc older t) as [sxs t1]. rewrite intern_r_eq. reflexivity.
Qed.

Definition LB (bc : bctx) (t : ntab) (lb : option (expr * positive * binfo)) : Prop :=
  match lb with Some (b', id, bi) => In (b', id) (nt_bucket t (bkey b')) /\ bi = BI b' (base_rangeB bc b') | None => True end.
Definition LG (gs : gst) (lg : option (positive * positive * positive)) : Prop :=
  match lg with Some (b, gk, gid) => exists inner, pt_get (gs_gid gs) b = Some inner /\ pt_get inner gk = Some gid | None => True end.
Lemma intern_c_eq : forall bc t lb b, NTI bc t -> LB bc t lb -> intern_c bc t lb b = intern bc t b.
Proof.
  intros bc t lb b HT HL. destruct lb as [[[b' id] bi]|]; [|exact (internF_eq bc t b)]. cbn [intern_c]. rewrite internF_eq, BLKF.expr_eqbF_eq.
  destruct (expr_eqb b b') eqn:E; [|reflexivity]. apply p_expr_eqb_eq in E. subst b'.
  destruct HL as [HIn ->]. unfold intern.
  destruct (alookupE (nt_bucket t (bkey b)) b) as [id0|] eqn:HL.
  - pose proof (alookupE_Some _ _ _ HL) as H0. destruct HT as [HA HB].
    rewrite (HB _ _ _ _ H0 HIn). rewrite (proj1 (proj2 (HA _ _ _ HIn))). reflexivity.
  - exfalso. exact (alookupE_None _ _ id HL HIn).
Qed.
Lemma ggroup_c_eq : forall gs lg bid gk, LG gs lg -> ggroup_c gs lg bid gk = ggroupK gs bid gk.
Proof.
  intros gs lg bid gk HL. destruct lg as [[[b gk'] gid]|]; [|reflexivity]. cbn [ggroup_c].
  destruct (Pos.eqb_spec bid b) as [->|]; [|reflexivity]. destruct (Pos.eqb_spec gk gk') as [->|]; [|reflexivity].
  destruct HL as (inner & H1 & H2). unfold ggroupK. rewrite H1, H2. reflexivity.
Qed.
Lemma LB_mono : forall bc t t' lb, (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k)) -> LB bc t lb -> LB bc t' lb.
Proof. intros bc t t' [[[b' id] bi]|] Hm H; [|exact I]. destruct H as [H1 H2]. split; [apply Hm; exact H1|exact H2]. Qed.
Lemma ggroupK_LG : forall gs bid gk gid gs0, ggroupK gs bid gk = (gid, gs0) -> LG gs0 (Some (bid, gk, gid)).
Proof.
  intros gs bid gk gid gs0 H. unfold ggroupK in H.
  destruct (pt_get (match pt_get (gs_gid gs) bid with Some i => i | None => PTLeaf end) gk) as [g|] eqn:E.
  - injection H as <- <-. exists (match pt_get (gs_gid gs) bid with Some i => i | None => PTLeaf end). split; [|exact E].
    destruct (pt_get (gs_gid gs) bid) as [i|] eqn:E2; [reflexivity|]. rewrite pt_get_leaf in E. discriminate.
  - injection H as <- <-. cbn [gs_gid LG]. eexists. rewrite pt_gss. split; [reflexivity|]. apply pt_gss.
Qed.
Lemma bnd_addF_gid : forall gs gid bid obr lo hi, gs_gid (bnd_addF gs gid bid obr lo hi) = gs_gid gs.
Proof.
  intros. unfold bnd_addF. destruct (pt_get (gs_bnds gs) gid) as [[[b o] [l h]]|]; [|reflexivity].
  destruct (Z.leb l lo); [destruct (Z.leb hi h)|]; reflexivity.
Qed.
Lemma scanF2_eq : forall bc kn t gs lb lg, NTI bc t -> LB bc t lb -> LG gs lg -> scanF2 bc kn t gs lb lg = scanF bc kn t gs.
Proof.
  intros bc kn. induction kn as [|K rest IH]; intros t gs lb lg HT HL HG; [reflexivity|].
  cbn [scanF2 scanF]. destruct (kdescrF K) as [[[kb kk] om]|] eqn:HD.
  - rewrite (intern_c_eq _ _ _ _ HT HL).
    destruct (intern bc t kb) as [[bid bi] t1] eqn:EI.
    destruct (intern_ok _ _ _ _ _ _ HT EI) as (HT1 & Hbi & HIn & Hm1).
    assert (HL1 : LB bc t1 (Some (kb, bid, bi))) by (split; assumption).
    destruct om as [m|].
    + rewrite (ggroup_c_eq _ _ _ _ HG). unfold ggroupF.
      destruct (ggroupK gs bid (gkeyF kk)) as [gid gs0] eqn:EG.
      rewrite (IH _ _ _ _ HT1 HL1); [reflexivity|]. cbn [LG]. rewrite bnd_addF_gid. exact (ggroupK_LG _ _ _ _ _ EG).
    + rewrite (IH _ _ _ _ HT1 HL1 HG). reflexivity.
  - rewrite (IH _ _ _ _ HT HL HG). reflexivity.
Qed.

Definition nonov (si : sxi) (a e : PrimInt63.int) : bool :=
  match si_iv si with Some (c, d) => if PrimInt63.leb e c then true else PrimInt63.leb d a | None => false end.
Fixpoint chainKI (bc : bctx) (xo : option bx) (fl : list (sxi * list sxi)) (a e : PrimInt63.int) (K : kentry) (okb : option expr)
         (same_of : positive -> bool) (br2 : option (Z * Z)) : list kentry :=
  match fl with
  | [] => [K]
  | (si, rest) :: fl' =>
      if nonov si a e then chainKI bc xo fl' a e K okb same_of br2 else
      match prune1pcKX bc si xo K (same_of (sx_bid (si_sx si))) br2 None with
      | PKeep => chainKI bc xo fl' a e K okb same_of br2
      | PRepl l =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2F2 bc xo rest K' okb same_of br2 None else chain_slowF bc rest [K']
                                  | None => chain_slowF bc rest [K']
                                  end) l
          | None => chain_slowF bc rest l
          end
      end
  end.
Definition osame (b : positive) (si : sxi) : bool := if Pos.eqb b (sx_bid (si_sx si)) then false else true.

Lemma chainKFF2_eqG2 : forall bc X xo skip sxs K okb same_of br2 pre,
  XOK bc X -> BXOK bc xo -> okb = kbase K -> PRE_OK bc K br2 pre ->
  (forall sx, In sx sxs -> skip (mk_sxi X sx) = true ->
     pk_rel K PKeep (prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2)) ->
  chainKFF2 bc xo (mk_flG skip (map (mk_sxi X) sxs)) K okb same_of br2 pre = chainK2 bc sxs K okb same_of br2.
Proof.
  intros bc X xo skip sxs K okb same_of br2 pre HX Hxo Hokb HP. induction sxs as [|sx rest IH]; intros HS; [reflexivity|].
  assert (IH' : chainKFF2 bc xo (mk_flG skip (map (mk_sxi X) rest)) K okb same_of br2 pre = chainK2 bc rest K okb same_of br2)
    by (apply IH; intros sx' Hin; apply HS; right; exact Hin).
  cbn [map mk_flG chainK2].
  destruct (skip (mk_sxi X sx)) eqn:EV.
  { destruct (HS sx (or_introl eq_refl) EV) as [E|[_ E2]].
    - rewrite <- E. exact IH'.
    - rewrite E2, IH'. destruct okb as [kb|].
      + cbn [flat_map]. rewrite <- Hokb, p_expr_eqb_refl, app_nil_r. reflexivity.
      + symmetry. apply chain_slow_nobase. symmetry. exact Hokb. }
  cbn [chainKFF2]. rewrite prune1pcKX_eq. cbn [si_sx si_bx mk_sxi].
  destruct (prune1pcKF2_rel bc (xget X (sx_bid sx)) xo (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 pre (HX (sx_bid sx)) Hxo HP)
    as [E|[E1 E2]].
  - rewrite E. destruct (prune1pcK _ _ _ _ _ K _ br2) as [|l]; [exact IH'|].
    destruct okb as [kb|]; [|(rewrite chain_slowF_eq; reflexivity)].
    apply flat_map_ext_in. intros K' _. destruct (kbase K') as [kb'|] eqn:HB; [|(rewrite chain_slowF_eq; reflexivity)].
    destruct (expr_eqb kb' kb) eqn:EQ; [|(rewrite chain_slowF_eq; reflexivity)].
    apply p_expr_eqb_eq in EQ. subst kb'. apply chainK2F2_eq; [exact HX|exact Hxo|symmetry; exact HB|exact I].
  - rewrite E1, E2, IH'.
    destruct okb as [kb|].
    + cbn [flat_map]. rewrite <- Hokb, p_expr_eqb_refl, app_nil_r. reflexivity.
    + symmetry. apply chain_slow_nobase. symmetry. exact Hokb.
Qed.

Lemma chainKI_eq : forall bc xo p sis a e K okb same_of br2,
  chainKI bc xo (mk_flG p sis) a e K okb same_of br2
  = chainKFF2 bc xo (mk_flG (fun si => if p si then true else nonov si a e) sis) K okb same_of br2 None.
Proof.
  intros bc xo p sis a e K okb same_of br2. induction sis as [|si rest IH]; [reflexivity|].
  cbn [mk_flG]. destruct (p si); [exact IH|]. cbn [chainKI]. destruct (nonov si a e); [exact IH|].
  cbn [chainKFF2]. destruct (prune1pcKX bc si xo K (same_of (sx_bid (si_sx si))) br2 None); [exact IH|reflexivity].
Qed.

Lemma nonov_num : forall X sx a e, nonov (mk_sxi X sx) a e = true ->
  Uint63Axioms.to_Z e <= a_off (sx_a sx) + 2 ^ 59 \/ a_off (sx_a sx) + Z.of_nat (sx_w sx) + 2 ^ 59 <= Uint63Axioms.to_Z a.
Proof.
  intros X sx a e H. unfold nonov in H. cbn [si_iv mk_sxi] in H.
  destruct (iv_of (a_off (sx_a sx)) (Z.of_nat (sx_w sx))) as [[c d]|] eqn:E; [|discriminate].
  apply iv_of_val in E. destruct E as (Ec & Ed & _).
  destruct (PrimInt63.leb e c) eqn:E1.
  - left. apply ileb_le in E1. lia.
  - right. apply ileb_le in H. lia.
Qed.
Lemma nonov_keep : forall bc X sx K a e same br2,
  ent_iv K = Some (a, e) -> nonov (mk_sxi X sx) a e = true ->
  match kbase K with Some _ => same = true | None => a_base (sx_a sx) = ELit 0 end ->
  pk_rel K PKeep (prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K same br2).
Proof.
  intros bc X sx K a e same br2 HI HN HS. apply nonov_num in HN.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    cbn [ent_iv] in HI; try discriminate; cbn [kbase] in HS.
  -   subst same. apply iv_of_val in HI. destruct HI as (Ha & He & Hm). left. unfold prune1pcK. cbv zeta.
    destruct (Z.leb_spec (kk + Z.of_nat w') (a_off (sx_a sx))); [reflexivity|].
    destruct (Z.leb_spec (a_off (sx_a sx) + Z.of_nat (sx_w sx)) kk); [reflexivity|]. lia.
  -   destruct len as [l0| | | | | | |]; try discriminate. destruct l0 as [|p|p]; try discriminate.
    subst same. apply iv_of_val in HI. destruct HI as (Ha & He & Hm). right. split; [reflexivity|].
    unfold prune1pcK. cbv zeta. rewrite ktrim_nov; [reflexivity|]. unfold nov.
    destruct (Z.ltb_spec 0 (Z.pos p)); [|lia]. destruct (Z.ltb_spec (Z.pos p) two64); [|rewrite two64_val in *; lia].
    destruct (Z.leb_spec (kk + Z.pos p) (a_off (sx_a sx))); [reflexivity|]. apply Z.leb_le. lia.
  -   destruct len as [l0| | | | | | |]; try discriminate.
    subst same. apply iv_of_val in HI. destruct HI as (Ha & He & Hm). left. unfold prune1pcK. cbv zeta.
    rewrite (Z.mod_small l0 (2 ^ 64)) by lia.
    destruct (Z.leb_spec (kk + l0) (a_off (sx_a sx))); [reflexivity|].
    destruct (Z.leb_spec (a_off (sx_a sx) + Z.of_nat (sx_w sx)) kk); [reflexivity|]. lia.
  -   destruct (Z.ltb_spec lo hi) as [Hlh|]; [|discriminate].
    destruct (z2b lo) as [a'|] eqn:Ea; [|discriminate]. destruct (z2b hi) as [e''|] eqn:Ee; [|discriminate].
    injection HI as <- <-. apply z2b_val in Ea. apply z2b_val in Ee. right. split; [reflexivity|].
    unfold prune1pcK. cbv zeta. rewrite HS. rewrite img_nov_eq; [reflexivity|]. unfold img_nov.
    destruct (Z.ltb_spec lo hi); [|lia]. destruct (Z.leb_spec hi (a_off (sx_a sx))); [reflexivity|]. apply Z.leb_le. lia.
  -   destruct len as [l0| | | | | | |]; try discriminate. destruct l0 as [|p|p]; try discriminate.
    subst same. apply iv_of_val in HI. destruct HI as (Ha & He & Hm). right. split; [reflexivity|].
    unfold prune1pcK. cbv zeta. rewrite ktrim_nov; [reflexivity|]. unfold nov.
    destruct (Z.ltb_spec 0 (Z.pos p)); [|lia]. destruct (Z.ltb_spec (Z.pos p) two64); [|rewrite two64_val in *; lia].
    destruct (Z.leb_spec (kk + Z.pos p) (a_off (sx_a sx))); [reflexivity|]. apply Z.leb_le. lia.
  -   destruct len as [l0| | | | | | |]; try discriminate. destruct l0 as [|p|p]; try discriminate.
    subst same. apply iv_of_val in HI. destruct HI as (Ha & He & Hm). right. split; [reflexivity|].
    unfold prune1pcK. cbv zeta. rewrite ktrim_nov; [reflexivity|]. unfold nov.
    destruct (Z.ltb_spec 0 (Z.pos p)); [|lia]. destruct (Z.ltb_spec (Z.pos p) two64); [|rewrite two64_val in *; lia].
    destruct (Z.leb_spec (kk + Z.pos p) (a_off (sx_a sx))); [reflexivity|]. apply Z.leb_le. lia.
Qed.

Lemma mk_flG_nil : forall skip sis, mk_flG skip sis = [] -> forall si, In si sis -> skip si = true.
Proof.
  intros skip sis. induction sis as [|x r IH]; intros H si Hin; [destruct Hin|].
  cbn [mk_flG] in H. destruct (skip x) eqn:E; [|discriminate].
  destruct Hin as [<-|Hin]; [exact E|exact (IH H si Hin)].
Qed.
Lemma mk_flG_ext : forall skip1 skip2 sis, (forall si, In si sis -> skip1 si = skip2 si) -> mk_flG skip1 sis = mk_flG skip2 sis.
Proof.
  intros skip1 skip2 sis. induction sis as [|x r IH]; intros H; [reflexivity|].
  cbn [mk_flG]. rewrite (H x (or_introl eq_refl)), IH by (intros; apply H; right; assumption). reflexivity.
Qed.
Lemma mk_flG_all : forall skip sis, (forall si, In si sis -> skip si = true) -> mk_flG skip sis = [].
Proof.
  intros skip sis. induction sis as [|x r IH]; intros H; [reflexivity|].
  cbn [mk_flG]. rewrite (H x (or_introl eq_refl)). apply IH. intros; apply H; right; assumption.
Qed.

Local Notation int := PrimInt63.int.
Local Notation toZ := Uint63Axioms.to_Z.
Lemma z2l_bound : forall z l, z2l z = Some l -> toZ l = z /\ 0 <= z < 2 ^ 59.
Proof. exact z2l_val. Qed.
Lemma rng2l_val : forall o a b, rng2l o = Some (a, b) -> exists lo hi, o = Some (lo, hi) /\ toZ a = lo /\ toZ b = hi /\ 0 <= lo < 2 ^ 59 /\ 0 <= hi < 2 ^ 59.
Proof.
  intros [[lo hi]|] a b H; [|discriminate]. cbn [rng2l] in H.
  destruct (z2l lo) as [a'|] eqn:Ea; [|discriminate]. destruct (z2l hi) as [b'|] eqn:Eb; [|discriminate].
  injection H as <- <-. apply z2l_val in Ea. apply z2l_val in Eb. exists lo, hi. intuition.
Qed.
Lemma mk_abj_val : forall rng k w A B, mk_abj rng (iv_of k w) = Some (A, B) ->
  exists lo1 hi1, rng = Some (lo1, hi1) /\ toZ A = hi1 + k + w + 2 ^ 59 /\ toZ B = lo1 + k + 2 ^ 59 /\ 0 <= w < 2 ^ 59.
Proof.
  intros rng k w A B H. unfold mk_abj in H. destruct (iv_of k w) as [[c d]|] eqn:EI; [|discriminate].
  destruct (rng2l rng) as [[lo1 hi1]|] eqn:ER; [|discriminate]. injection H as <- <-.
  pose proof (iv_of_kb _ _ _ _ EI) as Hk. apply iv_of_val in EI. destruct EI as (Ec & Ed & Hw).
  apply rng2l_val in ER. destruct ER as (lo & hi & -> & Elo & Ehi & Hlo & Hhi).
  exists lo, hi. split; [reflexivity|]. rewrite !add_nov by lia. repeat split; lia.
Qed.

Definition gqj_of (gq : option (Z * Z)) : option (int * int) :=
  match rng2l gq with Some (a, b) => Some (PrimInt63.add a B59, PrimInt63.add b B59) | None => None end.
Definition verdictJ (si : sxi) (b : positive) (gqj : option (int * int)) : bool :=
  if Pos.eqb b (sx_bid (si_sx si)) then false else
  match si_abj si, gqj with
  | Some (A, B), Some (gl, gh) => if PrimInt63.leb A gl then true else PrimInt63.leb gh B
  | _, _ => false
  end.
Lemma zlit64_small : forall z, 0 <= z < 2 ^ 60 -> zlit64 z = z.
Proof. intros z H. unfold zlit64. destruct (Z.leb_spec 0 z), (Z.ltb_spec z two64); cbn [andb]; try reflexivity; rewrite two64_val in *; lia. Qed.
Lemma verdictJ_F : forall X sx b gq, verdictJ (mk_sxi X sx) b (gqj_of gq) = true -> verdictF (mk_sxi X sx) b gq = true.
Proof.
  intros X sx b gq H. unfold verdictJ in H. unfold verdictF. cbn [si_sx si_ab si_abj mk_sxi] in *.
  destruct (Pos.eqb b (sx_bid sx)); [discriminate|].
  destruct (mk_abj (sp_rng (sx_sp sx)) (iv_of (a_off (sx_a sx)) (Z.of_nat (sx_w sx)))) as [[A B]|] eqn:EA; [|discriminate].
  apply mk_abj_val in EA. destruct EA as (lo1 & hi1 & -> & EA & EB & Hw).
  unfold gqj_of in H. destruct (rng2l gq) as [[a b']|] eqn:EG; [|discriminate].
  apply rng2l_val in EG. destruct EG as (GL & GH & -> & Ea & Eb & HGL & HGH).
  unfold sx_m1. rewrite (zlit64_small (Z.of_nat (sx_w sx))) by lia.
  assert (E1 : toZ (PrimInt63.add a B59) = GL + 2 ^ 59) by (rewrite add_nov by (rewrite B59_val; lia); rewrite B59_val; lia).
  assert (E2 : toZ (PrimInt63.add b' B59) = GH + 2 ^ 59) by (rewrite add_nov by (rewrite B59_val; lia); rewrite B59_val; lia).
  destruct (PrimInt63.leb A (PrimInt63.add a B59)) eqn:L1.
  - apply ileb_le in L1. destruct (Z.leb_spec (hi1 + a_off (sx_a sx) + Z.of_nat (sx_w sx)) GL); [reflexivity|lia].
  - apply ileb_le in H. destruct (Z.leb (hi1 + a_off (sx_a sx) + Z.of_nat (sx_w sx)) GL); [reflexivity|]. apply Z.leb_le. lia.
Qed.

Lemma ileb_gt : forall x y, PrimInt63.leb x y = false -> toZ y < toZ x.
Proof.
  intros x y H. destruct (Z.lt_ge_cases (toZ y) (toZ x)) as [L|L]; [exact L|].
  exfalso. assert (X : PrimInt63.leb x y = true) by (apply Uint63Axioms.leb_spec; lia). congruence.
Qed.
Lemma ileb_true : forall x y, toZ x <= toZ y -> PrimInt63.leb x y = true.
Proof. intros x y H. apply Uint63Axioms.leb_spec. exact H. Qed.
Definition imax (x y : int) : int := if PrimInt63.leb x y then y else x.
Definition imin (x y : int) : int := if PrimInt63.leb x y then x else y.
Lemma imax_l : forall x y, toZ x <= toZ (imax x y). Proof. intros x y. unfold imax. destruct (PrimInt63.leb x y) eqn:E; [apply ileb_le in E; exact E|lia]. Qed.
Lemma imax_r : forall x y, toZ y <= toZ (imax x y). Proof. intros x y. unfold imax. destruct (PrimInt63.leb x y) eqn:E; [lia|apply ileb_gt in E; lia]. Qed.
Lemma imin_l : forall x y, toZ (imin x y) <= toZ x. Proof. intros x y. unfold imin. destruct (PrimInt63.leb x y) eqn:E; [lia|apply ileb_gt in E; lia]. Qed.
Lemma imin_r : forall x y, toZ (imin x y) <= toZ y. Proof. intros x y. unfold imin. destruct (PrimInt63.leb x y) eqn:E; [apply ileb_le in E; exact E|lia]. Qed.

Definition hull : Type := (int * int * int * int)%type.
Definition IMAXV : int := Uint63.of_Z (2 ^ 62).
Fixpoint hull_of (fl : list (sxi * list sxi)) : option hull :=
  match fl with
  | [] => Some (i0, IMAXV, IMAXV, i0)
  | (si, _) :: r =>
      match hull_of r with
      | Some (A0, B0, c0, d0) =>
          match si_abj si with
          | Some (A, B) => match si_iv si with
                           | Some (c, d) => Some (imax A0 A, imin B0 B, imin c0 c, imax d0 d)
                           | None => None
                           end
          | None => None
          end
      | None => None
      end
  end.
Lemma hull_of_cov : forall fl A0 B0 c0 d0, hull_of fl = Some (A0, B0, c0, d0) ->
  forall si r, In (si, r) fl -> exists A B c d, si_abj si = Some (A, B) /\ si_iv si = Some (c, d) /\
     toZ A <= toZ A0 /\ toZ B0 <= toZ B /\ toZ c0 <= toZ c /\ toZ d <= toZ d0.
Proof.
  induction fl as [|[s0 r0] rest IH]; intros A0 B0 c0 d0 H si r Hin; [destruct Hin|].
  cbn [hull_of] in H. destruct (hull_of rest) as [[[[A1 B1] c1] d1]|] eqn:ER; [|discriminate].
  destruct (si_abj s0) as [[A B]|] eqn:EA; [|discriminate]. destruct (si_iv s0) as [[c d]|] eqn:EI; [|discriminate].
  injection H as <- <- <- <-.
  destruct Hin as [E|Hin].
  - injection E as <- <-. exists A, B, c, d. split; [exact EA|]. split; [exact EI|].
    pose proof (imax_r A1 A). pose proof (imin_r B1 B). pose proof (imin_r c1 c). pose proof (imax_r d1 d). lia.
  - destruct (IH _ _ _ _ eq_refl si r Hin) as (A' & B' & c' & d' & H1 & H2 & H3 & H4 & H5 & H6).
    exists A', B', c', d'. split; [exact H1|]. split; [exact H2|].
    pose proof (imax_l A1 A). pose proof (imin_l B1 B). pose proof (imin_l c1 c). pose proof (imax_l d1 d). lia.
Qed.
Lemma mk_flG_in : forall skip sis si, In si sis -> skip si = false -> exists r, In (si, r) (mk_flG skip sis).
Proof.
  intros skip sis si. induction sis as [|x rest IH]; intros Hin Hs; [destruct Hin|].
  cbn [mk_flG]. destruct Hin as [<-|Hin].
  - rewrite Hs. exists rest. left. reflexivity.
  - destruct (IH Hin Hs) as [r Hr]. exists r. destruct (skip x); [exact Hr|right; exact Hr].
Qed.

Record sbe := SBE { sbe_b : positive; sbe_fl : list (sxi * list sxi); sbe_h : option hull }.
Fixpoint sb_find (l : list sbe) (b : positive) : option sbe :=
  match l with [] => None | e :: r => if Pos.eqb b (sbe_b e) then Some e else sb_find r b end.
Fixpoint mk_sbl (all l : list sxi) (acc : list sbe) : list sbe :=
  match l with
  | [] => acc
  | si :: r => let b := sx_bid (si_sx si) in
               match sb_find acc b with
               | Some _ => mk_sbl all r acc
               | None => let fl := mk_flG (osame b) all in mk_sbl all r (SBE b fl (hull_of fl) :: acc)
               end
  end.
Definition SBE_OK (all : list sxi) (e : sbe) : Prop := sbe_h e = hull_of (mk_flG (osame (sbe_b e)) all).
Definition SBL_OK (all cur : list sxi) (l : list sbe) : Prop :=
  forall e, In e l -> SBE_OK all e /\ sbe_fl e = mk_flG (osame (sbe_b e)) cur.
Lemma sb_find_in : forall l b e, sb_find l b = Some e -> In e l /\ sbe_b e = b.
Proof.
  induction l as [|x r IH]; intros b e H; [discriminate|]. cbn [sb_find] in H.
  destruct (Pos.eqb_spec b (sbe_b x)) as [->|NE].
  - injection H as <-. split; [left; reflexivity|reflexivity].
  - destruct (IH b e H) as [H1 H2]. split; [right; exact H1|exact H2].
Qed.
Lemma sb_find_none : forall l b, sb_find l b = None -> forall e, In e l -> sbe_b e <> b.
Proof.
  induction l as [|x r IH]; intros b H e Hin; [destruct Hin|]. cbn [sb_find] in H.
  destruct (Pos.eqb b (sbe_b x)) eqn:EB; [discriminate|]. apply Pos.eqb_neq in EB.
  destruct Hin as [<-|Hin]; [intros E; apply EB; symmetry; exact E|exact (IH b H e Hin)].
Qed.
Lemma mk_sbl_ok : forall all l acc, SBL_OK all all acc ->
  SBL_OK all all (mk_sbl all l acc) /\
  (forall si, In si l -> exists e, In e (mk_sbl all l acc) /\ sbe_b e = sx_bid (si_sx si)) /\
  (forall e, In e acc -> In e (mk_sbl all l acc)).
Proof.
  intros all l. induction l as [|si r IH]; intros acc H; cbn [mk_sbl].
  - split; [exact H|]. split; [intros si []|intros e He; exact He].
  - destruct (sb_find acc (sx_bid (si_sx si))) as [e0|] eqn:EF.
    + destruct (IH acc H) as (H1 & H2 & H3). split; [exact H1|]. split; [|exact H3].
      intros si' [<-|Hin]; [|exact (H2 si' Hin)].
      destruct (sb_find_in _ _ _ EF) as [Hin0 Hb0]. exists e0. split; [apply H3; exact Hin0|exact Hb0].
    + set (e1 := SBE (sx_bid (si_sx si)) (mk_flG (osame (sx_bid (si_sx si))) all) (hull_of (mk_flG (osame (sx_bid (si_sx si))) all))).
      assert (H' : SBL_OK all all (e1 :: acc)).
      { intros e [<-|Hin]; [split; reflexivity|exact (H e Hin)]. }
      destruct (IH _ H') as (H1 & H2 & H3). split; [exact H1|]. split.
      * intros si' [<-|Hin]; [|exact (H2 si' Hin)]. exists e1. split; [apply H3; left; reflexivity|reflexivity].
      * intros e He. apply H3. right. exact He.
Qed.

Fixpoint forallbF {T : Type} (f : T -> bool) (l : list T) : bool :=
  match l with [] => true | x :: r => if f x then forallbF f r else false end.
Lemma forallbF_in : forall T (f : T -> bool) l, forallbF f l = true -> forall x, In x l -> f x = true.
Proof.
  intros T f l. induction l as [|y r IH]; intros H x Hin; [destruct Hin|]. cbn [forallbF] in H.
  destruct (f y) eqn:E; [|discriminate]. destruct Hin as [<-|Hin]; [exact E|exact (IH H x Hin)].
Qed.
Definition hv_other (h : option hull) (gqj : option (int * int)) : bool :=
  match h, gqj with
  | Some (A0, B0, _, _), Some (gl, gh) => if PrimInt63.leb A0 gl then true else PrimInt63.leb gh B0
  | _, _ => false
  end.
Definition hv_same (h : option hull) (giv : option (int * int)) : bool :=
  match h, giv with
  | Some (_, _, c0, d0), Some (gl, gh) => if PrimInt63.leb gh c0 then true else PrimInt63.leb d0 gl
  | _, _ => false
  end.
Definition skipv5 (bc : bctx) (b : positive) (glo ghi : Z) (gx : option gxi) (gqj : option (int * int)) (si : sxi) : bool :=
  if verdictJ si b gqj then true else linV2 bc si b glo ghi gx.
Definition skipo5 (bc : bctx) (b : positive) (glo ghi : Z) (gx : option gxi) (gqj : option (int * int)) (si : sxi) : bool :=
  if Pos.eqb b (sx_bid (si_sx si)) then true else skipv5 bc b glo ghi gx gqj si.

Definition smemo : Type := list (saddr * expr * bool).
Fixpoint sm_find (m : smemo) (c : saddr) (e : expr) : option bool :=
  match m with
  | [] => None
  | (c', e', r) :: rest =>
      if (if expr_eqbF (a_base c) (a_base c') then if Z.eqb (a_off c) (a_off c') then expr_eqbF e e' else false else false) then Some r
      else sm_find rest c e
  end.
Fixpoint in_sidesM (bc : bctx) (m : smemo) (D : list (saddr * expr)) (b : expr) (k n : Z) : bool * smemo :=
  match D with
  | [] => (false, m)
  | (c, e) :: r =>
      match sm_find m c e with
      | Some true => (true, m)
      | Some false => in_sidesM bc m r b k n
      | None => if sub_itvB bc b k n c e then (true, (c, e, true) :: m) else in_sidesM bc ((c, e, false) :: m) r b k n
      end
  end.
Definition linV2M (bc : bctx) (si : sxi) (b : positive) (glo ghi : Z) (gx : option gxi) (m : smemo) : bool * smemo :=
  match gx with
  | Some x =>
      if Pos.eqb b (sx_bid (si_sx si)) then (false, m) else
      if (if Z.leb 0 (ghi - glo) then Z.ltb (ghi - glo) two63z else false) then
        let sx := si_sx si in
        if in_sides_num bc (sp_D (sx_sp sx)) (gx_b x) glo (ghi - glo) then (true, m)
        else if lin_apartF bc (si_bx si) (gx_bx x) (a_base (sx_a sx)) (a_off (sx_a sx)) (zlit64F (Z.of_nat (sx_w sx))) (gx_b x) glo (ghi - glo) then (true, m)
        else in_sidesM bc m (sp_D (sx_sp sx)) (gx_b x) glo (ghi - glo)
      else (false, m)
  | None => (false, m)
  end.

Fixpoint mk_flM (bc : bctx) (b : positive) (glo ghi : Z) (gx : option gxi) (gqj : option (int * int)) (same_skip : bool) (m : smemo)
         (sis : list sxi) : list (sxi * list sxi) :=
  match sis with
  | [] => []
  | si :: srest =>
      if Pos.eqb b (sx_bid (si_sx si)) then
        (if same_skip then mk_flM bc b glo ghi gx gqj same_skip m srest else (si, srest) :: mk_flM bc b glo ghi gx gqj same_skip m srest)
      else if verdictJ si b gqj then mk_flM bc b glo ghi gx gqj same_skip m srest
      else let '(v, m') := linV2M bc si b glo ghi gx m in
           if v then mk_flM bc b glo ghi gx gqj same_skip m' srest else (si, srest) :: mk_flM bc b glo ghi gx gqj same_skip m' srest
  end.
Definition MEMO_OK (bc : bctx) (b : expr) (k n : Z) (m : smemo) : Prop := forall c e r, In (c, e, r) m -> r = sub_itvB bc b k n c e.
Lemma sm_find_ok : forall bc b k n m c e r, MEMO_OK bc b k n m -> sm_find m c e = Some r -> r = sub_itvB bc b k n c e.
Proof.
  intros bc b k n m c e r. induction m as [|[[c' e'] r'] rest IH]; intros H HF; [discriminate|]. cbn [sm_find] in HF. eF.
  destruct (if expr_eqb (a_base c) (a_base c') then if Z.eqb (a_off c) (a_off c') then expr_eqb e e' else false else false) eqn:E.
  - injection HF as <-. destruct (expr_eqb (a_base c) (a_base c')) eqn:E1; [|discriminate]. destruct (Z.eqb_spec (a_off c) (a_off c')) as [E2|]; [|discriminate].
    apply p_expr_eqb_eq in E1. apply p_expr_eqb_eq in E. subst e'. destruct c as [cb co], c' as [cb' co']. cbn [a_base a_off] in *. subst cb' co'.
    apply H. left. reflexivity.
  - apply IH; [intros c0 e0 r0 H0; apply H; right; exact H0|exact HF].
Qed.
Lemma in_sidesM_ok : forall bc D b k n m, MEMO_OK bc b k n m ->
  fst (in_sidesM bc m D b k n) = in_sidesB bc D b k n /\ MEMO_OK bc b k n (snd (in_sidesM bc m D b k n)).
Proof.
  intros bc D b k n. induction D as [|[c e] r IH]; intros m H; [split; [reflexivity|exact H]|].
  cbn [in_sidesM in_sidesB]. destruct (sm_find m c e) as [[|]|] eqn:EF.
  - rewrite <- (sm_find_ok bc b k n m c e true H EF). split; [reflexivity|exact H].
  - rewrite <- (sm_find_ok bc b k n m c e false H EF). exact (IH m H).
  - destruct (sub_itvB bc b k n c e) eqn:ES.
    + split; [reflexivity|]. intros c0 e0 r0 [E|H0]; [injection E as <- <- <-; symmetry; exact ES|exact (H c0 e0 r0 H0)].
    + apply IH. intros c0 e0 r0 [E|H0]; [injection E as <- <- <-; symmetry; exact ES|exact (H c0 e0 r0 H0)].
Qed.
Definition GMEMO (bc : bctx) (glo ghi : Z) (gx : option gxi) (m : smemo) : Prop :=
  match gx with Some x => MEMO_OK bc (gx_b x) glo (ghi - glo) m | None => True end.
Lemma linV2M_ok : forall bc si b glo ghi gx m, GMEMO bc glo ghi gx m ->
  fst (linV2M bc si b glo ghi gx m) = linV2 bc si b glo ghi gx /\ GMEMO bc glo ghi gx (snd (linV2M bc si b glo ghi gx m)).
Proof.
  intros bc si b glo ghi gx m H. unfold linV2M, linV2. destruct gx as [x|]; [|split; [reflexivity|exact H]]. cbn [GMEMO] in *.
  destruct (Pos.eqb b (sx_bid (si_sx si))); [split; [reflexivity|exact H]|].
  destruct (if Z.leb 0 (ghi - glo) then Z.ltb (ghi - glo) two63z else false); [|split; [reflexivity|exact H]]. cbv zeta.
  destruct (in_sides_num bc (sp_D (sx_sp (si_sx si))) (gx_b x) glo (ghi - glo)); [split; [reflexivity|exact H]|].
  destruct (lin_apartF _ _ _ _ _ _ _ _ _); [split; [reflexivity|exact H]|].
  exact (in_sidesM_ok bc _ _ _ _ m H).
Qed.
Lemma mk_flM_eq : forall bc b glo ghi gx gqj sis m, GMEMO bc glo ghi gx m ->
  mk_flM bc b glo ghi gx gqj true m sis = mk_flG (skipo5 bc b glo ghi gx gqj) sis /\
  mk_flM bc b glo ghi gx gqj false m sis = mk_flG (skipv5 bc b glo ghi gx gqj) sis.
Proof.
  intros bc b glo ghi gx gqj sis. induction sis as [|si rest IH]; intros m H; [split; reflexivity|].
  cbn [mk_flM mk_flG]. unfold skipo5 at 1, skipv5 at 1 2.
  destruct (Pos.eqb b (sx_bid (si_sx si))) eqn:EB.
  - destruct (IH m H) as [I1 I2]. split; [exact I1|].
    assert (EV : verdictJ si b gqj = false) by (unfold verdictJ; rewrite EB; reflexivity).
    assert (EL : linV2 bc si b glo ghi gx = false) by (unfold linV2; destruct gx; [rewrite EB|]; reflexivity).
    rewrite EV, EL, I2. reflexivity.
  - destruct (verdictJ si b gqj); [exact (IH m H)|].
    destruct (linV2M_ok bc si b glo ghi gx m H) as [E1 E2].
    destruct (linV2M bc si b glo ghi gx m) as [v m']. cbn [fst snd] in E1, E2. rewrite <- E1.
    destruct (IH m' E2) as [I1 I2]. destruct v; [split; assumption|]. rewrite I1, I2. split; reflexivity.
Qed.
Definition enj_of (K : kentry) (br2 : option (Z * Z)) (h2o e2o : option Z) : option (int * int * option int) :=
  match eni_of2 K br2 h2o e2o with
  | Some (el, eh, e2) => Some (PrimInt63.add el B59, PrimInt63.add eh B59, match e2 with Some x => Some (PrimInt63.add x B59) | None => None end)
  | None => None
  end.
Definition symnumJ (si : sxi) (enj : option (int * int * option int)) : bool :=
  match si_a2j si, enj with
  | Some (A, B), Some (el, eh, e2) =>
      if PrimInt63.leb A el then true else if PrimInt63.leb eh B then true else
      match e2 with Some e => PrimInt63.leb e B | None => false end
  | _, _ => false
  end.

Lemma ent_iv_descr : forall K a e kb kk m, ent_iv K = Some (a, e) -> kdescr K = Some (kb, kk, Some m) ->
  toZ a = kk + 2 ^ 59 /\ toZ e = kk + m + 2 ^ 59.
Proof.
  intros K a e kb kk m HI HD.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [ent_iv kdescr] in *; try discriminate.
  - injection HD as <- <- <-. apply iv_of_val in HI. destruct HI as (Ha & He & Hm). rewrite (zlit64_small _) by lia. split; assumption.
  - destruct len as [l0| | | | | | |]; try discriminate. destruct l0 as [|p|p]; try discriminate.
    injection HD as <- <- <-. apply iv_of_val in HI. destruct HI as (Ha & He & Hm). rewrite (zlit64_small _) by lia. split; assumption.
  - destruct len as [l0| | | | | | |]; try discriminate.
    injection HD as <- <- <-. apply iv_of_val in HI. destruct HI as (Ha & He & Hm). rewrite (zlit64_small _) by lia. split; assumption.
  - destruct (Z.ltb_spec lo hi) as [Hlh|]; [|discriminate].
    destruct (z2b lo) as [a'|] eqn:Ea; [|discriminate]. destruct (z2b hi) as [e''|] eqn:Ee; [|discriminate].
    injection HI as <- <-. apply z2b_val in Ea. apply z2b_val in Ee.
    destruct (Z.ltb_spec (hi - lo) (2 ^ 64)); [|lia]. injection HD as <- <- <-.
    rewrite (zlit64_small (hi - lo)) by lia. split; lia.
  - destruct len as [l0| | | | | | |]; try discriminate. destruct l0 as [|p|p]; try discriminate.
    injection HD as <- <- <-. apply iv_of_val in HI. destruct HI as (Ha & He & Hm). rewrite (zlit64_small _) by lia. split; assumption.
  - destruct len as [l0| | | | | | |]; try discriminate. destruct l0 as [|p|p]; try discriminate.
    injection HD as <- <- <-. apply iv_of_val in HI. destruct HI as (Ha & He & Hm). rewrite (zlit64_small _) by lia. split; assumption.
Qed.

Lemma nonov_hull : forall X sx a e gl gh c0 d0 A B c d,
  si_iv (mk_sxi X sx) = Some (c, d) -> si_abj (mk_sxi X sx) = Some (A, B) ->
  toZ c0 <= toZ c -> toZ d <= toZ d0 ->
  PrimInt63.leb gl a = true -> PrimInt63.leb e gh = true ->
  (if PrimInt63.leb gh c0 then true else PrimInt63.leb d0 gl) = true ->
  nonov (mk_sxi X sx) a e = true.
Proof.
  intros X sx a e gl gh c0 d0 A B c d HI _ Hc Hd H1 H2 H3. unfold nonov. rewrite HI.
  apply ileb_le in H1. apply ileb_le in H2.
  destruct (PrimInt63.leb gh c0) eqn:E.
  - apply ileb_le in E. rewrite (ileb_true e c) by lia. reflexivity.
  - apply ileb_le in H3. destruct (PrimInt63.leb e c); [reflexivity|]. apply ileb_true. lia.
Qed.

Lemma p2iS_bound : forall p acc pw r, 0 <= toZ acc < toZ pw -> p2iS p acc pw = Some r -> toZ r < 2 ^ 62.
Proof.
  induction p as [q IH|q IH|]; intros acc pw r Ha H; cbn [p2iS] in H;
    (destruct (PrimInt63.ltb m61 pw) eqn:El; [discriminate|]);
    (assert (Q : toZ pw <= 2 ^ 61) by (rewrite <- m61_val; destruct (Z.le_gt_cases (toZ pw) (toZ m61)) as [Y|Y]; [exact Y|];
        apply Uint63Axioms.ltb_spec in Y; congruence));
    (assert (E2 : toZ (PrimInt63.add pw pw) = toZ pw + toZ pw) by (apply add_nov; lia)).
  - assert (E1 : toZ (PrimInt63.add acc pw) = toZ acc + toZ pw) by (apply add_nov; lia).
    apply IH in H; [exact H|rewrite E1, E2; lia].
  - apply IH in H; [exact H|rewrite E2; lia].
  - injection H as <-. rewrite add_nov by lia. lia.
Qed.
Lemma z2i_bound : forall z i, z2i z = Some i -> toZ i = z /\ 0 <= z < 2 ^ 62.
Proof.
  intros z i H. pose proof (z2i_val z i H) as V. split; [exact V|].
  destruct z as [|p|p]; cbn [z2i] in H; [lia| |discriminate].
  pose proof (proj2 (P2Q.p2iQ4_val p i H)). lia.
Qed.
Lemma jleb : forall x y a b, toZ x = a + 2 ^ 59 -> toZ y = b + 2 ^ 59 -> PrimInt63.leb x y = Z.leb a b.
Proof.
  intros x y a b Hx Hy. destruct (PrimInt63.leb x y) eqn:E; symmetry.
  - apply ileb_le in E. apply Z.leb_le. lia.
  - apply ileb_gt in E. apply Z.leb_gt. lia.
Qed.
Lemma addB_val : forall z i, z2i z = Some i -> toZ (PrimInt63.add i B59) = z + 2 ^ 59.
Proof. intros z i H. apply z2i_bound in H. destruct H as [V B]. rewrite add_nov by (rewrite B59_val; lia). rewrite B59_val. lia. Qed.
Lemma symnumJ_keep : forall bc X sx K br2,
  symnumJ (mk_sxi X sx) (enj_of K br2 (fst (mk_pre bc K br2)) (snd (mk_pre bc K br2))) = true ->
  prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K false br2 = PKeep.
Proof.
  intros bc X sx K br2 H. unfold symnumJ in H. cbn [si_a2j mk_sxi] in H.
  destruct (sp_h1 (sx_sp sx)) as [h1|] eqn:E2; [|discriminate].
  destruct (Z.eqb_spec h1 (Z.of_nat (sx_w sx))) as [Eh1|]; [|discriminate].
  destruct (mk_abj (sp_rng (sx_sp sx)) (iv_of (a_off (sx_a sx)) (Z.of_nat (sx_w sx)))) as [[A B]|] eqn:EA; [|discriminate].
  apply mk_abj_val in EA. destruct EA as (lo1 & hi1 & E1 & EA & EB & Hw).
  assert (EA' : toZ A = (hi1 + a_off (sx_a sx) + h1) + 2 ^ 59) by lia.
  assert (EB' : toZ B = (lo1 + a_off (sx_a sx)) + 2 ^ 59) by lia.
  assert (GEN : forall kb kk len lo2 hi2 h2, (forall z, len <> ELit z) -> xhiB bc len = Some h2 ->
     match (match (match z2i (lo2 + kk), z2i (hi2 + kk + h2) with
            | Some el, Some eh => match end_hiB bc kb kk len lo2 hi2 h2 with
                                  | None => Some (el, eh, None)
                                  | Some e2 => match z2i e2 with Some i => Some (el, eh, Some i) | None => None end end
            | _, _ => None end) with
            | Some (el, eh, e2) => Some (PrimInt63.add el B59, PrimInt63.add eh B59, match e2 with Some x => Some (PrimInt63.add x B59) | None => None end)
            | None => None end) with
     | Some (el, eh, e2i) => if PrimInt63.leb A el then true else if PrimInt63.leb eh B then true else
                              match e2i with Some e => PrimInt63.leb e B | None => false end
     | None => false end = true ->
     ranges_apart_pcB bc (sx_sp sx) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx)) (Some (lo2, hi2)) kb kk len = true).
  { intros kb kk len lo2 hi2 h2 Hn Eh HH.
    destruct (z2i (lo2 + kk)) as [el|] eqn:Eel; [|discriminate]. destruct (z2i (hi2 + kk + h2)) as [eh|] eqn:Eeh; [|discriminate].
    apply (rap_num bc _ _ _ _ _ _ _ _ lo1 hi1 h1 lo2 hi2 h2 Hn E1 E2 eq_refl Eh).
    destruct (end_hiB bc kb kk len lo2 hi2 h2) as [e2|].
    - destruct (z2i e2) as [ei|] eqn:Ee; [|discriminate]. cbv iota beta in HH.
      rewrite (jleb _ _ _ _ EA' (addB_val _ _ Eel)), (jleb _ _ _ _ (addB_val _ _ Eeh) EB'), (jleb _ _ _ _ (addB_val _ _ Ee) EB') in HH. exact HH.
    - cbv iota beta in HH. rewrite (jleb _ _ _ _ EA' (addB_val _ _ Eel)), (jleb _ _ _ _ (addB_val _ _ Eeh) EB') in HH. exact HH. }
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    try (cbv [enj_of eni_of2 fst snd mk_pre] in H; cbv iota beta in H; discriminate);
    (destruct len as [z| | | | | | |]; [cbv [enj_of eni_of2 fst snd mk_pre] in H; cbv iota beta in H; discriminate| ..]);
    cbv [enj_of eni_of2 fst snd mk_pre] in H; cbv iota beta zeta in H;
    (destruct br2 as [[lo2 hi2]|]; [|discriminate]);
    (lazymatch type of H with context [xhiB bc ?l] => destruct (xhiB bc l) as [h2|] eqn:Eh; [|discriminate] end);
    unfold prune1pcK; cbv zeta;
    (lazymatch goal with |- context [ranges_apart_pcB _ _ _ _ _ _ ?b ?k ?l] =>
       rewrite (GEN b k l lo2 hi2 h2 ltac:(intros ? ?; discriminate) Eh H) end); reflexivity.
Qed.

Lemma hv_other_verdictJ : forall X sx b gqj A0 B0 c0 d0 fl r,
  hull_of fl = Some (A0, B0, c0, d0) -> In (mk_sxi X sx, r) fl -> Pos.eqb b (sx_bid sx) = false ->
  hv_other (Some (A0, B0, c0, d0)) gqj = true -> verdictJ (mk_sxi X sx) b gqj = true.
Proof.
  intros X sx b gqj A0 B0 c0 d0 fl r HH Hin Hne HV.
  destruct (hull_of_cov _ _ _ _ _ HH _ _ Hin) as (A & B & c & d & EA & EI & L1 & L2 & L3 & L4).
  unfold verdictJ. cbn [si_sx mk_sxi]. rewrite Hne. change (si_abj (mk_sxi X sx)) with (si_abj (mk_sxi X sx)) in EA.
  cbn [si_abj mk_sxi] in EA. cbn [si_abj mk_sxi]. rewrite EA.
  unfold hv_other in HV. destruct gqj as [[gl gh]|]; [|discriminate].
  destruct (PrimInt63.leb A0 gl) eqn:E.
  - apply ileb_le in E. rewrite (ileb_true A gl) by lia. reflexivity.
  - apply ileb_le in HV. destruct (PrimInt63.leb A gl); [reflexivity|]. apply ileb_true. lia.
Qed.

Definition ssvJ (s t : sxi) : bool :=
  match si_abj t, si_eabj s with
  | Some (A, B), Some (el, eh) => if PrimInt63.leb A el then true else PrimInt63.leb eh B
  | _, _ => false
  end.

Definition skipS5 (bc : bctx) (s t : sxi) : bool :=
  if Pos.eqb (sx_bid (si_sx s)) (sx_bid (si_sx t)) then
    match si_iv s with Some (a, e) => nonov t a e | None => false end
  else if ssvJ s t then true
  else in_sides_num bc (sp_D (sx_sp (si_sx s))) (a_base (sx_a (si_sx t))) (a_off (sx_a (si_sx t))) (sx_m1 (si_sx t)).
Definition hs_other (h : option hull) (el eh : int) : bool :=
  match h with Some (A0, B0, _, _) => if PrimInt63.leb A0 el then true else PrimInt63.leb eh B0 | None => false end.
Fixpoint sb_pop (l : list sbe) (b : positive) : list sbe :=
  match l with
  | [] => []
  | e :: r => (if Pos.eqb b (sbe_b e) then SBE (sbe_b e) (match sbe_fl e with [] => [] | _ :: tl => tl end) (sbe_h e) else e) :: sb_pop r b
  end.
Fixpoint stores_partF5 (bc : bctx) (sis : list sxi) (R : list sbe) : list kentry :=
  match sis with
  | [] => []
  | si :: newer =>
      let sx := si_sx si in
      let b := sx_bid sx in
      let R' := sb_pop R b in
      stores_partF5 bc newer R' ++
      (let gen := fun _ : unit => chainKFF2 bc (si_bx si) (mk_flG (skipS5 bc si) newer) (KWord (sx_a sx) (sx_w sx) (sx_v sx))
                                    (Some (a_base (sx_a sx))) (Pos.eqb b) (sx_br sx) None in
       match si_iv si, si_eabj si with
       | Some (a, e), Some (el, eh) =>
           if forallbF (fun e' => if Pos.eqb b (sbe_b e') then true else hs_other (sbe_h e') el eh) R'
           then match sb_find R' b with
                | Some se => chainKI bc (si_bx si) (sbe_fl se) a e (KWord (sx_a sx) (sx_w sx) (sx_v sx))
                                     (Some (a_base (sx_a sx))) (Pos.eqb b) (sx_br sx)
                | None => gen tt
                end
           else gen tt
       | _, _ => gen tt
       end)
  end.

Lemma disj_sidesB_in : forall bc kd b k n c m, In (c, m) (disj_sidesB bc kd b k n) ->
  exists c' m', (In (KDisj c' m' c m) kd \/ In (KDisj c m c' m') kd) /\ sub_itvB bc b k n c' m' = true.
Proof.
  intros bc kd b k n c m. induction kd as [|K rest IH]; intros H; [destruct H|].
  assert (REC : In (c, m) (disj_sidesB bc rest b k n) ->
                exists c' m', (In (KDisj c' m' c m) (K :: rest) \/ In (KDisj c m c' m') (K :: rest)) /\ sub_itvB bc b k n c' m' = true).
  { intros H0. destruct (IH H0) as (c' & m' & [HI|HI] & HS); exists c', m'; (split; [|exact HS]); [left|right]; right; exact HI. }
  destruct K as [a w' v|a len|a len bk|lo hi|e' m'|e' lo' hi'|a en|c1 m1 c2 m2|a len fc|a len]; cbn [disj_sidesB] in H; try exact (REC H).
  destruct (sub_itvB bc b k n c1 m1) eqn:E1; destruct (sub_itvB bc b k n c2 m2) eqn:E2; cbn [In] in H.
  - destruct H as [E|[E|H]]; [injection E as <- <-; exists c1, m1; split; [left; left; reflexivity|exact E1]
                              |injection E as <- <-; exists c2, m2; split; [right; left; reflexivity|exact E2]|exact (REC H)].
  - destruct H as [E|H]; [injection E as <- <-; exists c1, m1; split; [left; left; reflexivity|exact E1]|exact (REC H)].
  - destruct H as [E|H]; [injection E as <- <-; exists c2, m2; split; [right; left; reflexivity|exact E2]|exact (REC H)].
  - exact (REC H).
Qed.
Lemma disj_sidesB_intro : forall bc kd b k n c1 m1 c2 m2, In (KDisj c1 m1 c2 m2) kd ->
  (sub_itvB bc b k n c1 m1 = true -> In (c2, m2) (disj_sidesB bc kd b k n)) /\
  (sub_itvB bc b k n c2 m2 = true -> In (c1, m1) (disj_sidesB bc kd b k n)).
Proof.
  intros bc kd b k n c1 m1 c2 m2. induction kd as [|K rest IH]; intros H; [destruct H|].
  destruct H as [->|H].
  - cbn [disj_sidesB]. split; intros E; rewrite E.
    + left. reflexivity.
    + destruct (sub_itvB bc b k n c1 m1); [right; left; reflexivity|left; reflexivity].
  - destruct (IH H) as [I1 I2].
    destruct K as [a w' v|a len|a len bk|lo hi|e' m'|e' lo' hi'|a en|d1 p1 d2 p2|a len fc|a len]; cbn [disj_sidesB]; try (split; assumption).
    split; intros E; destruct (sub_itvB bc b k n d1 p1); destruct (sub_itvB bc b k n d2 p2); cbn [In]; auto.
Qed.
Lemma in_sidesB_intro : forall bc D b k n c m, In (c, m) D -> sub_itvB bc b k n c m = true -> in_sidesB bc D b k n = true.
Proof.
  intros bc D b k n c m. induction D as [|[c0 m0] r IH]; intros H E; [destruct H|]. cbn [in_sidesB].
  destruct H as [H|H]; [injection H as -> ->; rewrite E; reflexivity|]. destruct (sub_itvB bc b k n c0 m0); [reflexivity|exact (IH H E)].
Qed.
Lemma in_sides_num_ex : forall bc D b k n, in_sides_num bc D b k n = true -> exists c m, In (c, m) D /\ sub_itvB bc b k n c m = true.
Proof.
  intros bc D b k n. induction D as [|[c0 m0] r IH]; cbn [in_sides_num]; [discriminate|].
  destruct (num_sub bc b k n c0 m0) eqn:E.
  - intros _. exists c0, m0. split; [left; reflexivity|]. unfold num_sub in E. unfold sub_itvB. cbv [andb].
    destruct (if expr_eqb b (a_base c0) then Z.leb (a_off c0) k else false); [|discriminate]. rewrite E. reflexivity.
  - intros H. destruct (IH H) as (c & m & HI & HS). exists c, m. split; [right; exact HI|exact HS].
Qed.

Lemma sym_sides : forall bc kd bs ks ns bt kt nt,
  in_sides_num bc (disj_sidesB bc kd bs ks ns) bt kt nt = true -> in_sidesB bc (disj_sidesB bc kd bt kt nt) bs ks ns = true.
Proof.
  intros bc kd bs ks ns bt kt nt H. destruct (in_sides_num_ex _ _ _ _ _ H) as (c & m & HI & HT).
  destruct (disj_sidesB_in _ _ _ _ _ _ _ HI) as (c' & m' & [HF|HF] & HS).
  -
    apply (in_sidesB_intro bc _ bs ks ns c' m'); [|exact HS]. exact (proj2 (disj_sidesB_intro bc kd bt kt nt c' m' c m HF) HT).
  - apply (in_sidesB_intro bc _ bs ks ns c' m'); [|exact HS]. exact (proj1 (disj_sidesB_intro bc kd bt kt nt c m c' m' HF) HT).
Qed.
Lemma sym_keep : forall bc s t,
  sx_sp s = mk_sprepB bc (a_base (sx_a s)) (a_off (sx_a s)) (elen (sx_w s)) ->
  sx_sp t = mk_sprepB bc (a_base (sx_a t)) (a_off (sx_a t)) (elen (sx_w t)) ->
  in_sides_num bc (sp_D (sx_sp s)) (a_base (sx_a t)) (a_off (sx_a t)) (sx_m1 t) = true ->
  prune1pcK bc (sx_sp t) (sx_a t) (sx_w t) (sx_v t) (KWord (sx_a s) (sx_w s) (sx_v s)) false (sx_br s) = PKeep.
Proof.
  intros bc s t Hs Ht H. rewrite Hs in H. cbn [sp_D mk_sprepB elen] in H. unfold sx_m1 in H. apply sym_sides in H.
  destruct (sx_a s) as [kb kk] eqn:Ea. cbn [a_base a_off] in H. unfold prune1pcK. cbv zeta. unfold ranges_apart_pcB, elen. cbv zeta.
  rewrite Ht at 2. cbn [sp_D mk_sprepB elen]. rewrite H.
  destruct (match sp_rng (sx_sp t) with Some (lo1, hi1) => _ | None => false end); reflexivity.
Qed.
Lemma ssvJ_keep : forall bc X s t, ssvJ (mk_sxi X s) (mk_sxi X t) = true -> Pos.eqb (sx_bid s) (sx_bid t) = false ->
  prune1pcK bc (sx_sp t) (sx_a t) (sx_w t) (sx_v t) (KWord (sx_a s) (sx_w s) (sx_v s)) false (sx_br s) = PKeep.
Proof.
  intros bc X s t H Hne. unfold ssvJ in H. cbn [si_abj si_eabj mk_sxi] in H.
  destruct (mk_abj (sp_rng (sx_sp t)) (iv_of (a_off (sx_a t)) (Z.of_nat (sx_w t)))) as [[A B]|] eqn:EAt; [|discriminate].
  destruct (obr_eqb (sx_br s) (sp_rng (sx_sp s))) eqn:EO; [|discriminate]. apply obr_eqb_eq in EO.
  destruct (mk_abj (sp_rng (sx_sp s)) (iv_of (a_off (sx_a s)) (Z.of_nat (sx_w s)))) as [[As Bs]|] eqn:EAs; [|discriminate].
  apply mk_abj_val in EAt. destruct EAt as (lo1 & hi1 & Et & EA & EB & Hwt).
  apply mk_abj_val in EAs. destruct EAs as (lo2 & hi2 & Es & EAs & EBs & Hws).
  rewrite Es in EO.
  destruct (sx_a s) as [kb kk] eqn:Ea. cbn [a_off] in *. unfold prune1pcK. cbv zeta. unfold ranges_apart_pcB, elen. cbv zeta. rewrite Et, EO.
  rewrite (zlit64_small (Z.of_nat (sx_w t))) by lia. rewrite (zlit64_small (Z.of_nat (sx_w s))) by lia.
  destruct (PrimInt63.leb A Bs) eqn:L.
  - apply ileb_le in L. destruct (Z.leb_spec (hi1 + a_off (sx_a t) + Z.of_nat (sx_w t)) (lo2 + kk)); [reflexivity|lia].
  - apply ileb_le in H. destruct (Z.leb (hi1 + a_off (sx_a t) + Z.of_nat (sx_w t)) (lo2 + kk)); [reflexivity|]. cbn [orb].
    destruct (Z.leb_spec (hi2 + kk + Z.of_nat (sx_w s)) (lo1 + a_off (sx_a t))); [reflexivity|lia].
Qed.
Lemma sb_pop_ok : forall all si newer R, SBL_OK all (si :: newer) R -> SBL_OK all newer (sb_pop R (sx_bid (si_sx si))).
Proof.
  intros all si newer R. induction R as [|e r IH]; intros H; [intros e []|].
  cbn [sb_pop]. intros e' [<-|Hin].
  - destruct (H e (or_introl eq_refl)) as [HOK HFL].
    destruct (Pos.eqb_spec (sx_bid (si_sx si)) (sbe_b e)) as [Eb|NE].
    + split; [exact HOK|]. cbn [sbe_fl sbe_b]. rewrite HFL. cbn [mk_flG]. unfold osame at 1. rewrite <- Eb, Pos.eqb_refl. reflexivity.
    + split; [exact HOK|]. rewrite HFL. cbn [mk_flG]. unfold osame at 1.
      destruct (Pos.eqb_spec (sbe_b e) (sx_bid (si_sx si))) as [Eb|_]; [exfalso; apply NE; symmetry; exact Eb|reflexivity].
  - apply IH; [|exact Hin]. intros e0 H0. apply H. right. exact H0.
Qed.
Lemma sb_pop_bases : forall R b e0, In e0 R -> exists e, In e (sb_pop R b) /\ sbe_b e = sbe_b e0 /\ sbe_h e = sbe_h e0.
Proof.
  induction R as [|x r IH]; intros b e0 Hin; [destruct Hin|]. cbn [sb_pop]. destruct Hin as [<-|Hin].
  - eexists. split; [left; reflexivity|]. destruct (Pos.eqb b (sbe_b x)); split; reflexivity.
  - destruct (IH b e0 Hin) as (e & H1 & H2). exists e. split; [right; exact H1|exact H2].
Qed.

Lemma stores_partF5_eq : forall bc X tt all sxs R, XOK bc X -> Forall (SX_OK bc tt) sxs ->
  SBL_OK all (map (mk_sxi X) sxs) R ->
  (forall si, In si (map (mk_sxi X) sxs) -> exists e, In e R /\ sbe_b e = sx_bid (si_sx si)) ->
  (forall si, In si (map (mk_sxi X) sxs) -> In si all) ->
  stores_partF5 bc (map (mk_sxi X) sxs) R = stores_part bc sxs.
Proof.
  intros bc X tt all sxs. induction sxs as [|sx rest IH]; intros R HX HSX HR HC HI; [reflexivity|].
  pose proof (Forall_inv HSX) as HSX0. pose proof (Forall_inv_tail HSX) as HSXr.
  cbn [map stores_partF5 stores_part]. cbv zeta.
  assert (HR' : SBL_OK all (map (mk_sxi X) rest) (sb_pop R (sx_bid (si_sx (mk_sxi X sx))))) by (apply sb_pop_ok; exact HR).
  assert (HC' : forall si, In si (map (mk_sxi X) rest) -> exists e, In e (sb_pop R (sx_bid (si_sx (mk_sxi X sx)))) /\ sbe_b e = sx_bid (si_sx si)).
  { intros si Hsi. destruct (HC si (or_intror Hsi)) as (e0 & He0 & Hb0).
    destruct (sb_pop_bases R (sx_bid (si_sx (mk_sxi X sx))) e0 He0) as (e & H1 & H2 & _). exists e. split; [exact H1|congruence]. }
  rewrite (IH _ HX HSXr HR' HC' (fun si Hsi => HI si (or_intror Hsi))). f_equal.
  cbn [si_sx si_bx si_iv si_eabj mk_sxi].
  assert (GEN : chainKFF2 bc (xget X (sx_bid sx)) (mk_flG (skipS5 bc (mk_sxi X sx)) (map (mk_sxi X) rest)) (KWord (sx_a sx) (sx_w sx) (sx_v sx))
                  (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx) None
                = chainK2 bc rest (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx)).
  { apply (chainKFF2_eqG2 bc X); [exact HX|apply HX| |exact I|].
    - destruct (sx_a sx); reflexivity.
    - intros t Hin Ht. unfold skipS5 in Ht. cbn [si_sx si_iv mk_sxi] in Ht.
      destruct (Pos.eqb (sx_bid sx) (sx_bid t)) eqn:ES.
      + destruct (iv_of (a_off (sx_a sx)) (Z.of_nat (sx_w sx))) as [[a e]|] eqn:EIV; [|discriminate].
        apply (nonov_keep bc X t _ a e _ _); [|exact Ht|].
        * destruct (sx_a sx) as [kb kk]. exact EIV.
        * destruct (sx_a sx) as [kb kk]. reflexivity.
      + left. symmetry. destruct (ssvJ (mk_sxi X sx) (mk_sxi X t)) eqn:EJ; [exact (ssvJ_keep bc X sx t EJ ES)|].
        exact (sym_keep bc sx t (proj2 (proj2 HSX0)) (proj2 (proj2 (proj1 (Forall_forall _ _) HSXr t Hin))) Ht). }
  destruct (iv_of (a_off (sx_a sx)) (Z.of_nat (sx_w sx))) as [[a e]|] eqn:EIV; [|exact GEN].
  destruct (if obr_eqb (sx_br sx) (sp_rng (sx_sp sx))
            then match mk_abj (sp_rng (sx_sp sx)) (Some (a, e)) with Some (A, B) => Some (B, A) | None => None end else None) as [[el eh]|] eqn:EE; [|exact GEN].
  destruct (forallbF (fun e' => if Pos.eqb (sx_bid sx) (sbe_b e') then true else hs_other (sbe_h e') el eh)
                     (sb_pop R (sx_bid sx))) eqn:EALL; [|exact GEN].
  destruct (sb_find (sb_pop R (sx_bid sx)) (sx_bid sx)) as [se|] eqn:ESB; [|exact GEN].
  destruct (sb_find_in _ _ _ ESB) as [Hse Hseb]. destruct (HR' se Hse) as [_ HFL]. cbn [si_sx mk_sxi] in HFL. rewrite Hseb in HFL.
  rewrite HFL, chainKI_eq.
  apply (chainKFF2_eqG2 bc X); [exact HX|apply HX| |exact I|].
  - destruct (sx_a sx); reflexivity.
  - intros t Ht HSK. unfold osame in HSK. cbn [si_sx mk_sxi] in HSK.
    destruct (Pos.eqb (sx_bid sx) (sx_bid t)) eqn:ES.
    + apply (nonov_keep bc X t _ a e _ _); [|exact HSK|].
      * destruct (sx_a sx) as [kb kk]. exact EIV.
      * destruct (sx_a sx) as [kb kk]. reflexivity.
    + left. symmetry. apply (ssvJ_keep bc X sx t); [|exact ES].

      destruct (HC' (mk_sxi X t) (in_map _ _ _ Ht)) as (e' & He' & Hb'). cbn [si_sx mk_sxi] in Hb'.
      pose proof (forallbF_in _ _ _ EALL e' He') as HV. cbv beta in HV. rewrite Hb', ES in HV.
      destruct (HR' e' He') as [HOK _]. unfold SBE_OK in HOK. rewrite Hb' in HOK.
      destruct (mk_flG_in (osame (sx_bid t)) all (mk_sxi X t) (HI _ (or_intror (in_map _ _ _ Ht)))) as [r Hr].
      { unfold osame. cbn [si_sx mk_sxi]. rewrite Pos.eqb_refl. reflexivity. }
      rewrite HOK in HV. unfold hs_other in HV.
      destruct (hull_of (mk_flG (osame (sx_bid t)) all)) as [[[[A0 B0] c0] d0]|] eqn:EH; [|discriminate].
      destruct (hull_of_cov _ _ _ _ _ EH _ _ Hr) as (A & B & c & d & EA & _ & LA & LB & _ & _).
      unfold ssvJ. rewrite EA. cbn [si_eabj mk_sxi]. rewrite EIV, EE.
      destruct (PrimInt63.leb A0 el) eqn:L.
      * apply ileb_le in L. rewrite (ileb_true A el) by lia. reflexivity.
      * apply ileb_le in HV. destruct (PrimInt63.leb A el); [reflexivity|]. apply ileb_true. lia.
Qed.

Definition GSI (gs : gst) : Prop :=
  (forall bid gk inner gid, pt_get (gs_gid gs) bid = Some inner -> pt_get inner gk = Some gid ->
      Pos.lt gid (gs_next gs) /\ exists o lh, pt_get (gs_bnds gs) gid = Some (bid, o, lh)) /\
  (forall gid v, pt_get (gs_bnds gs) gid = Some v -> Pos.lt gid (gs_next gs)).
Definition gmono (gs gs' : gst) : Prop :=
  forall gid b o l h, pt_get (gs_bnds gs) gid = Some (b, o, (l, h)) ->
    exists l' h', pt_get (gs_bnds gs') gid = Some (b, o, (l', h')) /\ l' <= l /\ h <= h'.
Lemma gmono_refl : forall gs, gmono gs gs.
Proof. intros gs gid b o l h H. exists l, h. split; [exact H|lia]. Qed.
Lemma gmono_trans : forall a b c, gmono a b -> gmono b c -> gmono a c.
Proof.
  intros a b c H1 H2 gid b0 o l h H. destruct (H1 _ _ _ _ _ H) as (l1 & h1 & E1 & L1 & L2).
  destruct (H2 _ _ _ _ _ E1) as (l2 & h2 & E2 & L3 & L4). exists l2, h2. split; [exact E2|lia].
Qed.
Lemma GSI_empty : GSI gst_empty.
Proof.
  split.
  - intros bid gk inner gid H. cbn in H. rewrite pt_get_leaf in H. discriminate.
  - intros gid v H. cbn in H. rewrite pt_get_leaf in H. discriminate.
Qed.

Lemma bnd_addF_ok : forall gs gid bid obr lo hi,
  (forall b o lh, pt_get (gs_bnds gs) gid = Some (b, o, lh) -> b = bid) ->
  gs_gid (bnd_addF gs gid bid obr lo hi) = gs_gid gs /\ gs_next (bnd_addF gs gid bid obr lo hi) = gs_next gs /\
  (exists o l h, pt_get (gs_bnds (bnd_addF gs gid bid obr lo hi)) gid = Some (bid, o, (l, h)) /\ l <= lo /\ hi <= h) /\
  (forall g, g <> gid -> pt_get (gs_bnds (bnd_addF gs gid bid obr lo hi)) g = pt_get (gs_bnds gs) g) /\
  gmono gs (bnd_addF gs gid bid obr lo hi).
Proof.
  intros gs gid bid obr lo hi HB. unfold bnd_addF.
  destruct (pt_get (gs_bnds gs) gid) as [[[b o] [l h]]|] eqn:E.
  - pose proof (HB _ _ _ eq_refl) as ->.
    destruct (Z.leb l lo) eqn:L1'; [destruct (Z.leb hi h) eqn:L2'|];
      [apply Z.leb_le in L1'; apply Z.leb_le in L2'|apply Z.leb_le in L1'; apply Z.leb_gt in L2'|apply Z.leb_gt in L1'].
    + split; [reflexivity|]. split; [reflexivity|]. split; [exists o, l, h; split; [exact E|lia]|]. split; [reflexivity|apply gmono_refl].
    + cbn [gs_gid gs_next gs_bnds]. split; [reflexivity|]. split; [reflexivity|].
      split; [exists o, l, hi; rewrite pt_gss; split; [reflexivity|lia]|]. split; [intros g NE; apply pt_gso; exact NE|].
      unfold gmono. cbn [gs_bnds]. intros g b0 o0 l0 h0 H0. destruct (Pos.eq_dec g gid) as [->|NE].
      * rewrite E in H0. injection H0 as <- <- <- <-. exists l, hi. rewrite pt_gss. split; [reflexivity|lia].
      * exists l0, h0. rewrite pt_gso by exact NE. split; [exact H0|lia].
    + cbn [gs_gid gs_next gs_bnds]. split; [reflexivity|]. split; [reflexivity|].
      split; [exists o, lo, (if Z.leb hi h then h else hi); rewrite pt_gss; split; [reflexivity|destruct (Z.leb_spec hi h); lia]|].
      split; [intros g NE; apply pt_gso; exact NE|].
      unfold gmono. cbn [gs_bnds]. intros g b0 o0 l0 h0 H0. destruct (Pos.eq_dec g gid) as [->|NE].
      * rewrite E in H0. injection H0 as <- <- <- <-. exists lo, (if Z.leb hi h then h else hi). rewrite pt_gss. split; [reflexivity|destruct (Z.leb_spec hi h); lia].
      * exists l0, h0. rewrite pt_gso by exact NE. split; [exact H0|lia].
  - cbn [gs_gid gs_next gs_bnds]. split; [reflexivity|]. split; [reflexivity|].
    split; [exists obr, lo, hi; rewrite pt_gss; split; [reflexivity|lia]|]. split; [intros g NE; apply pt_gso; exact NE|].
    unfold gmono. cbn [gs_bnds]. intros g b0 o0 l0 h0 H0. destruct (Pos.eq_dec g gid) as [->|NE]; [rewrite E in H0; discriminate|].
    exists l0, h0. rewrite pt_gso by exact NE. split; [exact H0|lia].
Qed.
Lemma gstep_ok : forall gs bid gk obr lo hi gid gs0, GSI gs -> ggroupK gs bid gk = (gid, gs0) ->
  GSI (bnd_addF gs0 gid bid obr lo hi) /\ gmono gs (bnd_addF gs0 gid bid obr lo hi) /\
  exists o l h, pt_get (gs_bnds (bnd_addF gs0 gid bid obr lo hi)) gid = Some (bid, o, (l, h)) /\ l <= lo /\ hi <= h.
Proof.
  intros gs bid gk obr lo hi gid gs0 [G1 G2] H. unfold ggroupK in H.
  set (inner0 := match pt_get (gs_gid gs) bid with Some i => i | None => PTLeaf end) in *.
  destruct (pt_get inner0 gk) as [g|] eqn:EG.
  -
    injection H as <- <-.
    assert (HI : pt_get (gs_gid gs) bid = Some inner0).
    { unfold inner0 in *. destruct (pt_get (gs_gid gs) bid) as [i|]; [reflexivity|]. rewrite pt_get_leaf in EG. discriminate. }
    destruct (G1 _ _ _ _ HI EG) as [L (o0 & lh0 & B0)].
    assert (HB : forall b o lh, pt_get (gs_bnds gs) g = Some (b, o, lh) -> b = bid) by (intros b o lh E; rewrite B0 in E; injection E as <- _ _; reflexivity).
    destruct (bnd_addF_ok gs g bid obr lo hi HB) as (E1 & E2 & E3 & E4 & E5).
    split; [|split; [exact E5|exact E3]].
    split.
    + intros bid' gk' inner gid' H1 H2. rewrite E1 in H1. rewrite E2. destruct (G1 _ _ _ _ H1 H2) as [L' (o' & lh' & B')].
      split; [exact L'|]. destruct (Pos.eq_dec gid' g) as [->|NE].
      * rewrite B0 in B'. injection B' as <- _ _. destruct E3 as (o3 & l3 & h3 & E3 & _). exists o3, (l3, h3). exact E3.
      * exists o', lh'. rewrite (E4 _ NE). exact B'.
    + intros g' v Hv. rewrite E2. destruct (Pos.eq_dec g' g) as [->|NE]; [exact L|]. rewrite (E4 _ NE) in Hv. exact (G2 _ _ Hv).
  -
    injection H as <- <-.
    set (gs0 := GST (pt_set bid (pt_set gk (gs_next gs) inner0) (gs_gid gs)) (Pos.succ (gs_next gs)) (gs_bnds gs)).
    assert (HN : pt_get (gs_bnds gs) (gs_next gs) = None).
    { destruct (pt_get (gs_bnds gs) (gs_next gs)) as [v|] eqn:E; [|reflexivity]. pose proof (G2 _ _ E) as L. exfalso. exact (Pos.lt_irrefl _ L). }
    assert (HB : forall b o lh, pt_get (gs_bnds gs0) (gs_next gs) = Some (b, o, lh) -> b = bid) by (intros b o lh E; cbn [gs0 gs_bnds] in E; rewrite HN in E; discriminate).
    destruct (bnd_addF_ok gs0 (gs_next gs) bid obr lo hi HB) as (E1 & E2 & E3 & E4 & E5).
    split; [|split; [exact E5|exact E3]].
    split.
    + intros bid' gk' inner gid' H1 H2. rewrite E1 in H1. rewrite E2. cbn [gs0 gs_gid gs_next] in *.
      assert (OLD : forall inner1, pt_get (gs_gid gs) bid' = Some inner1 -> pt_get inner1 gk' = Some gid' ->
                Pos.lt gid' (Pos.succ (gs_next gs)) /\ exists o lh, pt_get (gs_bnds (bnd_addF gs0 (gs_next gs) bid obr lo hi)) gid' = Some (bid', o, lh)).
      { intros inner1 Q1 Q2. destruct (G1 _ _ _ _ Q1 Q2) as [L' (o' & lh' & B')]. split; [apply Pos.lt_lt_succ; exact L'|].
        exists o', lh'. rewrite E4; [exact B'|]. intros ->. exact (Pos.lt_irrefl _ L'). }
      destruct (Pos.eq_dec bid' bid) as [->|NEb].
      * rewrite pt_gss in H1. injection H1 as <-.
        destruct (Pos.eq_dec gk' gk) as [->|NEk].
        -- rewrite pt_gss in H2. injection H2 as <-. split; [apply Pos.lt_succ_diag_r|].
           destruct E3 as (o3 & l3 & h3 & E3 & _). exists o3, (l3, h3). exact E3.
        -- rewrite pt_gso in H2 by exact NEk. unfold inner0 in H2.
           destruct (pt_get (gs_gid gs) bid) as [i|] eqn:EI; [exact (OLD i eq_refl H2)|rewrite pt_get_leaf in H2; discriminate].
      * rewrite pt_gso in H1 by exact NEb. exact (OLD inner H1 H2).
    + intros g' v Hv. rewrite E2. cbn [gs0 gs_next]. destruct (Pos.eq_dec g' (gs_next gs)) as [->|NE]; [apply Pos.lt_succ_diag_r|].
      rewrite (E4 _ NE) in Hv. cbn [gs0 gs_bnds] in Hv. apply Pos.lt_lt_succ. exact (G2 _ _ Hv).
Qed.
Definition in_grp (gs : gst) (e : einfoF) : Prop :=
  match ef_m e with
  | Some _ => exists o l h, pt_get (gs_bnds gs) (ef_gid e) = Some (ef_bid e, o, (l, h)) /\ l <= ef_k e /\ ef_end e <= h
  | None => True
  end.
Definition in_grpo (gs : gst) (oi : option einfoF) : Prop := match oi with Some e => in_grp gs e | None => True end.
Lemma scanF_grp : forall bc kn t gs infos t' gs', GSI gs -> scanF bc kn t gs = (infos, t', gs') ->
  GSI gs' /\ gmono gs gs' /\ Forall (in_grpo gs') infos.
Proof.
  intros bc kn. induction kn as [|K rest IH]; intros t gs infos t' gs' HG H.
  - cbn in H. injection H as <- <- <-. split; [exact HG|]. split; [apply gmono_refl|constructor].
  - cbn [scanF] in H. destruct (kdescrF K) as [[[kb kk] om]|].
    + destruct (intern bc t kb) as [[bid bi] t1].
      destruct om as [m|].
      * unfold ggroupF in H. destruct (ggroupK gs bid (gkeyF kk)) as [gid gs0] eqn:EG.
        destruct (scanF bc rest t1 (bnd_addF gs0 gid bid (bi_br bi) kk (kk + m))) as [[infos2 t2] gs2] eqn:ES.
        injection H as <- <- <-.
        destruct (gstep_ok gs bid (gkeyF kk) (bi_br bi) kk (kk + m) gid gs0 HG EG) as (HG1 & HM1 & (o & l & h & E1 & L1 & L2)).
        destruct (IH _ _ _ _ _ HG1 ES) as (HG2 & HM2 & HF).
        split; [exact HG2|]. split; [exact (gmono_trans _ _ _ HM1 HM2)|].
        constructor; [|exact HF]. cbn [in_grpo in_grp ef_m ef_gid ef_bid ef_k ef_end].
        destruct (HM2 _ _ _ _ _ E1) as (l' & h' & E2 & L3 & L4). exists o, l', h'. split; [exact E2|lia].
      * destruct (scanF bc rest t1 gs) as [[infos2 t2] gs2] eqn:ES. injection H as <- <- <-.
        destruct (IH _ _ _ _ _ HG ES) as (HG2 & HM2 & HF).
        split; [exact HG2|]. split; [exact HM2|]. constructor; [exact I|exact HF].
    + destruct (scanF bc rest t gs) as [[infos2 t2] gs2] eqn:ES. injection H as <- <- <-.
      destruct (IH _ _ _ _ _ HG ES) as (HG2 & HM2 & HF).
      split; [exact HG2|]. split; [exact HM2|]. constructor; [exact I|exact HF].
Qed.

Inductive sameb := SNone | SClean (fl : list (sxi * list sxi)) | SDirty (fl : list (sxi * list sxi)).
Record grp6 := GRP6 { k_flo : list (sxi * list sxi); k_fl : list (sxi * list sxi); k_same : sameb }.
Definition mk_glF6 (bc : bctx) (info : ptree binfo) (X : ptree (option bx)) (bnds : gtab) (sis : list sxi) (sbl : list sbe) : ptree (option grp6) :=
  pt_map (fun g : gval =>
     match g with
     | (b, _, (glo, ghi)) =>
         match pt_get info b with
         | Some bi =>
             let gx := if is_litb (bi_base bi) then None else Some (GXI (bi_base bi) (xget X b)) in
             let gqj := gqj_of (match bi_br bi with Some (lo2, hi2) => Some (glo + lo2, ghi + hi2) | None => None end) in
             let flo := if forallbF (fun e => if Pos.eqb b (sbe_b e) then true else hv_other (sbe_h e) gqj) sbl then []
                        else mk_flM bc b glo ghi gx gqj true [] sis in
             Some (GRP6 flo
                        (match flo with [] => [] | _ :: _ => mk_flM bc b glo ghi gx gqj false [] sis end)
                        (match sb_find sbl b with
                         | Some e => if hv_same (sbe_h e) (match z2b glo with Some a => match z2b ghi with Some e' => Some (a, e') | None => None end | None => None end)
                                     then SClean (sbe_fl e) else SDirty (sbe_fl e)
                         | None => SNone
                         end))
         | None => None
         end
     end) bnds.
Definition sameof (K : kentry) (ei : einfoF) : positive -> bool := match kbase K with Some _ => Pos.eqb (ef_bid ei) | None => fun _ => false end.
Definition br2of (K : kentry) (ei : einfoF) : option (Z * Z) := match kbase K with Some _ => ef_br ei | None => None end.

Fixpoint chainKP (bc : bctx) (xo : option bx) (fl : list (sxi * list sxi)) (a e : int) (K : kentry) (okb : option expr)
         (same_of : positive -> bool) (br2 : option (Z * Z)) : list kentry :=
  match fl with
  | [] => [K]
  | (si, rest) :: fl' =>
      if nonov si a e then chainKP bc xo fl' a e K okb same_of br2 else
      match prune1pcKX bc si xo K (same_of (sx_bid (si_sx si))) br2 None with
      | PKeep => chainKP bc xo fl' a e K okb same_of br2
      | PRepl l =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' =>
                                      if expr_eqb kb' kb then
                                        match ent_iv K' with
                                        | Some (a', e') =>
                                            if (if PrimInt63.leb a a' then PrimInt63.leb e' e else false)
                                            then chainKP bc xo fl' a' e' K' okb same_of br2
                                            else chainK2F2 bc xo rest K' okb same_of br2 None
                                        | None => chainK2F2 bc xo rest K' okb same_of br2 None
                                        end
                                      else chain_slowF bc rest [K']
                                  | None => chain_slowF bc rest [K']
                                  end) l
          | None => chain_slowF bc rest l
          end
      end
  end.
Definition PREM (bc : bctx) (X : ptree (option bx)) (p : sxi -> bool) (okb : option expr) (same_of : positive -> bool) (br2 : option (Z * Z))
           (sxs : list stx) (a e : int) : Prop :=
  forall K' a' e', kbase K' = okb -> ent_iv K' = Some (a', e') -> toZ a <= toZ a' -> toZ e' <= toZ e ->
  forall sx, In sx sxs -> (if p (mk_sxi X sx) then true else nonov (mk_sxi X sx) a' e') = true ->
    pk_rel K' PKeep (prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K' (same_of (sx_bid sx)) br2).
Lemma chainKP_eq : forall bc X xo p okb same_of br2 sxs a e K,
  XOK bc X -> BXOK bc xo -> PREM bc X p okb same_of br2 sxs a e -> kbase K = okb -> ent_iv K = Some (a, e) ->
  chainKP bc xo (mk_flG p (map (mk_sxi X) sxs)) a e K okb same_of br2 = chainK2 bc sxs K okb same_of br2.
Proof.
  intros bc X xo p okb same_of br2 sxs. induction sxs as [|sx rest IH]; intros a e K HX Hxo HP HK HI; [reflexivity|].
  assert (HP' : forall a' e', toZ a <= toZ a' -> toZ e' <= toZ e -> PREM bc X p okb same_of br2 rest a' e').
  { intros a' e' L1 L2 K' a'' e'' H1 H2 L3 L4 sx' Hin HS. apply (HP K' a'' e'' H1 H2); [lia|lia|right; exact Hin|exact HS]. }
  assert (IH' : chainKP bc xo (mk_flG p (map (mk_sxi X) rest)) a e K okb same_of br2 = chainK2 bc rest K okb same_of br2)
    by (apply IH; [exact HX|exact Hxo|apply HP'; lia|exact HK|exact HI]).
  assert (SKIP : (if p (mk_sxi X sx) then true else nonov (mk_sxi X sx) a e) = true ->
                 chainK2 bc (sx :: rest) K okb same_of br2 = chainK2 bc rest K okb same_of br2).
  { intros HS. cbn [chainK2].
    destruct (HP K a e HK HI ltac:(lia) ltac:(lia) sx (or_introl eq_refl) HS) as [E|[_ E2]].
    - rewrite <- E. reflexivity.
    - rewrite E2. destruct okb as [kb|].
      + cbn [flat_map]. rewrite HK, p_expr_eqb_refl, app_nil_r. reflexivity.
      + apply chain_slow_nobase. exact HK. }
  cbn [map mk_flG].
  destruct (p (mk_sxi X sx)) eqn:EP; [rewrite (SKIP eq_refl); exact IH'|].
  cbn [chainKP]. destruct (nonov (mk_sxi X sx) a e) eqn:EN; [rewrite (SKIP eq_refl); exact IH'|].
  cbn [chainK2]. rewrite prune1pcKX_eq. cbn [si_sx si_bx mk_sxi].
  destruct (prune1pcKF2_rel bc (xget X (sx_bid sx)) xo (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 None (HX (sx_bid sx)) Hxo I)
    as [E|[E1 E2]].
  - rewrite E. destruct (prune1pcK _ _ _ _ _ K _ br2) as [|l]; [exact IH'|].
    destruct okb as [kb|]; [|(rewrite chain_slowF_eq; reflexivity)].
    apply flat_map_ext_in. intros K' _. destruct (kbase K') as [kb'|] eqn:HB; [|(rewrite chain_slowF_eq; reflexivity)].
    destruct (expr_eqb kb' kb) eqn:EQ; [|(rewrite chain_slowF_eq; reflexivity)].
    apply p_expr_eqb_eq in EQ. subst kb'.
    destruct (ent_iv K') as [[a' e']|] eqn:EI'; [|apply chainK2F2_eq; [exact HX|exact Hxo|symmetry; exact HB|exact I]].
    destruct (if PrimInt63.leb a a' then PrimInt63.leb e' e else false) eqn:EC; [|apply chainK2F2_eq; [exact HX|exact Hxo|symmetry; exact HB|exact I]].
    destruct (PrimInt63.leb a a') eqn:L1; [|discriminate]. apply ileb_le in L1. apply ileb_le in EC.
    apply IH; [exact HX|exact Hxo|apply HP'; assumption|exact HB|exact EI'].
  - rewrite E1, E2, IH'.
    destruct okb as [kb|].
    + cbn [flat_map]. rewrite HK, p_expr_eqb_refl, app_nil_r. reflexivity.
    + symmetry. apply chain_slow_nobase. exact HK.
Qed.

Lemma ent_iv_kdescr : forall K a e, ent_iv K = Some (a, e) ->
  exists kb kk m, kdescr K = Some (kb, kk, Some m) /\ toZ a = kk + 2 ^ 59 /\ toZ e = kk + m + 2 ^ 59.
Proof.
  intros K a e HI.
  assert (G : forall kb kk m, kdescr K = Some (kb, kk, Some m) -> exists kb kk m, kdescr K = Some (kb, kk, Some m) /\ toZ a = kk + 2 ^ 59 /\ toZ e = kk + m + 2 ^ 59).
  { intros kb kk m HD. exists kb, kk, m. split; [exact HD|]. exact (ent_iv_descr _ _ _ _ _ _ HI HD). }
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [ent_iv] in HI; try discriminate.
  - eapply G. reflexivity.
  - destruct len as [l0| | | | | | |]; try discriminate. eapply G. reflexivity.
  - destruct len as [l0| | | | | | |]; try discriminate. eapply G. reflexivity.
  - destruct (Z.ltb_spec lo hi) as [Hlh|]; [|discriminate].
    destruct (z2b lo) as [a'|] eqn:Ea; [|discriminate]. destruct (z2b hi) as [e''|] eqn:Ee; [|discriminate].
    apply z2b_val in Ea. apply z2b_val in Ee. eapply G. cbn [kdescr].
    destruct (Z.ltb_spec (hi - lo) (2 ^ 64)); [reflexivity|lia].
  - destruct len as [l0| | | | | | |]; try discriminate. eapply G. reflexivity.
  - destruct len as [l0| | | | | | |]; try discriminate. eapply G. reflexivity.
Qed.
Section GrpKeep.
Variables (bc : bctx) (X : ptree (option bx)) (t : ntab) (sxs : list stx).
Hypotheses (HX : XOK bc X) (HT : NTI bc t) (HS : Forall (SX_OK bc t) sxs).
Variables (bid : positive) (kb : expr) (glo ghi : Z).
Hypothesis HIn : In (kb, bid) (nt_bucket t (bkey kb)).
Let obr := base_rangeB bc kb.
Let gx := if is_litb kb then None else Some (GXI kb (xget X bid)).
Let gqj := gqj_of (match obr with Some (lo2, hi2) => Some (glo + lo2, ghi + hi2) | None => None end).
Definition prG (K' : kentry) (sx : stx) : pk_res :=
  prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K'
    (match kbase K' with Some _ => Pos.eqb bid | None => fun _ => false end (sx_bid sx))
    (match kbase K' with Some _ => obr | None => None end).
Lemma grp_keepJ : forall K' kk' m' sx, kdescr K' = Some (kb, kk', Some m') -> glo <= kk' -> kk' + m' <= ghi ->
  In sx sxs -> verdictJ (mk_sxi X sx) bid gqj = true -> prG K' sx = PKeep.
Proof.
  intros K' kk' m' sx HD Hlo Hhi Hsx EV. unfold prG.
  set (ei' := EI bid xH kb obr kk' (Some m')).
  assert (Hinb : inb (bid, obr, (glo, ghi)) ei' = true).
  { unfold inb. cbn [ei' ei_m ei_bid ei_br ei_k]. rewrite Pos.eqb_refl, obr_eqb_refl.
    apply Z.leb_le in Hlo. rewrite Hlo. cbn [andb]. apply Z.leb_le. exact Hhi. }
  assert (HK' : EINF bc t K' (Some ei')) by (cbn [EINF ei' ei_kb ei_k ei_m ei_bid ei_br]; exact (conj HD (conj HIn eq_refl))).
  unfold gqj in EV. apply verdictJ_F in EV.
  change (match obr with Some (lo2, hi2) => Some (glo + lo2, ghi + hi2) | None => None end) with (gq_of (bid, obr, (glo, ghi))) in EV.
  rewrite verdictF_eq in EV.
  exact (verdict_keepG bc t sx _ ei' K' HT (proj1 (Forall_forall _ _) HS sx Hsx) HK' Hinb EV).
Qed.
Lemma grp_keepV : forall K' kk' m' sx, kdescr K' = Some (kb, kk', Some m') -> glo <= kk' -> kk' + m' <= ghi ->
  In sx sxs -> skipv5 bc bid glo ghi gx gqj (mk_sxi X sx) = true -> prG K' sx = PKeep.
Proof.
  intros K' kk' m' sx HD Hlo Hhi Hsx HSK. unfold skipv5 in HSK.
  destruct (verdictJ (mk_sxi X sx) bid gqj) eqn:EV; [exact (grp_keepJ K' kk' m' sx HD Hlo Hhi Hsx EV)|].
  unfold gx in HSK. destruct (is_litb kb) eqn:Hlit; [unfold linV2 in HSK; discriminate|].
  apply (linV2_linV _ _ _ obr) in HSK. unfold prG.
  set (ei' := EI bid xH kb obr kk' (Some m')).
  assert (Hinb : inb (bid, obr, (glo, ghi)) ei' = true).
  { unfold inb. cbn [ei' ei_m ei_bid ei_br ei_k]. rewrite Pos.eqb_refl, obr_eqb_refl.
    apply Z.leb_le in Hlo. rewrite Hlo. cbn [andb]. apply Z.leb_le. exact Hhi. }
  refine (linV_keep bc X sx bid obr glo ghi (GXI kb (xget X bid)) K' ei' HX (HX _) Hlit _ Hinb HSK).
  unfold member_ok. rewrite HD. cbn [gx_b]. rewrite p_expr_eqb_refl.
  apply Z.leb_le in Hlo. rewrite Hlo. apply Z.leb_le. exact Hhi.
Qed.

Lemma grp_oth : forall sbl K' kk' m' sx,
  SBL_OK (map (mk_sxi X) sxs) (map (mk_sxi X) sxs) sbl ->
  (forall si, In si (map (mk_sxi X) sxs) -> exists e, In e sbl /\ sbe_b e = sx_bid (si_sx si)) ->
  (if forallbF (fun e => if Pos.eqb bid (sbe_b e) then true else hv_other (sbe_h e) gqj) sbl then []
   else mk_flG (skipo5 bc bid glo ghi gx gqj) (map (mk_sxi X) sxs)) = [] ->
  kdescr K' = Some (kb, kk', Some m') -> glo <= kk' -> kk' + m' <= ghi ->
  In sx sxs -> Pos.eqb bid (sx_bid sx) = false -> prG K' sx = PKeep.
Proof.
  intros sbl K' kk' m' sx HSB1 HSB2 EFLO HD Hlo Hhi Hsx Hne.
  destruct (forallbF (fun e => if Pos.eqb bid (sbe_b e) then true else hv_other (sbe_h e) gqj) sbl) eqn:EALL.
  - apply (grp_keepJ K' kk' m' sx HD Hlo Hhi Hsx).
    destruct (HSB2 (mk_sxi X sx) (in_map _ _ _ Hsx)) as (se & Hse & Hseb). cbn [si_sx mk_sxi] in Hseb.
    pose proof (forallbF_in _ _ _ EALL se Hse) as HV. cbv beta in HV. rewrite Hseb, Hne in HV.
    destruct (HSB1 se Hse) as [HOK _]. unfold SBE_OK in HOK. rewrite Hseb in HOK.
    destruct (mk_flG_in (osame (sx_bid sx)) (map (mk_sxi X) sxs) (mk_sxi X sx) (in_map _ _ _ Hsx)) as [r Hr].
    { unfold osame. cbn [si_sx mk_sxi]. rewrite Pos.eqb_refl. reflexivity. }
    rewrite HOK in HV. destruct (hull_of (mk_flG (osame (sx_bid sx)) (map (mk_sxi X) sxs))) as [[[[A0 B0] c0] d0]|] eqn:EH; [|discriminate].
    exact (hv_other_verdictJ X sx bid gqj A0 B0 c0 d0 _ r EH Hr Hne HV).
  - apply (grp_keepV K' kk' m' sx HD Hlo Hhi Hsx).
    pose proof (mk_flG_nil _ _ EFLO (mk_sxi X sx) (in_map _ _ _ Hsx)) as HSO.
    unfold skipo5 in HSO. cbn [si_sx mk_sxi] in HSO. rewrite Hne in HSO. exact HSO.
Qed.
End GrpKeep.

Definition ksym (K : kentry) : option (expr * Z * expr) :=
  match K with
  | KZero (SA kb kk) len | KUnk (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
      match len with ELit _ => None | _ => Some (kb, kk, len) end
  | _ => None
  end.
Fixpoint in_sidesXM (bc : bctx) (m : smemo) (D : list (saddr * expr)) (b : expr) (k : Z) (n : expr) : bool * smemo :=
  match D with
  | [] => (false, m)
  | (c, e) :: r =>
      match sm_find m c e with
      | Some true => (true, m)
      | Some false => in_sidesXM bc m r b k n
      | None => if sub_itv_xB bc b k n c e then (true, (c, e, true) :: m) else in_sidesXM bc ((c, e, false) :: m) r b k n
      end
  end.
Definition MEMO_OKX (bc : bctx) (b : expr) (k : Z) (n : expr) (m : smemo) : Prop := forall c e r, In (c, e, r) m -> r = sub_itv_xB bc b k n c e.
Lemma sm_find_okX : forall bc b k n m c e r, MEMO_OKX bc b k n m -> sm_find m c e = Some r -> r = sub_itv_xB bc b k n c e.
Proof.
  intros bc b k n m c e r. induction m as [|[[c' e'] r'] rest IH]; intros H HF; [discriminate|]. cbn [sm_find] in HF. eF.
  destruct (if expr_eqb (a_base c) (a_base c') then if Z.eqb (a_off c) (a_off c') then expr_eqb e e' else false else false) eqn:E.
  - injection HF as <-. destruct (expr_eqb (a_base c) (a_base c')) eqn:E1; [|discriminate]. destruct (Z.eqb_spec (a_off c) (a_off c')) as [E2|]; [|discriminate].
    apply p_expr_eqb_eq in E1. apply p_expr_eqb_eq in E. subst e'. destruct c as [cb co], c' as [cb' co']. cbn [a_base a_off] in *. subst cb' co'.
    apply H. left. reflexivity.
  - apply IH; [intros c0 e0 r0 H0; apply H; right; exact H0|exact HF].
Qed.
Lemma in_sidesXM_ok : forall bc D b k n m, MEMO_OKX bc b k n m ->
  fst (in_sidesXM bc m D b k n) = in_sides_xB bc D b k n /\ MEMO_OKX bc b k n (snd (in_sidesXM bc m D b k n)).
Proof.
  intros bc D b k n. induction D as [|[c e] r IH]; intros m H; [split; [reflexivity|exact H]|].
  cbn [in_sidesXM in_sides_xB]. destruct (sm_find m c e) as [[|]|] eqn:EF.
  - rewrite <- (sm_find_okX bc b k n m c e true H EF). split; [reflexivity|exact H].
  - rewrite <- (sm_find_okX bc b k n m c e false H EF). exact (IH m H).
  - destruct (sub_itv_xB bc b k n c e) eqn:ES.
    + split; [reflexivity|]. intros c0 e0 r0 [E|H0]; [injection E as <- <- <-; symmetry; exact ES|exact (H c0 e0 r0 H0)].
    + apply IH. intros c0 e0 r0 [E|H0]; [injection E as <- <- <-; symmetry; exact ES|exact (H c0 e0 r0 H0)].
Qed.

Definition skipX (bc : bctx) (same_of : positive -> bool) (enj : option (PrimInt63.int * PrimInt63.int * option PrimInt63.int))
           (sym : option (expr * Z * expr)) (si : sxi) : bool :=
  if same_of (sx_bid (si_sx si)) then false
  else if symnumJ si enj then true
  else match sym with Some (b, k, n) => in_sides_xB bc (sp_Dx (sx_sp (si_sx si))) b k n | None => false end.
Fixpoint mk_flX (bc : bctx) (same_of : positive -> bool) (enj : option (PrimInt63.int * PrimInt63.int * option PrimInt63.int))
         (sym : option (expr * Z * expr)) (m : smemo) (sis : list sxi) : list (sxi * list sxi) :=
  match sis with
  | [] => []
  | si :: srest =>
      if same_of (sx_bid (si_sx si)) then (si, srest) :: mk_flX bc same_of enj sym m srest
      else if symnumJ si enj then mk_flX bc same_of enj sym m srest
      else match sym with
           | Some (b, k, n) =>
               let '(v, m') := in_sidesXM bc m (sp_Dx (sx_sp (si_sx si))) b k n in
               if v then mk_flX bc same_of enj sym m' srest else (si, srest) :: mk_flX bc same_of enj sym m' srest
           | None => (si, srest) :: mk_flX bc same_of enj sym m srest
           end
  end.
Lemma mk_flX_eq : forall bc same_of enj sym sis m,
  match sym with Some (b, k, n) => MEMO_OKX bc b k n m | None => True end ->
  mk_flX bc same_of enj sym m sis = mk_flG (skipX bc same_of enj sym) sis.
Proof.
  intros bc same_of enj sym sis. induction sis as [|si rest IH]; intros m H; [reflexivity|].
  cbn [mk_flX mk_flG]. unfold skipX at 1.
  destruct (same_of (sx_bid (si_sx si))); [rewrite (IH m H); reflexivity|].
  destruct (symnumJ si enj); [exact (IH m H)|].
  destruct sym as [[[b k] n]|]; [|rewrite (IH m H); reflexivity].
  destruct (in_sidesXM_ok bc (sp_Dx (sx_sp (si_sx si))) b k n m H) as [E1 E2].
  destruct (in_sidesXM bc m (sp_Dx (sx_sp (si_sx si))) b k n) as [v m']. cbn [fst snd] in E1, E2. rewrite <- E1.
  rewrite (IH m' E2). reflexivity.
Qed.

Lemma sidesx_keep : forall bc sx K b k n br2, ksym K = Some (b, k, n) ->
  in_sides_xB bc (sp_Dx (sx_sp sx)) b k n = true ->
  prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K false br2 = PKeep.
Proof.
  intros bc sx K b k n br2 HK HS.
  assert (RAP : forall z1, ranges_apart_pcB bc (sx_sp sx) (a_base (sx_a sx)) (a_off (sx_a sx)) (ELit z1) br2 b k n = true).
  { intros z1. unfold ranges_apart_pcB.
    destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
      cbn [ksym] in HK; try discriminate;
      (destruct len as [z| | | | | | |]; [discriminate| ..]); injection HK as <- <- <-; rewrite HS;
      match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end. }
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    cbn [ksym] in HK; try discriminate;
    (destruct len as [z| | | | | | |]; [discriminate| ..]); injection HK as <- <- <-;
    unfold prune1pcK, elen; cbv zeta; rewrite RAP; reflexivity.
Qed.

Fixpoint entriesGF8 (bc : bctx) (X : ptree (option bx)) (sis : list sxi) (gl : ptree (option grp6))
         (kn : list kentry) (infos : list (option einfoF)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | Some ei =>
           match ef_m ei with
           | Some _ =>
               match pt_get gl (ef_gid ei) with
               | Some (Some g) =>
                   match k_flo g with
                   | [] => match k_same g with
                           | SNone => [K]
                           | SClean fl => match ent_iv K with
                                          | Some _ => [K]
                                          | None => chainKFF2 bc (xget X (ef_bid ei)) fl K (kbase K) (sameof K ei) (br2of K ei) None
                                          end
                           | SDirty fl => match ent_iv K with
                                          | Some (a, e) => chainKP bc (xget X (ef_bid ei)) fl a e K (kbase K) (sameof K ei) (br2of K ei)
                                          | None => chainKFF2 bc (xget X (ef_bid ei)) fl K (kbase K) (sameof K ei) (br2of K ei) None
                                          end
                           end
                   | _ :: _ => chainKFF2 bc (xget X (ef_bid ei)) (k_fl g) K (kbase K) (sameof K ei) (br2of K ei) None
                   end
               | _ => chainK2F2 bc (xget X (ef_bid ei)) sis K (kbase K) (sameof K ei) (br2of K ei) None
               end
           | None =>
               let p := mk_pre bc K (br2of K ei) in
               let enj := enj_of K (br2of K ei) (fst p) (snd p) in
               chainKFF2 bc (xget X (ef_bid ei)) (mk_flX bc (sameof K ei) enj (ksym K) [] sis)
                         K (kbase K) (sameof K ei) (br2of K ei) (Some p)
           end
       | None => if is_fact_entry K then [K] else chainK2F2 bc None sis K None (fun _ => false) None None
       end) ++ entriesGF8 bc X sis gl rest irest
  | _, _ => []
  end.

Lemma entriesGF8_C : forall bc X t sxs gs kn infos, XOK bc X -> NTI bc t -> Forall (SX_OK bc t) sxs -> Forall2 (EINFF bc t) kn infos ->
  Forall (in_grpo gs) infos ->
  entriesGF8 bc X (map (mk_sxi X) sxs)
             (mk_glF6 bc (nt_info t) X (gs_bnds gs) (map (mk_sxi X) sxs) (mk_sbl (map (mk_sxi X) sxs) (map (mk_sxi X) sxs) [])) kn infos
  = entC bc sxs kn (map (option_map ef_ei) infos).
Proof.
  intros bc X t sxs gs kn infos HX HT HS HF HG.
  set (sis := map (mk_sxi X) sxs).
  assert (SBL0 : SBL_OK sis sis []) by (intros e []).
  destruct (mk_sbl_ok sis sis [] SBL0) as (HSB1 & HSB2 & _).
  set (sbl := mk_sbl sis sis []) in *.
  induction HF as [|K oi rest irest HK HF IH]; [reflexivity|].
  pose proof (Forall_inv HG) as HG0. specialize (IH (Forall_inv_tail HG)).
  cbn [entriesGF8 entC map]. rewrite IH. f_equal.
  destruct oi as [ei|].
  - cbn [option_map ei_bid ei_br ef_ei]. destruct HK as [HK HE]. unfold sameof, br2of.
    destruct (ef_m ei) as [m|] eqn:Hm.
    2:{ rewrite mk_flX_eq by (destruct (ksym K) as [[[b0 k0] n0]|]; [intros c0 e0 r0 []|exact I]).
        apply chainKFF2_eqG; [exact HX|apply HX|reflexivity|reflexivity|].
        intros sx _ HSK. unfold skipX in HSK. cbn [mk_sxi si_sx] in HSK.
        destruct (match kbase K with Some _ => Pos.eqb (ef_bid ei) | None => fun _ => false end (sx_bid sx)) eqn:ES; [discriminate|].
        match type of HSK with (if symnumJ ?a ?b then _ else _) = true => destruct (symnumJ a b) eqn:ESN end.
        - exact (symnumJ_keep bc X sx K _ ESN).
        - destruct (ksym K) as [[[b0 k0] n0]|] eqn:EKS; [|discriminate]. exact (sidesx_keep bc sx K b0 k0 n0 _ EKS HSK). }
    cbn [in_grpo] in HG0. unfold in_grp in HG0. rewrite Hm in HG0. destruct HG0 as (obr0 & glo & ghi & EB & Hlo & Hhi).
    rewrite (HE m eq_refl) in Hhi.
    unfold mk_glF6. rewrite pt_get_map, EB.
    destruct (pt_get (nt_info t) (ef_bid ei)) as [bi|] eqn:Hbi.
    2:{ apply chainK2F2_eq; [exact HX|apply HX|reflexivity|exact I]. }
    cbn [k_flo k_fl k_same].
    assert (GM0 : forall gx, GMEMO bc glo ghi gx []) by (intros [x|]; [intros c e r []|exact I]).
    rewrite (proj1 (mk_flM_eq bc (ef_bid ei) glo ghi _ _ sis [] (GM0 _))), (proj2 (mk_flM_eq bc (ef_bid ei) glo ghi _ _ sis [] (GM0 _))).
    cbn [EINF ef_ei ei_kb ei_k ei_m ei_bid ei_br] in HK. destruct HK as (HD & HIn & Hbr). rewrite Hm in HD.
    rewrite (nti_info _ _ _ _ HT HIn) in Hbi. injection Hbi as <-. cbn [bi_base bi_br]. rewrite Hbr.
    set (obr := base_rangeB bc (ef_kb ei)).
    set (gx := if is_litb (ef_kb ei) then None else Some (GXI (ef_kb ei) (xget X (ef_bid ei)))).
    set (gqj := gqj_of (match obr with Some (lo2, hi2) => Some (glo + lo2, ghi + hi2) | None => None end)).
    set (flo := if forallbF (fun e => if Pos.eqb (ef_bid ei) (sbe_b e) then true else hv_other (sbe_h e) gqj) sbl then []
                else mk_flG (skipo5 bc (ef_bid ei) glo ghi gx gqj) sis).
    change (match kbase K with Some _ => Pos.eqb (ef_bid ei) | None => fun _ => false end) with
           (match kbase K with Some _ => Pos.eqb (ef_bid ei) | None => fun _ : positive => false end).

    assert (PRG : forall K' sx, kbase K' = kbase K ->
       prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K'
         (match kbase K with Some _ => Pos.eqb (ef_bid ei) | None => fun _ => false end (sx_bid sx))
         (match kbase K with Some _ => obr | None => None end) = prG bc (ef_bid ei) (ef_kb ei) K' sx).
    { intros K' sx E. unfold prG. rewrite E. reflexivity. }
    destruct flo as [|p0 fl0] eqn:EFLO.
    2:{ apply chainKFF2_eqG; [exact HX|apply HX|reflexivity|exact I|]. intros sx Hsx HSK. rewrite (PRG K sx eq_refl).
        exact (grp_keepV bc X t sxs HX HT HS (ef_bid ei) (ef_kb ei) glo ghi HIn K (ef_k ei) m sx HD Hlo Hhi Hsx HSK). }

    assert (OTH : forall K' kk' m' sx, kbase K' = kbase K -> kdescr K' = Some (ef_kb ei, kk', Some m') -> glo <= kk' -> kk' + m' <= ghi ->
       In sx sxs -> Pos.eqb (ef_bid ei) (sx_bid sx) = false ->
       pk_rel K' PKeep (prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K'
         (match kbase K with Some _ => Pos.eqb (ef_bid ei) | None => fun _ => false end (sx_bid sx))
         (match kbase K with Some _ => obr | None => None end))).
    { intros K' kk' m' sx EKB HD' Hlo' Hhi' Hsx Hne. left. symmetry. rewrite (PRG K' sx EKB).
      exact (grp_oth bc X t sxs HX HT HS (ef_bid ei) (ef_kb ei) glo ghi HIn sbl K' kk' m' sx HSB1 HSB2 EFLO HD' Hlo' Hhi' Hsx Hne). }
    assert (SAMEC : forall sx, In sx sxs -> Pos.eqb (ef_bid ei) (sx_bid sx) = true ->
      match kbase K with Some _ => (match kbase K with Some _ => Pos.eqb (ef_bid ei) | None => fun _ => false end (sx_bid sx)) = true
                       | None => a_base (sx_a sx) = ELit 0 end).
    { intros sx Hsx ES. destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
      - rewrite HB. exact ES.
      - cbn [kbase]. pose proof (proj1 (Forall_forall _ _) HS sx Hsx) as (SXin & _ & _).
        rewrite (nt_same_eq _ _ _ _ _ _ HT HIn SXin), Hkb in ES. apply p_expr_eqb_eq in ES. symmetry. exact ES. }
    assert (FULL : forall se, In se sbl -> sbe_b se = ef_bid ei ->
       chainKFF2 bc (xget X (ef_bid ei)) (sbe_fl se) K (kbase K)
         (match kbase K with Some _ => Pos.eqb (ef_bid ei) | None => fun _ => false end)
         (match kbase K with Some _ => obr | None => None end) None
       = chainK2 bc sxs K (kbase K) (match kbase K with Some _ => Pos.eqb (ef_bid ei) | None => fun _ => false end)
                 (match kbase K with Some _ => obr | None => None end)).
    { intros se Hse Hseb. destruct (HSB1 se Hse) as [_ HFL]. rewrite Hseb in HFL. rewrite HFL.
      apply chainKFF2_eqG2; [exact HX|apply HX|reflexivity|exact I|].
      intros sx Hsx HSK. unfold osame in HSK. cbn [si_sx mk_sxi] in HSK.
      destruct (Pos.eqb (ef_bid ei) (sx_bid sx)) eqn:ES; [discriminate|exact (OTH K _ _ sx eq_refl HD Hlo Hhi Hsx ES)]. }
    destruct (sb_find sbl (ef_bid ei)) as [se|] eqn:ESB.
    + destruct (sb_find_in _ _ _ ESB) as [Hse Hseb]. destruct (HSB1 se Hse) as [HOK HFL]. unfold SBE_OK in HOK. rewrite Hseb in HOK, HFL.
      destruct (hv_same (sbe_h se) (match z2b glo with Some a => match z2b ghi with Some e' => Some (a, e') | None => None end | None => None end)) eqn:EHS.
      *
        destruct (ent_iv K) as [[a e]|] eqn:EIV; [|exact (FULL se Hse Hseb)].
        rewrite <- (chainKFF2_eqG2 bc X (xget X (ef_bid ei)) (fun _ => true) sxs K (kbase K) _ _ None HX (HX _) eq_refl I).
        -- fold sis. rewrite mk_flG_all by reflexivity. reflexivity.
        -- intros sx Hsx _. destruct (Pos.eqb (ef_bid ei) (sx_bid sx)) eqn:ES; [|exact (OTH K _ _ sx eq_refl HD Hlo Hhi Hsx ES)].
           destruct (mk_flG_in (osame (ef_bid ei)) sis (mk_sxi X sx) (in_map _ _ _ Hsx)) as [r Hr].
           { unfold osame. cbn [si_sx mk_sxi]. rewrite ES. reflexivity. }
           rewrite HOK in EHS. unfold hv_same in EHS.
           destruct (hull_of (mk_flG (osame (ef_bid ei)) sis)) as [[[[A0 B0] c0] d0]|] eqn:EH; [|discriminate].
           destruct (z2b glo) as [gl'|] eqn:EGL; [|discriminate]. destruct (z2b ghi) as [gh'|] eqn:EGH; [|discriminate].
           destruct (hull_of_cov _ _ _ _ _ EH _ _ Hr) as (A & B & c & d & EA & EI & _ & _ & Lc & Ld).
           destruct (ent_iv_descr _ _ _ _ _ _ EIV HD) as [Va Ve]. apply z2b_val in EGL. apply z2b_val in EGH.
           apply (nonov_keep bc X sx K a e _ _ EIV); [|exact (SAMEC sx Hsx ES)].
           apply (nonov_hull X sx a e gl' gh' c0 d0 A B c d EI EA Lc Ld); [apply ileb_true; lia|apply ileb_true; lia|exact EHS].
      *
        destruct (ent_iv K) as [[a e]|] eqn:EIV; [|exact (FULL se Hse Hseb)].
        rewrite HFL. fold sis. destruct (ent_iv_descr _ _ _ _ _ _ EIV HD) as [Va Ve].
        apply chainKP_eq; [exact HX|apply HX| |reflexivity|exact EIV].
        intros K' a' e' EKB EI' La Le sx Hsx HSK. unfold osame in HSK. cbn [si_sx mk_sxi] in HSK.
        destruct (Pos.eqb (ef_bid ei) (sx_bid sx)) eqn:ES.
        -- apply (nonov_keep bc X sx K' a' e' _ _ EI' HSK). rewrite EKB. exact (SAMEC sx Hsx ES).
        -- destruct (ent_iv_kdescr _ _ _ EI') as (kb' & kk' & m' & HD' & Va' & Ve').
           assert (Ekb : kb' = ef_kb ei).
           { destruct (kdescr_kbase _ _ _ _ HD') as [HB'|(lo' & hi' & -> & Hkb' & _)];
               destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & _)].
             - rewrite HB', HB in EKB. injection EKB as ->. reflexivity.
             - rewrite HB' in EKB. cbn [kbase] in EKB. discriminate.
             - rewrite HB in EKB. cbn [kbase] in EKB. discriminate.
             - congruence. }
           subst kb'. apply (OTH K' kk' m' sx EKB HD'); [lia|lia|exact Hsx|exact ES].
    + rewrite <- (chainKFF2_eqG2 bc X (xget X (ef_bid ei)) (fun _ => true) sxs K (kbase K) _ _ None HX (HX _) eq_refl I).
      * fold sis. rewrite mk_flG_all by reflexivity. reflexivity.
      * intros sx Hsx _. apply (OTH K _ _ sx eq_refl HD Hlo Hhi Hsx). apply Pos.eqb_neq. intros Ebb.
        destruct (HSB2 (mk_sxi X sx) (in_map _ _ _ Hsx)) as (se & Hse & Hseb). cbn [si_sx mk_sxi] in Hseb.
        apply (sb_find_none _ _ ESB se Hse). rewrite Hseb. symmetry. exact Ebb.
  - cbn [EINFF] in HK. cbn [option_map].
    destruct (is_fact_entry K) eqn:HFK.
    + symmetry. apply chainK2_fact. exact HFK.
    + apply chainK2F2_eq; [exact HX|intros x Hx; discriminate|symmetry; apply kdescr_None_kbase; exact HK|exact I].
Qed.

Definition i16 : int := Uint63.of_Z 16.
Definition i4 : int := Uint63.of_Z 4.
Definition sgran (x : int) : int := PrimInt63.lsr x i4.
Fixpoint i2p (fuel : nat) (i : int) : positive :=
  match fuel with
  | O => xH
  | S f => if PrimInt63.leb i i1 then xH
           else if PrimInt63.eqb (PrimInt63.land i i1) i0 then xO (i2p f (PrimInt63.lsr i i1)) else xI (i2p f (PrimInt63.lsr i i1))
  end.
Definition gkeyI (g : int) : positive := i2p 62 g.
Definition sfl : Type := list (sxi * list sxi).
Record ixb := IXB { ixb_b : positive; ixb_ok : bool; ixb_t : ptree sfl }.
Definition sbucket (t : ptree sfl) (k : positive) : sfl := match pt_get t k with Some l => l | None => [] end.
Fixpoint ix_find (l : list ixb) (b : positive) : option ixb :=
  match l with [] => None | x :: r => if Pos.eqb b (ixb_b x) then Some x else ix_find r b end.
Fixpoint ix_upd (l : list ixb) (b : positive) (f : ixb -> ixb) : list ixb :=
  match l with
  | [] => [f (IXB b true PTLeaf)]
  | x :: r => if Pos.eqb b (ixb_b x) then f x :: r else x :: ix_upd r b f
  end.
Definition narrow (c d : int) : bool := if PrimInt63.ltb c d then PrimInt63.leb (PrimInt63.sub d c) i16 else false.
Definition ix_ins (p : sxi * list sxi) (c d : int) (x : ixb) : ixb :=
  if narrow c d then
    let k1 := gkeyI (sgran c) in
    let k2 := gkeyI (sgran (PrimInt63.sub d i1)) in
    let t1 := pt_set k1 (p :: sbucket (ixb_t x) k1) (ixb_t x) in
    IXB (ixb_b x) (ixb_ok x) (if Pos.eqb k1 k2 then t1 else pt_set k2 (p :: sbucket t1 k2) t1)
  else IXB (ixb_b x) false (ixb_t x).
Definition ix_add (l : list ixb) (si : sxi) (newer : list sxi) : list ixb :=
  let b := sx_bid (si_sx si) in
  match si_iv si with
  | Some (c, d) => ix_upd l b (ix_ins (si, newer) c d)
  | None => ix_upd l b (fun x => IXB (ixb_b x) false (ixb_t x))
  end.
Definition ix_cands (l : list ixb) (b : positive) (a e : int) : option sfl :=
  match ix_find l b with
  | Some x =>
      if ixb_ok x then
        if PrimInt63.ltb a e then
          let g := sgran a in
          if PrimInt63.eqb g (sgran (PrimInt63.sub e i1)) then Some (sbucket (ixb_t x) (gkeyI g)) else None
        else None
      else None
  | None => None
  end.
Fixpoint sp9 (bc : bctx) (sbl : list sbe) (sis : list sxi) : list ixb * list kentry :=
  match sis with
  | [] => ([], [])
  | si :: newer =>
      let '(ixs, racc) := sp9 bc sbl newer in
      let sx := si_sx si in
      let b := sx_bid sx in
      let K := KWord (sx_a sx) (sx_w sx) (sx_v sx) in
      let gen := fun _ : unit => chainKFF2 bc (si_bx si) (mk_flG (skipS5 bc si) newer) K (Some (a_base (sx_a sx))) (Pos.eqb b) (sx_br sx) None in
      let P := match si_iv si, si_eabj si with
               | Some (a, e), Some (el, eh) =>
                   if forallbF (fun e' => if Pos.eqb b (sbe_b e') then true else hs_other (sbe_h e') el eh) sbl
                   then chainKI bc (si_bx si) (match ix_cands ixs b a e with Some fl => fl | None => mk_flG (osame b) newer end) a e K
                                (Some (a_base (sx_a sx))) (Pos.eqb b) (sx_br sx)
                   else gen tt
               | _, _ => gen tt
               end in
      (ix_add ixs si newer, rev_append P racc)
  end.
Definition stores_partF9 (bc : bctx) (sis : list sxi) (sbl : list sbe) : list kentry := rev' (snd (sp9 bc sbl sis)).

Definition notouch (G : int) (si : sxi) : Prop :=
  exists c d, si_iv si = Some (c, d) /\ toZ c < toZ d /\ toZ d - toZ c <= 16 /\ G <> sgran c /\ G <> sgran (PrimInt63.sub d i1).
Inductive SubG (G : int) : sfl -> sfl -> Prop :=
| SubG_nil : SubG G [] []
| SubG_keep : forall x c f, SubG G c f -> SubG G (x :: c) (x :: f)
| SubG_drop : forall x c f, notouch G (fst x) -> SubG G c f -> SubG G c (x :: f).
Lemma SubG_refl : forall G l, SubG G l l.
Proof. intros G l. induction l as [|x r IH]; [constructor|constructor; exact IH]. Qed.
Lemma i16_val : toZ i16 = 16. Proof. reflexivity. Qed.
Lemma i4_val : toZ i4 = 4. Proof. reflexivity. Qed.
Lemma sgran_val : forall x, toZ (sgran x) = toZ x / 16.
Proof. intros x. unfold sgran. rewrite Uint63Axioms.lsr_spec, i4_val. reflexivity. Qed.
Lemma iltb_ge : forall x y, PrimInt63.ltb x y = false -> toZ y <= toZ x.
Proof.
  intros x y H. destruct (Z.lt_ge_cases (toZ x) (toZ y)) as [L|G]; [|exact G].
  apply Uint63Axioms.ltb_spec in L. congruence.
Qed.
Lemma notouch_nonov : forall G si a e, notouch G si -> toZ a < toZ e -> sgran a = G -> sgran (PrimInt63.sub e i1) = G -> nonov si a e = true.
Proof.
  intros G si a e (c & d & HI & Hcd & Hw & N1 & N2) Hae G1 G2. unfold nonov. rewrite HI.
  destruct (PrimInt63.leb e c) eqn:E1; [reflexivity|]. apply ileb_gt in E1.
  destruct (PrimInt63.leb d a) eqn:E2; [reflexivity|]. apply ileb_gt in E2. exfalso.
  assert (Se : toZ (PrimInt63.sub e i1) = toZ e - 1) by (rewrite sub_nov; rewrite i1_val; [reflexivity|pose proof (Uint63.to_Z_bounded a); lia]).
  assert (Sd : toZ (PrimInt63.sub d i1) = toZ d - 1) by (rewrite sub_nov; rewrite i1_val; [reflexivity|pose proof (Uint63.to_Z_bounded c); lia]).
  assert (Ga : toZ a / 16 = toZ G) by (rewrite <- G1; symmetry; apply sgran_val).
  assert (Ge : (toZ e - 1) / 16 = toZ G) by (rewrite <- Se, <- G2; symmetry; apply sgran_val).
  assert (NC : toZ G <> toZ c / 16) by (intros E; apply N1; apply Uint63.to_Z_inj; rewrite sgran_val; exact E).
  assert (ND : toZ G <> (toZ d - 1) / 16) by (intros E; apply N2; apply Uint63.to_Z_inj; rewrite sgran_val, Sd; exact E).
  pose proof (Uint63.to_Z_bounded a). pose proof (Uint63.to_Z_bounded c).
  set (x := Z.max (toZ a) (toZ c)).
  assert (X1 : x / 16 = toZ G).
  { assert (toZ a / 16 <= x / 16) by (apply Z.div_le_mono; lia). assert (x / 16 <= (toZ e - 1) / 16) by (apply Z.div_le_mono; lia). lia. }
  assert (X2 : x / 16 = toZ c / 16 \/ x / 16 = (toZ d - 1) / 16).
  { assert (toZ c / 16 <= x / 16) by (apply Z.div_le_mono; lia). assert (x / 16 <= (toZ d - 1) / 16) by (apply Z.div_le_mono; lia).
    assert ((toZ d - 1) / 16 <= toZ c / 16 + 1).
    { replace (toZ c / 16 + 1) with ((toZ c + 1 * 16) / 16) by (rewrite Z.div_add by lia; reflexivity). apply Z.div_le_mono; lia. }
    lia. }
  destruct X2 as [X2|X2]; congruence.
Qed.
Lemma SubG_chainKI : forall bc xo G cands fl a e K okb same_of br2, SubG G cands fl ->
  toZ a < toZ e -> sgran a = G -> sgran (PrimInt63.sub e i1) = G ->
  chainKI bc xo cands a e K okb same_of br2 = chainKI bc xo fl a e K okb same_of br2.
Proof.
  intros bc xo G cands fl a e K okb same_of br2 HS Hae G1 G2. induction HS as [|[si rest] c f HS IH|[si rest] c f HN HS IH].
  - reflexivity.
  - cbn [chainKI]. rewrite IH. reflexivity.
  - cbn [chainKI]. cbn [fst] in HN. rewrite (notouch_nonov G si a e HN Hae G1 G2). exact IH.
Qed.

Definition IXE_OK (newer : list sxi) (x : ixb) : Prop :=
  ixb_ok x = true -> forall G, SubG G (sbucket (ixb_t x) (gkeyI G)) (mk_flG (osame (ixb_b x)) newer).
Definition IXL_OK (newer : list sxi) (l : list ixb) : Prop :=
  (forall b x, ix_find l b = Some x -> ixb_b x = b /\ IXE_OK newer x) /\
  (forall b, ix_find l b = None -> mk_flG (osame b) newer = []).
Lemma ix_find_upd_same : forall l b f, (forall x, ixb_b (f x) = ixb_b x) ->
  ix_find (ix_upd l b f) b = Some (f (match ix_find l b with Some x => x | None => IXB b true PTLeaf end)).
Proof.
  intros l b f Hf. induction l as [|y r IH]; cbn [ix_upd ix_find].
  - rewrite Hf. cbn [ixb_b]. rewrite Pos.eqb_refl. reflexivity.
  - destruct (Pos.eqb b (ixb_b y)) eqn:E; cbn [ix_find].
    + rewrite Hf, E. reflexivity.
    + rewrite E. exact IH.
Qed.
Lemma ix_find_upd_other : forall l b b' f, (forall x, ixb_b (f x) = ixb_b x) -> b' <> b ->
  ix_find (ix_upd l b f) b' = ix_find l b'.
Proof.
  intros l b b' f Hf NE. induction l as [|y r IH]; cbn [ix_upd ix_find].
  - rewrite Hf. cbn [ixb_b]. destruct (Pos.eqb_spec b' b) as [E|_]; [exfalso; exact (NE E)|reflexivity].
  - destruct (Pos.eqb b (ixb_b y)) eqn:E; cbn [ix_find].
    + rewrite Hf. apply Pos.eqb_eq in E. destruct (Pos.eqb_spec b' (ixb_b y)) as [E'|_]; [exfalso; apply NE; rewrite E', E; reflexivity|reflexivity].
    + rewrite IH. reflexivity.
Qed.
Lemma mk_flG_osame_same : forall si newer, mk_flG (osame (sx_bid (si_sx si))) (si :: newer) = (si, newer) :: mk_flG (osame (sx_bid (si_sx si))) newer.
Proof. intros si newer. cbn [mk_flG]. unfold osame at 1. rewrite Pos.eqb_refl. reflexivity. Qed.
Lemma mk_flG_osame_other : forall b si newer, b <> sx_bid (si_sx si) -> mk_flG (osame b) (si :: newer) = mk_flG (osame b) newer.
Proof.
  intros b si newer NE. cbn [mk_flG]. unfold osame at 1. destruct (Pos.eqb_spec b (sx_bid (si_sx si))) as [E|_]; [exfalso; exact (NE E)|reflexivity].
Qed.
Lemma sbucket_set : forall (t : ptree sfl) k k' v, sbucket (pt_set k' v t) k = if Pos.eqb k k' then v else sbucket t k.
Proof.
  intros t k k' v. unfold sbucket. destruct (Pos.eqb_spec k k') as [->|NE]; [rewrite pt_gss; reflexivity|rewrite (pt_gso _ _ _ _ _ NE); reflexivity].
Qed.
Lemma narrow_val : forall c d, narrow c d = true -> toZ c < toZ d /\ toZ d - toZ c <= 16.
Proof.
  intros c d H. unfold narrow in H. destruct (PrimInt63.ltb c d) eqn:E; [|discriminate]. apply iltb_lt in E. apply ileb_le in H.
  rewrite sub_nov, i16_val in H by lia. lia.
Qed.
Lemma IXE_ins : forall si newer c d x, si_iv si = Some (c, d) -> ixb_b x = sx_bid (si_sx si) ->
  (ixb_ok x = true -> forall G, SubG G (sbucket (ixb_t x) (gkeyI G)) (mk_flG (osame (sx_bid (si_sx si))) newer)) ->
  IXE_OK (si :: newer) (ix_ins (si, newer) c d x).
Proof.
  intros si newer c d x HI Hb HX. unfold ix_ins. destruct (narrow c d) eqn:EN; [|intros H; discriminate H].
  destruct (narrow_val _ _ EN) as [N1 N2].
  intros Hok G. cbn [ixb_ok ixb_b ixb_t] in *. rewrite Hb, mk_flG_osame_same. specialize (HX Hok G).
  set (k1 := gkeyI (sgran c)) in *. set (k2 := gkeyI (sgran (PrimInt63.sub d i1))) in *.
  assert (DROP : gkeyI G <> k1 -> gkeyI G <> k2 -> notouch G si).
  { intros D1 D2. exists c, d. split; [exact HI|]. split; [exact N1|]. split; [exact N2|].
    split; intros E; [apply D1|apply D2]; unfold k1, k2; rewrite E; reflexivity. }
  destruct (Pos.eqb k1 k2) eqn:E12.
  - apply Pos.eqb_eq in E12. rewrite sbucket_set. destruct (Pos.eqb_spec (gkeyI G) k1) as [E1|NE1].
    + apply SubG_keep. rewrite <- E1. exact HX.
    + apply SubG_drop; [cbn [fst]; apply DROP; [exact NE1|rewrite <- E12; exact NE1]|exact HX].
  - apply Pos.eqb_neq in E12. rewrite sbucket_set. destruct (Pos.eqb_spec (gkeyI G) k2) as [E2|NE2].
    + rewrite sbucket_set. destruct (Pos.eqb_spec k2 k1) as [E|_]; [exfalso; apply E12; symmetry; exact E|]. apply SubG_keep. rewrite <- E2. exact HX.
    + rewrite sbucket_set. destruct (Pos.eqb_spec (gkeyI G) k1) as [E1|NE1].
      * apply SubG_keep. rewrite <- E1. exact HX.
      * apply SubG_drop; [cbn [fst]; apply DROP; assumption|exact HX].
Qed.
Lemma IXL_OK_add : forall newer l si, IXL_OK newer l -> IXL_OK (si :: newer) (ix_add l si newer).
Proof.
  intros newer l si [H1 H2]. set (b := sx_bid (si_sx si)).
  assert (KEEP : forall f, (forall x, ixb_b (f x) = ixb_b x) ->
            (forall x, ixb_b x = b -> (ixb_ok x = true -> forall G, SubG G (sbucket (ixb_t x) (gkeyI G)) (mk_flG (osame b) newer)) -> IXE_OK (si :: newer) (f x)) ->
            IXL_OK (si :: newer) (ix_upd l b f)).
  { intros f Hf HF. split.
    - intros b' x' HF'. destruct (Pos.eq_dec b' b) as [->|NE].
      + rewrite (ix_find_upd_same l b f Hf) in HF'. injection HF' as <-. rewrite Hf.
        destruct (ix_find l b) as [x0|] eqn:E0.
        * destruct (H1 b x0 E0) as [Hb0 HX0]. split; [exact Hb0|]. apply HF; [exact Hb0|]. intros Hok G. specialize (HX0 Hok G). rewrite Hb0 in HX0. exact HX0.
        * split; [reflexivity|]. apply HF; [reflexivity|]. intros _ G. cbn [ixb_t]. unfold sbucket. rewrite pt_get_leaf, (H2 b E0). constructor.
      + rewrite (ix_find_upd_other l b b' f Hf NE) in HF'. destruct (H1 b' x' HF') as [Hb' HX']. split; [exact Hb'|].
        intros Hok G. rewrite Hb', (mk_flG_osame_other b' si newer NE). specialize (HX' Hok G). rewrite Hb' in HX'. exact HX'.
    - intros b' HN. destruct (Pos.eq_dec b' b) as [->|NE].
      + rewrite (ix_find_upd_same l b f Hf) in HN. discriminate HN.
      + rewrite (ix_find_upd_other l b b' f Hf NE) in HN. rewrite (mk_flG_osame_other b' si newer NE). exact (H2 b' HN). }
  unfold ix_add. fold b. destruct (si_iv si) as [[c d]|] eqn:HI.
  - apply KEEP.
    + intros x. unfold ix_ins. destruct (narrow c d); reflexivity.
    + intros x Hb HX. apply (IXE_ins si newer c d x HI Hb HX).
  - apply KEEP; [intros x; reflexivity|]. intros x _ _ H. discriminate H.
Qed.

Definition sbkey (e : sbe) : positive * option hull := (sbe_b e, sbe_h e).
Lemma sb_pop_keys : forall R b, map sbkey (sb_pop R b) = map sbkey R.
Proof. induction R as [|e r IH]; intros b; [reflexivity|]. cbn [sb_pop map]. rewrite IH. f_equal. destruct (Pos.eqb b (sbe_b e)); reflexivity. Qed.
Lemma forallbF_keys : forall (g : positive * option hull -> bool) R S, map sbkey R = map sbkey S ->
  forallbF (fun e => g (sbkey e)) R = forallbF (fun e => g (sbkey e)) S.
Proof.
  intros g R. induction R as [|e r IH]; intros S H; destruct S as [|e' s']; try discriminate; [reflexivity|].
  cbn [map] in H. assert (H0 : sbkey e = sbkey e') by congruence. assert (Hr : map sbkey r = map sbkey s') by congruence.
  cbn [forallbF]. rewrite H0, (IH s' Hr). reflexivity.
Qed.
Lemma forallbF_hs : forall b el eh R S, map sbkey R = map sbkey S ->
  forallbF (fun e' => if Pos.eqb b (sbe_b e') then true else hs_other (sbe_h e') el eh) R
  = forallbF (fun e' => if Pos.eqb b (sbe_b e') then true else hs_other (sbe_h e') el eh) S.
Proof. intros b el eh R S H. exact (forallbF_keys (fun p => if Pos.eqb b (fst p) then true else hs_other (snd p) el eh) R S H). Qed.
Lemma sb_find_some : forall R b, (exists e, In e R /\ sbe_b e = b) -> exists se, sb_find R b = Some se.
Proof.
  induction R as [|x r IH]; intros b (e & Hin & Hb); [destruct Hin|]. cbn [sb_find].
  destruct (Pos.eqb_spec b (sbe_b x)) as [_|NE]; [eexists; reflexivity|].
  destruct Hin as [<-|Hin]; [exfalso; apply NE; symmetry; exact Hb|]. apply IH. exists e. split; assumption.
Qed.
Lemma ix_cands_ok : forall newer l b a e fl, IXL_OK newer l -> ix_cands l b a e = Some fl ->
  forall bc xo K okb same_of br2, chainKI bc xo fl a e K okb same_of br2 = chainKI bc xo (mk_flG (osame b) newer) a e K okb same_of br2.
Proof.
  intros newer l b a e fl [H1 _] HC bc xo K okb same_of br2. unfold ix_cands in HC.
  destruct (ix_find l b) as [x|] eqn:EF; [|discriminate]. destruct (H1 b x EF) as [Hb HX].
  destruct (ixb_ok x) eqn:Eok; [|discriminate]. destruct (PrimInt63.ltb a e) eqn:El; [|discriminate].
  destruct (PrimInt63.eqb (sgran a) (sgran (PrimInt63.sub e i1))) eqn:Eg; [|discriminate]. injection HC as <-.
  apply Uint63Axioms.eqb_correct in Eg. apply iltb_lt in El.
  specialize (HX Eok (sgran a)). rewrite Hb in HX.
  apply (SubG_chainKI bc xo (sgran a)); [exact HX|exact El|reflexivity|symmetry; exact Eg].
Qed.

Lemma sp9_eq : forall bc all sbl sis R,
  SBL_OK all sis R -> (forall si, In si sis -> exists e, In e R /\ sbe_b e = sx_bid (si_sx si)) -> map sbkey R = map sbkey sbl ->
  IXL_OK sis (fst (sp9 bc sbl sis)) /\ rev (snd (sp9 bc sbl sis)) = stores_partF5 bc sis R.
Proof.
  intros bc all sbl sis. induction sis as [|si newer IH]; intros R HR HC HK.
  - cbn [sp9 fst snd stores_partF5 rev]. split; [|reflexivity]. split; [intros b x H; discriminate H|intros b _; reflexivity].
  - cbn [sp9 stores_partF5]. cbv zeta.
    set (b := sx_bid (si_sx si)).
    assert (HR' : SBL_OK all newer (sb_pop R b)) by (apply sb_pop_ok; exact HR).
    assert (HC' : forall si', In si' newer -> exists e, In e (sb_pop R b) /\ sbe_b e = sx_bid (si_sx si')).
    { intros si' Hsi. destruct (HC si' (or_intror Hsi)) as (e0 & He0 & Hb0).
      destruct (sb_pop_bases R b e0 He0) as (e & E1 & E2 & _). exists e. split; [exact E1|congruence]. }
    assert (HK' : map sbkey (sb_pop R b) = map sbkey sbl) by (rewrite sb_pop_keys; exact HK).
    destruct (IH _ HR' HC' HK') as [HIX HREV].
    destruct (sp9 bc sbl newer) as [ixs racc] eqn:ESP. cbn [fst snd] in *.
    split; [apply IXL_OK_add; exact HIX|].
    rewrite rev_append_rev, rev_app_distr, rev_involutive, HREV. f_equal.
    destruct (si_iv si) as [[a e]|] eqn:EIV; [|reflexivity].
    destruct (si_eabj si) as [[el eh]|] eqn:EE; [|reflexivity].
    rewrite (forallbF_hs b el eh (sb_pop R b) sbl HK').
    destruct (forallbF _ sbl); [|reflexivity].
    destruct (sb_find_some (sb_pop R b) b) as [se ESB].
    { destruct (HC si (or_introl eq_refl)) as (e0 & He0 & Hb0). destruct (sb_pop_bases R b e0 He0) as (e1 & E1 & E2 & _).
      exists e1. split; [exact E1|]. rewrite E2. exact Hb0. }
    rewrite ESB. destruct (sb_find_in _ _ _ ESB) as [Hse Hseb]. destruct (HR' se Hse) as [_ HFL]. rewrite HFL, Hseb.
    destruct (ix_cands ixs b a e) as [fl|] eqn:EC; [|reflexivity].
    apply (ix_cands_ok newer ixs b a e fl HIX EC).
Qed.
Lemma stores_partF9_eq : forall bc all sis sbl,
  SBL_OK all sis sbl -> (forall si, In si sis -> exists e, In e sbl /\ sbe_b e = sx_bid (si_sx si)) ->
  stores_partF9 bc sis sbl = stores_partF5 bc sis sbl.
Proof.
  intros bc all sis sbl H1 H2. unfold stores_partF9, rev'. rewrite <- rev_alt. exact (proj2 (sp9_eq bc all sbl sis sbl H1 H2 eq_refl)).
Qed.

Definition long_log (sis : list sxi) : bool := match skipn 512 sis with [] => false | _ :: _ => true end.
Definition stores_partX (bc : bctx) (sis : list sxi) (sbl : list sbe) : list kentry :=
  if long_log sis then stores_partF9 bc sis sbl else stores_partF5 bc sis sbl.
Lemma stores_partX_eq : forall bc all sis sbl,
  SBL_OK all sis sbl -> (forall si, In si sis -> exists e, In e sbl /\ sbe_b e = sx_bid (si_sx si)) ->
  stores_partX bc sis sbl = stores_partF5 bc sis sbl.
Proof. intros bc all sis sbl H1 H2. unfold stores_partX. destruct (long_log sis); [exact (stores_partF9_eq bc all sis sbl H1 H2)|reflexivity]. Qed.

Definition carryGF8C (bc : bctx) (log : list sentry) (scs : list sprep) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxsC2 log scs nt_empty in
  let '(r, gs) := scanF2 bc kn t0 gst_empty None None in
  let '(infos, t1) := r in
  let sbs := store_bases sxs PTLeaf in
  let X := pt_map (fun bi => if existsbF (fun sb => shares_var sb (bi_base bi)) sbs then Some (mk_bx bc (bi_base bi)) else None) (nt_info t1) in
  let sis := map (mk_sxi X) sxs in
  let sbl := mk_sbl sis sis [] in
  stores_partF5 bc sis sbl ++ entriesGF8 bc X sis (mk_glF6 bc (nt_info t1) X (gs_bnds gs) sis sbl) kn infos.
Lemma carryGF8_eq : forall bc log kn, carryGF8C bc log (map (mk_sctx bc (mk_bext bc)) log) kn = carryG bc log kn.
Proof.
  intros bc log kn. unfold carryGF8C, carryG. rewrite mk_stxsC2_eq.
  destruct (mk_stxs bc log nt_empty) as [sxs t0] eqn:E0.
  destruct (mk_stxs_okG _ _ _ _ _ (NTI_empty bc) E0) as (HT0 & HS0 & _).
  rewrite (scanF2_eq bc kn t0 gst_empty None None HT0 I I).
  destruct (scanF bc kn t0 gst_empty) as [[infos t1] gs] eqn:ES.
  destruct (scan_entries bc kn t0 gst_empty) as [[infos' t1'] gs'] eqn:ES'.
  destruct (scanF_sim _ _ _ _ _ _ _ _ _ _ _ ES ES') as [<- HI].
  destruct (scanF_okG _ _ _ _ _ _ _ HT0 ES) as (HT1 & Hm & HF).
  destruct (scan_entries_okG _ _ _ _ _ _ _ HT0 ES') as (_ & _ & HF').
  destruct (scanF_grp _ _ _ _ _ _ _ GSI_empty ES) as (_ & _ & HGR).
  assert (HS1 : Forall (SX_OK bc t1) sxs).
  { apply Forall_impl with (P := SX_OK bc t0); [|exact HS0]. intros sx. apply SX_OK_mono. exact Hm. }
  cbv zeta.
  match goal with |- context [mk_sbl ?s ?s []] => destruct (mk_sbl_ok s s [] (fun e (H : In e []) => match H with end)) as (HSB1 & HSB2 & _) end.
  rewrite (stores_partF5_eq bc _ t0 _ sxs _ (XOK_map _ _ _) HS0 HSB1 HSB2 (fun si H => H)). f_equal.
  rewrite (entriesGF8_C bc _ t1 sxs gs kn infos); [|apply XOK_map|exact HT1|exact HS1|exact HF|exact HGR].
  rewrite (entriesG_C bc t1 sxs _ kn infos' HT1 HS1 HF'). apply entC_strip. exact HI.
Qed.

Fixpoint mk_stxsR (log : list sentry) (scs : list sprep) (t : ntab) : list stx * ntab :=
  match log, scs with
  | SE a w v :: older, sp :: scs' =>
      let '(rs, t1) := mk_stxsR older scs' t in
      let '(r, t2) := intern_r t1 (a_base a) (sp_rng sp) in
      let '(bid, bi) := r in
      (STX a w v sp bid (bi_br bi) :: rs, t2)
  | _, _ => ([], t)
  end.
Definition mk_stxsC3 (log : list sentry) (scs : list sprep) (t : ntab) : list stx * ntab :=
  let '(rs, t') := mk_stxsR log scs t in (rev' rs, t').
Lemma mk_stxsR_eq : forall log scs t, mk_stxsR log scs t = (rev (fst (mk_stxsC2 log scs t)), snd (mk_stxsC2 log scs t)).
Proof.
  induction log as [|[a w v] older IH]; intros scs t; [reflexivity|]. destruct scs as [|sp scs']; [reflexivity|].
  cbn [mk_stxsR mk_stxsC2]. rewrite IH. destruct (mk_stxsC2 older scs' t) as [sxs t1]. cbn [fst snd].
  destruct (intern_r t1 (a_base a) (sp_rng sp)) as [[bid bi] t2]. cbn [fst snd]. rewrite rev_app_distr. reflexivity.
Qed.
Lemma mk_stxsC3_eq : forall log scs t, mk_stxsC3 log scs t = mk_stxsC2 log scs t.
Proof.
  intros log scs t. unfold mk_stxsC3. rewrite mk_stxsR_eq. destruct (mk_stxsC2 log scs t) as [sxs t1]. cbn [fst snd].
  unfold rev'. rewrite <- rev_alt, rev_involutive. reflexivity.
Qed.
Definition carryGF9C (bc : bctx) (log : list sentry) (scs : list sprep) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxsC3 log scs nt_empty in
  let '(r, gs) := scanF2 bc kn t0 gst_empty None None in
  let '(infos, t1) := r in
  let sbs := store_bases sxs PTLeaf in
  let X := pt_map (fun bi => if existsbF (fun sb => shares_var sb (bi_base bi)) sbs then Some (mk_bx bc (bi_base bi)) else None) (nt_info t1) in
  let sis := map (mk_sxi X) sxs in
  let sbl := mk_sbl sis sis [] in
  stores_partX bc sis sbl ++ entriesGF8 bc X sis (mk_glF6 bc (nt_info t1) X (gs_bnds gs) sis sbl) kn infos.
Lemma carryGF9C_eq8 : forall bc log scs kn, carryGF9C bc log scs kn = carryGF8C bc log scs kn.
Proof.
  intros bc log scs kn. unfold carryGF9C, carryGF8C. rewrite mk_stxsC3_eq.
  destruct (mk_stxsC2 log scs nt_empty) as [sxs t0]. destruct (scanF2 bc kn t0 gst_empty None None) as [[infos t1] gs]. cbv zeta.
  match goal with |- context [mk_sbl ?s ?s []] => destruct (mk_sbl_ok s s [] (fun e (H : In e []) => match H with end)) as (HSB1 & HSB2 & _);
    rewrite (stores_partX_eq bc s s (mk_sbl s s []) HSB1 HSB2) end.
  reflexivity.
Qed.

Definition carryKF (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryGF9C bc log (map (mk_sctx bc (mk_bext bc)) log) kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Definition carryKF_ctx (bc : bctx) (log : list sentry) (scs : list sprep) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryGF9C bc log scs kn, [], [])
  | _, _ => carryB bc log kn hints
  end.

Lemma carryKF_eq : carryKF = carryK.
Proof.
  fe. rename x into bc, x0 into log, x1 into kn, x2 into hints. unfold carryKF, carryK.
  destruct log as [|s older]; [reflexivity|]. destruct hints; [|reflexivity]. rewrite carryGF9C_eq8, carryGF8_eq. reflexivity.
Qed.
Lemma carryKF_ctx_eq : forall bc log kn hints, carryKF_ctx bc log (map (mk_sctx bc (mk_bext bc)) log) kn hints = carryKF bc log kn hints.
Proof. intros bc log kn hints. unfold carryKF_ctx, carryKF. destruct log; [reflexivity|]. destruct hints; reflexivity. Qed.

Definition omax (a b : option Z) : option Z :=
  match a, b with Some x, Some y => Some (Z.max x y) | Some x, None => Some x | None, o => o end.
Definition oshift (o : option Z) (d : Z) : option Z := match o with Some l => Some (l + d) | None => None end.
Definition ok_lo (o : option Z) (c : Z) : bool := match o with Some l => Z.leb 0 (l + c) | None => false end.

Definition lin_lo (bc : bctx) (ts : list (Z * expr)) : option Z :=
  let la := match lin_range (erangeB bc) 0 ts with Some (lo, _) => Some lo | None => None end in
  let lb := match bc_fs bc with
            | [] => None
            | fs => match sum_subst fs ts 0 0 false with
                    | (ts', (lo0, hi0), true) =>
                        match lin_range (erangeB bc) 0 ts' with Some (lo, _) => Some (lo + lo0) | None => None end
                    | _ => None
                    end
            end in
  omax la lb.
Lemma ok_lo_omax : forall a b c, ok_lo (omax a b) c = (ok_lo a c || ok_lo b c)%bool.
Proof.
  intros [x|] [y|] c; cbn [omax ok_lo]; rewrite ?Bool.orb_false_r; try reflexivity.
  destruct (Z.leb_spec 0 (x + c)), (Z.leb_spec 0 (y + c)), (Z.leb_spec 0 (Z.max x y + c)); cbn [orb]; try reflexivity; lia.
Qed.
Lemma ok_lo_oshift : forall o d c, ok_lo (oshift o d) c = ok_lo o (c + d).
Proof. intros [l|] d c; cbn [oshift ok_lo]; [|reflexivity]. f_equal. ring. Qed.
Lemma lin_testB_lo : forall bc c ts, lin_testB bc c ts (fun lo _ => Z.leb 0 lo) = ok_lo (lin_lo bc ts) c.
Proof.
  intros bc c ts. unfold lin_testB, lin_test_relB, lin_lo. rewrite ok_lo_omax.
  rewrite (lin_range_shift _ c ts).
  destruct (bc_fs bc) as [|f fs].
  - destruct (lin_range (erangeB bc) 0 ts) as [[lo hi]|]; cbn [ok_lo]; rewrite ?Bool.orb_false_r; [|reflexivity].
    destruct (Z.leb 0 (lo + c)); reflexivity.
  - destruct (sum_subst (f :: fs) ts 0 0 false) as [[ts' [lo0 hi0]] [|]].
    + rewrite (lin_range_shift _ c ts').
      destruct (lin_range (erangeB bc) 0 ts) as [[lo hi]|]; destruct (lin_range (erangeB bc) 0 ts') as [[lo' hi']|]; cbn [ok_lo orb];
        rewrite ?Bool.orb_false_r; try reflexivity.
      * replace (lo' + c + lo0) with (lo' + lo0 + c) by ring. destruct (Z.leb 0 (lo + c)); reflexivity.
      * destruct (Z.leb 0 (lo + c)); reflexivity.
      * f_equal. ring.
    + destruct (lin_range (erangeB bc) 0 ts) as [[lo hi]|]; cbn [ok_lo]; rewrite ?Bool.orb_false_r; [|reflexivity].
      destruct (Z.leb 0 (lo + c)); reflexivity.
Qed.

Record gp := GP { gp_u : option Z; gp_s : option (Z * Z) }.
Definition mk_gp (bc : bctx) (ts : list (Z * expr)) : gp :=
  let l1 := lin_lo bc ts in
  let '(c2, t2) := srl_expandB bc ts in
  let l2 := oshift (lin_lo bc t2) c2 in
  let l3 := if has_srl t2 then let '(c3, t3) := srl_expandB bc t2 in oshift (lin_lo bc t3) (c2 + c3) else None in
  let j := srl_scale_need ts in
  GP (omax l1 (omax l2 l3))
     (if (if Z.ltb 0 j then Z.leb j 24 else false) then
        let sc := 2 ^ j in
        let ts' := List.map (fun t => (sc * fst t, snd t)) ts in
        let '(c2', t2') := srl_expandB bc ts' in
        let '(c3', t3') := (if has_srl t2' then srl_expandB bc t2' else (0, t2')) in
        match lin_lo bc t3' with Some l => Some (sc, l + c2' + c3') | None => None end
      else None).
Definition ge0P (g : gp) (C : Z) : bool :=
  if ok_lo (gp_u g) C then true else match gp_s g with Some (sc, l) => Z.leb 0 (l + sc * C) | None => false end.
Lemma lin_ge0_scaledB_gp : forall bc C ts, lin_ge0_scaledB bc C ts = match gp_s (mk_gp bc ts) with Some (sc, l) => Z.leb 0 (l + sc * C) | None => false end.
Proof.
  intros bc C ts. unfold lin_ge0_scaledB, mk_gp.
  destruct (srl_expandB bc ts) as [c2 t2]. cbn [gp_s].
  destruct (if Z.ltb 0 (srl_scale_need ts) then Z.leb (srl_scale_need ts) 24 else false); [|reflexivity].
  cbv zeta.
  destruct (srl_expandB bc (List.map (fun t => (2 ^ srl_scale_need ts * fst t, snd t)) ts)) as [c2' t2'].
  destruct (if has_srl t2' then srl_expandB bc t2' else (0, t2')) as [c3' t3'].
  rewrite lin_testB_lo. destruct (lin_lo bc t3') as [l|]; cbn [ok_lo]; [|reflexivity]. f_equal. ring.
Qed.
Lemma lin_ge0B_gp : forall bc pos neg, lin_ge0B bc pos neg =
  (xt_nowrapB bc pos && xt_nowrapB bc neg && ge0P (mk_gp bc (lsub_e (xt_lin pos) (xt_lin neg))) (xt_const pos - xt_const neg))%bool.
Proof.
  intros bc pos neg. unfold lin_ge0B. f_equal.
  set (ts := lsub_e (xt_lin pos) (xt_lin neg)). set (C := xt_const pos - xt_const neg).
  unfold ge0P. rewrite <- lin_ge0_scaledB_gp. unfold mk_gp.
  destruct (srl_expandB bc ts) as [c2 t2] eqn:E2. cbn [gp_u].
  rewrite !ok_lo_omax, !lin_testB_lo.
  destruct (ok_lo (lin_lo bc ts) C); [reflexivity|]. cbn [orb].
  rewrite ok_lo_oshift. destruct (ok_lo (lin_lo bc t2) (C + c2)); [reflexivity|]. cbn [orb].
  destruct (has_srl t2).
  - destruct (srl_expandB bc t2) as [c3 t3]. rewrite lin_testB_lo, ok_lo_oshift.
    replace (C + (c2 + c3)) with (C + c2 + c3) by ring. destruct (ok_lo (lin_lo bc t3) (C + c2 + c3)); reflexivity.
  - reflexivity.
Qed.

Inductive xin :=
| XNo
| XLin (gA : gp) (a1 a2 : Z) (gB : gp) (b2 : Z)
| XNum (a lo1 hi1 b : Z).
Record binf := BINF { bi_l1 : Z; bi_nw : bool; bi_x1 : list (Z * expr); bi_rng : option (Z * Z) }.
Definition mk_binf (bc : bctx) (b1 : expr) : binf :=
  BINF (fst (lin_of b1)) (lin_nowrapRB bc b1) (xt_lin [(b1, 0)]) (base_rangeB bc b1).
Definition gp_dead (g : gp) : bool := match g with GP None None => true | _ => false end.
Definition mk_xin (bc : bctx) (b1 : expr) (bi : binf) (cb : expr) (co : Z) (m : expr) : xin :=
  if shares_var b1 cb then
    if bi_nw bi then
      if lin_nowrapRB bc cb then
        let gA := mk_gp bc (lsub_e (bi_x1 bi) (xt_lin [(cb, co)])) in
        if gp_dead gA then XNo else
        if lin_nowrapRB bc m then
          XLin gA (bi_l1 bi) (fst (lin_of cb) + co + 0) (mk_gp bc (lsub_e (xt_lin [(cb, co); (m, 0)]) (bi_x1 bi)))
               (fst (lin_of cb) + co + (fst (lin_of m) + 0 + 0))
        else XNo
      else XNo
    else XNo
  else if novars cb then
    match xloB bc cb, xhiB bc cb with
    | Some lo2, Some hi2 =>
        if Z.eqb lo2 hi2 then
          match bi_rng bi, xloB bc m with
          | Some (lo1, hi1), Some l2 => XNum (lo2 + co) lo1 hi1 (lo2 + co + l2)
          | _, _ => XNo
          end
        else XNo
    | _, _ => XNo
    end
  else XNo.

Definition xeval (x : xin) (k sn zn : Z) (nwn : bool) : bool :=
  match x with
  | XNo => false
  | XLin gA a1 a2 gB b2 =>
      if ge0P gA (a1 + k + 0 - a2) then (if nwn then ge0P gB (b2 - (a1 + k + (sn + 0 + 0))) else false) else false
  | XNum a lo1 hi1 b => if Z.leb a (lo1 + k) then Z.leb (hi1 + k + zn) b else false
  end.
Lemma gp_dead_false : forall g C, gp_dead g = true -> ge0P g C = false.
Proof. intros [[u|] [s|]] C H; try discriminate. reflexivity. Qed.
Lemma xeval_eq : forall bc b1 cb co m k n,
  xeval (mk_xin bc b1 (mk_binf bc b1) cb co m) k (snorm n) (zlit64 n) (lin_nowrapRB bc (ELit n)) = xinsideB bc b1 k (ELit n) cb co m.
Proof.
  intros bc b1 cb co m k n. unfold mk_xin, xinsideB. cbn [bi_l1 bi_nw bi_x1 bi_rng mk_binf].
  destruct (shares_var b1 cb).
  - unfold xinside0B. rewrite !lin_ge0B_gp. cbn [xt_nowrapB xt_const].
    change (xt_lin [(b1, k)]) with (xt_lin [(b1, 0)]).
    change (xt_lin [(b1, k); (ELit n, 0)]) with (xt_lin [(b1, 0)]).
    change (fst (lin_of (ELit n))) with (snorm n).
    destruct (lin_nowrapRB bc b1); [|reflexivity]. destruct (lin_nowrapRB bc cb); [|reflexivity]. cbn [andb].
    destruct (gp_dead (mk_gp bc (lsub_e (xt_lin [(b1, 0)]) (xt_lin [(cb, co)])))) eqn:ED.
    { rewrite (gp_dead_false _ _ ED). reflexivity. }
    destruct (lin_nowrapRB bc m); cbn [xeval andb].
    + destruct (ge0P _ (fst (lin_of b1) + k + 0 - (fst (lin_of cb) + co + 0))); [|reflexivity].
      destruct (lin_nowrapRB bc (ELit n)); reflexivity.
    + destruct (ge0P _ (fst (lin_of b1) + k + 0 - (fst (lin_of cb) + co + 0))); reflexivity.
  - destruct (novars cb); [|reflexivity]. unfold xinside_numB.
    destruct (xloB bc cb) as [lo2|]; [|reflexivity]. destruct (xhiB bc cb) as [hi2|]; [|reflexivity].
    destruct (Z.eqb lo2 hi2); [|reflexivity].
    destruct (base_rangeB bc b1) as [[lo1 hi1]|]; [|reflexivity]. cbn [xhiB].
    destruct (xloB bc m) as [l2|]; [|reflexivity]. cbn [xeval].
    destruct (Z.leb (lo2 + co) (lo1 + k)); reflexivity.
Qed.

Record sidet := SDT { sd_off : Z; sd_xlo : option Z; sd_x : xin }.
Definition mk_sidet (bc : bctx) (b1 : expr) (bi : binf) (c : saddr) (m : expr) : sidet :=
  SDT (a_off c) (if expr_eqbF b1 (a_base c) then xloB bc m else None) (mk_xin bc b1 bi (a_base c) (a_off c) m).
Definition num_subW (s : sidet) (k n : Z) : bool :=
  match sd_xlo s with
  | Some ml => if Z.leb (sd_off s) k then Z.leb (k + n) (sd_off s + ml) else false
  | None => false
  end.
Definition sd_dead (s : sidet) : bool := match sd_xlo s, sd_x s with None, XNo => true | _, _ => false end.
Inductive wrow := WR (c1 : saddr) (m1 : expr) (s1 : sidet) (c2 : saddr) (m2 : expr) (s2 : sidet).
Fixpoint mk_rows (bc : bctx) (b1 : expr) (bi : binf) (kd : list kentry) : list wrow :=
  match kd with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let s1 := mk_sidet bc b1 bi c1 m1 in
      let s2 := mk_sidet bc b1 bi c2 m2 in
      if (if sd_dead s1 then sd_dead s2 else false) then mk_rows bc b1 bi rest
      else WR c1 m1 s1 c2 m2 s2 :: mk_rows bc b1 bi rest
  | _ :: rest => mk_rows bc b1 bi rest
  end.
Fixpoint disj_bothW (rows : list wrow) (k n sn zn : Z) (nwn : bool) : list (saddr * expr) * list (saddr * expr) :=
  match rows with
  | [] => ([], [])
  | WR c1 m1 s1 c2 m2 s2 :: rest =>
      let '(r, rx) := disj_bothW rest k n sn zn nwn in
      let x2 := xeval (sd_x s2) k sn zn nwn in
      let x1 := xeval (sd_x s1) k sn zn nwn in
      let r1 := if (if num_subW s2 k n then true else x2) then (c1, m1) :: r else r in
      let rx1 := if x2 then (c1, m1) :: rx else rx in
      ((if (if num_subW s1 k n then true else x1) then (c2, m2) :: r1 else r1),
       (if x1 then (c2, m2) :: rx1 else rx1))
  end.
Lemma num_subW_eq : forall bc b1 c m k n, num_subW (mk_sidet bc b1 (mk_binf bc b1) c m) k n = num_sub bc b1 k n c m.
Proof.
  intros bc b1 c m k n. unfold num_subW, num_sub, mk_sidet. cbn [sd_off sd_xlo].
  eF.
  destruct (expr_eqb b1 (a_base c)); [|reflexivity].
  destruct (xloB bc m) as [ml|]; [|destruct (Z.leb (a_off c) k); reflexivity].
  destruct (Z.leb (a_off c) k); reflexivity.
Qed.
Lemma sd_dead_false : forall bc b1 c m k n, sd_dead (mk_sidet bc b1 (mk_binf bc b1) c m) = true ->
  num_sub bc b1 k n c m = false /\ xinsideB bc b1 k (ELit n) (a_base c) (a_off c) m = false.
Proof.
  intros bc b1 c m k n H. rewrite <- num_subW_eq, <- xeval_eq. unfold sd_dead, num_subW in *.
  cbn [sd_xlo sd_x mk_sidet] in *. eF.
  destruct (if expr_eqb b1 (a_base c) then xloB bc m else None); [discriminate|].
  destruct (mk_xin bc b1 (mk_binf bc b1) (a_base c) (a_off c) m); try discriminate. split; reflexivity.
Qed.
Lemma disj_bothW_eq : forall bc b1 kd k n,
  disj_bothW (mk_rows bc b1 (mk_binf bc b1) kd) k n (snorm n) (zlit64 n) (lin_nowrapRB bc (ELit n)) = disj_both bc kd b1 k n.
Proof.
  intros bc b1 kd k n. induction kd as [|K rest IH]; [reflexivity|].
  destruct K as [a w' v|a len|a len bk|lo hi|e' m'|e' lo' hi'|a en|c1 m1 c2 m2|a len fc|a len]; cbn [mk_rows disj_both]; try exact IH.
  destruct (if sd_dead (mk_sidet bc b1 (mk_binf bc b1) c1 m1) then sd_dead (mk_sidet bc b1 (mk_binf bc b1) c2 m2) else false) eqn:ED.
  - destruct (sd_dead (mk_sidet bc b1 (mk_binf bc b1) c1 m1)) eqn:E1; [|discriminate].
    destruct (sd_dead_false bc b1 c1 m1 k n E1) as [N1 X1]. destruct (sd_dead_false bc b1 c2 m2 k n ED) as [N2 X2].
    rewrite IH, N1, N2, X1, X2. destruct (disj_both bc rest b1 k n) as [r rx]. reflexivity.
  - cbn [disj_bothW]. rewrite IH. destruct (disj_both bc rest b1 k n) as [r rx].
    rewrite !num_subW_eq. cbn [sd_x mk_sidet]. rewrite !xeval_eq. reflexivity.
Qed.

Record wtab := WT { wt_rng : option (Z * Z); wt_rows : list wrow }.
Definition mk_wtab (bc : bctx) (kd : list kentry) (b1 : expr) : wtab :=
  let bi := mk_binf bc b1 in WT (bi_rng bi) (mk_rows bc b1 bi kd).
Definition mk_sctxW (bc : bctx) (kd : list kentry) (t : wtab) (a : saddr) (w : nat) : sprep :=
  let n := Z.of_nat w in
  if (if Z.leb 0 n then Z.ltb n two63z else false) then
    let '(D, Dx) := disj_bothW (wt_rows t) (a_off a) n n n true in SPrep (wt_rng t) (Some n) D Dx
  else mk_sprepF bc kd (a_base a) (a_off a) (elen w).
Lemma mk_sctxW_eq : forall bc kd a w, mk_sctxW bc kd (mk_wtab bc kd (a_base a)) a w = mk_sprepF bc kd (a_base a) (a_off a) (elen w).
Proof.
  intros bc kd a w. unfold mk_sctxW. cbv zeta.
  destruct (if Z.leb 0 (Z.of_nat w) then Z.ltb (Z.of_nat w) two63z else false) eqn:EN; [|reflexivity].
  assert (Hn : 0 <= Z.of_nat w < two63z).
  { destruct (Z.leb_spec 0 (Z.of_nat w)); [|discriminate]. destruct (Z.ltb_spec (Z.of_nat w) two63z); [lia|discriminate]. }
  assert (Hz : zlit64 (Z.of_nat w) = Z.of_nat w).
  { unfold zlit64. rewrite two63z_val in Hn. destruct (Z.leb_spec 0 (Z.of_nat w)), (Z.ltb_spec (Z.of_nat w) two64); cbn [andb]; try reflexivity; rewrite two64_val in *; lia. }
  assert (Hs : snorm (Z.of_nat w) = Z.of_nat w) by (apply snorm_small; rewrite mtwo63z_val; rewrite two63z_val in *; lia).
  pose proof (disj_bothW_eq bc (a_base a) kd (a_off a) (Z.of_nat w)) as HD.
  rewrite Hs, Hz, (lin_nowrapRB_lit bc _ Hn) in HD.
  unfold mk_wtab. cbn [wt_rows wt_rng]. rewrite HD.
  unfold mk_sprepF, elen. rewrite Hz, Z.eqb_refl. cbn [bi_rng mk_binf xhiB]. rewrite Hz. reflexivity.
Qed.

Definition wtabs : Type := list (expr * wtab).
Definition wt_empty : wtabs := [].
Fixpoint wc_find (c : wtabs) (b : expr) : option wtab :=
  match c with [] => None | (b', t) :: r => if expr_eqbF b b' then Some t else wc_find r b end.
Definition mk_sctx_c1 (bc : bctx) (ex : bext) (c : wtabs) (s : sentry) : sprep * wtabs :=
  match s with
  | SE a w v =>
      match wc_find c (a_base a) with
      | Some t => (mk_sctxW bc (be_kd ex) t a w, c)
      | None => let t := mk_wtab bc (be_kd ex) (a_base a) in (mk_sctxW bc (be_kd ex) t a w, (a_base a, t) :: c)
      end
  end.
Definition WTOK (bc : bctx) (ex : bext) (c : wtabs) : Prop := forall b t, In (b, t) c -> t = mk_wtab bc (be_kd ex) b.
Lemma WTOK_empty : forall bc ex, WTOK bc ex wt_empty.
Proof. intros bc ex b t []. Qed.
Lemma wc_find_ok : forall bc ex c b t, WTOK bc ex c -> wc_find c b = Some t -> t = mk_wtab bc (be_kd ex) b.
Proof.
  intros bc ex c b t. induction c as [|[b' t'] r IH]; intros H HF; [discriminate|]. cbn [wc_find] in HF. eF.
  destruct (expr_eqb b b') eqn:E.
  - injection HF as <-. apply p_expr_eqb_eq in E. subst b'. apply H. left. reflexivity.
  - apply IH; [intros b0 t0 Hin; apply H; right; exact Hin|exact HF].
Qed.
Lemma mk_sctx_c1_fst : forall bc ex c s, WTOK bc ex c -> fst (mk_sctx_c1 bc ex c s) = mk_sctx bc ex s.
Proof.
  intros bc ex c [a w v] H. unfold mk_sctx_c1, mk_sctx.
  destruct (wc_find c (a_base a)) as [t|] eqn:EF; cbn [fst].
  - rewrite (wc_find_ok bc ex c _ t H EF). apply mk_sctxW_eq.
  - apply mk_sctxW_eq.
Qed.
Lemma mk_sctx_c1_ok : forall bc ex c s, WTOK bc ex c -> WTOK bc ex (snd (mk_sctx_c1 bc ex c s)).
Proof.
  intros bc ex c [a w v] H. unfold mk_sctx_c1.
  destruct (wc_find c (a_base a)) as [t|] eqn:EF; cbn [snd]; [exact H|].
  intros b t [E|Hin]; [injection E as <- <-; reflexivity|exact (H b t Hin)].
Qed.

Definition rmemo : Type := list (expr * option (Z * Z)).
Fixpoint rm_find (M : rmemo) (a : expr) : option (option (Z * Z)) :=
  match M with [] => None | (a', r) :: rest => if expr_eqbF a a' then Some r else rm_find rest a end.
Definition rm_get (bc : bctx) (M : rmemo) (a : expr) : option (Z * Z) * rmemo :=
  match rm_find M a with Some r => (r, M) | None => let r := erangeB bc a in (r, (a, r) :: M) end.
Definition MOK (bc : bctx) (M : rmemo) : Prop := forall a r, In (a, r) M -> r = erangeB bc a.
Lemma rm_find_ok : forall bc M a r, MOK bc M -> rm_find M a = Some r -> r = erangeB bc a.
Proof.
  intros bc M a r. induction M as [|[a' r'] rest IH]; intros H HF; [discriminate|]. cbn [rm_find] in HF. eF.
  destruct (expr_eqb a a') eqn:E.
  - injection HF as <-. apply p_expr_eqb_eq in E. subst a'. apply H. left. reflexivity.
  - apply IH; [intros a0 r0 H0; apply H; right; exact H0|exact HF].
Qed.
Lemma rm_get_ok : forall bc M a, MOK bc M -> fst (rm_get bc M a) = erangeB bc a /\ MOK bc (snd (rm_get bc M a)).
Proof.
  intros bc M a H. unfold rm_get. destruct (rm_find M a) as [r|] eqn:E; cbn [fst snd].
  - split; [exact (rm_find_ok bc M a r H E)|exact H].
  - split; [reflexivity|]. intros a0 r0 [E0|H0]; [injection E0 as <- <-; reflexivity|exact (H a0 r0 H0)].
Qed.
Fixpoint lin_rangeM (bc : bctx) (M : rmemo) (c : Z) (ts : list (Z * expr)) : option (Z * Z) * rmemo :=
  match ts with
  | [] => (Some (c, c), M)
  | (k, a) :: rest =>
      let '(ra, M1) := rm_get bc M a in
      match ra with
      | Some (al, ah) =>
          let '(rr, M2) := lin_rangeM bc M1 c rest in
          (match rr with
           | Some (lo, hi) => if Z.leb 0 k then Some (lo + k * al, hi + k * ah) else Some (lo + k * ah, hi + k * al)
           | None => None
           end, M2)
      | None => (None, M1)
      end
  end.
Lemma lin_rangeM_ok : forall bc c ts M, MOK bc M ->
  fst (lin_rangeM bc M c ts) = lin_range (erangeB bc) c ts /\ MOK bc (snd (lin_rangeM bc M c ts)).
Proof.
  intros bc c ts. induction ts as [|[k a] rest IH]; intros M H; [split; [reflexivity|exact H]|].
  cbn [lin_rangeM lin_range]. destruct (rm_get_ok bc M a H) as [E1 H1]. destruct (rm_get bc M a) as [ra M1]. cbn [fst snd] in E1, H1.
  rewrite <- E1. destruct ra as [[al ah]|]; [|split; [reflexivity|exact H1]].
  destruct (IH M1 H1) as [E2 H2]. destruct (lin_rangeM bc M1 c rest) as [rr M2]. cbn [fst snd] in *. rewrite <- E2.
  split; [|exact H2]. destruct rr as [[lo hi]|]; reflexivity.
Qed.
Definition lin_loM (bc : bctx) (M : rmemo) (ts : list (Z * expr)) : option Z * rmemo :=
  let '(ra, M1) := lin_rangeM bc M 0 ts in
  let la := match ra with Some (lo, _) => Some lo | None => None end in
  match bc_fs bc with
  | [] => (omax la None, M1)
  | fs => match sum_subst fs ts 0 0 false with
          | (ts', (lo0, hi0), true) =>
              let '(rb, M2) := lin_rangeM bc M1 0 ts' in
              (omax la (match rb with Some (lo, _) => Some (lo + lo0) | None => None end), M2)
          | _ => (omax la None, M1)
          end
  end.
Lemma lin_loM_ok : forall bc ts M, MOK bc M -> fst (lin_loM bc M ts) = lin_lo bc ts /\ MOK bc (snd (lin_loM bc M ts)).
Proof.
  intros bc ts M H. unfold lin_loM, lin_lo.
  destruct (lin_rangeM_ok bc 0 ts M H) as [E1 H1]. destruct (lin_rangeM bc M 0 ts) as [ra M1]. cbn [fst snd] in E1, H1. rewrite <- E1.
  destruct (bc_fs bc) as [|f fs]; [split; [reflexivity|exact H1]|].
  destruct (sum_subst (f :: fs) ts 0 0 false) as [[ts' [lo0 hi0]] [|]]; [|split; [reflexivity|exact H1]].
  destruct (lin_rangeM_ok bc 0 ts' M1 H1) as [E2 H2]. destruct (lin_rangeM bc M1 0 ts') as [rb M2]. cbn [fst snd] in *. rewrite <- E2.
  split; [reflexivity|exact H2].
Qed.
Definition mk_gpM (bc : bctx) (M : rmemo) (ts : list (Z * expr)) : gp * rmemo :=
  let '(l1, M1) := lin_loM bc M ts in
  let '(c2, t2) := srl_expandB bc ts in
  let '(l2r, M2) := lin_loM bc M1 t2 in
  let l2 := oshift l2r c2 in
  let '(l3, M3) := if has_srl t2 then let '(c3, t3) := srl_expandB bc t2 in let '(l3r, M3) := lin_loM bc M2 t3 in (oshift l3r (c2 + c3), M3)
                   else (None, M2) in
  let j := srl_scale_need ts in
  if (if Z.ltb 0 j then Z.leb j 24 else false) then
    let sc := 2 ^ j in
    let ts' := List.map (fun t => (sc * fst t, snd t)) ts in
    let '(c2', t2') := srl_expandB bc ts' in
    let '(c3', t3') := (if has_srl t2' then srl_expandB bc t2' else (0, t2')) in
    let '(l4, M4) := lin_loM bc M3 t3' in
    (GP (omax l1 (omax l2 l3)) (match l4 with Some l => Some (sc, l + c2' + c3') | None => None end), M4)
  else (GP (omax l1 (omax l2 l3)) None, M3).
Lemma mk_gpM_ok : forall bc ts M, MOK bc M -> fst (mk_gpM bc M ts) = mk_gp bc ts /\ MOK bc (snd (mk_gpM bc M ts)).
Proof.
  intros bc ts M H. unfold mk_gpM, mk_gp.
  destruct (lin_loM_ok bc ts M H) as [E1 H1]. destruct (lin_loM bc M ts) as [l1 M1]. cbn [fst snd] in E1, H1. rewrite <- E1.
  destruct (srl_expandB bc ts) as [c2 t2].
  destruct (lin_loM_ok bc t2 M1 H1) as [E2 H2]. destruct (lin_loM bc M1 t2) as [l2r M2]. cbn [fst snd] in E2, H2. rewrite <- E2.
  assert (S3 : exists l3 M3, (if has_srl t2 then let '(c3, t3) := srl_expandB bc t2 in let '(l3r, M3) := lin_loM bc M2 t3 in (oshift l3r (c2 + c3), M3) else (None, M2)) = (l3, M3)
               /\ l3 = (if has_srl t2 then let '(c3, t3) := srl_expandB bc t2 in oshift (lin_lo bc t3) (c2 + c3) else None) /\ MOK bc M3).
  { destruct (has_srl t2); [|exists None, M2; split; [reflexivity|split; [reflexivity|exact H2]]].
    destruct (srl_expandB bc t2) as [c3 t3]. destruct (lin_loM_ok bc t3 M2 H2) as [E3 H3]. destruct (lin_loM bc M2 t3) as [l3r M3]. cbn [fst snd] in E3, H3.
    exists (oshift l3r (c2 + c3)), M3. split; [reflexivity|]. split; [rewrite E3; reflexivity|exact H3]. }
  destruct S3 as (l3 & M3 & -> & -> & H3). cbv zeta.
  destruct (if Z.ltb 0 (srl_scale_need ts) then Z.leb (srl_scale_need ts) 24 else false); [|split; [reflexivity|exact H3]].
  destruct (srl_expandB bc (List.map (fun t => (2 ^ srl_scale_need ts * fst t, snd t)) ts)) as [c2' t2'].
  destruct (if has_srl t2' then srl_expandB bc t2' else (0, t2')) as [c3' t3'].
  destruct (lin_loM_ok bc t3' M3 H3) as [E4 H4]. destruct (lin_loM bc M3 t3') as [l4 M4]. cbn [fst snd] in *. rewrite <- E4.
  split; [reflexivity|exact H4].
Qed.

Definition nmemo : Type := list (expr * bool).
Fixpoint nm_find (N : nmemo) (e : expr) : option bool :=
  match N with [] => None | (e', r) :: rest => if expr_eqbF e e' then Some r else nm_find rest e end.
Definition nm_get (bc : bctx) (N : nmemo) (e : expr) : bool * nmemo :=
  match nm_find N e with Some r => (r, N) | None => let r := lin_nowrapRB bc e in (r, (e, r) :: N) end.
Definition NOK (bc : bctx) (N : nmemo) : Prop := forall e r, In (e, r) N -> r = lin_nowrapRB bc e.
Lemma nm_get_ok : forall bc N e, NOK bc N -> fst (nm_get bc N e) = lin_nowrapRB bc e /\ NOK bc (snd (nm_get bc N e)).
Proof.
  intros bc N e H. unfold nm_get.
  assert (F : forall r, nm_find N e = Some r -> r = lin_nowrapRB bc e).
  { clear - H. induction N as [|[e' r'] rest IH]; intros r HF; [discriminate|]. cbn [nm_find] in HF. eF.
    destruct (expr_eqb e e') eqn:E.
    - injection HF as <-. apply p_expr_eqb_eq in E. subst e'. apply H. left. reflexivity.
    - apply IH; [intros e0 r0 H0; apply H; right; exact H0|exact HF]. }
  destruct (nm_find N e) as [r|]; cbn [fst snd].
  - split; [exact (F r eq_refl)|exact H].
  - split; [reflexivity|]. intros e0 r0 [E0|H0]; [injection E0 as <- <-; reflexivity|exact (H e0 r0 H0)].
Qed.
Definition bmemo : Type := (rmemo * nmemo)%type.
Definition BOK (bc : bctx) (B : bmemo) : Prop := MOK bc (fst B) /\ NOK bc (snd B).
Definition mk_xinM (bc : bctx) (B : bmemo) (b1 : expr) (bi : binf) (cb : expr) (co : Z) (m : expr) : xin * bmemo :=
  if shares_var b1 cb then
    if bi_nw bi then
      let '(nwc, N1) := nm_get bc (snd B) cb in
      if nwc then
        let '(gA, M1) := mk_gpM bc (fst B) (lsub_e (bi_x1 bi) (xt_lin [(cb, co)])) in
        if gp_dead gA then (XNo, (M1, N1)) else
        let '(nwm, N2) := nm_get bc N1 m in
        if nwm then
          let '(gB, M2) := mk_gpM bc M1 (lsub_e (xt_lin [(cb, co); (m, 0)]) (bi_x1 bi)) in
          (XLin gA (bi_l1 bi) (fst (lin_of cb) + co + 0) gB (fst (lin_of cb) + co + (fst (lin_of m) + 0 + 0)), (M2, N2))
        else (XNo, (M1, N2))
      else (XNo, (fst B, N1))
    else (XNo, B)
  else (mk_xin bc b1 bi cb co m, B).
Lemma mk_xinM_ok : forall bc b1 bi cb co m B, BOK bc B ->
  fst (mk_xinM bc B b1 bi cb co m) = mk_xin bc b1 bi cb co m /\ BOK bc (snd (mk_xinM bc B b1 bi cb co m)).
Proof.
  intros bc b1 bi cb co m [M N] [HM HN]. unfold mk_xinM. cbn [fst snd]. destruct (shares_var b1 cb) eqn:ES; [|split; [reflexivity|split; assumption]].
  unfold mk_xin. rewrite ES.
  destruct (bi_nw bi); [|split; [reflexivity|split; assumption]].
  destruct (nm_get_ok bc N cb HN) as [EN1 HN1]. destruct (nm_get bc N cb) as [nwc N1]. cbn [fst snd] in EN1, HN1. rewrite <- EN1.
  destruct nwc; [|split; [reflexivity|split; assumption]].
  destruct (mk_gpM_ok bc (lsub_e (bi_x1 bi) (xt_lin [(cb, co)])) M HM) as [E1 H1].
  destruct (mk_gpM bc M (lsub_e (bi_x1 bi) (xt_lin [(cb, co)]))) as [gA M1]. cbn [fst snd] in E1, H1. rewrite <- E1.
  destruct (gp_dead gA); [split; [reflexivity|split; assumption]|].
  destruct (nm_get_ok bc N1 m HN1) as [EN2 HN2]. destruct (nm_get bc N1 m) as [nwm N2]. cbn [fst snd] in EN2, HN2. rewrite <- EN2.
  destruct nwm; [|split; [reflexivity|split; assumption]].
  destruct (mk_gpM_ok bc (lsub_e (xt_lin [(cb, co); (m, 0)]) (bi_x1 bi)) M1 H1) as [E2 H2].
  destruct (mk_gpM bc M1 (lsub_e (xt_lin [(cb, co); (m, 0)]) (bi_x1 bi))) as [gB M2]. cbn [fst snd] in *. rewrite <- E2.
  split; [reflexivity|split; assumption].
Qed.
Definition mk_sidetM (bc : bctx) (B : bmemo) (b1 : expr) (bi : binf) (c : saddr) (m : expr) : sidet * bmemo :=
  let '(x, B1) := mk_xinM bc B b1 bi (a_base c) (a_off c) m in
  (SDT (a_off c) (if expr_eqbF b1 (a_base c) then xloB bc m else None) x, B1).
Lemma mk_sidetM_ok : forall bc b1 bi c m B, BOK bc B ->
  fst (mk_sidetM bc B b1 bi c m) = mk_sidet bc b1 bi c m /\ BOK bc (snd (mk_sidetM bc B b1 bi c m)).
Proof.
  intros bc b1 bi c m B H. unfold mk_sidetM, mk_sidet. destruct (mk_xinM_ok bc b1 bi (a_base c) (a_off c) m B H) as [E1 H1].
  destruct (mk_xinM bc B b1 bi (a_base c) (a_off c) m) as [x B1]. cbn [fst snd] in *. rewrite <- E1. split; [reflexivity|exact H1].
Qed.
Fixpoint mk_rowsM (bc : bctx) (B : bmemo) (b1 : expr) (bi : binf) (kd : list kentry) : list wrow * bmemo :=
  match kd with
  | [] => ([], B)
  | KDisj c1 m1 c2 m2 :: rest =>
      let '(s1, B1) := mk_sidetM bc B b1 bi c1 m1 in
      let '(s2, B2) := mk_sidetM bc B1 b1 bi c2 m2 in
      let '(rows, B3) := mk_rowsM bc B2 b1 bi rest in
      ((if (if sd_dead s1 then sd_dead s2 else false) then rows else WR c1 m1 s1 c2 m2 s2 :: rows), B3)
  | _ :: rest => mk_rowsM bc B b1 bi rest
  end.
Lemma mk_rowsM_ok : forall bc b1 bi kd B, BOK bc B ->
  fst (mk_rowsM bc B b1 bi kd) = mk_rows bc b1 bi kd /\ BOK bc (snd (mk_rowsM bc B b1 bi kd)).
Proof.
  intros bc b1 bi kd. induction kd as [|K rest IH]; intros B H; [split; [reflexivity|exact H]|].
  destruct K as [a w' v|a len|a len bk|lo hi|e' m'|e' lo' hi'|a en|c1 m1 c2 m2|a len fc|a len]; cbn [mk_rowsM mk_rows]; try exact (IH B H).
  destruct (mk_sidetM_ok bc b1 bi c1 m1 B H) as [E1 H1]. destruct (mk_sidetM bc B b1 bi c1 m1) as [s1 B1]. cbn [fst snd] in E1, H1.
  destruct (mk_sidetM_ok bc b1 bi c2 m2 B1 H1) as [E2 H2]. destruct (mk_sidetM bc B1 b1 bi c2 m2) as [s2 B2]. cbn [fst snd] in E2, H2.
  destruct (IH B2 H2) as [E3 H3]. destruct (mk_rowsM bc B2 b1 bi rest) as [rows B3]. cbn [fst snd] in *.
  rewrite <- E1, <- E2, <- E3. split; [|exact H3]. destruct (if sd_dead s1 then sd_dead s2 else false); reflexivity.
Qed.
Definition mk_wtabM (bc : bctx) (B : bmemo) (kd : list kentry) (b1 : expr) : wtab * bmemo :=
  let bi := mk_binf bc b1 in
  let '(rows, B1) := mk_rowsM bc B b1 bi kd in (WT (bi_rng bi) rows, B1).
Lemma mk_wtabM_ok : forall bc kd b1 B, BOK bc B -> fst (mk_wtabM bc B kd b1) = mk_wtab bc kd b1 /\ BOK bc (snd (mk_wtabM bc B kd b1)).
Proof.
  intros bc kd b1 B H. unfold mk_wtabM, mk_wtab. destruct (mk_rowsM_ok bc b1 (mk_binf bc b1) kd B H) as [E1 H1].
  destruct (mk_rowsM bc B b1 (mk_binf bc b1) kd) as [rows B1]. cbn [fst snd] in *. rewrite <- E1. split; [reflexivity|exact H1].
Qed.

Definition wcache : Type := (bmemo * list (expr * wtab))%type.
Definition wc_empty : wcache := (([], []), []).
Definition mk_sctx_c (bc : bctx) (ex : bext) (c : wcache) (s : sentry) : sprep * wcache :=
  match s with
  | SE a w v =>
      match wc_find (snd c) (a_base a) with
      | Some t => (mk_sctxW bc (be_kd ex) t a w, c)
      | None => let '(t, B') := mk_wtabM bc (fst c) (be_kd ex) (a_base a) in (mk_sctxW bc (be_kd ex) t a w, (B', (a_base a, t) :: snd c))
      end
  end.
Definition WCOK (bc : bctx) (ex : bext) (c : wcache) : Prop := BOK bc (fst c) /\ WTOK bc ex (snd c).
Lemma WCOK_empty : forall bc ex, WCOK bc ex wc_empty.
Proof. intros bc ex. split; [split; [intros a r []|intros e r []]|apply WTOK_empty]. Qed.
Lemma mk_sctx_c_fst : forall bc ex c s, WCOK bc ex c -> fst (mk_sctx_c bc ex c s) = mk_sctx bc ex s.
Proof.
  intros bc ex [B c] [a w v] [HB HC]. unfold mk_sctx_c, mk_sctx. cbn [fst snd].
  destruct (wc_find c (a_base a)) as [t|] eqn:EF; cbn [fst].
  - rewrite (wc_find_ok bc ex c _ t HC EF). apply mk_sctxW_eq.
  - destruct (mk_wtabM_ok bc (be_kd ex) (a_base a) B HB) as [E1 _]. destruct (mk_wtabM bc B (be_kd ex) (a_base a)) as [t B']. cbn [fst] in *.
    rewrite E1. apply mk_sctxW_eq.
Qed.
Lemma mk_sctx_c_ok : forall bc ex c s, WCOK bc ex c -> WCOK bc ex (snd (mk_sctx_c bc ex c s)).
Proof.
  intros bc ex [B c] [a w v] [HB HC]. unfold mk_sctx_c. cbn [fst snd].
  destruct (wc_find c (a_base a)) as [t|] eqn:EF; cbn [snd]; [split; assumption|].
  destruct (mk_wtabM_ok bc (be_kd ex) (a_base a) B HB) as [E1 H1]. destruct (mk_wtabM bc B (be_kd ex) (a_base a)) as [t B']. cbn [fst snd] in *.
  split; [exact H1|]. intros b t0 [E|Hin]; [injection E as <- <-; exact E1|exact (HC b t0 Hin)].
Qed.

End CARF.
