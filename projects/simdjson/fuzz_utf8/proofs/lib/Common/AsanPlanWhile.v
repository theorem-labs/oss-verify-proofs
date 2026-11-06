(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AxSymExec3 AxSymExec3B.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Module APW.
Import AX2. Import AX2B. Import APC.

Section WithSegs.
Variable A : atable.
Variable nx0 : nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sbind : Type := list (nat * expr).

Fixpoint sg_get (sg : sbind) (n : nat) : option expr :=
  match sg with
  | [] => None
  | (v, e) :: rest => if Nat.eqb v n then Some e else sg_get rest n
  end.

(* [comment removed for export] *)
Definition sg_dom_in (lo hi : nat) (sg : sbind) : bool :=
  forallb (fun p => Nat.leb lo (fst p) && Nat.ltb (fst p) hi)%bool sg.
Definition sg_dom_ge (lo : nat) (sg : sbind) : bool :=
  forallb (fun p => Nat.leb lo (fst p)) sg.

(* [comment removed for export] *)
Fixpoint esubsts (sg : sbind) (x : expr) : expr :=
  match x with
  | ELit _ => x
  | EVar n => match sg_get sg n with Some e => e | None => x end
  | EAlu op a b => mkAlu op (esubsts sg a) (esubsts sg b)
  | EAluw op a b => mkAluw op (esubsts sg a) (esubsts sg b)
  | EMd op a b => mkMd op (esubsts sg a) (esubsts sg b)
  | EMdw op a b => mkMdw op (esubsts sg a) (esubsts sg b)
  | EExt sx lo n a => EExt sx lo n (esubsts sg a)
  | EBlob _ _ _ _ => x
  end.
Definition asubsts (sg : sbind) (a : saddr) : saddr := SA (esubsts sg (a_base a)) (a_off a).
Definition ksubsts (sg : sbind) (K : kentry) : kentry :=
  match K with
  | KWord a w v => KWord (asubsts sg a) w (esubsts sg v)
  | KZero a n => KZero (asubsts sg a) (esubsts sg n)
  | KBlob a n k => KBlob (asubsts sg a) (esubsts sg n) k
  | KImg lo hi => K
  | KAlign x m => KAlign (esubsts sg x) m
  | KRange x lo hi => KRange (esubsts sg x) lo hi
  | KWr a n => KWr (asubsts sg a) (esubsts sg n)
  | KDisj a1 n1 a2 n2 => KDisj (asubsts sg a1) (esubsts sg n1) (asubsts sg a2) (esubsts sg n2)
  | KFill a n c => KFill (asubsts sg a) (esubsts sg n) c
  | KUnk a n => KUnk (asubsts sg a) (esubsts sg n)
  end.
Definition psubsts (sg : sbind) (p : expr * expr) : expr * expr := (esubsts sg (fst p), esubsts sg (snd p)).
Definition msubsts (sg : sbind) (m : amap) : amap := AM (esubsts sg (am_base m)) (esubsts sg (am_len m)) (am_kind m).
Definition fsubsts (sg : sbind) (f : afd) : afd :=
  match f with FdFile k l o => FdFile k (esubsts sg l) (esubsts sg o) | _ => f end.
(* [comment removed for export] *)
Definition insts (sg : sbind) (inv : acs) : acs :=
  ACS (mk_ss (pc inv) (map (esubsts sg) (s_regs (a_ss inv))) (map (ksubsts sg) (kn inv)) (nxt inv))
      (map (msubsts sg) (a_maps inv)) (a_totsz inv) (a_ylo inv) (a_eager inv)
      (map (psubsts sg) (a_vis inv)) (map (psubsts sg) (a_ghost inv)) (a_abytes inv)
      (esubsts sg (a_brk inv)) (fsubsts sg (a_fd inv)) (a_tidset inv).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition slotb (lo hi : nat) (v : nat) : bool := (Nat.leb lo v && Nat.ltb v hi)%bool.

(* [comment removed for export] *)
Fixpoint evar_in (v : nat) (e : expr) : bool :=
  match e with
  | ELit _ => false
  | EVar n => Nat.eqb n v
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evar_in v a || evar_in v b
  | EExt _ _ _ a => evar_in v a
  | EBlob _ _ _ _ => false
  end%bool.

(* [comment removed for export] *)
Fixpoint free_slots (lo hi : nat) (sg : sbind) (e : expr) (acc : list nat) : list nat :=
  match e with
  | ELit _ => acc
  | EVar n => if slotb lo hi n then match sg_get sg n with Some _ => acc | None => n :: acc end else acc
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => free_slots lo hi sg a (free_slots lo hi sg b acc)
  | EExt _ _ _ a => free_slots lo hi sg a acc
  | EBlob _ _ _ _ => acc
  end.

(* [comment removed for export] *)
Fixpoint match_bare (lo hi : nat) (rs ts : list expr) (sg : sbind) : sbind :=
  match rs, ts with
  | r :: rs', EVar v :: ts' =>
      if slotb lo hi v then
        match sg_get sg v with
        | Some _ => match_bare lo hi rs' ts' sg
        | None => match_bare lo hi rs' ts' (sg ++ [(v, r)])
        end
      else match_bare lo hi rs' ts' sg
  | _ :: rs', _ :: ts' => match_bare lo hi rs' ts' sg
  | _, _ => sg
  end.

(* [comment removed for export] *)
Fixpoint coeff_of (v : nat) (ts : list (Z * expr)) : Z :=
  match ts with
  | [] => 0
  | (k, EVar n) :: rest => if Nat.eqb n v then k else coeff_of v rest
  | _ :: rest => coeff_of v rest
  end.

(* [comment removed for export] *)
Definition ldivk (k : Z) (l : lin) : option lin :=
  if Z.eqb k 0 then None else
  if (Z.eqb (fst l mod k) 0 && forallb (fun t => Z.eqb (fst t mod k) 0) (snd l))%bool
  then Some (fst l / k, map (fun t => (fst t / k, snd t)) (snd l)) else None.
Definition solve1 (lo hi : nat) (sg : sbind) (r t1 : expr) : sbind :=
  let t := esubsts sg t1 in            (* [comment removed for export] *)
  match free_slots lo hi sg t [] with
  | v :: rest =>
      if forallb (Nat.eqb v) rest then
        let t0 := esubst v (ELit 0) t in
        if evar_in v t0 then sg else
        let k := coeff_of v (snd (lin_of t)) in
        match ldivk k (lin_of (mkAlu ALU_SUB r t0)) with
        | Some l => sg ++ [(v, unlin l)]
        | None => sg
        end
      else sg
  | [] => sg
  end.
Fixpoint match_lin (lo hi : nat) (rs ts : list expr) (sg : sbind) : sbind :=
  match rs, ts with
  | r :: rs', t :: ts' => match_lin lo hi rs' ts' (match t with EVar _ => sg | ELit _ => sg | _ => solve1 lo hi sg r t end)
  | _, _ => sg
  end.

(* [comment removed for export] *)
Fixpoint find_kword (k : list kentry) (a : saddr) (w : nat) : option expr :=
  match k with
  | [] => None
  | KWord a' w' e :: rest => if (saddr_eqb_h a' a && Nat.eqb w' w)%bool then Some e else find_kword rest a w
  | _ :: rest => find_kword rest a w
  end.
Fixpoint match_kwords (lo hi : nat) (k : list kentry) (tk : list kentry) (sg : sbind) : sbind :=
  match tk with
  | [] => sg
  | KWord a w (EVar v) :: rest =>
      let sg' :=
        if slotb lo hi v then
          match sg_get sg v with
          | Some _ => sg
          | None =>
              match free_slots lo hi sg (a_base a) [] with
              | [] => match find_kword k (asubsts sg a) w with Some e => sg ++ [(v, e)] | None => sg end
              | _ => sg
              end
          end
        else sg in
      match_kwords lo hi k rest sg'
  (* [comment removed for export] *)
  | KWord a w t :: rest =>
      let sg' := match free_slots lo hi sg (a_base a) [] with
                 | [] => match find_kword k (asubsts sg a) w with Some e => solve1 lo hi sg e t | None => sg end
                 | _ => sg
                 end in
      match_kwords lo hi k rest sg'
  | _ :: rest => match_kwords lo hi k rest sg
  end.

(* [comment removed for export] *)
Definition infer_sg (lo hi : nat) (hints : sbind) (cs inv : acs) : sbind :=
  let rs := s_regs (a_ss cs) in
  let ts := s_regs (a_ss inv) in
  let sg1 := match_bare lo hi rs ts hints in
  let sg2 := match_lin lo hi rs ts sg1 in
  match_kwords lo hi (kn cs) (kn inv) sg2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint coeff_of_e (x : expr) (ts : list (Z * expr)) : Z :=
  match ts with
  | [] => 0
  | (k, a) :: rest => if expr_eqb a x then k else coeff_of_e x rest
  end.
(* [comment removed for export] *)
Definition elim1_test1 (kn : list kentry) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) (f : sfact) (t : Z * expr) : bool :=
  let '(fts, (flo, fhi)) := f in
  let '(kF, x) := t in
  let kT := coeff_of_e x ts in
  if (Z.eqb kT 0 || Z.eqb kF 0 || negb (Z.eqb (kT mod kF) 0))%bool then false
  else let lam := kT / kF in
       lin_test kn c (sub_fact lam fts ts)
         (fun lo hi => if Z.leb 0 lam then test (lo + lam * flo) (hi + lam * fhi) else test (lo + lam * fhi) (hi + lam * flo)).
Definition lin_test_elim1 (kn : list kentry) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  existsb (fun f : sfact => existsb (elim1_test1 kn c ts test f) (fst f)) (sum_facts kn kn).

(* [comment removed for export] *)
Definition krange_lin (kn : list kentry) (e : expr) (lo hi : Z) : bool :=
  let l := lin_of e in
  (Z.leb 0 lo && Z.ltb hi two64
   && (if lin_test kn (fst l) (snd l) (fun a _ => Z.leb lo a) then true else lin_test_elim1 kn (fst l) (snd l) (fun a _ => Z.leb lo a))
   && (if lin_test kn (fst l) (snd l) (fun _ b => Z.leb b hi) then true else lin_test_elim1 kn (fst l) (snd l) (fun _ b => Z.leb b hi)))%bool.

(* [comment removed for export] *)
Definition klen_weaker (k : list kentry) (X K : kentry) : bool :=
  match X, K with
  | KUnk a n, KUnk a' n' | KZero a n, KZero a' n' | KWr a n, KWr a' n' =>
      saddr_eqb_h a a' && lin_ge0 k [(n, 0)] [(n', 0)]
  | KFill a n c, KFill a' n' c' => saddr_eqb_h a a' && Z.eqb c c' && lin_ge0 k [(n, 0)] [(n', 0)]
  | _, _ => false
  end%bool.

(* [comment removed for export] *)
Definition cover_step (k : list kentry) (cur : expr) (kb : expr) (kk : Z) (len : expr) : option expr :=
  if (lin_ge0 k [(cur, 0)] [(kb, kk)]
      && negb (lin_ge0 k [(cur, 0)] [(kb, kk); (len, 0)])
      && lin_ge0 k [(ELit 0, two64m1)] [(kb, kk); (len, 0)])%bool
  then Some (eadd (eaddz kb kk) len) else None.
Fixpoint cover_sym1 (allk rem : list kentry) (wok : bool) (cur : expr) : option (expr * list kentry) :=
  match rem with
  | [] => None
  | X :: rest =>
      match (match X with
             | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
                 cover_step allk cur kb kk len
             | KWord (SA kb kk) w _ => if wok then cover_step allk cur kb kk (ELit (Z.of_nat w)) else None
             | _ => None
             end) with
      | Some cur' => Some (cur', rest)
      | None => match cover_sym1 allk rest wok cur with
                | Some (cur', rest') => Some (cur', X :: rest')
                | None => None
                end
      end
  end.
Fixpoint cover_sym_go (fuel : nat) (k rem : list kentry) (wok : bool) (cur stop : expr) : bool :=
  match fuel with
  | O => false
  | S f => if lin_ge0 k [(cur, 0)] [(stop, 0)] then true
           else match cover_sym1 k rem wok cur with
                | Some (cur', rem') => cover_sym_go f k rem' wok cur' stop
                | None => false
                end
  end.
Definition kunk_cover_sym (k : list kentry) (K : kentry) : bool :=
  match K with
  | KUnk (SA b o) n =>
      (kflat_h k K && lin_ge0 k [(ELit 0, two64m1)] [(b, o); (n, 0)]
       && cover_sym_go (S (length k)) k k (Z.leb (img_lo A) (img_hi A) && off_image_x A k b o n) (eaddz b o) (eadd (eaddz b o) n))%bool
  | _ => false
  end.
(* [comment removed for export] *)
Definition coverw_step (k : list kentry) (cur : expr) (X : kentry) : option expr :=
  match X with KWr (SA kb kk) len => cover_step k cur kb kk len | _ => None end.
Fixpoint coverw_sym1 (allk rem : list kentry) (cur : expr) : option (expr * list kentry) :=
  match rem with
  | [] => None
  | X :: rest =>
      match coverw_step allk cur X with
      | Some cur' => Some (cur', rest)
      | None => match coverw_sym1 allk rest cur with
                | Some (cur', rest') => Some (cur', X :: rest')
                | None => None
                end
      end
  end.
Fixpoint coverw_go (fuel : nat) (k rem : list kentry) (cur stop : expr) : bool :=
  match fuel with
  | O => false
  | S f => if lin_ge0 k [(cur, 0)] [(stop, 0)] then true
           else match coverw_sym1 k rem cur with
                | Some (cur', rem') => coverw_go f k rem' cur' stop
                | None => false
                end
  end.
Definition kwr_cover_sym (k : list kentry) (K : kentry) : bool :=
  match K with
  | KWr (SA b o) n =>
      (kflat_h k K && lin_ge0 k [(ELit 0, two64m1)] [(b, o); (n, 0)]
       && coverw_go (S (length k)) k k (eaddz b o) (eadd (eaddz b o) n))%bool
  | _ => false
  end.

(* [comment removed for export] *)
Definition kn_incl1_s (k : list kentry) (K : kentry) : bool :=
  if kn_incl1_h A k K then true else
  match K with
  | KRange e lo hi => if fact_ok k K then true else krange_lin k e lo hi
  | KAlign _ _ => fact_ok k K
  | KDisj _ _ _ _ => fact_ok k K
  | KUnk _ _ =>
      if (if kflat_h k K then existsb (fun X => klen_weaker k X K) k else false) then true else kunk_cover_sym k K
  | KZero _ _ | KFill _ _ _ =>
      if kflat_h k K then existsb (fun X => klen_weaker k X K) k else false
  | KWr (SA b o) n =>      (* [comment removed for export] *)
      if kflat_h k K then (if existsb (fun X => klen_weaker k X K) k then true else if kwritable_x k k b o n then true else kwr_cover_sym k K) else false   (* [comment removed for export] *)
  | _ => false
  end.
(* [comment removed for export] *)
Fixpoint find_win (w : nat) (k : list kentry) (K : kentry) : option (list kentry) :=
  match w, k with
  | O, _ => None
  | _, [] => None
  | S w', X :: k' => if kentry_eqb X K then Some k' else find_win w' k' K
  end.
Fixpoint subseq_left (k tk : list kentry) (acc : list kentry) : list kentry :=
  match tk with
  | [] => acc
  | K :: tk' => match find_win 16 k K with
               | Some k' => subseq_left k' tk' acc
               | None => subseq_left k tk' (K :: acc)
               end
  end.
Definition kn_incl_s (k : list kentry) (tk : list kentry) : bool := forallb (kn_incl1_s k) (subseq_left k tk []).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint regs_match_s (k : list kentry) (rs ts : list expr) : bool :=
  match rs, ts with
  | [], [] => true
  | r :: rs', t :: ts' => (if expr_eqb r t then true else respell_ok k r t) && regs_match_s k rs' ts'
  | _, _ => false
  end%bool.

(* [comment removed for export] *)
Definition ematch_s (k : list kentry) (a e : expr) : bool := if expr_eqb a e then true else respell_ok k a e.
Definition afd_match_s (k : list kentry) (x y : afd) : bool :=
  match x, y with
  | FdStd, FdStd => true
  | FdDir, FdDir => true
  | FdFile i l o, FdFile i' l' o' => (Nat.eqb i i' && ematch_s k l l' && ematch_s k o o')%bool
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition entails_t (cs : acs) (T : acs) : bool :=
  (Z.eqb (pc cs) (pc T)
   && match s_log (a_ss T) with [] => true | _ => false end
   && match s_resv (a_ss T) with None => true | _ => false end
   && Nat.eqb (length (s_regs (a_ss T))) 32
   && regs_match_s (kn cs) (s_regs (a_ss cs)) (s_regs (a_ss T))
   && kn_incl_s (kn cs) (kn T)
   && list_eqb amap_eqb (a_maps cs) (a_maps T)
   && list_eqb pair_eqb (a_vis cs) (a_vis T)
   && list_eqb pair_eqb (a_ghost cs) (a_ghost T)
   && ematch_s (kn cs) (a_brk cs) (a_brk T)
   && afd_match_s (kn cs) (a_fd cs) (a_fd T)
   && Bool.eqb (a_tidset cs) (a_tidset T)
   && Z.leb (a_totsz cs) (a_totsz T) && Z.leb (a_ylo T) (a_ylo cs)
   && Z.leb (a_eager cs) (a_eager T) && Z.leb (a_abytes cs) (a_abytes T))%bool.

(* [comment removed for export] *)
Definition entails_s (lo hi : nat) (hints : sbind) (cs inv : acs) : option sbind :=
  let sg := infer_sg lo hi hints cs inv in
  if (sg_dom_in lo hi sg && entails_t cs (insts sg inv))%bool then Some sg else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_snext (s : shape) : bool := match s with SNext => true | _ => false end.
Fixpoint no_next (s : shape) : bool :=
  match s with
  | SNext => false
  | SEmitP _ _ s' => no_next s'
  | SAlt2 a b => no_next a && no_next b
  | SCase _ _ a b => no_next a && no_next b
  | _ => true
  end%bool.

(* [comment removed for export] *)
Definition salt2c (a b : shape) : shape := if shape_eqb a b then a else salt2 a b.
Definition salt2_in (lc : option loopctx) (a b : shape) : shape :=
  match lc with Some (WC _ _ _ _ _ _ _) => salt2c a b | _ => salt2 a b end.

(* [comment removed for export] *)
Definition template_ok (lo : nat) (x : acs) : bool :=
  (fresh_ok nx0 x
   && match s_log (a_ss x) with [] => true | _ => false end
   && match s_resv (a_ss x) with None => true | _ => false end
   && Nat.eqb (length (s_regs (a_ss x))) 32
   && Nat.leb lo (nxt x))%bool.

(* [comment removed for export] *)
Definition head_ok (lo : nat) (V : expr) (T : acs) : bool := (template_ok lo T && expr_vars_lt (nxt T) V)%bool.
Definition while_okN (cs : acs) (lo : nat) (heads : list acs) (V : expr) (xs : shape) : bool :=
  (Nat.leb nx0 lo && Nat.leb (nxt cs) lo && forallb (head_ok lo V) heads
   && (is_snext xs || no_next xs) && shape_vars_lt nx0 xs)%bool.

(* [comment removed for export] *)
Definition variant_dec (k : list kentry) (sg : sbind) (V : expr) : bool :=
  lin_ge0 k [(V, 0)] [(esubsts sg V, 1)].
Definition variant_le (k : list kentry) (sg : sbind) (V : expr) : bool :=
  lin_ge0 k [(V, 0)] [(esubsts sg V, 0)].
Definition variant_ok (k : list kentry) (sg : sbind) (V : expr) (cur h : nat) : bool :=
  if variant_dec k sg V then true else (Nat.ltb cur h && variant_le k sg V)%bool.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kflat_hB (bc : AX2B.bctx) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w _ => flat_xB bc b o (ELit (Z.of_nat w))
  | KZero (SA b o) n | KBlob (SA b o) n _ | KWr (SA b o) n | KFill (SA b o) n _ | KUnk (SA b o) n => flat_xB bc b o n
  | _ => true
  end.
Lemma kflat_hB_eqf : forall k, kflat_hB (AX2B.mkbc k) = kflat_h k.
Proof. intros. apply functional_extensionality; intros K. unfold kflat_hB, kflat_h. rewrite flat_xB_eqf. reflexivity. Qed.
Definition kunk_coveredB (bc : AX2B.bctx) (k : list kentry) (K : kentry) : bool :=
  match K with
  | KUnk (SA b o) (ELit n) =>
      if (Z.ltb 0 n && Z.leb n (2 ^ 40) && Z.leb (img_lo A) (img_hi A))%bool then
        if flat_xB bc b o (ELit n) then if off_image_xB A bc b o (ELit n) then cover_x (S (length k)) k b o (o + n) else false else false
      else false
  | _ => false
  end.
Lemma kunk_coveredB_eqf : forall k, kunk_coveredB (AX2B.mkbc k) k = kunk_covered A k.
Proof.
  intros. apply functional_extensionality; intros K. unfold kunk_coveredB, kunk_covered. rewrite flat_xB_eqf, off_image_xB_eqf.
  destruct K as [| | | | | | | | |[b o] [n| | | | | | |]]; try reflexivity.
  destruct (Z.ltb 0 n && Z.leb n (2 ^ 40) && Z.leb (img_lo A) (img_hi A))%bool; [|reflexivity].
  destruct (flat_x k b o (ELit n)); [|reflexivity]. destruct (off_image_x A k b o (ELit n)); reflexivity.
Qed.
Definition kn_incl1_hB (ix : knix) (bc : AX2B.bctx) (k : list kentry) (K : kentry) : bool :=
  if kn_memb ix K then true
  else if (if kflat_hB bc K then existsb (fun X => kentry_eqb_h X K) k else false) then true
  else if kimg_sub_covered k K then true
  else kunk_coveredB bc k K.
Lemma kn_incl1_hB_eq : forall k K, kn_incl1_hB (kn_ix k) (AX2B.mkbc k) k K = kn_incl1_h A k K.
Proof. intros. unfold kn_incl1_hB, kn_incl1_h. rewrite kn_memb_eq, kflat_hB_eqf, kunk_coveredB_eqf. reflexivity. Qed.
Definition fact_okB (bc : AX2B.bctx) (K : kentry) : bool :=
  match K with
  | KRange e lo hi =>
      match xlo2B bc e, xhi2B bc e with
      | Some l, Some h => Z.leb lo l && Z.leb h hi
      | _, _ => false
      end
  | KAlign e m => Z.ltb 0 m && Z.eqb m (2 ^ (Z.log2 m)) && Z.leb (Z.log2 m) (AX2B.ealignB bc e)
  | KDisj (SA b1 k1) n1 (SA b2 k2) n2 => AX2B.ranges_apart_xB bc b1 k1 n1 b2 k2 n2
  | _ => false
  end%bool.
Lemma fact_okB_eqf : forall k, fact_okB (AX2B.mkbc k) = fact_ok k.
Proof.
  intros. apply functional_extensionality; intros K. unfold fact_okB, fact_ok.
  rewrite xlo2B_eqf, xhi2B_eqf, AX2B.ealignB_eqf, AX2B.ranges_apart_xB_eqf. reflexivity.
Qed.
Definition elim1_test1B (bc : AX2B.bctx) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) (f : sfact) (t : Z * expr) : bool :=
  let '(fts, (flo, fhi)) := f in
  let '(kF, x) := t in
  let kT := coeff_of_e x ts in
  if (Z.eqb kT 0 || Z.eqb kF 0 || negb (Z.eqb (kT mod kF) 0))%bool then false
  else let lam := kT / kF in
       AX2B.lin_testB bc c (sub_fact lam fts ts)
         (fun lo hi => if Z.leb 0 lam then test (lo + lam * flo) (hi + lam * fhi) else test (lo + lam * fhi) (hi + lam * flo)).
Definition lin_test_elim1B (bc : AX2B.bctx) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  existsb (fun f : sfact => existsb (elim1_test1B bc c ts test f) (fst f)) (AX2B.bc_fs bc).
Lemma lin_test_elim1B_eqf : forall k, lin_test_elim1B (AX2B.mkbc k) = lin_test_elim1 k.
Proof.
  intros. apply functional_extensionality; intros c. apply functional_extensionality; intros ts. apply functional_extensionality; intros test.
  unfold lin_test_elim1B, lin_test_elim1. rewrite AX2B.bc_fs_mkbc. f_equal.
  apply functional_extensionality; intros [fts [flo fhi]]. f_equal. apply functional_extensionality; intros [kF x].
  unfold elim1_test1B, elim1_test1. rewrite AX2B.lin_testB_eqf. reflexivity.
Qed.
Definition krange_linB (bc : AX2B.bctx) (e : expr) (lo hi : Z) : bool :=
  let l := lin_of e in
  if (Z.leb 0 lo && Z.ltb hi two64)%bool then
    if (if AX2B.lin_testB bc (fst l) (snd l) (fun a _ => Z.leb lo a) then true else lin_test_elim1B bc (fst l) (snd l) (fun a _ => Z.leb lo a))
    then (if AX2B.lin_testB bc (fst l) (snd l) (fun _ b => Z.leb b hi) then true else lin_test_elim1B bc (fst l) (snd l) (fun _ b => Z.leb b hi))
    else false
  else false.
Lemma krange_linB_eqf : forall k, krange_linB (AX2B.mkbc k) = krange_lin k.
Proof.
  intros. apply functional_extensionality; intros e. apply functional_extensionality; intros lo. apply functional_extensionality; intros hi.
  unfold krange_linB, krange_lin. rewrite AX2B.lin_testB_eqf, lin_test_elim1B_eqf. cbv zeta.
  destruct (Z.leb 0 lo); destruct (Z.ltb hi two64); cbn [andb]; try reflexivity.
  all: match goal with |- _ = (?a && ?b)%bool => destruct a; destruct b; reflexivity end.
Qed.
Definition klen_weakerB (bc : AX2B.bctx) (X K : kentry) : bool :=
  match X, K with
  | KUnk a n, KUnk a' n' | KZero a n, KZero a' n' | KWr a n, KWr a' n' =>
      if saddr_eqb_h a a' then AX2B.lin_ge0B bc [(n, 0)] [(n', 0)] else false
  | KFill a n c, KFill a' n' c' => if (saddr_eqb_h a a' && Z.eqb c c')%bool then AX2B.lin_ge0B bc [(n, 0)] [(n', 0)] else false
  | _, _ => false
  end.
Lemma klen_weakerB_eqf : forall k, klen_weakerB (AX2B.mkbc k) = klen_weaker k.
Proof.
  intros. apply functional_extensionality; intros X. apply functional_extensionality; intros K.
  unfold klen_weakerB, klen_weaker. rewrite AX2B.lin_ge0B_eqf.
  destruct X, K; try reflexivity; try (destruct (saddr_eqb_h _ _); reflexivity);
  destruct (saddr_eqb_h _ _); cbn [andb]; try reflexivity; destruct (Z.eqb _ _); reflexivity.
Qed.
Definition cover_stepB (bc : AX2B.bctx) (cur : expr) (kb : expr) (kk : Z) (len : expr) : option expr :=
  if AX2B.lin_ge0B bc [(cur, 0)] [(kb, kk)] then
    if negb (AX2B.lin_ge0B bc [(cur, 0)] [(kb, kk); (len, 0)]) then
      if AX2B.lin_ge0B bc [(ELit 0, two64m1)] [(kb, kk); (len, 0)] then Some (eadd (eaddz kb kk) len) else None
    else None
  else None.
Lemma cover_stepB_eqf : forall k, cover_stepB (AX2B.mkbc k) = cover_step k.
Proof.
  intros. apply functional_extensionality; intros cur. apply functional_extensionality; intros kb.
  apply functional_extensionality; intros kk. apply functional_extensionality; intros len.
  unfold cover_stepB, cover_step. rewrite AX2B.lin_ge0B_eqf.
  destruct (lin_ge0 k [(cur, 0)] [(kb, kk)]); [|reflexivity]. destruct (lin_ge0 k [(cur, 0)] [(kb, kk); (len, 0)]); [reflexivity|].
  cbn [negb andb]. destruct (lin_ge0 k [(ELit 0, two64m1)] [(kb, kk); (len, 0)]); reflexivity.
Qed.
Fixpoint cover_sym1B (bc : AX2B.bctx) (rem : list kentry) (wok : bool) (cur : expr) : option (expr * list kentry) :=
  match rem with
  | [] => None
  | X :: rest =>
      match (match X with
             | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
                 cover_stepB bc cur kb kk len
             | KWord (SA kb kk) w _ => if wok then cover_stepB bc cur kb kk (ELit (Z.of_nat w)) else None
             | _ => None
             end) with
      | Some cur' => Some (cur', rest)
      | None => match cover_sym1B bc rest wok cur with
                | Some (cur', rest') => Some (cur', X :: rest')
                | None => None
                end
      end
  end.
Lemma cover_sym1B_eqf : forall k, cover_sym1B (AX2B.mkbc k) = cover_sym1 k.
Proof.
  intros. apply functional_extensionality; intros rem. induction rem as [|X rest IH]; apply functional_extensionality; intros wok; apply functional_extensionality; intros cur; [reflexivity|].
  cbn [cover_sym1B cover_sym1]. rewrite cover_stepB_eqf, IH. reflexivity.
Qed.
Fixpoint cover_sym_goB (fuel : nat) (bc : AX2B.bctx) (rem : list kentry) (wok : bool) (cur stop : expr) : bool :=
  match fuel with
  | O => false
  | S f => if AX2B.lin_ge0B bc [(cur, 0)] [(stop, 0)] then true
           else match cover_sym1B bc rem wok cur with
                | Some (cur', rem') => cover_sym_goB f bc rem' wok cur' stop
                | None => false
                end
  end.
Lemma cover_sym_goB_eqf : forall k fuel, cover_sym_goB fuel (AX2B.mkbc k) = cover_sym_go fuel k.
Proof.
  intros k fuel. induction fuel as [|f IH]; apply functional_extensionality; intros rem; apply functional_extensionality; intros wok;
    apply functional_extensionality; intros cur; apply functional_extensionality; intros stop; [reflexivity|].
  cbn [cover_sym_goB cover_sym_go]. rewrite AX2B.lin_ge0B_eqf, cover_sym1B_eqf, IH. reflexivity.
Qed.
Definition kunk_cover_symB (bc : AX2B.bctx) (k : list kentry) (K : kentry) : bool :=
  match K with
  | KUnk (SA b o) n =>
      if kflat_hB bc K then
        if AX2B.lin_ge0B bc [(ELit 0, two64m1)] [(b, o); (n, 0)] then
          cover_sym_goB (S (length k)) bc k (Z.leb (img_lo A) (img_hi A) && off_image_xB A bc b o n) (eaddz b o) (eadd (eaddz b o) n)
        else false
      else false
  | _ => false
  end.
Lemma kunk_cover_symB_eqf : forall k, kunk_cover_symB (AX2B.mkbc k) k = kunk_cover_sym k.
Proof.
  intros. apply functional_extensionality; intros K. unfold kunk_cover_symB, kunk_cover_sym.
  rewrite kflat_hB_eqf, AX2B.lin_ge0B_eqf, cover_sym_goB_eqf, off_image_xB_eqf.
  destruct K as [| | | | | | | | |[b o] n]; try reflexivity.
  destruct (kflat_h k _); [|reflexivity]. destruct (lin_ge0 k _ _); reflexivity.
Qed.
Definition coverw_stepB (bc : AX2B.bctx) (cur : expr) (X : kentry) : option expr :=
  match X with KWr (SA kb kk) len => cover_stepB bc cur kb kk len | _ => None end.
Fixpoint coverw_sym1B (bc : AX2B.bctx) (rem : list kentry) (cur : expr) : option (expr * list kentry) :=
  match rem with
  | [] => None
  | X :: rest =>
      match coverw_stepB bc cur X with
      | Some cur' => Some (cur', rest)
      | None => match coverw_sym1B bc rest cur with
                | Some (cur', rest') => Some (cur', X :: rest')
                | None => None
                end
      end
  end.
Lemma coverw_sym1B_eqf : forall k, coverw_sym1B (AX2B.mkbc k) = coverw_sym1 k.
Proof.
  intros. apply functional_extensionality; intros rem. induction rem as [|X rest IH]; apply functional_extensionality; intros cur; [reflexivity|].
  cbn [coverw_sym1B coverw_sym1]. unfold coverw_stepB, coverw_step. rewrite cover_stepB_eqf, IH. reflexivity.
Qed.
Fixpoint coverw_goB (fuel : nat) (bc : AX2B.bctx) (rem : list kentry) (cur stop : expr) : bool :=
  match fuel with
  | O => false
  | S f => if AX2B.lin_ge0B bc [(cur, 0)] [(stop, 0)] then true
           else match coverw_sym1B bc rem cur with
                | Some (cur', rem') => coverw_goB f bc rem' cur' stop
                | None => false
                end
  end.
Lemma coverw_goB_eqf : forall k fuel, coverw_goB fuel (AX2B.mkbc k) = coverw_go fuel k.
Proof.
  intros k fuel. induction fuel as [|f IH]; apply functional_extensionality; intros rem;
    apply functional_extensionality; intros cur; apply functional_extensionality; intros stop; [reflexivity|].
  cbn [coverw_goB coverw_go]. rewrite AX2B.lin_ge0B_eqf, coverw_sym1B_eqf, IH. reflexivity.
Qed.
Definition kwr_cover_symB (bc : AX2B.bctx) (k : list kentry) (K : kentry) : bool :=
  match K with
  | KWr (SA b o) n =>
      if kflat_hB bc K then
        if AX2B.lin_ge0B bc [(ELit 0, two64m1)] [(b, o); (n, 0)] then coverw_goB (S (length k)) bc k (eaddz b o) (eadd (eaddz b o) n) else false
      else false
  | _ => false
  end.
Lemma kwr_cover_symB_eqf : forall k, kwr_cover_symB (AX2B.mkbc k) k = kwr_cover_sym k.
Proof.
  intros. apply functional_extensionality; intros K. unfold kwr_cover_symB, kwr_cover_sym.
  rewrite kflat_hB_eqf, AX2B.lin_ge0B_eqf, coverw_goB_eqf.
  destruct K as [| | | | | |[b o] n| | |]; try reflexivity.
  destruct (kflat_h k _); [|reflexivity]. destruct (lin_ge0 k _ _); reflexivity.
Qed.
Definition kn_incl1_sB (ix : knix) (bc : AX2B.bctx) (k : list kentry) (K : kentry) : bool :=
  if kn_incl1_hB ix bc k K then true else
  match K with
  | KRange e lo hi => if fact_okB bc K then true else krange_linB bc e lo hi
  | KAlign _ _ => fact_okB bc K
  | KDisj _ _ _ _ => fact_okB bc K
  | KUnk _ _ =>
      if (if kflat_hB bc K then existsb (fun X => klen_weakerB bc X K) k else false) then true else kunk_cover_symB bc k K
  | KZero _ _ | KFill _ _ _ =>
      if kflat_hB bc K then existsb (fun X => klen_weakerB bc X K) k else false
  | KWr (SA b o) n =>
      if kflat_hB bc K then (if existsb (fun X => klen_weakerB bc X K) k then true else if kwritable_xB bc k b o n then true else kwr_cover_symB bc k K) else false
  | _ => false
  end.
Lemma kn_incl1_sB_eq : forall k K, kn_incl1_sB (kn_ix k) (AX2B.mkbc k) k K = kn_incl1_s k K.
Proof.
  intros k K. unfold kn_incl1_sB, kn_incl1_s.
  rewrite kn_incl1_hB_eq, fact_okB_eqf, krange_linB_eqf, kflat_hB_eqf, klen_weakerB_eqf, kunk_cover_symB_eqf, kwr_cover_symB_eqf, kwritable_xB_eqf.
  reflexivity.
Qed.
Definition kn_incl_sB (ix : knix) (bc : AX2B.bctx) (k : list kentry) (tk : list kentry) : bool :=
  forallb (kn_incl1_sB ix bc k) (subseq_left k tk []).
Lemma kn_incl_sB_eq : forall k tk, kn_incl_sB (kn_ix k) (AX2B.mkbc k) k tk = kn_incl_s k tk.
Proof.
  intros. unfold kn_incl_sB, kn_incl_s. apply forallb_ext. intros K. apply kn_incl1_sB_eq.
Qed.
Definition respell_okB (bc : AX2B.bctx) (a e : expr) : bool :=
  match AX2B.decide_branchB bc BC_EQ a e with
  | Some true => true
  | _ => match AX2B.erangeB bc (mkAlu ALU_SUB a e) with
         | Some (lo, hi) => (Z.eqb lo 0 && Z.eqb hi 0)%bool
         | None => false
         end
  end.
Lemma respell_okB_eqf : forall k, respell_okB (AX2B.mkbc k) = respell_ok k.
Proof.
  intros. apply functional_extensionality; intros a. apply functional_extensionality; intros e.
  unfold respell_okB, respell_ok. rewrite AX2B.decide_branchB_eqf, AX2B.erangeB_eqf. reflexivity.
Qed.
Fixpoint regs_match_sB (bc : AX2B.bctx) (rs ts : list expr) : bool :=
  match rs, ts with
  | [], [] => true
  | r :: rs', t :: ts' => if (if expr_eqb r t then true else respell_okB bc r t) then regs_match_sB bc rs' ts' else false
  | _, _ => false
  end.
Lemma regs_match_sB_eqf : forall k rs ts, regs_match_sB (AX2B.mkbc k) rs ts = regs_match_s k rs ts.
Proof.
  intros k rs. induction rs as [|r rs' IH]; intros [|t ts']; try reflexivity.
  cbn [regs_match_sB regs_match_s]. rewrite respell_okB_eqf, IH.
  destruct (if expr_eqb r t then true else respell_ok k r t); reflexivity.
Qed.
Definition ematch_sB (bc : AX2B.bctx) (a e : expr) : bool := if expr_eqb a e then true else respell_okB bc a e.
Definition afd_match_sB (bc : AX2B.bctx) (x y : afd) : bool :=
  match x, y with
  | FdStd, FdStd => true
  | FdDir, FdDir => true
  | FdFile i l o, FdFile i' l' o' => if Nat.eqb i i' then if ematch_sB bc l l' then ematch_sB bc o o' else false else false
  | _, _ => false
  end.
Lemma ematch_sB_eqf : forall k, ematch_sB (AX2B.mkbc k) = ematch_s k.
Proof. intros. apply functional_extensionality; intros a. apply functional_extensionality; intros e. unfold ematch_sB, ematch_s. rewrite respell_okB_eqf. reflexivity. Qed.
Lemma afd_match_sB_eqf : forall k x y, afd_match_sB (AX2B.mkbc k) x y = afd_match_s k x y.
Proof.
  intros. unfold afd_match_sB, afd_match_s. rewrite ematch_sB_eqf. destruct x, y; try reflexivity.
  destruct (Nat.eqb _ _); [|reflexivity]. cbn [andb]. destruct (ematch_s k _ _); [|reflexivity]. reflexivity.
Qed.
(* [comment removed for export] *)
Definition entails_tB (ix : knix) (bc : AX2B.bctx) (cs : acs) (T : acs) : bool :=
  if (Z.eqb (pc cs) (pc T)
      && match s_log (a_ss T) with [] => true | _ => false end
      && match s_resv (a_ss T) with None => true | _ => false end
      && Nat.eqb (length (s_regs (a_ss T))) 32
      && list_eqb amap_eqb (a_maps cs) (a_maps T)
      && list_eqb pair_eqb (a_vis cs) (a_vis T)
      && list_eqb pair_eqb (a_ghost cs) (a_ghost T)
      && Bool.eqb (a_tidset cs) (a_tidset T)
      && Z.leb (a_totsz cs) (a_totsz T) && Z.leb (a_ylo T) (a_ylo cs)
      && Z.leb (a_eager cs) (a_eager T) && Z.leb (a_abytes cs) (a_abytes T))%bool
  then if regs_match_sB bc (s_regs (a_ss cs)) (s_regs (a_ss T))
       then if ematch_sB bc (a_brk cs) (a_brk T)
            then if afd_match_sB bc (a_fd cs) (a_fd T) then kn_incl_sB ix bc (kn cs) (kn T) else false
            else false
       else false
  else false.
Lemma entails_tB_eq : forall cs T, entails_tB (kn_ix (kn cs)) (AX2B.mkbc (kn cs)) cs T = entails_t cs T.
Proof.
  intros cs T. unfold entails_tB, entails_t.
  rewrite regs_match_sB_eqf, ematch_sB_eqf, afd_match_sB_eqf, kn_incl_sB_eq.
  (* [comment removed for export] *)
  set (b1 := Z.eqb (pc cs) (pc T)). set (b2 := match s_log (a_ss T) with [] => true | _ => false end).
  set (b3 := match s_resv (a_ss T) with None => true | _ => false end). set (b4 := Nat.eqb (length (s_regs (a_ss T))) 32).
  set (b5 := regs_match_s (kn cs) (s_regs (a_ss cs)) (s_regs (a_ss T))). set (b6 := kn_incl_s (kn cs) (kn T)).
  set (b7 := list_eqb amap_eqb (a_maps cs) (a_maps T)). set (b8 := list_eqb pair_eqb (a_vis cs) (a_vis T)).
  set (b9 := list_eqb pair_eqb (a_ghost cs) (a_ghost T)). set (b10 := ematch_s (kn cs) (a_brk cs) (a_brk T)).
  set (b11 := afd_match_s (kn cs) (a_fd cs) (a_fd T)). set (b12 := Bool.eqb (a_tidset cs) (a_tidset T)).
  set (b13 := Z.leb (a_totsz cs) (a_totsz T)). set (b14 := Z.leb (a_ylo T) (a_ylo cs)).
  set (b15 := Z.leb (a_eager cs) (a_eager T)). set (b16 := Z.leb (a_abytes cs) (a_abytes T)).
  clearbody b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16.
  destruct b1; [|reflexivity]. destruct b2; [|reflexivity]. destruct b3; [|reflexivity]. destruct b4; [|reflexivity].
  cbn [andb]. destruct b7; [|destruct b5; [destruct b6|]; reflexivity]. destruct b8; [|destruct b5; [destruct b6|]; reflexivity].
  destruct b9; [|destruct b5; [destruct b6|]; reflexivity]. destruct b12, b13, b14, b15, b16, b5, b10, b11, b6; reflexivity.
Qed.
(* [comment removed for export] *)
Definition kw_nfkey (a : saddr) : Z := snd (split_lit (eaddz (a_base a) (a_off a))).
Definition kwP (a : saddr) (X : kentry) : bool := match X with KWord a' _ _ => Z.eqb (a_off a') (a_off a) | _ => false end.
Definition kwQ (a : saddr) (X : kentry) : bool :=
  match X with KWord a' _ _ => if Z.eqb (a_off a') (a_off a) then false else Z.eqb (kw_nfkey a') (kw_nfkey a) | _ => false end.
Record kwix := KWX { kw_o : ptree (list (positive * kentry)); kw_n : ptree (list (positive * kentry)) }.
Definition kwb (t : ptree (list (positive * kentry))) (z : Z) : list (positive * kentry) :=
  match pt_get t (zkey z) with Some l => l | None => [] end.
Fixpoint kw_build (k : list kentry) (i : positive) : kwix :=
  match k with
  | [] => KWX PTLeaf PTLeaf
  | X :: rest =>
      let r := kw_build rest (Pos.succ i) in
      match X with
      | KWord a' _ _ =>
          let zo := a_off a' in let zn := kw_nfkey a' in
          KWX (pt_set (zkey zo) ((i, X) :: kwb (kw_o r) zo) (kw_o r)) (pt_set (zkey zn) ((i, X) :: kwb (kw_n r) zn) (kw_n r))
      | _ => r
      end
  end.
Definition kw_cands (ix : kwix) (a : saddr) : list kentry :=
  AX2B.kx_merge (kwb (kw_o ix) (a_off a)) (List.filter (fun t => kwQ a (snd t)) (kwb (kw_n ix) (kw_nfkey a))).
Lemma kwb_set : forall t z x z', kwb (pt_set (zkey z) (x :: kwb t z) t) z' = if Z.eqb z' z then x :: kwb t z' else kwb t z'.
Proof.
  intros t z x z'. unfold kwb at 1. destruct (Z.eqb_spec z' z) as [->|NE].
  - rewrite pt_gss. reflexivity.
  - rewrite pt_gso; [reflexivity|]. intros E. apply NE. apply zkey_inj. exact E.
Qed.
Definition kwo_key (z : Z) (X : kentry) : bool := match X with KWord a' _ _ => Z.eqb (a_off a') z | _ => false end.
Definition kwn_key (z : Z) (X : kentry) : bool := match X with KWord a' _ _ => Z.eqb (kw_nfkey a') z | _ => false end.
Lemma kw_build_spec : forall k i,
  (forall z, kwb (kw_o (kw_build k i)) z = List.filter (fun t => kwo_key z (snd t)) (AX2B.tagged k i))
  /\ (forall z, kwb (kw_n (kw_build k i)) z = List.filter (fun t => kwn_key z (snd t)) (AX2B.tagged k i)).
Proof.
  induction k as [|X rest IH]; intros i.
  - split; intros z; cbn; unfold kwb; rewrite pt_get_leaf; reflexivity.
  - destruct (IH (Pos.succ i)) as [HA HB]. cbn [kw_build AX2B.tagged List.filter snd].
    destruct X as [a' w' e'| | | | | | | | |]; try (split; [exact HA | exact HB]).
    cbn [kw_o kw_n kwo_key kwn_key]. split; intros z.
    + rewrite kwb_set, HA. destruct (Z.eqb_spec z (a_off a')) as [->|NE]; [rewrite Z.eqb_refl; reflexivity|].
      destruct (Z.eqb_spec (a_off a') z); [congruence|reflexivity].
    + rewrite kwb_set, HB. destruct (Z.eqb_spec z (kw_nfkey a')) as [->|NE]; [rewrite Z.eqb_refl; reflexivity|].
      destruct (Z.eqb_spec (kw_nfkey a') z); [congruence|reflexivity].
Qed.
Lemma filter_filter_tag : forall (P Q : kentry -> bool) (l : list (positive * kentry)),
  List.filter (fun t => Q (snd t)) (List.filter (fun t => P (snd t)) l) = List.filter (fun t => (fun X => P X && Q X)%bool (snd t)) l.
Proof.
  intros P Q l. induction l as [|t r IH]; [reflexivity|]. cbn. destruct (P (snd t)); cbn; [|exact IH].
  destruct (Q (snd t)); [cbn; rewrite IH; reflexivity | exact IH].
Qed.
Lemma kw_cands_eq : forall k a, kw_cands (kw_build k 1%positive) a = List.filter (fun X => kwP a X || kwQ a X)%bool k.
Proof.
  intros k a. unfold kw_cands. destruct (kw_build_spec k 1%positive) as [HA HB]. rewrite HA, HB.
  rewrite (filter_filter_tag (kwn_key (kw_nfkey a)) (kwQ a)).
  rewrite <- (AX2B.kx_merge_filters (kwP a) (kwQ a) k 1%positive).
  - f_equal; try reflexivity.
    all: apply filter_ext; intros [i X]; cbn [snd]; unfold kwP, kwo_key, kwQ, kwn_key;
         destruct X as [a' w' e'| | | | | | | | |]; try reflexivity;
         destruct (Z.eqb (kw_nfkey a') (kw_nfkey a)), (Z.eqb (a_off a') (a_off a)); reflexivity.
  - intros X HP. unfold kwP in HP. unfold kwQ. destruct X; try discriminate. rewrite HP. reflexivity.
Qed.
Lemma saddr_eqb_h_keys : forall a' a w e, saddr_eqb_h a' a = true -> (kwP a (KWord a' w e) || kwQ a (KWord a' w e))%bool = true.
Proof.
  intros a' a w0 e0 H. unfold kwP, kwQ. unfold saddr_eqb_h, saddr_eqb in H.
  destruct (Z.eqb_spec (a_off a') (a_off a)) as [E|NE]; [reflexivity|]. cbn [orb].
  apply Bool.orb_prop in H. destruct H as [H|H].
  - apply andb_prop in H as [_ H]. exfalso. revert H. destruct (Z.eqb_spec (a_off a') (a_off a)); [congruence|discriminate].
  - apply AX2B.p_expr_eqb_eq in H. unfold kw_nfkey. rewrite H. apply Z.eqb_refl.
Qed.
Lemma find_kword_filter : forall k a w,
  find_kword (List.filter (fun X => kwP a X || kwQ a X)%bool k) a w = find_kword k a w.
Proof.
  intros k a w. induction k as [|X rest IH]; [reflexivity|]. cbn [List.filter].
  destruct (kwP a X || kwQ a X)%bool eqn:HK.
  - destruct X; cbn [find_kword]; rewrite IH; reflexivity.
  - destruct X as [a' w' e'| | | | | | | | |]; cbn [find_kword]; try exact IH.
    destruct (saddr_eqb_h a' a) eqn:HS; [|cbn [andb]; exact IH].
    exfalso. rewrite (saddr_eqb_h_keys a' a w' e' HS) in HK. discriminate HK.
Qed.
Definition find_kwordI (ix : kwix) (a : saddr) (w : nat) : option expr := find_kword (kw_cands ix a) a w.
Lemma find_kwordI_eq : forall k a w, find_kwordI (kw_build k 1%positive) a w = find_kword k a w.
Proof. intros. unfold find_kwordI. rewrite kw_cands_eq. apply find_kword_filter. Qed.
Fixpoint match_kwordsI (lo hi : nat) (ix : kwix) (tk : list kentry) (sg : sbind) : sbind :=
  match tk with
  | [] => sg
  | KWord a w (EVar v) :: rest =>
      let sg' :=
        if slotb lo hi v then
          match sg_get sg v with
          | Some _ => sg
          | None =>
              match free_slots lo hi sg (a_base a) [] with
              | [] => match find_kwordI ix (asubsts sg a) w with Some e => sg ++ [(v, e)] | None => sg end
              | _ => sg
              end
          end
        else sg in
      match_kwordsI lo hi ix rest sg'
  | KWord a w t :: rest =>
      let sg' := match free_slots lo hi sg (a_base a) [] with
                 | [] => match find_kwordI ix (asubsts sg a) w with Some e => solve1 lo hi sg e t | None => sg end
                 | _ => sg
                 end in
      match_kwordsI lo hi ix rest sg'
  | _ :: rest => match_kwordsI lo hi ix rest sg
  end.
Lemma match_kwordsI_eq : forall lo hi k tk sg, match_kwordsI lo hi (kw_build k 1%positive) tk sg = match_kwords lo hi k tk sg.
Proof.
  intros lo hi k tk. induction tk as [|K rest IH]; intros sg; [reflexivity|].
  cbn [match_kwordsI match_kwords]. rewrite ?find_kwordI_eq.
  destruct K as [a w [| | | | | | |]| | | | | | | | |]; rewrite ?find_kwordI_eq, ?IH; try reflexivity.
Qed.
Definition infer_sgI (lo hi : nat) (hints : sbind) (cs inv : acs) : sbind :=
  let rs := s_regs (a_ss cs) in
  let ts := s_regs (a_ss inv) in
  let sg1 := match_bare lo hi rs ts hints in
  let sg2 := match_lin lo hi rs ts sg1 in
  match_kwordsI lo hi (kw_build (kn cs) 1%positive) (kn inv) sg2.
Lemma infer_sgI_eq : infer_sgI = infer_sg.
Proof.
  apply functional_extensionality; intros lo. apply functional_extensionality; intros hi.
  apply functional_extensionality; intros hints. apply functional_extensionality; intros cs. apply functional_extensionality; intros inv.
  unfold infer_sgI, infer_sg. rewrite match_kwordsI_eq. reflexivity.
Qed.
(* [comment removed for export] *)
Definition sbindN : Type := list (N * expr).
Definition toN (sg : sbind) : sbindN := map (fun p => (N.of_nat (fst p), snd p)) sg.
Fixpoint sg_getN (sg : sbindN) (n : N) : option expr :=
  match sg with
  | [] => None
  | (v, e) :: rest => if N.eqb v n then Some e else sg_getN rest n
  end.
Lemma sg_getN_eq : forall sg n, sg_getN (toN sg) (N.of_nat n) = sg_get sg n.
Proof.
  induction sg as [|[v e] r IH]; intros n; [reflexivity|]. cbn [toN map sg_getN sg_get fst snd]. fold (toN r).
  destruct (Nat.eqb v n) eqn:E.
  - apply Nat.eqb_eq in E. subst. rewrite N.eqb_refl. reflexivity.
  - replace (N.eqb (N.of_nat v) (N.of_nat n)) with false; [apply IH|].
    symmetry. apply N.eqb_neq. intros H. apply Nat2N.inj in H. apply Nat.eqb_neq in E. contradiction.
Qed.
Fixpoint esubstsN (sg : sbindN) (x : expr) : expr :=
  match x with
  | ELit _ => x
  | EVar n => match sg_getN sg (N.of_nat n) with Some e => e | None => x end
  | EAlu op a b => mkAlu op (esubstsN sg a) (esubstsN sg b)
  | EAluw op a b => mkAluw op (esubstsN sg a) (esubstsN sg b)
  | EMd op a b => mkMd op (esubstsN sg a) (esubstsN sg b)
  | EMdw op a b => mkMdw op (esubstsN sg a) (esubstsN sg b)
  | EExt sx lo n a => EExt sx lo n (esubstsN sg a)
  | EBlob _ _ _ _ => x
  end.
Lemma esubstsN_eq : forall sg x, esubstsN (toN sg) x = esubsts sg x.
Proof. intros sg x. induction x; cbn [esubstsN esubsts]; rewrite ?IHx1, ?IHx2, ?IHx, ?sg_getN_eq; reflexivity. Qed.
Lemma esubstsN_eqf : forall sg, esubstsN (toN sg) = esubsts sg.
Proof. intros. apply functional_extensionality. apply esubstsN_eq. Qed.
Definition asubstsN (sg : sbindN) (a : saddr) : saddr := SA (esubstsN sg (a_base a)) (a_off a).
Definition ksubstsN (sg : sbindN) (K : kentry) : kentry :=
  match K with
  | KWord a w v => KWord (asubstsN sg a) w (esubstsN sg v)
  | KZero a n => KZero (asubstsN sg a) (esubstsN sg n)
  | KBlob a n k => KBlob (asubstsN sg a) (esubstsN sg n) k
  | KImg lo hi => K
  | KAlign x m => KAlign (esubstsN sg x) m
  | KRange x lo hi => KRange (esubstsN sg x) lo hi
  | KWr a n => KWr (asubstsN sg a) (esubstsN sg n)
  | KDisj a1 n1 a2 n2 => KDisj (asubstsN sg a1) (esubstsN sg n1) (asubstsN sg a2) (esubstsN sg n2)
  | KFill a n c => KFill (asubstsN sg a) (esubstsN sg n) c
  | KUnk a n => KUnk (asubstsN sg a) (esubstsN sg n)
  end.
Definition psubstsN (sg : sbindN) (p : expr * expr) : expr * expr := (esubstsN sg (fst p), esubstsN sg (snd p)).
Definition msubstsN (sg : sbindN) (m : amap) : amap := AM (esubstsN sg (am_base m)) (esubstsN sg (am_len m)) (am_kind m).
Definition fsubstsN (sg : sbindN) (f : afd) : afd :=
  match f with FdFile k l o => FdFile k (esubstsN sg l) (esubstsN sg o) | _ => f end.
Lemma ksubstsN_eqf : forall sg, ksubstsN (toN sg) = ksubsts sg.
Proof.
  intros. apply functional_extensionality. intros K. unfold ksubstsN, ksubsts, asubstsN, asubsts.
  destruct K; rewrite ?esubstsN_eq; reflexivity.
Qed.
Lemma psubstsN_eqf : forall sg, psubstsN (toN sg) = psubsts sg.
Proof. intros. apply functional_extensionality. intros p. unfold psubstsN, psubsts. rewrite !esubstsN_eq. reflexivity. Qed.
Lemma msubstsN_eqf : forall sg, msubstsN (toN sg) = msubsts sg.
Proof. intros. apply functional_extensionality. intros m. unfold msubstsN, msubsts. rewrite !esubstsN_eq. reflexivity. Qed.
Lemma fsubstsN_eqf : forall sg, fsubstsN (toN sg) = fsubsts sg.
Proof. intros. apply functional_extensionality. intros f. unfold fsubstsN, fsubsts. destruct f; rewrite ?esubstsN_eq; reflexivity. Qed.
Definition instsN (sg : sbind) (inv : acs) : acs :=
  let s := toN sg in
  ACS (mk_ss (pc inv) (map (esubstsN s) (s_regs (a_ss inv))) (map (ksubstsN s) (kn inv)) (nxt inv))
      (map (msubstsN s) (a_maps inv)) (a_totsz inv) (a_ylo inv) (a_eager inv)
      (map (psubstsN s) (a_vis inv)) (map (psubstsN s) (a_ghost inv)) (a_abytes inv)
      (esubstsN s (a_brk inv)) (fsubstsN s (a_fd inv)) (a_tidset inv).
Lemma instsN_eq : forall sg inv, instsN sg inv = insts sg inv.
Proof.
  intros. unfold instsN, insts. cbv zeta.
  rewrite esubstsN_eqf, ksubstsN_eqf, psubstsN_eqf, msubstsN_eqf, fsubstsN_eqf. reflexivity.
Qed.
Lemma instsN_eqf : instsN = insts.
Proof. apply functional_extensionality; intros sg. apply functional_extensionality; intros inv. apply instsN_eq. Qed.

(* [comment removed for export] *)
Definition fromN (sg : sbindN) : sbind := map (fun p => (N.to_nat (fst p), snd p)) sg.
Lemma fromN_toN : forall sg, fromN (toN sg) = sg.
Proof. induction sg as [|[v e] r IH]; [reflexivity|]. cbn [toN fromN map fst snd]. fold (toN r). fold (fromN (toN r)). rewrite IH, Nat2N.id. reflexivity. Qed.
Lemma toN_app : forall a b, toN (a ++ b) = toN a ++ toN b.
Proof. intros. unfold toN. apply map_app. Qed.
Definition slotbN (lo hi v : N) : bool := (N.leb lo v && N.ltb v hi)%bool.
Lemma slotbN_eq : forall lo hi v, slotbN (N.of_nat lo) (N.of_nat hi) (N.of_nat v) = slotb lo hi v.
Proof.
  intros. unfold slotbN, slotb. f_equal.
  - destruct (Nat.leb lo v) eqn:E; [apply Nat.leb_le in E; apply N.leb_le; lia | apply Nat.leb_gt in E; apply N.leb_gt; lia].
  - destruct (Nat.ltb v hi) eqn:E; [apply Nat.ltb_lt in E; apply N.ltb_lt; lia | apply Nat.ltb_ge in E; apply N.ltb_ge; lia].
Qed.
Fixpoint free_slotsN (lo hi : N) (sg : sbindN) (e : expr) (acc : list nat) : list nat :=
  match e with
  | ELit _ => acc
  | EVar n => let nn := N.of_nat n in
              if slotbN lo hi nn then match sg_getN sg nn with Some _ => acc | None => n :: acc end else acc
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => free_slotsN lo hi sg a (free_slotsN lo hi sg b acc)
  | EExt _ _ _ a => free_slotsN lo hi sg a acc
  | EBlob _ _ _ _ => acc
  end.
Lemma free_slotsN_eq : forall lo hi sg e acc, free_slotsN (N.of_nat lo) (N.of_nat hi) (toN sg) e acc = free_slots lo hi sg e acc.
Proof.
  intros lo hi sg e. induction e; intros acc; cbn [free_slotsN free_slots]; rewrite ?slotbN_eq, ?sg_getN_eq, ?IHe2, ?IHe1, ?IHe; reflexivity.
Qed.
Fixpoint match_bareN (lo hi : N) (rs ts : list expr) (sg : sbindN) : sbindN :=
  match rs, ts with
  | r :: rs', EVar v :: ts' =>
      let vn := N.of_nat v in
      if slotbN lo hi vn then
        match sg_getN sg vn with
        | Some _ => match_bareN lo hi rs' ts' sg
        | None => match_bareN lo hi rs' ts' (sg ++ [(vn, r)])
        end
      else match_bareN lo hi rs' ts' sg
  | _ :: rs', _ :: ts' => match_bareN lo hi rs' ts' sg
  | _, _ => sg
  end.
Lemma match_bareN_eq : forall lo hi rs ts sg,
  match_bareN (N.of_nat lo) (N.of_nat hi) rs ts (toN sg) = toN (match_bare lo hi rs ts sg).
Proof.
  intros lo hi rs. induction rs as [|r rs' IH]; intros ts sg; [destruct ts as [|[] ?]; reflexivity|].
  destruct ts as [|t ts']; [reflexivity|].
  destruct t; cbn [match_bareN match_bare]; try apply IH.
  rewrite slotbN_eq, sg_getN_eq. destruct (slotb lo hi n); [|apply IH].
  destruct (sg_get sg n); [apply IH|]. rewrite <- IH, toN_app. reflexivity.
Qed.
Definition solve1N (lo hi : N) (sg : sbindN) (r t1 : expr) : sbindN :=
  let t := esubstsN sg t1 in
  match free_slotsN lo hi sg t [] with
  | v :: rest =>
      if forallb (Nat.eqb v) rest then
        let t0 := esubst v (ELit 0) t in
        if evar_in v t0 then sg else
        let k := coeff_of v (snd (lin_of t)) in
        match ldivk k (lin_of (mkAlu ALU_SUB r t0)) with
        | Some l => sg ++ [(N.of_nat v, unlin l)]
        | None => sg
        end
      else sg
  | [] => sg
  end.
Lemma solve1N_eq : forall lo hi sg r t1, solve1N (N.of_nat lo) (N.of_nat hi) (toN sg) r t1 = toN (solve1 lo hi sg r t1).
Proof.
  intros. unfold solve1N, solve1. cbv zeta. rewrite esubstsN_eq, free_slotsN_eq.
  destruct (free_slots lo hi sg (esubsts sg t1) []) as [|v rest]; [reflexivity|].
  destruct (forallb (Nat.eqb v) rest); [|reflexivity].
  destruct (evar_in v _); [reflexivity|].
  destruct (ldivk _ _); [|reflexivity]. rewrite toN_app. reflexivity.
Qed.
Fixpoint match_linN (lo hi : N) (rs ts : list expr) (sg : sbindN) : sbindN :=
  match rs, ts with
  | r :: rs', t :: ts' => match_linN lo hi rs' ts' (match t with EVar _ => sg | ELit _ => sg | _ => solve1N lo hi sg r t end)
  | _, _ => sg
  end.
Lemma match_linN_eq : forall lo hi rs ts sg,
  match_linN (N.of_nat lo) (N.of_nat hi) rs ts (toN sg) = toN (match_lin lo hi rs ts sg).
Proof.
  intros lo hi rs. induction rs as [|r rs' IH]; intros ts sg; [destruct ts; reflexivity|].
  destruct ts as [|t ts']; [reflexivity|]. cbn [match_linN match_lin].
  destruct t; rewrite ?solve1N_eq; apply IH.
Qed.
Fixpoint match_kwordsIN (lo hi : N) (ix : kwix) (tk : list kentry) (sg : sbindN) : sbindN :=
  match tk with
  | [] => sg
  | KWord a w (EVar v) :: rest =>
      let vn := N.of_nat v in
      let sg' :=
        if slotbN lo hi vn then
          match sg_getN sg vn with
          | Some _ => sg
          | None =>
              match free_slotsN lo hi sg (a_base a) [] with
              | [] => match find_kwordI ix (asubstsN sg a) w with Some e => sg ++ [(vn, e)] | None => sg end
              | _ => sg
              end
          end
        else sg in
      match_kwordsIN lo hi ix rest sg'
  | KWord a w t :: rest =>
      let sg' := match free_slotsN lo hi sg (a_base a) [] with
                 | [] => match find_kwordI ix (asubstsN sg a) w with Some e => solve1N lo hi sg e t | None => sg end
                 | _ => sg
                 end in
      match_kwordsIN lo hi ix rest sg'
  | _ :: rest => match_kwordsIN lo hi ix rest sg
  end.
Lemma asubstsN_eq : forall sg a, asubstsN (toN sg) a = asubsts sg a.
Proof. intros. unfold asubstsN, asubsts. rewrite esubstsN_eq. reflexivity. Qed.
Lemma match_kwordsIN_eq : forall lo hi ix tk sg,
  match_kwordsIN (N.of_nat lo) (N.of_nat hi) ix tk (toN sg) = toN (match_kwordsI lo hi ix tk sg).
Proof.
  intros lo hi ix tk. induction tk as [|K rest IH]; intros sg; [reflexivity|].
  destruct K as [a w t| | | | | | | | |]; cbn [match_kwordsIN match_kwordsI]; try apply IH.
  destruct t; rewrite ?slotbN_eq, ?sg_getN_eq, ?free_slotsN_eq, ?asubstsN_eq;
    try (destruct (free_slots lo hi sg (a_base a) []); [|apply IH];
         destruct (find_kwordI ix (asubsts sg a) w); [|apply IH]; rewrite solve1N_eq; apply IH).
  destruct (slotb lo hi n); [|apply IH]. destruct (sg_get sg n); [apply IH|].
  destruct (free_slots lo hi sg (a_base a) []); [|apply IH].
  destruct (find_kwordI ix (asubsts sg a) w); [|apply IH]. rewrite <- IH, toN_app. reflexivity.
Qed.
Definition infer_sgN (lo hi : nat) (hints : sbind) (cs inv : acs) : sbind :=
  let rs := s_regs (a_ss cs) in
  let ts := s_regs (a_ss inv) in
  let lon := N.of_nat lo in let hin := N.of_nat hi in
  let sg1 := match_bareN lon hin rs ts (toN hints) in
  let sg2 := match_linN lon hin rs ts sg1 in
  fromN (match_kwordsIN lon hin (kw_build (kn cs) 1%positive) (kn inv) sg2).
Lemma infer_sgN_eq : forall lo hi hints cs inv, infer_sgN lo hi hints cs inv = infer_sgI lo hi hints cs inv.
Proof.
  intros. unfold infer_sgN, infer_sgI. cbv zeta. rewrite match_bareN_eq, match_linN_eq, match_kwordsIN_eq. apply fromN_toN.
Qed.

Definition entails_sM (lo hi : nat) (hints : sbind) (cs inv : acs) : option sbind :=
  let sg := infer_sgN lo hi hints cs inv in   (* [comment removed for export] *)
  if sg_dom_in lo hi sg then
    (let k := kn cs in
     if entails_tB (kn_ix k) (AX2B.mkbc k) cs (instsN sg inv) then Some sg else None)   (* [comment removed for export] *)
  else None.
Lemma entails_sM_eq : entails_sM = entails_s.
Proof.
  apply functional_extensionality; intros lo. apply functional_extensionality; intros hi.
  apply functional_extensionality; intros hints. apply functional_extensionality; intros cs. apply functional_extensionality; intros inv.
  unfold entails_sM, entails_s. rewrite infer_sgN_eq, infer_sgI_eq. cbv zeta. rewrite instsN_eq, entails_tB_eq. destruct (sg_dom_in lo hi _); [|reflexivity]. cbn [andb]. reflexivity.
Qed.
End WithSegs.
End APW.
