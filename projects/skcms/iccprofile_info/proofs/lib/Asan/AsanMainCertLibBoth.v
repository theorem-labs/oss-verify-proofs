(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsFuzzContract.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanFO BothAsanPlanImages AsanInit
  AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanMainHooksBoth AsanMainDefsBoth AsanMainTreeBoth.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition KCm : nat := 0.
Definition BFUELm : nat := 400000.
Definition FUELm : nat := 5000.

(* [comment removed for export] *)
Definition mrun (HS : nat -> option acs) (h : nat) (IT : itab) (C : class) (p : plan) : cres :=
  APF.check ASEGS IT INFO_BOTH NX0 AsanInit.LIMIT (XNm ASEGS INFO_BOTH NX0 RPN.RP_BOTH (iotab_of C)) (XEm ASEGS INFO_BOTH NX0)
            (XBm ASEGS NX0 (iotab_of C)) HS_none KCm BFUELm FUELm None (main_start HS h C) p.
Definition mrun_from (IT : itab) (C : class) (cs : acs) (p : plan) : cres :=
  APF.check ASEGS IT INFO_BOTH NX0 AsanInit.LIMIT (XNm ASEGS INFO_BOTH NX0 RPN.RP_BOTH (iotab_of C)) (XEm ASEGS INFO_BOTH NX0)
            (XBm ASEGS NX0 (iotab_of C)) HS_none KCm BFUELm FUELm None cs p.
(* [comment removed for export] *)
Definition errst (r : cres) : acs := match r with CErr _ _ cs => cs | COk _ => asan_init end.
(* [comment removed for export] *)
Definition ok_child (C : class) (cs : acs) : acs :=
  match XBm ASEGS NX0 (iotab_of C) 0 [] cs with Some (_, b) => b | None => cs end.
(* [comment removed for export] *)
Definition vstA (er : expr) (mid : Z) (cs : acs) : acs := set_kn cs (KRange er (fst (ebounds (kn cs) er)) mid :: kn cs).
Definition vstB (er : expr) (mid : Z) (cs : acs) : acs := set_kn cs (KRange er (mid + 1) (snd (ebounds (kn cs) er)) :: kn cs).
Definition vmeet (cs0 ca cb : acs) : acs :=
  match node_diamond_join INFO_BOTH NX0 (nxt cs0) (pc ca) [] ca cb with Some js => js | None => asan_init end.
(* [comment removed for export] *)
Definition kn_meet2 (k0 k1 : list kentry) : list kentry := List.filter (fun K => existsb (kentry_eqb K) k1) k0.
Definition acs_meet (a b : acs) : option acs :=
  if (Z.eqb (pc a) (pc b)
      && list_eqb expr_eqb (s_regs (a_ss a)) (s_regs (a_ss b))
      && list_eqb amap_eqb (a_maps a) (a_maps b)
      && list_eqb pair_eqb (a_vis a) (a_vis b)
      && list_eqb pair_eqb (a_ghost a) (a_ghost b)
      && expr_eqb (a_brk a) (a_brk b)
      && afd_eqb (a_fd a) (a_fd b)
      && Bool.eqb (a_tidset a) (a_tidset b))%bool
  then Some (ACS (mk_ss (pc a) (s_regs (a_ss a)) (kn_meet2 (kn a) (kn b)) (Nat.max (nxt a) (nxt b)))
                (a_maps a) (Z.max (a_totsz a) (a_totsz b)) (Z.min (a_ylo a) (a_ylo b)) (Z.max (a_eager a) (a_eager b))
                (a_vis a) (a_ghost a) (Z.max (a_abytes a) (a_abytes b)) (a_brk a) (a_fd a) (a_tidset a))
  else None.
Fixpoint meet_list (l : list acs) : option acs :=
  match l with [] => None | [a] => Some a | a :: r => match meet_list r with Some m => acs_meet a m | None => None end end.
Definition meet_list_d (d : acs) (l : list acs) : acs := match meet_list l with Some m => m | None => d end.
(* [comment removed for export] *)
Definition meet_diag (a b : acs) :=
  (Z.eqb (pc a) (pc b), list_eqb expr_eqb (s_regs (a_ss a)) (s_regs (a_ss b)), list_eqb amap_eqb (a_maps a) (a_maps b),
   list_eqb pair_eqb (a_vis a) (a_vis b), list_eqb pair_eqb (a_ghost a) (a_ghost b), expr_eqb (a_brk a) (a_brk b),
   afd_eqb (a_fd a) (a_fd b), Bool.eqb (a_tidset a) (a_tidset b),
   map fst (List.filter (fun x => negb (expr_eqb (fst (snd x)) (snd (snd x)))) (combine (seq 0 32) (combine (s_regs (a_ss a)) (s_regs (a_ss b)))))).
(* [comment removed for export] *)
Fixpoint seq_end (p q : plan) : plan :=
  match p with
  | PRun s k => PRun s (seq_end k q)
  | PX x a k => PX x a (seq_end k q)
  | PExt i a k => PExt i a (seq_end k q)
  | PEmit i a k => PEmit i a (seq_end k q)
  | PFresh r l b k => PFresh r l b (seq_end k q)
  | PFact K k => PFact K (seq_end k q)
  | PJoin b o n k => PJoin b o n (seq_end k q)
  | PRespell r e k => PRespell r e (seq_end k q)
  | PShDisj a b c d k => PShDisj a b c d (seq_end k q)
  | PDisjDia b1 b2 o j rs k => PDisjDia b1 b2 o j rs (seq_end k q)
  | PMmap a k => PMmap a (seq_end k q)
  | PMmapIn a k c => PMmapIn a (seq_end k q) c
  | PExt2 i a k1 k2 => PExt2 i a (seq_end k1 q) (seq_end k2 q)
  | PCase2 e m k1 k2 => PCase2 e m (seq_end k1 q) (seq_end k2 q)
  | PSplit e m k1 k2 => PSplit e m (seq_end k1 q) (seq_end k2 q)
  | PDiamond j rs k => PDiamond j rs (seq_end k q)
  | PForget ixs k => PForget ixs (seq_end k q)
  | PGcKeep ws k => PGcKeep ws (seq_end k q)
  | PBump m k => PBump m (seq_end k q)
  | PHavoc rs k => PHavoc rs (seq_end k q)   (* [comment removed for export] *)
  | PHavocWords bs k => PHavocWords bs (seq_end k q)
  | PCaseDisjO b1 b2 o k1 k2 => PCaseDisjO b1 b2 o (seq_end k1 q) (seq_end k2 q)
  | PAbstractCell b n k => PAbstractCell b n (seq_end k q)
  | PWordFresh b n k => PWordFresh b n (seq_end k q)
  | PDropRange b n k => PDropRange b n (seq_end k q)
  | PContra => q
  | other => other
  end.
(* [comment removed for export] *)
Definition flen_find (lo hi : Z) (k : list kentry) : expr :=
  match find (fun K => match K with KRange (EVar _) a b => (Z.eqb a lo && Z.eqb b hi)%bool | _ => false end) k with
  | Some (KRange e _ _) => e | _ => ELit 0 end.
(* [comment removed for export] *)
Fixpoint disj_ixs (i : nat) (k : list kentry) : list nat :=
  match k with [] => [] | K :: r => match K with KDisj _ _ _ _ => i :: disj_ixs (S i) r | _ => disj_ixs (S i) r end end.

(* [comment removed for export] *)
Section PreB.
  Variables KC BF FU : nat.
  Definition seg_ok_b (IT : itab) (ch : acs) (C : class) (L : nat) (p : plan) (HT : list (nat * (nat * acs))) : bool :=
    match APF.check ASEGS IT INFO_BOTH NX0 AsanInit.LIMIT (XNm ASEGS INFO_BOTH NX0 RPN.RP_BOTH (iotab_of C)) (XEm ASEGS INFO_BOTH NX0)
                    (XBm ASEGS NX0 (iotab_of C)) (hs_of HT) KC BF FU None (pay_start ch C) p with
    | COk s => AsanShape.class_seg_ok (lv_of HT) L C s
    | CErr _ _ _ => false
    end.
  Lemma mtree_ok_pre_b : forall IT lo hi ch C L p HT PT,
    (Nat.leb lo L && Nat.leb L hi)%bool = true -> seg_ok_b IT ch C L p HT = true -> mcover HT PT = true ->
    mforest_ok KC BF FU IT L HT C PT = true -> mtree_ok KC BF FU IT lo hi ch C (MPre L p HT PT) = true.
  Proof.
    intros IT lo hi ch C L p HT PT HL HS HC HF. rewrite mtree_ok_MPre. unfold seg_ok_b in HS.
    destruct (APF.check _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) as [s|]; [|discriminate HS].
    rewrite HL, HS, HC, HF. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma mforest_ok_one : forall IT L lv S C t,
    mtree_ok KC BF FU IT (Nat.max L 1) lv S C t = true -> mforest_ok KC BF FU IT L [(0%nat, (lv, S))] C [(0%nat, t)] = true.
  Proof. intros IT L lv S C t H. eapply mforest_ok_cons; [reflexivity | exact H | apply mforest_ok_nil]. Qed.
End PreB.
