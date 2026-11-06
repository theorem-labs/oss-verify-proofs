(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AzSymExec3 AzSymExec3B AzPlan AzNodesArith GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
#[local] Notation "a || b" := (if a then true else b) (at level 50, left associativity, only parsing) : bool_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive smode : Type := MS | ML.

Definition hole (m : smode) : nat := match m with MS => 0%nat | ML => 1%nat end.
(* [comment removed for export] *)
Definition strS (obj s : expr) : list kentry := [ KWord (SA obj 0) 1 (escale 2 s); KRange s 0 22 ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record gtable : Type := GT {
  g_ro_lo : Z; g_ro_hi : Z;        (* [comment removed for export] *)
  g_img_lo : Z; g_img_hi : Z;      (* [comment removed for export] *)
  g_newh_got : Z; g_newh_cell : Z; g_newh_val : Z;
                                   (* [comment removed for export] *)
  g_priv : list (Z * Z);           (* [comment removed for export] *)
  g_tp : Z;                        (* [comment removed for export] *)
  g_errno : Z;                     (* [comment removed for export] *)
  g_malloc : Z; g_free : Z;        (* [comment removed for export] *)
  g_malloc_thunk : Z; g_free_thunk : Z;   (* [comment removed for export] *)
  g_opnew : Z; g_opdel : Z; g_opdel_sized : Z;   (* [comment removed for export] *)
  g_memcpy : Z; g_memset : Z; g_memmove : Z; g_strlen : Z;
  g_hello : Z;                      (* [comment removed for export] *)
  g_str_resize : Z;                 (* [comment removed for export] *)
  g_amemcpy : Z; g_amemset : Z; g_amemmove : Z;  (* [comment removed for export] *)
  g_stkmal : Z -> Z;                              (* [comment removed for export] *)
  g_opnew_kn : list kentry                        (* [comment removed for export] *)
}.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition errw (G : gtable) (z : Z) : Prop := g_errno G <= z < g_errno G + 4.
Definition g_privx (G : gtable) : list (Z * Z) := (g_errno G, g_errno G + 4) :: g_priv G.
Lemma errw_dec : forall G z, {errw G z} + {~ errw G z}.
Proof.
  intros G z. unfold errw. destruct (Z_lt_le_dec z (g_errno G)) as [H|H]; [right; lia|].
  destruct (Z_lt_le_dec z (g_errno G + 4)) as [H'|H']; [left; lia | right; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition MSTK : Z := 2048.                (* [comment removed for export] *)
Definition MSTK_F : Z := 256.               (* [comment removed for export] *)
Definition MSTK_A : Z := 3584.              (* [comment removed for export] *)
Definition MSTK_N : Z := 3600.              (* [comment removed for export] *)
Definition FAKEMAX : Z := 2 ^ 20.           (* [comment removed for export] *)
Definition FMIN : Z := 2 ^ 11.              (* [comment removed for export] *)
Definition NMAX : Z := 2 ^ 40.              (* [comment removed for export] *)
Definition MBLK : Z := 2 ^ 20 + 2 ^ 13.     (* [comment removed for export] *)
Definition mcost (nhi : Z) : Z := nhi + MBLK.   (* [comment removed for export] *)
Definition MCNT : Z := 1.                   (* [comment removed for export] *)
Definition LMAX : Z := 64.
                 (* [comment removed for export] *)
Definition GBUDGET : Z := 3 * 2 ^ 32.       (* [comment removed for export] *)
Definition GCOUNT : Z := LMAX.               (* [comment removed for export] *)
(* [comment removed for export] *)
Definition EVT : Z := 2 ^ 28.                (* [comment removed for export] *)
Definition kcost (nhi : Z) : Z := EVT.          (* [comment removed for export] *)
Definition KFREE : Z := EVT.                (* [comment removed for export] *)
Definition GKCAP : Z := 2 ^ 39.             (* [comment removed for export] *)
(* [comment removed for export] *)
Definition SHMAPLO : Z := 0x7fff7000.
Definition SHMAPLEN : Z := KHI - SHMAPLO.




Definition ID_STRLEN : nat := 4.
Definition ID_AMEMCPY : nat := 5.

Definition ID_AMEMMOVE : nat := 7.









   (* [comment removed for export] *)

Section WithTables.
Variable segs : list MemImageType.Segment.
Variable IT : itab.
Variable A : atable.
Variable nx0 : nat.
Variable G : gtable.
Variable bcap ccap : Z.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition load_range_fact (sz : msize) (sx : bool) (v : nat) : list kentry :=
  match sz, sx with
  | SZ1, false => [KRange (EVar v) 0 255]
  | SZ2, false => [KRange (EVar v) 0 65535]
  | SZ4, false => [KRange (EVar v) 0 4294967295]
  | _, _ => []
  end.

(* [comment removed for export] *)
Definition node_imgload (cs : acs) : option acs :=
  match itab_lookup IT (pc cs) with
  | Some (Load sz sx rd rs imm) =>
      let n := msize_bytes sz in
      let a := eaddz (sr_get (s_regs (a_ss cs)) rs) (bv_signed imm) in
      match xlo (kn cs) a, xhi (kn cs) a with
      | Some lo, Some hi =>
          if (fresh_ok nx0 cs && Z.leb (g_ro_lo G) lo && Z.leb (hi + Z.of_nat n) (g_ro_hi G) && negb (bv_eqb rd 0%bv)
              && Z.leb 0 (pc cs) && Z.ltb (pc cs + 4) two64
              && Nat.eqb (length (s_regs (a_ss cs))) 32)%bool
          then let v := nxt cs in
               let ss := a_ss cs in
               Some (with_ss cs (mk_ss (pc cs + 4) (sr_upd (s_regs ss) (ridx rd) (EVar v))
                                       (load_range_fact sz sx v ++ s_know ss) (S v)))
          else None
      | _, _ => None
      end
  | Some _ => Some cs      (* [comment removed for export] *)
  | None => Some cs
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kentry_range (K : kentry) : option (expr * Z * expr) :=
  match K with
  | KWord (SA b k) w _ => Some (b, k, ELit (Z.of_nat w))
  | KZero (SA b k) n | KBlob (SA b k) n _ | KWr (SA b k) n | KFill (SA b k) n _ | KUnk (SA b k) n => Some (b, k, n)
  | _ => None
  end.

Fixpoint lit_disjoint (lo hi : Z) (ps : list (Z * Z)) : bool :=
  match ps with
  | [] => true
  | (a, b) :: r => ((hi <=? a) || (b <=? lo)) && lit_disjoint lo hi r
  end%bool.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition owned_x (k : list kentry) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (b : expr) (off : Z) (n : expr) : bool :=
  existsb (fun bl => let '(lb, lk) := split_lit (fst bl) in xinside k b off n lb lk (snd bl)) live
  || in_floor k fl top bud b off n.

(* [comment removed for export] *)
Definition top_ok (k : list kentry) (fl : option expr) (top : expr) (bud : Z) : bool :=
  let '(tb, tk) := split_lit top in
  match base_range k tb with
  | Some (tlo, thi) =>
      match fl with
      | None => (Z.leb 0 bud && Z.leb CEIL (tlo + tk - bud) && Z.ltb (thi + tk) two64)%bool
      | Some _ => (Z.leb 0 bud && Z.ltb 0 (tlo + tk) && Z.ltb (thi + tk) two64)%bool
      end
  | None => false
  end.
(* [comment removed for export] *)
Definition floor_term (fl : option expr) (top : expr) (bud : Z) : expr * Z :=
  match fl with Some f => (f, 0) | None => let '(tb, tk) := split_lit top in (tb, tk - bud) end.
(* [comment removed for export] *)
Definition stack_x (k : list kentry) (fl : option expr) (top : expr) (bud : Z) (e : expr) : bool :=
  top_ok k fl top bud && lin_ge0 k [(e, 0)] [floor_term fl top bud].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition send_hi (k : list kentry) (b : expr) (off : Z) (n : expr) (dflt : Z) : Z :=
  if match b, n with ELit _, ELit _ => true | _, _ => false end then dflt
  else match xrange2 k (eadd (eaddz b off) n) with Some (_, j) => Z.min j dflt | None => dflt end.
Definition srange_x (k : list kentry) (fl : option expr) (top : expr) (bud : Z) (b : expr) (off : Z) (n : expr) : bool :=
  top_ok k fl top bud && lin_ge0 k [(b, off)] [floor_term fl top bud]
  && match base_range k b, xhi k n with
     | Some (blo, bhi), Some nh => Z.leb 0 (blo + off) && Z.leb 0 nh && Z.ltb (bhi + off + nh) two64
                                   && Z.leb (send_hi k b off n (bhi + off + nh)) two47
     | _, _ => false
     end.

(* [comment removed for export] *)
Definition bflat_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match base_range k b, xhi k n with
  | Some (lo, hi), Some nh => Z.leb 0 (lo + off) && Z.ltb (hi + off) two64 && Z.leb (hi + off + nh) two64
  | _, _ => false
  end%bool.
(* [comment removed for export] *)
Definition owned_sp_x (k : list kentry) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (b : expr) (off : Z) (n : expr) : bool :=
  existsb (fun bl => let '(lb, lk) := split_lit (fst bl) in xinside k b off n lb lk (snd bl)) live
  || (in_floor k fl top bud b off n && lin_ge0 k [(b, off)] [(sp, 0)]).
(* [comment removed for export] *)
Definition live_flat (cs : acs) : bool :=
  forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x (kn cs) lb lk (snd bl)) (a_vis cs ++ a_fake cs ++ a_ghost cs).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition above_x (k : list kentry) (top sp : expr) (b : expr) (off : Z) (n : expr) : bool :=
  match xlo k top with
  | Some tlo => Z.ltb 0 tlo && lin_ge0 k [(b, off)] [(top, 0)] && lin_ge0 k [(top, 0)] [(sp, 0)] && flat_x k b off n
  | None => false
  end%bool.
Definition keep_sticky (k : list kentry) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (K : kentry) : bool :=
  match K with
  | KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ => true
  | KImg lo hi => Z.leb (g_ro_lo G) lo && Z.leb hi (g_img_hi G) && lit_disjoint lo hi (g_privx G)   (* [comment removed for export] *)
  | KWr (SA b off) n | KUnk (SA b off) n => owned_x k live fl top bud b off n || above_x k top sp b off n   (* [comment removed for export] *)
  | _ => false
  end%bool.
(* [comment removed for export] *)
Definition img_lit_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match xlo k (eaddz b off), xhi k (eaddz b off), xhi k n with
  | Some lo, Some hi, Some nh => Z.leb (g_ro_lo G) lo && Z.leb (hi + nh) (g_img_hi G) && Z.leb 0 nh && lit_disjoint lo (hi + nh) (g_privx G)   (* [comment removed for export] *)
  | _, _, _ => false
  end%bool.
(* [comment removed for export] *)
Definition above_sp (k : list kentry) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (b : expr) (off : Z) (n : expr) : bool :=
  let '(spb, spk) := split_lit sp in
  (stack_x k fl top bud sp
   && (xinside k b off n spb spk (ELit two47) || xinside0 k b off n spb spk (ELit two47)))%bool.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shadow_kept (k : list kentry) (objs : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (b : expr) (off : Z) (n : expr) : bool :=
  match srl3_base b, n with
  | Some xb, ELit nn =>
      Z.leb 3 (ealign k xb) && Z.leb 0 nn
      && ((Z.leb SB off && Z.ltb nn (2 ^ 43) && srange_x k fl top bud xb (8 * (off - SB)) (ELit (8 * nn)))
          || shadow_objs_x k objs xb off nn)
  | _, _ => false
  end%bool.
(* [comment removed for export] *)
Definition ishadow_lit_x (b : expr) (off : Z) (n : expr) : bool :=
  match b, n with
  | ELit 0, ELit nn => Z.leb (SB + g_ro_lo G / 8) off && Z.leb 0 nn && Z.leb (off + nn) (SB + g_img_hi G / 8)
  | _, _ => false
  end%bool.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition keep_shadow (k : list kentry) (objs : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b off) w _ => shadow_kept k objs fl top bud b off (ELit (Z.of_nat w)) || ishadow_lit_x b off (ELit (Z.of_nat w))
  | KZero (SA b off) n | KFill (SA b off) n _ | KBlob (SA b off) n _ => shadow_kept k objs fl top bud b off n || ishadow_lit_x b off n
  | KWr (SA b off) n | KUnk (SA b off) n => shadow_kept k objs fl top bud b off n || ishadow_lit_x b off n   (* [comment removed for export] *)
  | KShOk (SA b off) n =>
      match xlo k n with Some nl => Z.ltb 0 nl | None => false end
      && (existsb (fun bl => let '(lb, lk) := split_lit (fst bl) in xinside k b off n lb lk (snd bl) && bflat_x k lb lk (snd bl)) objs
          || srange_x k fl top bud b off n        (* [comment removed for export] *)
          || img_lit_x k b off n)
  | _ => false
  end%bool.

(* [comment removed for export] *)
Definition errno_apart_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  (Z.leb 0 (g_errno G) && Z.ltb (g_errno G + 4) two64 && ranges_apart_x k b off n (ELit 0) (g_errno G) (ELit 4))%bool.
Definition keep_content (stk : Z) (k : list kentry) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (K : kentry) : bool :=
  match K with
  | KWord _ _ _ | KZero _ _ | KFill _ _ _ | KBlob _ _ _ =>
      match kentry_range K with
      | Some (b, off, n) =>
          let '(spb, spk) := split_lit sp in
          (owned_x k live fl top bud b off n && ranges_apart_x k b off n spb (spk - stk) (ELit stk) && errno_apart_x k b off n) || above_x k top sp b off n
          || img_lit_x k b off n
      | None => false
      end
  | _ => false
  end%bool.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition keep_kfpc (k : list kentry) (sp : expr) (K : kentry) : bool :=
  match K with KFpc _ lo _ => lin_ge0 k [(lo, 0)] [(sp, 0)] | _ => false end.
Definition keep_owned_ref (stk : Z) (k : list kentry) (live objs : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (v : nat) : list kentry :=
  let '(spb, spk) := split_lit sp in
  List.filter (fun K => kentry_vars_lt v K && keep_sticky k live fl top bud sp K)%bool k
  ++ List.filter (fun K => kentry_vars_lt v K && keep_content stk k live fl top bud sp K)%bool
       (kn_cutout (kn_cutout k spb (spk - stk) (ELit stk)) (ELit 0) (g_errno G) (ELit 4))   (* [comment removed for export] *)
  ++ List.filter (fun K => kentry_vars_lt v K && keep_shadow k objs fl top bud sp K)%bool k      (* [comment removed for export] *)
  ++ List.filter (fun K => kentry_vars_lt v K && keep_kfpc k sp K)%bool k.           (* [comment removed for export] *)
(* [comment removed for export] *)
Definition exists_inside_b (bc : AX2B.bctx) (b : expr) (off : Z) (n : expr) (live : list (expr * expr)) : bool :=
  existsbL (fun bl => let '(lb, lk) := split_lit (fst bl) in AX2B.xinsideB bc b off n lb lk (snd bl)) live.
Lemma exists_inside_b_eq : forall k b off n live,
  exists_inside_b (AX2B.mkbc k) b off n live = existsb (fun bl => let '(lb, lk) := split_lit (fst bl) in xinside k b off n lb lk (snd bl)) live.
Proof. intros. unfold exists_inside_b. rewrite existsbL_eq, AX2B.xinsideB_eqf. reflexivity. Qed.
Definition owned_x_b (bc : AX2B.bctx) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (b : expr) (off : Z) (n : expr) : bool :=
  if exists_inside_b bc b off n live then true else in_floorB bc fl top bud b off n.
Lemma owned_x_b_eq : forall k live fl top bud b off n, owned_x_b (AX2B.mkbc k) live fl top bud b off n = owned_x k live fl top bud b off n.
Proof. intros. unfold owned_x_b, owned_x. rewrite exists_inside_b_eq, in_floorB_eqf. reflexivity. Qed.
Definition above_x_b (bc : AX2B.bctx) (top sp : expr) (b : expr) (off : Z) (n : expr) : bool :=
  match AX2B.xloB bc top with
  | Some tlo => if Z.ltb 0 tlo then (if AX2B.lin_ge0B bc [(b, off)] [(top, 0)] then (if AX2B.lin_ge0B bc [(top, 0)] [(sp, 0)] then flat_xB bc b off n else false) else false) else false
  | None => false
  end.
Lemma above_x_b_eq : forall k top sp b off n, above_x_b (AX2B.mkbc k) top sp b off n = above_x k top sp b off n.
Proof.
  intros. unfold above_x_b, above_x. rewrite AX2B.xloB_eqf, AX2B.lin_ge0B_eqf, flat_xB_eqf.
  destruct (xlo k top) as [tlo|]; [|reflexivity]. destruct (Z.ltb 0 tlo); [|reflexivity]. cbn [andb].
  destruct (lin_ge0 k [(b, off)] [(top, 0)]); [|reflexivity]. cbn [andb]. destruct (lin_ge0 k [(top, 0)] [(sp, 0)]); reflexivity.
Qed.
Definition keep_sticky_b (bc : AX2B.bctx) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (K : kentry) : bool :=
  match K with
  | KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ => true
  | KImg lo hi => Z.leb (g_ro_lo G) lo && Z.leb hi (g_img_hi G) && lit_disjoint lo hi (g_privx G)
  | KWr (SA b off) n | KUnk (SA b off) n => if owned_x_b bc live fl top bud b off n then true else above_x_b bc top sp b off n
  | _ => false
  end%bool.
Lemma keep_sticky_b_eq : forall k live fl top bud sp K, keep_sticky_b (AX2B.mkbc k) live fl top bud sp K = keep_sticky k live fl top bud sp K.
Proof. intros. unfold keep_sticky_b, keep_sticky. destruct K; try reflexivity; destruct a; rewrite owned_x_b_eq, above_x_b_eq; reflexivity. Qed.
Definition img_lit_x_b (bc : AX2B.bctx) (b : expr) (off : Z) (n : expr) : bool :=
  match AX2B.xloB bc (eaddz b off), AX2B.xhiB bc (eaddz b off), AX2B.xhiB bc n with
  | Some lo, Some hi, Some nh => Z.leb (g_ro_lo G) lo && Z.leb (hi + nh) (g_img_hi G) && Z.leb 0 nh && lit_disjoint lo (hi + nh) (g_privx G)
  | _, _, _ => false
  end%bool.
Lemma img_lit_x_b_eq : forall k b off n, img_lit_x_b (AX2B.mkbc k) b off n = img_lit_x k b off n.
Proof. intros. unfold img_lit_x_b, img_lit_x. rewrite AX2B.xloB_eqf, AX2B.xhiB_eqf. reflexivity. Qed.
Definition top_ok_b (bc : AX2B.bctx) (fl : option expr) (top : expr) (bud : Z) : bool :=
  let '(tb, tk) := split_lit top in
  match AX2B.base_rangeB bc tb with
  | Some (tlo, thi) =>
      match fl with
      | None => (Z.leb 0 bud && Z.leb CEIL (tlo + tk - bud) && Z.ltb (thi + tk) two64)%bool
      | Some _ => (Z.leb 0 bud && Z.ltb 0 (tlo + tk) && Z.ltb (thi + tk) two64)%bool
      end
  | None => false
  end.
Lemma top_ok_b_eq : forall k fl top bud, top_ok_b (AX2B.mkbc k) fl top bud = top_ok k fl top bud.
Proof. intros. unfold top_ok_b, top_ok. rewrite AX2B.base_rangeB_eqf. reflexivity. Qed.
Definition stack_x_b (bc : AX2B.bctx) (fl : option expr) (top : expr) (bud : Z) (e : expr) : bool :=
  if top_ok_b bc fl top bud then AX2B.lin_ge0B bc [(e, 0)] [floor_term fl top bud] else false.
Lemma stack_x_b_eq : forall k fl top bud e, stack_x_b (AX2B.mkbc k) fl top bud e = stack_x k fl top bud e.
Proof. intros. unfold stack_x_b, stack_x. rewrite top_ok_b_eq, AX2B.lin_ge0B_eqf. reflexivity. Qed.
Definition above_sp_b (bc : AX2B.bctx) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (b : expr) (off : Z) (n : expr) : bool :=
  let '(spb, spk) := split_lit sp in
  if stack_x_b bc fl top bud sp
  then (if AX2B.xinsideB bc b off n spb spk (ELit two47) then true else AX2B.xinside0B bc b off n spb spk (ELit two47)) else false.
Lemma above_sp_b_eq : forall k fl top bud sp b off n, above_sp_b (AX2B.mkbc k) fl top bud sp b off n = above_sp k fl top bud sp b off n.
Proof. intros. unfold above_sp_b, above_sp. rewrite stack_x_b_eq, AX2B.xinsideB_eqf, AX2B.xinside0B_eqf. destruct (split_lit sp). reflexivity. Qed.
Definition keep_content_b (bc : AX2B.bctx) (stk : Z) (k : list kentry) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (K : kentry) : bool :=
  match K with
  | KWord _ _ _ | KZero _ _ | KFill _ _ _ | KBlob _ _ _ =>
      match kentry_range K with
      | Some (b, off, n) =>
          let '(spb, spk) := split_lit sp in
          if (if (if (if owned_x_b bc live fl top bud b off n then AX2B.ranges_apart_xB bc b off n spb (spk - stk) (ELit stk) else false)
                  then (0 <=? g_errno G) && (g_errno G + 4 <? two64) && AX2B.ranges_apart_xB bc b off n (ELit 0) (g_errno G) (ELit 4) else false)
              then true else above_x_b bc top sp b off n)
          then true else img_lit_x_b bc b off n
      | None => false
      end
  | _ => false
  end%bool.
Lemma keep_content_b_eq : forall stk k live fl top bud sp K,
  keep_content_b (AX2B.mkbc k) stk k live fl top bud sp K = keep_content stk k live fl top bud sp K.
Proof.
  intros. unfold keep_content_b, keep_content, errno_apart_x.
  destruct K; try reflexivity; (destruct (kentry_range _) as [[[b off] nn]|]; [|reflexivity]); destruct (split_lit sp) as [spb spk];
    rewrite owned_x_b_eq, above_x_b_eq, img_lit_x_b_eq, !AX2B.ranges_apart_xB_eqf; destruct (owned_x k live fl top bud b off nn); reflexivity.
Qed.
Definition keep_kfpc_b (bc : AX2B.bctx) (sp : expr) (K : kentry) : bool :=
  match K with KFpc _ lo _ => AX2B.lin_ge0B bc [(lo, 0)] [(sp, 0)] | _ => false end.
Lemma keep_kfpc_b_eq : forall k sp K, keep_kfpc_b (AX2B.mkbc k) sp K = keep_kfpc k sp K.
Proof. intros. unfold keep_kfpc_b, keep_kfpc. rewrite AX2B.lin_ge0B_eqf. reflexivity. Qed.
(* [comment removed for export] *)
Definition send_hi_b (bc : AX2B.bctx) (b : expr) (off : Z) (n : expr) (dflt : Z) : Z :=
  if match b, n with ELit _, ELit _ => true | _, _ => false end then dflt
  else match AX2B.xrange2B bc (eadd (eaddz b off) n) with Some (_, j) => Z.min j dflt | None => dflt end.
Lemma send_hi_b_fe : forall k, send_hi_b (AX2B.mkbc k) = send_hi k.
Proof. intros. do 4 (apply FunctionalExtensionality.functional_extensionality; intro). unfold send_hi_b, send_hi. rewrite AX2B.xrange2B_eqf. reflexivity. Qed.
Definition srange_x_b (bc : AX2B.bctx) (fl : option expr) (top : expr) (bud : Z) (b : expr) (off : Z) (n : expr) : bool :=
  if (if top_ok_b bc fl top bud then AX2B.lin_ge0B bc [(b, off)] [floor_term fl top bud] else false)
  then match AX2B.base_rangeB bc b, AX2B.xhiB bc n with
       | Some (blo, bhi), Some nh => if (Z.leb 0 (blo + off) && Z.leb 0 nh && Z.ltb (bhi + off + nh) two64)%bool
                                    then Z.leb (send_hi_b bc b off n (bhi + off + nh)) two47 else false
       | _, _ => false
       end
  else false.
Lemma srange_x_b_fe : forall k, srange_x_b (AX2B.mkbc k) = srange_x k.
Proof.
  intros. do 6 (apply FunctionalExtensionality.functional_extensionality; intro). unfold srange_x_b, srange_x.
  rewrite top_ok_b_eq, AX2B.lin_ge0B_eqf, AX2B.base_rangeB_eqf, AX2B.xhiB_eqf, send_hi_b_fe. reflexivity.
Qed.
Definition bflat_x_b (bc : AX2B.bctx) (b : expr) (off : Z) (n : expr) : bool :=
  match AX2B.base_rangeB bc b, AX2B.xhiB bc n with
  | Some (lo, hi), Some nh => Z.leb 0 (lo + off) && Z.ltb (hi + off) two64 && Z.leb (hi + off + nh) two64
  | _, _ => false
  end%bool.
Lemma bflat_x_b_fe : forall k, bflat_x_b (AX2B.mkbc k) = bflat_x k.
Proof. intros. do 3 (apply FunctionalExtensionality.functional_extensionality; intro). unfold bflat_x_b, bflat_x. rewrite AX2B.base_rangeB_eqf, AX2B.xhiB_eqf. reflexivity. Qed.
Lemma shadow_objs_xB_fe : forall k, shadow_objs_xB (AX2B.mkbc k) = shadow_objs_x k.
Proof. intros. do 4 (apply FunctionalExtensionality.functional_extensionality; intro). unfold shadow_objs_xB, shadow_objs_x. rewrite AX2B.xloB_eqf, AX2B.base_rangeB_eqf. reflexivity. Qed.
Definition shadow_kept_b (bc : AX2B.bctx) (objs : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (b : expr) (off : Z) (n : expr) : bool :=
  match srl3_base b, n with
  | Some xb, ELit nn =>
      if (Z.leb 3 (AX2B.ealignB bc xb) && Z.leb 0 nn)%bool
      then ((if (Z.leb SB off && Z.ltb nn (2 ^ 43))%bool then srange_x_b bc fl top bud xb (8 * (off - SB)) (ELit (8 * nn)) else false)
            || shadow_objs_xB bc objs xb off nn)
      else false
  | _, _ => false
  end%bool.
Lemma shadow_kept_b_fe : forall k, shadow_kept_b (AX2B.mkbc k) = shadow_kept k.
Proof.
  intros. do 7 (apply FunctionalExtensionality.functional_extensionality; intro). unfold shadow_kept_b, shadow_kept.
  rewrite AX2B.ealignB_eqf, srange_x_b_fe, shadow_objs_xB_fe. reflexivity.
Qed.
Lemma img_lit_x_b_fe : forall k, img_lit_x_b (AX2B.mkbc k) = img_lit_x k.
Proof. intros. do 3 (apply FunctionalExtensionality.functional_extensionality; intro). apply img_lit_x_b_eq. Qed.
Definition keep_shadow_b (bc : AX2B.bctx) (objs : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b off) w _ => shadow_kept_b bc objs fl top bud b off (ELit (Z.of_nat w)) || ishadow_lit_x b off (ELit (Z.of_nat w))
  | KZero (SA b off) n | KFill (SA b off) n _ | KBlob (SA b off) n _ => shadow_kept_b bc objs fl top bud b off n || ishadow_lit_x b off n
  | KWr (SA b off) n | KUnk (SA b off) n => shadow_kept_b bc objs fl top bud b off n || ishadow_lit_x b off n
  | KShOk (SA b off) n =>
      if match AX2B.xloB bc n with Some nl => Z.ltb 0 nl | None => false end
      then (AX2B.existsb_lz (fun bl => let '(lb, lk) := split_lit (fst bl) in
                                       if AX2B.xinsideB bc b off n lb lk (snd bl) then bflat_x_b bc lb lk (snd bl) else false) objs
            || srange_x_b bc fl top bud b off n
            || img_lit_x_b bc b off n)
      else false
  | _ => false
  end%bool.
Lemma keep_shadow_b_eq : forall k objs fl top bud sp K, keep_shadow_b (AX2B.mkbc k) objs fl top bud sp K = keep_shadow k objs fl top bud sp K.
Proof.
  intros. unfold keep_shadow_b, keep_shadow.
  rewrite shadow_kept_b_fe, AX2B.xloB_eqf, AX2B.xinsideB_eqf, bflat_x_b_fe, srange_x_b_fe, img_lit_x_b_fe. reflexivity.
Qed.
Definition keep_owned (stk : Z) (k : list kentry) (live objs : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (v : nat) : list kentry :=
  let '(spb, spk) := split_lit sp in
  let bc := AX2B.mkbc k in
  List.filter (fun K => if kentry_vars_lt v K then keep_sticky_b bc live fl top bud sp K else false) k
  ++ List.filter (fun K => if kentry_vars_lt v K then keep_content_b bc stk k live fl top bud sp K else false)
       (kn_cutoutM (kn_cutoutM k spb (spk - stk) (ELit stk)) (ELit 0) (g_errno G) (ELit 4))
  ++ List.filter (fun K => if kentry_vars_lt v K then keep_shadow_b bc objs fl top bud sp K else false) k   (* [comment removed for export] *)
  ++ List.filter (fun K => if kentry_vars_lt v K then keep_kfpc_b bc sp K else false) k.
Lemma keep_owned_eq : forall stk k live objs fl top bud sp v,
  keep_owned stk k live objs fl top bud sp v = keep_owned_ref stk k live objs fl top bud sp v.
Proof.
  intros. unfold keep_owned, keep_owned_ref. destruct (split_lit sp) as [spb spk]. cbv zeta. rewrite !kn_cutoutM_eq.
  f_equal; [apply filter_ext; intros K; rewrite keep_sticky_b_eq; destruct (kentry_vars_lt v K); reflexivity|].
  f_equal; [apply filter_ext; intros K; rewrite keep_content_b_eq; destruct (kentry_vars_lt v K); reflexivity|].
  f_equal; [apply filter_ext; intros K; rewrite keep_shadow_b_eq; destruct (kentry_vars_lt v K); reflexivity|].
  apply filter_ext; intros K; rewrite keep_kfpc_b_eq; destruct (kentry_vars_lt v K); reflexivity.
Qed.

(* [comment removed for export] *)
Definition ret_regs (sr : list expr) (nx : nat) (rv : option expr) : list expr :=
  let sr1 := sr_fresh sr caller_saved nx in
  match rv with Some e => sr_upd sr1 10 e | None => sr1 end.

(* [comment removed for export] *)
Definition call_ok_stk (stk : Z) (entry : Z) (cs : acs) : option Z :=
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs, reg_lit cs 4 with
  | Some ret, Some tp =>
      let k := kn cs in let sp := reg cs 2 in let '(spb, spk) := split_lit sp in
      if (Z.eqb tp (g_tp G) && fresh_ok nx0 cs && Nat.eqb (length (s_regs (a_ss cs))) 32
          && Z.leb 4 (ealign k sp) && kwritable_x k k spb (spk - stk) (ELit stk)
          && in_floor k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) spb (spk - stk) (ELit stk)     (* [comment removed for export] *)
          && match xhi k sp with Some hi => Z.leb (hi + 16) two47 | None => false end   (* [comment removed for export] *)
          && live_flat cs)%bool
      then Some ret else None
  | _, _ => None
  end.


(* [comment removed for export] *)
Fixpoint cost_hi (k : list kentry) (live : list (expr * expr)) : option Z :=
  match live with
  | [] => Some 0
  | (_, n) :: r => match xhi k n, cost_hi k r with Some h, Some c => Some (h + MBLK + c) | _, _ => None end
  end.

(* [comment removed for export] *)
Definition DMAXN : nat := 6%nat.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition kfpc_frame_ok (k : list kentry) (v lo : expr) : option expr :=
  if (lin_ge0 k [(v, -16)] [(lo, 0)] && Z.leb 3 (ealign k v)
      && match xhi k v with Some h => Z.ltb h two47 | None => false end   (* [comment removed for export] *)
      && kn_readable_x k v (-16) (ELit 16))%bool
  then match know_lookup segs k v (-16) 8 false [] [] with LHit w [] _ => Some w | _ => None end
  else None.

Definition kfpc_entailed (fact : bool) (k : list kentry) (fl : option expr) (top : expr) (bud : Z) (v lo : expr) (d : nat) : bool :=
  (lin_ge0 k [(lo, 0)] [(v, 0)] && (negb fact || lin_ge0 k [(ELit (CEIL - 1), 0)] [(v, 0)]))
  || (negb fact && stack_x k fl top bud lo && Z.ltb bud two47      (* [comment removed for export] *)
      && match xhi k v with Some vh => Z.ltb vh two47 | None => false end   (* [comment removed for export] *)
      && (let '(fb, fo) := floor_term fl top bud in ranges_apart_x k v 0 (ELit 1) fb fo (ELit (bud + WSTK))))
  || existsb (fun K => match K with
       | KFpc v' lo' d' =>
           expr_eqb v v' && Nat.leb d' d
           && (expr_eqb lo lo'
               || (lin_ge0 k [(lo', 0)] [(lo, 0)] && stack_x k fl top bud lo)      (* [comment removed for export] *)
               || (lin_ge0 k [(lo, 0)] [(lo', 0)] && lin_ge0 k [(v, -16)] [(lo, 0)]))
       | _ => false
       end) k
  || match d with
     | O => false
     | S dd => match kfpc_frame_ok k v lo with
               | Some w => lin_ge0 k [(v, 0)] [(w, 0)]
                           || existsb (fun K => match K with
                                                | KFpc v' lo' d' => expr_eqb v' w && expr_eqb lo' v && Nat.leb d' dd
                                                | _ => false
                                                end) k
               | None => false
               end
     end
  (* [comment removed for export] *)
  || (let '(vb, vc) := split_lit v in Z.leb 3 (ealign k vb) && negb (Z.eqb (vc mod 8) 0)).
Definition fpc_x (k : list kentry) (fl : option expr) (top : expr) (bud : Z) (s0 sp : expr) : bool := kfpc_entailed false k fl top bud s0 sp DMAXN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition disj_facts (p n : expr) (live : list (expr * expr)) : list kentry :=
  map (fun bl => let '(lb, lk) := split_lit (fst bl) in KDisj (SA p 0) n (SA lb lk) (snd bl)) live.
(* [comment removed for export] *)
Definition ghosts_ne (k : list kentry) (gh : list (expr * expr)) : list (expr * expr) :=
  List.filter (fun g => match xlo k (snd g) with Some l => Z.leb 1 l | None => false end) gh.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wend (k : list kentry) (g : expr * expr) : option Z :=
  match xhi k (fst g), xhi k (snd g) with
  | Some h, Some m => if Z.ltb (h + m) two64
                      then Some (match xhi k (eadd (fst g) (snd g)) with Some j => Z.min j (h + m) | None => h + m end)
                      else None
  | _, _ => None
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition floor_winI (fl : option expr) (top : expr) (bud : Z) : saddr * expr :=
  match fl with
  | Some f => (SA f 0, ELit (bud + WSTK))
  | None => let '(tb, tk) := split_lit top in (SA tb (tk - bud), ELit (bud + WSTK))
  end.
Definition ghosts_lo_ref (k : list kentry) (fl : option expr) (top : expr) (bud : Z) (gh : list (expr * expr)) : list (expr * expr) :=
  List.filter (fun g => match xlo k (snd g), wend k g with
                        | Some l, Some e => Z.leb 1 l
                                            && (Z.leb e CEIL
                                                || (let '(gb, gk) := split_lit (fst g) in let '(fw, fwl) := floor_winI fl top bud in
                                                    stack_x k fl top bud top && Z.ltb bud two47 && Z.leb e two47
                                                    && ranges_apart_x k gb gk (snd g) (a_base fw) (a_off fw) fwl))
                                            && (let '(gb, gk) := split_lit (fst g) in
                                                ranges_apart_x k gb gk (snd g) (ELit 0) (g_img_lo G) (ELit (g_img_hi G - g_img_lo G)))
                        | _, _ => false
                        end)%bool gh.
Definition ghosts_lo (k : list kentry) (fl : option expr) (top : expr) (bud : Z) (gh : list (expr * expr)) : list (expr * expr) :=
  let bc := AX2B.mkbc k in   (* [comment removed for export] *)
  List.filter (fun g => match xlo k (snd g), wend k g with
                        | Some l, Some e => Z.leb 1 l
                                            && (Z.leb e CEIL
                                                || (let '(gb, gk) := split_lit (fst g) in let '(fw, fwl) := floor_winI fl top bud in
                                                    stack_x k fl top bud top && Z.ltb bud two47 && Z.leb e two47
                                                    && AX2B.ranges_apart_xB bc gb gk (snd g) (a_base fw) (a_off fw) fwl))
                                            && (let '(gb, gk) := split_lit (fst g) in
                                                AX2B.ranges_apart_xB bc gb gk (snd g) (ELit 0) (g_img_lo G) (ELit (g_img_hi G - g_img_lo G)))
                        | _, _ => false
                        end)%bool gh.
Lemma ghosts_lo_eq : forall k fl top bud gh, ghosts_lo k fl top bud gh = ghosts_lo_ref k fl top bud gh.
Proof.
  intros. unfold ghosts_lo, ghosts_lo_ref. cbv zeta. apply filter_ext. intros g. rewrite !AX2B.ranges_apart_xB_eqf. reflexivity.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition win_lo47 (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match xhi k (eaddz b off), xhi k n with Some h, Some m => Z.ltb (h + m) two64 && Z.leb (send_hi k b off n (h + m)) two47 | _, _ => false end%bool.
   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition kdisj_of_fact (k : list kentry) (p n : expr) (K : kentry) : option kentry :=
  match kentry_range K with
  | Some (b, off, len) =>
      match b with
      | ELit _ => None                                   (* [comment removed for export] *)
      | _ => match xlo k len with
             | Some l => if Z.leb 1 l then Some (KDisj (SA p 0) n (SA b off) len) else None   (* [comment removed for export] *)
             | None => None
             end
      end
  | None => None
  end.
Fixpoint kdisj_of_facts (k : list kentry) (p n : expr) (ks : list kentry) (acc : list kentry) : list kentry :=
  match ks with
  | [] => acc
  | K :: r => match kdisj_of_fact k p n K with
              | Some D => if existsb (kentry_eqb D) acc then kdisj_of_facts k p n r acc else kdisj_of_facts k p n r (D :: acc)
              | None => kdisj_of_facts k p n r acc
              end
  end.
(* [comment removed for export] *)
Fixpoint kdisj_of_factsH (k : list kentry) (p n : expr) (ks : list kentry) (acc : list (PrimInt63.int * kentry)) : list kentry :=
  match ks with
  | [] => map snd acc
  | K :: r => match kdisj_of_fact k p n K with
              | Some D => let h := AzHashK.AHK.khash D in
                          if existsb (fun q => if PrimInt63.eqb h (fst q) then kentry_eqb D (snd q) else false) acc
                          then kdisj_of_factsH k p n r acc else kdisj_of_factsH k p n r ((h, D) :: acc)
              | None => kdisj_of_factsH k p n r acc
              end
  end.
Lemma kdisj_of_factsH_eq : forall k p n ks acc, kdisj_of_factsH k p n ks (APC.khl acc) = kdisj_of_facts k p n ks acc.
Proof.
  intros k p n ks. induction ks as [|K r IH]; intros acc.
  - cbn [kdisj_of_factsH kdisj_of_facts]. unfold APC.khl. rewrite map_map. cbn [snd]. apply map_id.
  - cbn [kdisj_of_factsH kdisj_of_facts]. destruct (kdisj_of_fact k p n K) as [D|]; [|apply IH].
    assert (E : existsb (fun q => if PrimInt63.eqb (AzHashK.AHK.khash D) (fst q) then kentry_eqb D (snd q) else false) (APC.khl acc)
                = existsb (kentry_eqb D) acc).
    { unfold APC.khl. induction acc as [|X acc' IHa]; [reflexivity|]. cbn [map existsb fst snd].
      rewrite (AzHashK.AHK.hash_guard kentry AzHashK.AHK.khash kentry_eqb APC.kentry_eqbT D X), IHa. reflexivity. }
    cbv zeta. rewrite E. destruct (existsb (kentry_eqb D) acc); [apply IH|].
    change ((AzHashK.AHK.khash D, D) :: APC.khl acc) with (APC.khl (D :: acc)). apply IH.
Qed.
Lemma kdisj_of_factsH_nil : forall k p n ks, kdisj_of_factsH k p n ks [] = kdisj_of_facts k p n ks [].
Proof. intros. exact (kdisj_of_factsH_eq k p n ks []). Qed.
(* [comment removed for export] *)
Definition block_rng (p n : expr) (nlo al : Z) : list kentry :=
  [KRange p PTRLO (PTRHI - nlo); KRange (eadd p n) (PTRLO + nlo) PTRHI; KAlign p al].
(* [comment removed for export] *)
Definition floor_win (fl : option expr) (top : expr) (bud : Z) : saddr * expr :=
  match fl with
  | Some f => (SA f 0, ELit (bud + WSTK))
  | None => let '(tb, tk) := split_lit top in (SA tb (tk - bud), ELit (bud + WSTK))
  end.
(* [comment removed for export] *)
Definition block_place (b n : expr) (nlo : Z) (flr : option expr) (top : expr) (bud : Z) : list kentry :=
  let '(fw, fl) := floor_win flr top bud in
  [KRange b PTRLO (PTRHI - nlo); KRange (eadd b n) (PTRLO + nlo) PTRHI;
   KDisj (SA b 0) n fw fl; KDisj (SA b 0) n (SA (ELit 0) (g_img_lo G)) (ELit (g_img_hi G - g_img_lo G));
   KDisj (SA b 0) n (SA (ELit 0) SHMAPLO) (ELit SHMAPLEN)].
(* [comment removed for export] *)
Definition block_sep (k : list kentry) (p n : expr) (flr : option expr) (top : expr) (bud : Z) (objs perm : list (expr * expr)) (kept : list kentry) : list kentry :=
  let '(fw, fl) := floor_win flr top bud in
  [KDisj (SA p 0) n fw fl;
   KDisj (SA p 0) n (SA (ELit 0) (g_img_lo G)) (ELit (g_img_hi G - g_img_lo G));
   KDisj (SA p 0) n (SA (ELit 0) SHMAPLO) (ELit SHMAPLEN)]
  ++ disj_facts p n (objs ++ ghosts_ne k perm)
  ++ kdisj_of_factsH k p n kept [].   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition node_alloc_core (stk : Z) (ret : Z) (nlo : Z) (cs : acs) : acs :=
  let k := kn cs in let n := reg cs 10 in let sp := reg cs 2 in
  let fl := acs_floor (a_maps cs) in
  let v := nxt cs in let p := EVar v in
  let kept := keep_owned stk k (a_vis cs ++ a_fake cs ++ a_ghost cs) (a_vis cs ++ a_fake cs ++ ghosts_ne k (a_ghost cs)) fl (a_brk cs) (a_ylo cs) sp (nxt cs) in
  let newf := (if Z.ltb 64512 nlo then [KAlign p 2048] else [])                         (* [comment removed for export] *)
              ++ block_rng p n nlo 16 ++ [KWr (SA p 0) n; KUnk (SA p 0) n; KShOk (SA p 0) n]
              ++ block_sep k p n fl (a_brk cs) (a_ylo cs) (a_vis cs ++ a_fake cs) (a_ghost cs) kept in   (* [comment removed for export] *)
  let ss := a_ss cs in
  ACS (mk_ss ret (ret_regs (s_regs ss) (S v) (Some p)) (newf ++ kept) (S v + NCS)%nat)
      (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) ((p, n) :: a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
      (eadd (a_meter cs) (ELit EVT)) (a_fake cs) (a_fbud cs).     (* [comment removed for export] *)
Definition node_alloc (stk : Z) (fpcreq : bool) (entry : Z) (cs : acs) : option acs :=
  match call_ok_stk stk entry cs with
  | None => None
  | Some ret =>
      let k := kn cs in let n := reg cs 10 in let sp := reg cs 2 in
      let fl := acs_floor (a_maps cs) in
      if (fpcreq && negb (fpc_x k fl (a_brk cs) (a_ylo cs) (reg cs 8) sp))%bool then None else
      match xlo k n, xhi k n, cost_hi k (a_vis cs), xhi k (a_meter cs) with
      | Some nlo, Some nhi, Some ch, Some mh =>
          if (Z.leb 1 nlo && Z.leb nhi NMAX && Z.leb (ch + mcost nhi) bcap && Z.leb (Z.of_nat (length (a_vis cs)) + MCNT) ccap
              && Z.leb (mh + kcost nhi) GKCAP
              && expr_vars_lt (nxt cs) n)%bool then Some (node_alloc_core stk ret nlo cs)
          else None
      | _, _, _, _ => None
      end
  end.
(* [comment removed for export] *)
Definition node_alloc_nb (stk : Z) (entry : Z) (nv mv : nat) (cs : acs) : option acs :=
  match call_ok_stk stk entry cs with
  | None => None
  | Some ret =>
      let k := kn cs in let n := reg cs 10 in let sp := reg cs 2 in
      let fl := acs_floor (a_maps cs) in
      if negb (fpc_x k fl (a_brk cs) (a_ylo cs) (reg cs 8) sp) then None else
      if negb (match a_vis cs with [] => true | _ => false end && expr_eqb n (EVar nv) && expr_eqb (a_meter cs) (EVar mv)
               && Nat.ltb nv (nxt cs))%bool then None else
      match xlo k n, xhi k n with
      | Some nlo, Some nhi => if (Z.leb 1 nlo && Z.leb nhi NMAX)%bool then Some (node_alloc_core stk ret nlo cs) else None
      | _, _ => None
      end
  end.

(* [comment removed for export] *)
Definition malloc_entry (cs : acs) : Z :=
  if Z.eqb (pc cs) (g_malloc_thunk G) then g_malloc_thunk G else g_malloc G.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition opnew_kn_ok (k : list kentry) : bool :=
  forallb (fun K => match K with
                    | KImg lo hi => existsb (fun X => match X with KImg lo' hi' => Z.leb lo' lo && Z.leb hi hi' | _ => false end) k
                    | _ => existsb (kentry_eqb K) k
                    end)%bool (g_opnew_kn G).
(* [comment removed for export] *)
Definition opnew_kn_wf : bool :=
  forallb (fun K => match K with
                    | KImg lo hi => Z.leb (g_img_lo G) lo && Z.leb lo hi && Z.leb hi (g_img_hi G)
                    | KWord (SA (ELit 0) o) w (ELit _) => Z.leb (g_img_lo G) o && Z.leb (o + Z.of_nat w) (g_img_hi G) && Nat.leb w 8
                    | KZero (SA (ELit 0) o) (ELit n) => Z.ltb 0 n && Z.leb (SB + g_ro_lo G / 8) o && Z.leb (o + n) (SB + g_img_hi G / 8)
                    | _ => false
                    end)%bool (g_opnew_kn G).
(* [comment removed for export] *)
Definition node_opnew (cs : acs) : option acs :=
  if (opnew_kn_ok (kn cs)
      && match xlo (kn cs) (a_fbud cs) with Some fb => Z.leb 1 fb | None => false end
      && afd_eqb (a_fd cs) FdStd)%bool
  then node_alloc MSTK_N false (g_opnew G) cs else None.

(* [comment removed for export] *)
Definition fresh_chk (args : list expr) (cs : acs) : bool :=
  match args with
  | [] => true
  | [ELit nmin] => match xlo (kn cs) (reg cs 10) with Some l => Z.leb nmin l | None => false end
  | _ => false
  end.
Definition node_null (stk : Z) (ret : Z) (cs : acs) : acs :=
  let k := kn cs in let ss := a_ss cs in
  ACS (mk_ss ret (ret_regs (s_regs ss) (nxt cs) (Some (ELit 0)))
              (keep_owned stk k (a_vis cs ++ a_fake cs ++ a_ghost cs) (a_vis cs ++ a_fake cs ++ ghosts_ne k (a_ghost cs))
                          (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) (nxt cs)) (nxt cs + NCS)%nat)
      (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
      (a_meter cs) (a_fake cs) (a_fbud cs).
Definition node_malloc2 (args : list expr) (cs : acs) : option (acs * acs) :=
  let entry := malloc_entry cs in
  if fresh_chk args cs then
    match call_ok_stk MSTK_A entry cs, xhi (kn cs) (a_meter cs), node_alloc MSTK_A true entry cs with
    | Some ret, Some mh, Some ok => if Z.leb (mh + EVT) GKCAP then Some (node_null MSTK_A ret cs, ok) else None
    | _, _, _ => None
    end
  else None.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint remove_block (p : expr) (live : list (expr * expr)) : option (expr * list (expr * expr)) :=
  match live with
  | [] => None
  | (b, n) :: r => if expr_eqb b p then Some (n, r)
                   else match remove_block p r with Some (m, r') => Some (m, (b, n) :: r') | None => None end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition node_release (stk : Z) (entry : Z) (cs : acs) : option acs :=
  match call_ok_stk stk entry cs with
  | None => None
  | Some ret =>
      let k := kn cs in let p := reg cs 10 in let sp := reg cs 2 in
      let ss := a_ss cs in let fl := acs_floor (a_maps cs) in
      if negb (fpc_x k fl (a_brk cs) (a_ylo cs) (reg cs 8) sp) then None else
      match p with
      | ELit 0 =>
          Some (with_ss cs (mk_ss ret (ret_regs (s_regs ss) (nxt cs) None)
                                 (keep_owned stk k (a_vis cs ++ a_fake cs ++ a_ghost cs) (a_vis cs ++ a_fake cs ++ ghosts_ne k (a_ghost cs)) fl (a_brk cs) (a_ylo cs) sp (nxt cs)) (nxt cs + NCS)%nat))
      | _ =>
          match remove_block p (a_vis cs), xhi k (a_meter cs) with
          | Some (m, live'), Some mh =>
              if negb (Z.leb (mh + KFREE) GKCAP) then None else
              Some (ACS (mk_ss ret (ret_regs (s_regs ss) (nxt cs) None)
                              (keep_owned stk k (live' ++ a_fake cs ++ a_ghost cs) (live' ++ a_fake cs ++ ghosts_ne k (a_ghost cs)) fl (a_brk cs) (a_ylo cs) sp (nxt cs)) (nxt cs + NCS)%nat)
                        (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) live'
                        (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (eadd (a_meter cs) (ELit KFREE)) (a_fake cs) (a_fbud cs))
          | _, _ => None
          end
      end
  end.

Definition node_free (cs : acs) : option acs :=
  if Z.eqb (pc cs) (g_free_thunk G) then node_release MSTK_A (g_free_thunk G) cs else node_release MSTK_A (g_free G) cs.
Definition node_opdel : acs -> option acs := node_release MSTK_A (g_opdel G).
Definition node_opdel_sized : acs -> option acs := node_release MSTK_A (g_opdel_sized G).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fcount_len (n : Z) (fk : list (expr * expr)) : Z :=
  Z.of_nat (length (List.filter (fun p => expr_eqb (snd p) (ELit n)) fk)).
(* [comment removed for export] *)
Definition shb (b : expr) : expr := EAlu ALU_SRL b (ELit 3).

(* [comment removed for export] *)
Definition node_stack_malloc (args : list expr) (cs : acs) : option acs :=
  match args with
  | [ELit k] =>
    if negb (Z.leb 0 k && Z.leb k 3)%bool then None else
    let n := 64 * 2 ^ k in
    match call_ok_stk MSTK_F (g_stkmal G k) cs with
    | None => None
    | Some ret =>
        let kn0 := kn cs in let sp := reg cs 2 in
        if negb (match reg cs 10 with ELit a0 => (Z.leb 1 a0 && Z.leb a0 n)%bool | _ => false end   (* [comment removed for export] *)
                 && Z.leb (fcount_len n (a_fake cs) + 1) (FAKEMAX / n)
                 && match xlo kn0 (a_fbud cs) with Some fb => Z.leb 1 fb | None => false end)%bool then None else   (* [comment removed for export] *)
        let v := nxt cs in let f := EVar v in let fl := acs_floor (a_maps cs) in
        let kept := keep_owned MSTK_F kn0 (a_vis cs ++ a_fake cs ++ a_ghost cs) (a_vis cs ++ a_fake cs ++ ghosts_ne kn0 (a_ghost cs)) fl (a_brk cs) (a_ylo cs) sp (nxt cs) in
        let newf := block_rng f (ELit n) n n ++ [KWr (SA f 0) (ELit n); KUnk (SA f 0) (ELit n);
                     KZero (SA (shb f) SB) (ELit (n / 8)); KUnk (SA (shb f) SB) (ELit (n / 8));   (* [comment removed for export] *)
                     KWr (SA (shb f) SB) (ELit (n / 8)); KShOk (SA f 0) (ELit n);
                     KDisj (SA (shb f) SB) (ELit (n / 8)) (SA (ELit 0) (SB + g_img_lo G / 8)) (ELit ((g_img_hi G - g_img_lo G) / 8))]   (* [comment removed for export] *)
                    ++ block_sep kn0 f (ELit n) fl (a_brk cs) (a_ylo cs) (a_vis cs ++ a_fake cs) (a_ghost cs) kept in   (* [comment removed for export] *)
        let ss := a_ss cs in
        Some (ACS (mk_ss ret (ret_regs (s_regs ss) (S v) (Some f)) (newf ++ kept) (S v + NCS)%nat)
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
                  (a_meter cs) ((f, ELit n) :: a_fake cs) (eaddz (a_fbud cs) (-1)))
    end
  | _ => None
  end.

Fixpoint remove_frame (f : expr) (fk : list (expr * expr)) : option (expr * list (expr * expr)) :=
  match fk with
  | [] => None
  | (b, n) :: r => if expr_eqb b f then Some (n, r)
                   else match remove_frame f r with Some (m, r') => Some (m, (b, n) :: r') | None => None end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition node_fake_release (cs : acs) : option acs :=
  match itab_lookup IT (pc cs), itab_lookup IT (pc cs + 4) with
  | Some (Load SZ8 _ rd rs imm), Some (Store SZ1 rs1 rs2 imm2) =>
      if negb (bv_eqb rs1 rd && bv_eqb rs2 0%bv && Z.eqb (bv_signed imm2) 0 && negb (bv_eqb rd 0%bv)
               && match fetch_word segs (Z_to_bv 64 (pc cs + 4)) with
                  | Some w => bv_eqb w (Z_to_bv 32 (0x23 + bv_unsigned rd * 2 ^ 15))
                  | None => false
                  end
               && fresh_ok nx0 cs && Z.leb 0 (pc cs) && Z.ltb (pc cs + 8) two64
               && Nat.eqb (length (s_regs (a_ss cs))) 32 && live_flat cs
               && (let '(spb, spk) := split_lit (reg cs 2) in bflat_x (kn cs) spb spk (ELit 0))
               && stack_x (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2))%bool then None else   (* [comment removed for export] *)
      let f := sr_get (s_regs (a_ss cs)) rs in
      match remove_frame f (a_fake cs) with
      | Some (ELit n, fk') =>
          if negb (Z.eqb (bv_signed imm) (n - 8) && Z.leb 8 n && Z.ltb n two47 && kn_readable_x (kn cs) f (n - 8) (ELit 8))%bool then None else
          let v := nxt cs in
          let k2 := keep_owned 0 (kn cs) (a_vis cs ++ fk' ++ a_ghost cs) (a_vis cs ++ fk' ++ ghosts_ne (kn cs) (a_ghost cs)) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) (nxt cs) in
          let ss := a_ss cs in
          Some (ACS (mk_ss (pc cs + 8) (sr_upd (s_regs ss) (ridx rd) (EVar v)) k2 (S v))
                    (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
                    (a_meter cs) fk' (eaddz (a_fbud cs) 1))
      | _ => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kshok_zero_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match xlo k (eaddz b off), xhi k (eaddz b off), xhi k n with
  | Some lo, Some hi, Some nhi =>
      Z.leb 0 lo && Z.leb (hi + nhi) two47 && bflat_x k b off n
      && kzero_x k k (ELit 0) (SB + lo / 8) (ELit ((hi + nhi + 7) / 8 - lo / 8))
  | _, _, _ => false
  end%bool.
(* [comment removed for export] *)
Definition shb_zero1 (k : list kentry) (sb : expr) (so : Z) : bool :=
  existsb (fun K => match K with
                    | KWord (SA b' o') 1%nat (ELit 0) => expr_eqb b' sb && Z.eqb o' so
                    | KZero (SA b' o') (ELit zn) => expr_eqb b' sb && Z.leb o' so && Z.ltb so (o' + zn) && Z.ltb zn two47
                    | _ => false end)%bool k.
Definition kshok_sym_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match n with
  | ELit nn => Z.leb 3 (ealign k b) && Z.leb 0 off && Z.ltb 0 nn && Z.leb nn 4096 && bflat_x k b off n
               && match xhi k (eaddz b off) with Some hi => Z.leb (hi + nn) two47 | None => false end
               && forallb (fun j => shb_zero1 k (shb b) (SB + j))
                          (map (fun i => off / 8 + Z.of_nat i) (seq 0 (Z.to_nat ((off + nn - 1) / 8 - off / 8 + 1))))
  | _ => false
  end%bool.
Definition kshok_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  kshok_entailed k k b off n || kshok_zero_x k b off n || kshok_sym_x k b off n.

Definition MSTK_M : Z := 2304.              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition mem_lit_x (lo hi : Z) : bool := (((0 <=? lo) && (hi <=? SB - 1)) || ((KHI <=? lo) && (hi <? two47)))%Z.
(* [comment removed for export] *)
Definition mem_x (k : list kentry) (b : expr) (off : Z) (n : expr) (lo hi : Z) : bool :=
  mem_lit_x lo hi || ((0 <=? lo)%Z && (hi <? two47)%Z && ranges_apart_x k b off n (ELit 0) SHMAPLO (ELit SHMAPLEN)).

(* [comment removed for export] *)
Definition shvis_x (k : list kentry) (fl : option expr) (top : expr) (bud : Z) (objs : list (expr * expr)) (b : expr) (off : Z) (n : expr) (endhi : Z) : bool :=
  existsb (fun bl => let '(lb, lk) := split_lit (fst bl) in xinside k b off n lb lk (snd bl)) objs
  || srange_x k fl top bud b off n                        (* [comment removed for export] *)
  || match xlo k (eaddz b off) with
     | Some lo => ((g_ro_lo G <=? lo) && (endhi <=? g_img_hi G))
     | None => false
     end%Z%bool.
(* [comment removed for export] *)
Definition mend_hi (k : list kentry) (e ne : expr) (ehi nhi : Z) : Z :=
  match xrange2 k (eadd e ne) with Some (_, j) => Z.min j (ehi + nhi) | None => ehi + nhi end.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition xlo2 (k : list kentry) (e : expr) : option Z := match xrange2 k e with Some (lo, _) => Some lo | None => None end.
Definition xhi2 (k : list kentry) (e : expr) : option Z := match xrange2 k e with Some (_, hi) => Some hi | None => None end.

(* [comment removed for export] *)
Definition mobjs (cs : acs) : list (expr * expr) := a_vis cs ++ map ffus (a_fake cs) ++ a_ghost cs.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition neq_x (k : list kentry) (db : expr) (dk : Z) (sb : expr) (sk : Z) : bool :=
  lin_ge0 k [(db, dk)] [(sb, sk + 1)] || lin_ge0 k [(sb, sk)] [(db, dk + 1)] || ranges_apart_x k db dk (ELit 1) sb sk (ELit 1).
(* [comment removed for export] *)
Definition below_scratch_x (k : list kentry) (sp : expr) (endhi : Z) : bool :=
  match xlo k sp with Some splo => Z.leb endhi (splo - MSTK_M) | None => false end.

(* [comment removed for export] *)
Definition havocD (k : list kentry) (db : expr) (dk : Z) (ne : expr) : list kentry := droprange_sel db k db dk ne.
Lemma havocD_eq : havocD = kn_havoc.
Proof.
  apply FunctionalExtensionality.functional_extensionality; intros k. apply FunctionalExtensionality.functional_extensionality; intros db.
  unfold havocD. rewrite droprange_sel_eq. reflexivity.
Qed.
Definition copyFB (fuel : nat) (k : list kentry) : expr -> Z -> expr -> Z -> Z -> option (list kentry) := copy_factsB segs (AX2B.mkbc k) fuel.
Lemma copyFB_eq : copyFB = copy_facts segs.
Proof.
  apply FunctionalExtensionality.functional_extensionality; intros fuel. apply FunctionalExtensionality.functional_extensionality; intros k.
  unfold copyFB. apply copy_factsB_eqf'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition flat_recheck_b (kh : list kentry) (objs : list (expr * expr)) : bool :=
  let bch := AX2B.mkbc kh in forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x_b bch lb lk (snd bl)) objs.
Lemma flat_recheck_b_fe : flat_recheck_b = (fun kh objs => forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x kh lb lk (snd bl)) objs).
Proof. do 2 (apply FunctionalExtensionality.functional_extensionality; intro). unfold flat_recheck_b. cbv zeta. rewrite bflat_x_b_fe. reflexivity. Qed.
Lemma owned_x_b_fe : forall k, owned_x_b (AX2B.mkbc k) = owned_x k.
Proof. intros. do 7 (apply FunctionalExtensionality.functional_extensionality; intro). apply owned_x_b_eq. Qed.
Definition live_flat_b (bc : AX2B.bctx) (cs : acs) : bool :=
  forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x_b bc lb lk (snd bl)) (a_vis cs ++ a_fake cs ++ a_ghost cs).
Lemma live_flat_b_eq : forall cs, live_flat_b (AX2B.mkbc (kn cs)) cs = live_flat cs.
Proof. intros. unfold live_flat_b, live_flat. rewrite bflat_x_b_fe. reflexivity. Qed.
Definition call_ok_stk_b (bc : AX2B.bctx) (stk : Z) (entry : Z) (cs : acs) : option Z :=
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs, reg_lit cs 4 with
  | Some ret, Some tp =>
      let k := kn cs in let sp := reg cs 2 in let '(spb, spk) := split_lit sp in
      if (Z.eqb tp (g_tp G) && fresh_ok nx0 cs && Nat.eqb (length (s_regs (a_ss cs))) 32
          && Z.leb 4 (AX2B.ealignB bc sp) && kwritable_xB bc k spb (spk - stk) (ELit stk)
          && in_floorB bc (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) spb (spk - stk) (ELit stk)
          && match AX2B.xhiB bc sp with Some hi => Z.leb (hi + 16) two47 | None => false end
          && live_flat_b bc cs)%bool
      then Some ret else None
  | _, _ => None
  end.
Lemma call_ok_stk_b_eq : forall stk entry cs, call_ok_stk_b (AX2B.mkbc (kn cs)) stk entry cs = call_ok_stk stk entry cs.
Proof.
  intros. unfold call_ok_stk_b, call_ok_stk. rewrite AX2B.ealignB_eqf, kwritable_xB_eqf, in_floorB_eqf, AX2B.xhiB_eqf, live_flat_b_eq. reflexivity.
Qed.
Definition kshok_zero_x_b (bc : AX2B.bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match AX2B.xloB bc (eaddz b off), AX2B.xhiB bc (eaddz b off), AX2B.xhiB bc n with
  | Some lo, Some hi, Some nhi =>
      Z.leb 0 lo && Z.leb (hi + nhi) two47 && bflat_x_b bc b off n
      && kzero_xB bc k (ELit 0) (SB + lo / 8) (ELit ((hi + nhi + 7) / 8 - lo / 8))
  | _, _, _ => false
  end%bool.
Lemma kshok_zero_x_b_fe : forall k, kshok_zero_x_b (AX2B.mkbc k) k = kshok_zero_x k.
Proof.
  intros. do 3 (apply FunctionalExtensionality.functional_extensionality; intro). unfold kshok_zero_x_b, kshok_zero_x.
  rewrite AX2B.xloB_eqf, AX2B.xhiB_eqf, bflat_x_b_fe, kzero_xB_eqf. reflexivity.
Qed.
Definition kshok_sym_x_b (bc : AX2B.bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match n with
  | ELit nn => Z.leb 3 (AX2B.ealignB bc b) && Z.leb 0 off && Z.ltb 0 nn && Z.leb nn 4096 && bflat_x_b bc b off n
               && match AX2B.xhiB bc (eaddz b off) with Some hi => Z.leb (hi + nn) two47 | None => false end
               && forallb (fun j => shb_zero1 k (shb b) (SB + j))
                          (map (fun i => off / 8 + Z.of_nat i) (seq 0 (Z.to_nat ((off + nn - 1) / 8 - off / 8 + 1))))
  | _ => false
  end%bool.
Lemma kshok_sym_x_b_fe : forall k, kshok_sym_x_b (AX2B.mkbc k) k = kshok_sym_x k.
Proof.
  intros. do 3 (apply FunctionalExtensionality.functional_extensionality; intro). unfold kshok_sym_x_b, kshok_sym_x.
  rewrite AX2B.ealignB_eqf, bflat_x_b_fe, AX2B.xhiB_eqf. reflexivity.
Qed.
Definition kshok_x_b (bc : AX2B.bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  AX2B.kshok_entailedB bc k b off n || kshok_zero_x_b bc k b off n || kshok_sym_x_b bc k b off n.
Lemma kshok_x_b_fe : forall k, kshok_x_b (AX2B.mkbc k) k = kshok_x k.
Proof.
  intros. do 3 (apply FunctionalExtensionality.functional_extensionality; intro). unfold kshok_x_b, kshok_x.
  rewrite AX2B.kshok_entailedB_eqf, kshok_zero_x_b_fe, kshok_sym_x_b_fe. reflexivity.
Qed.
Definition mem_x_b (bc : AX2B.bctx) (b : expr) (off : Z) (n : expr) (lo hi : Z) : bool :=
  mem_lit_x lo hi || ((0 <=? lo)%Z && (hi <? two47)%Z && AX2B.ranges_apart_xB bc b off n (ELit 0) SHMAPLO (ELit SHMAPLEN)).
Lemma mem_x_b_fe : forall k, mem_x_b (AX2B.mkbc k) = mem_x k.
Proof. intros. do 5 (apply FunctionalExtensionality.functional_extensionality; intro). unfold mem_x_b, mem_x. rewrite AX2B.ranges_apart_xB_eqf. reflexivity. Qed.
Definition shvis_x_b (bc : AX2B.bctx) (fl : option expr) (top : expr) (bud : Z) (objs : list (expr * expr)) (b : expr) (off : Z) (n : expr) (endhi : Z) : bool :=
  existsb (fun bl => let '(lb, lk) := split_lit (fst bl) in AX2B.xinsideB bc b off n lb lk (snd bl)) objs
  || srange_x_b bc fl top bud b off n
  || match AX2B.xloB bc (eaddz b off) with
     | Some lo => ((g_ro_lo G <=? lo) && (endhi <=? g_img_hi G))
     | None => false
     end%Z%bool.
Lemma shvis_x_b_fe : forall k, shvis_x_b (AX2B.mkbc k) = shvis_x k.
Proof.
  intros. do 8 (apply FunctionalExtensionality.functional_extensionality; intro). unfold shvis_x_b, shvis_x.
  rewrite AX2B.xinsideB_eqf, srange_x_b_fe, AX2B.xloB_eqf. reflexivity.
Qed.
Definition mend_hi_b (bc : AX2B.bctx) (e ne : expr) (ehi nhi : Z) : Z :=
  match AX2B.xrange2B bc (eadd e ne) with Some (_, j) => Z.min j (ehi + nhi) | None => ehi + nhi end.
Lemma mend_hi_b_fe : forall k, mend_hi_b (AX2B.mkbc k) = mend_hi k.
Proof. intros. do 4 (apply FunctionalExtensionality.functional_extensionality; intro). unfold mend_hi_b, mend_hi. rewrite AX2B.xrange2B_eqf. reflexivity. Qed.
Definition xlo2_b (bc : AX2B.bctx) (e : expr) : option Z := match AX2B.xrange2B bc e with Some (lo, _) => Some lo | None => None end.
Definition xhi2_b (bc : AX2B.bctx) (e : expr) : option Z := match AX2B.xrange2B bc e with Some (_, hi) => Some hi | None => None end.
Lemma xlo2_b_fe : forall k, xlo2_b (AX2B.mkbc k) = xlo2 k.
Proof. intros. apply FunctionalExtensionality.functional_extensionality; intro. unfold xlo2_b, xlo2. rewrite AX2B.xrange2B_eqf. reflexivity. Qed.
Lemma xhi2_b_fe : forall k, xhi2_b (AX2B.mkbc k) = xhi2 k.
Proof. intros. apply FunctionalExtensionality.functional_extensionality; intro. unfold xhi2_b, xhi2. rewrite AX2B.xrange2B_eqf. reflexivity. Qed.
Definition neq_x_b (bc : AX2B.bctx) (db : expr) (dk : Z) (sb : expr) (sk : Z) : bool :=
  AX2B.lin_ge0B bc [(db, dk)] [(sb, sk + 1)] || AX2B.lin_ge0B bc [(sb, sk)] [(db, dk + 1)] || AX2B.ranges_apart_xB bc db dk (ELit 1) sb sk (ELit 1).
Lemma neq_x_b_fe : forall k, neq_x_b (AX2B.mkbc k) = neq_x k.
Proof. intros. do 4 (apply FunctionalExtensionality.functional_extensionality; intro). unfold neq_x_b, neq_x. rewrite AX2B.lin_ge0B_eqf, AX2B.ranges_apart_xB_eqf. reflexivity. Qed.
Definition below_scratch_x_b (bc : AX2B.bctx) (sp : expr) (endhi : Z) : bool :=
  match AX2B.xloB bc sp with Some splo => Z.leb endhi (splo - MSTK_M) | None => false end.
Lemma below_scratch_x_b_fe : forall k, below_scratch_x_b (AX2B.mkbc k) = below_scratch_x k.
Proof. intros. do 2 (apply FunctionalExtensionality.functional_extensionality; intro). unfold below_scratch_x_b, below_scratch_x. rewrite AX2B.xloB_eqf. reflexivity. Qed.
Definition knread_x_b (bc : AX2B.bctx) (k : list kentry) (rb : expr) (rk : Z) (ne : expr) : bool :=
  existsb (fun K => match K with
                    | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
                        AX2B.xinsideB bc rb rk ne kb kk len
                    | _ => false
                    end) k.
Lemma knread_x_b_fe : forall k, knread_x_b (AX2B.mkbc k) k = kn_readable_x k.
Proof. intros. do 3 (apply FunctionalExtensionality.functional_extensionality; intro). unfold knread_x_b, kn_readable_x. rewrite AX2B.xinsideB_eqf. reflexivity. Qed.

Definition mem_ok_ref (entry : Z) (needsrc apart : bool) (cs : acs) : option (Z * (expr * Z) * (expr * Z) * (Z * Z) * list kentry) :=
  match call_ok_stk MSTK_M entry cs with
  | None => None
  | Some ret =>
      let k := kn cs in let '(spb, spk) := split_lit (reg cs 2) in
      let fl := acs_floor (a_maps cs) in let top := a_brk cs in let bud := a_ylo cs in
      let dst := reg cs 10 in let src := reg cs 11 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in let '(sb, sk) := split_lit src in
      match xlo k ne, xhi k ne, xlo2 k dst, xhi2 k dst with      (* [comment removed for export] *)
      | Some nlo, Some nhi, Some dlo, Some dhi =>
          let dend := mend_hi k dst ne dhi nhi in
          if Z.eqb nhi 0 then
            (* [comment removed for export] *)
            if (Z.leb 0 nlo && mem_x k db dk ne dlo dend && bflat_x k db dk ne
                && forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x k lb lk (snd bl)) (mobjs cs)
                && (negb needsrc
                    || match xlo2 k src, xhi2 k src with
                       | Some slo, Some shi => mem_x k sb sk ne slo (mend_hi k src ne shi nhi) && bflat_x k sb sk ne
                       | _, _ => false
                       end))%bool
            then let kh := havocD k db dk ne in   (* [comment removed for export] *)
                 if forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x kh lb lk (snd bl)) (a_vis cs ++ a_fake cs ++ a_ghost cs)
                 then Some (ret, (db, dk), (sb, sk), (nlo, nhi), kh) else None
            else None
          else
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && mem_x k db dk ne dlo dend
              && forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x k lb lk (snd bl)) (mobjs cs)
              && owned_x k (mobjs cs) fl top bud db dk ne && kwritable_x k k db dk ne
              && kshok_x k db dk ne && shvis_x k fl top bud (mobjs cs) db dk ne dend
              && (ranges_apart_x k db dk ne spb (spk - MSTK_M) (ELit MSTK_M) || below_scratch_x k (reg cs 2) dend)   (* [comment removed for export] *)
              && (negb needsrc
                  || match xlo2 k src, xhi2 k src with      (* [comment removed for export] *)
                     | Some slo, Some shi =>
                         let send := mend_hi k src ne shi nhi in
                         mem_x k sb sk ne slo send && kshok_x k sb sk ne && shvis_x k fl top bud (mobjs cs) sb sk ne send
                         && (ranges_apart_x k sb sk ne spb (spk - MSTK_M) (ELit MSTK_M) || below_scratch_x k (reg cs 2) send)   (* [comment removed for export] *)
                         && (negb apart || ranges_apart_x k db dk ne sb sk ne)
                         && (apart || neq_x k db dk sb sk || kn_readable_x k sb sk ne)   (* [comment removed for export] *)
                     | _, _ => false
                     end))%bool
          then match (if off_image_x A k db dk ne then Some k
                      else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) with
               | Some k0 =>
                   (* [comment removed for export] *)
                   let kh := havocD k0 db dk ne in   (* [comment removed for export] *)
                   if forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x kh lb lk (snd bl)) (a_vis cs ++ a_fake cs ++ a_ghost cs)
                   then Some (ret, (db, dk), (sb, sk), (nlo, nhi), kh) else None
               | None => None
               end
          else None
      | _, _, _, _ => None
      end
  end.
(* [comment removed for export] *)
Definition mem_ok (entry : Z) (needsrc apart : bool) (cs : acs) : option (Z * (expr * Z) * (expr * Z) * (Z * Z) * list kentry) :=
  let bc := AX2B.mkbc (kn cs) in   (* [comment removed for export] *)
  match call_ok_stk_b bc MSTK_M entry cs with
  | None => None
  | Some ret =>
      let k := kn cs in let '(spb, spk) := split_lit (reg cs 2) in
      let fl := acs_floor (a_maps cs) in let top := a_brk cs in let bud := a_ylo cs in
      let dst := reg cs 10 in let src := reg cs 11 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in let '(sb, sk) := split_lit src in
      match AX2B.xloB bc ne, AX2B.xhiB bc ne, xlo2_b bc dst, xhi2_b bc dst with      (* [comment removed for export] *)
      | Some nlo, Some nhi, Some dlo, Some dhi =>
          let dend := mend_hi_b bc dst ne dhi nhi in
          if Z.eqb nhi 0 then
            (* [comment removed for export] *)
            if (Z.leb 0 nlo && mem_x_b bc db dk ne dlo dend && bflat_x_b bc db dk ne
                && forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x_b bc lb lk (snd bl)) (mobjs cs)
                && (negb needsrc
                    || match xlo2_b bc src, xhi2_b bc src with
                       | Some slo, Some shi => mem_x_b bc sb sk ne slo (mend_hi_b bc src ne shi nhi) && bflat_x_b bc sb sk ne
                       | _, _ => false
                       end))%bool
            then let kh := havocD k db dk ne in   (* [comment removed for export] *)
                 if flat_recheck_b kh (a_vis cs ++ a_fake cs ++ a_ghost cs)   (* [comment removed for export] *)
                 then Some (ret, (db, dk), (sb, sk), (nlo, nhi), kh) else None
            else None
          else
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && mem_x_b bc db dk ne dlo dend
              && forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x_b bc lb lk (snd bl)) (mobjs cs)
              && owned_x_b bc (mobjs cs) fl top bud db dk ne && kwritable_xB bc k db dk ne
              && kshok_x_b bc k db dk ne && shvis_x_b bc fl top bud (mobjs cs) db dk ne dend
              && (AX2B.ranges_apart_xB bc db dk ne spb (spk - MSTK_M) (ELit MSTK_M) || below_scratch_x_b bc (reg cs 2) dend)   (* [comment removed for export] *)
              && (negb needsrc
                  || match xlo2_b bc src, xhi2_b bc src with      (* [comment removed for export] *)
                     | Some slo, Some shi =>
                         let send := mend_hi_b bc src ne shi nhi in
                         mem_x_b bc sb sk ne slo send && kshok_x_b bc k sb sk ne && shvis_x_b bc fl top bud (mobjs cs) sb sk ne send
                         && (AX2B.ranges_apart_xB bc sb sk ne spb (spk - MSTK_M) (ELit MSTK_M) || below_scratch_x_b bc (reg cs 2) send)   (* [comment removed for export] *)
                         && (negb apart || AX2B.ranges_apart_xB bc db dk ne sb sk ne)
                         && (apart || neq_x_b bc db dk sb sk || knread_x_b bc k sb sk ne)   (* [comment removed for export] *)
                     | _, _ => false
                     end))%bool
          then match (if off_image_xB A bc db dk ne then Some k
                      else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) with
               | Some k0 =>
                   (* [comment removed for export] *)
                   let kh := havocD k0 db dk ne in   (* [comment removed for export] *)
                   if flat_recheck_b kh (a_vis cs ++ a_fake cs ++ a_ghost cs)   (* [comment removed for export] *)
                   then Some (ret, (db, dk), (sb, sk), (nlo, nhi), kh) else None
               | None => None
               end
          else None
      | _, _, _, _ => None
      end
  end.
Lemma mem_ok_eq : forall entry needsrc apart cs, mem_ok entry needsrc apart cs = mem_ok_ref entry needsrc apart cs.
Proof.
  intros. unfold mem_ok, mem_ok_ref. cbv zeta.
  rewrite call_ok_stk_b_eq, ?AX2B.xloB_eqf, ?AX2B.xhiB_eqf, ?xlo2_b_fe, ?xhi2_b_fe, ?mend_hi_b_fe, ?mem_x_b_fe, ?bflat_x_b_fe, ?owned_x_b_fe,
    ?kwritable_xB_eqf, ?kshok_x_b_fe, ?shvis_x_b_fe, ?AX2B.ranges_apart_xB_eqf, ?below_scratch_x_b_fe, ?neq_x_b_fe, ?knread_x_b_fe,
    ?off_image_xB_eqf, ?flat_recheck_b_fe.
  cbv beta. reflexivity.
Qed.

(* [comment removed for export] *)
Definition mem_kept (cs : acs) (kh : list kentry) (v : nat) : list kentry :=
  keep_owned MSTK_M kh (a_vis cs ++ a_fake cs ++ a_ghost cs) (a_vis cs ++ a_fake cs ++ ghosts_ne kh (a_ghost cs)) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) v.

(* [comment removed for export] *)
Definition mem_post (cs : acs) (ret : Z) (rv : expr) (k' : list kentry) (extra : nat) : acs :=
  let v := nxt cs in let ss := a_ss cs in
  ACS (mk_ss ret (ret_regs (s_regs ss) v (Some rv)) k' (v + NCS + extra)%nat)
      (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
      (a_meter cs) (a_fake cs) (a_fbud cs).

(* [comment removed for export] *)
Definition kblob_at (k : list kentry) (sb : expr) (sk : Z) (ne : expr) : option nat :=
  match List.find (fun K => match K with
                             | KBlob (SA b o) len _ => expr_eqb b sb && Z.eqb o sk && expr_eqb len ne
                             | _ => false
                             end) k with
  | Some (KBlob _ _ j) => Some j
  | _ => None
  end.

(* [comment removed for export] *)
Definition copy_dst_facts (cs : acs) (db : expr) (dk : Z) (sb : expr) (sk : Z) (nlo nhi : Z) : option (list kentry * nat) :=
  let k := kn cs in let ne := reg cs 12 in let v := nxt cs in
  let r :=
    if Z.eqb nhi 0 then Some ([], 0%nat) else
    match kblob_at k sb sk ne with Some j => Some ([KBlob (SA db dk) ne j], 0%nat) | None =>     (* [comment removed for export] *)
    if (Z.ltb 0 nlo && kzero_x k k sb sk ne)%bool then Some ([KZero (SA db dk) ne], 0%nat) else
    let words := if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat in
    let kfresh := map (fun i => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (v + NCS + i)%nat)) (seq 0 words) in
    let havoc_src := if ((kwritable_x k k sb sk ne || kn_readable_x k sb sk ne) && flat_x k sb sk ne)%bool
                     then Some (kfresh ++ kblob_prefix k sb sk db dk nlo ++ (if Z.ltb 0 nlo then [KUnk (SA db dk) ne] else []), words)
                     else None in
    match ne with
    | ELit _ =>
        if (Z.leb nhi 2048 && flat_x k sb sk ne)%bool then
          match copyFB (Z.to_nat nhi) k sb sk db dk nhi with   (* [comment removed for export] *)
          | Some kc => Some (kc, 0%nat)
          | None => havoc_src
          end
        else havoc_src
    | _ => havoc_src
    end end in
  (* [comment removed for export] *)
  match r with
  | Some (newf, extra) => if kn_vars_lt (v + NCS + extra)%nat newf then Some (newf, extra) else None
  | None => None
  end.

(* [comment removed for export] *)
Definition fill_dst_facts (cs : acs) (db : expr) (dk : Z) (sb : expr) (sk : Z) (nlo nhi : Z) : option (list kentry * nat) :=
  match reg_lit cs 11 with
  | Some c => let c8 := c mod 256 in
              Some ((if Z.ltb 0 nlo then [if Z.eqb c8 0 then KZero (SA db dk) (reg cs 12) else KFill (SA db dk) (reg cs 12) c8] else []), 0%nat)
  | None => None
  end.

(* [comment removed for export] *)
Definition node_mem (entry : Z) (needsrc apart : bool)
           (facts : acs -> expr -> Z -> expr -> Z -> Z -> Z -> option (list kentry * nat)) (cs : acs) : option acs :=
  match mem_ok entry needsrc apart cs with
  | Some (ret, (db, dk), (sb, sk), (nlo, nhi), kh) =>
      match facts cs db dk sb sk nlo nhi with
      | Some (newf, extra) => Some (mem_post cs ret (reg cs 10) (newf ++ mem_kept cs kh (nxt cs)) extra)
      | None => None
      end
  | None => None
  end.

(* [comment removed for export] *)
Definition node_mcopy (entry : Z) : acs -> option acs := node_mem entry true true copy_dst_facts.
Definition node_mmove (entry : Z) : acs -> option acs := node_mem entry true false copy_dst_facts.
Definition node_mfill (entry : Z) : acs -> option acs := node_mem entry false false fill_dst_facts.

Definition node_memcpy (cs : acs) : option acs := node_mcopy (g_memcpy G) cs.
Definition node_memset (cs : acs) : option acs := node_mfill (g_memset G) cs.
Definition node_memmove (cs : acs) : option acs := node_mmove (g_memmove G) cs.
Definition node_amemcpy (cs : acs) : option acs := node_mcopy (g_amemcpy G) cs.
Definition node_amemset (cs : acs) : option acs := node_mfill (g_amemset G) cs.
Definition node_amemmove (cs : acs) : option acs := node_mmove (g_amemmove G) cs.




(* [comment removed for export] *)
Definition SLFUEL : nat := 4096.
Fixpoint img_strlen_from (a : Z) (fuel : nat) : option Z :=
  match fuel with
  | O => None
  | S f => match PropExec.seg_rom segs (Z_to_bv 64 a) with
           | Some b => if Z.eqb (bv_unsigned b) 0 then Some 0
                       else match img_strlen_from (a + 1) f with Some l => Some (l + 1) | None => None end
           | None => None
           end
  end.
Definition node_strlen (cs : acs) : option acs :=
  match call_ok_stk MSTK_M (g_strlen G) cs with
  | None => None
  | Some ret =>
      let k := kn cs in
      match reg_lit cs 10 with
      | Some s =>
          match img_strlen_from s SLFUEL with
          | Some len =>
              let lo := s - s mod 8 in let hi := s + len + 8 - (s + len) mod 8 in
              if (Z.leb (g_ro_lo G) lo && Z.leb hi (g_ro_hi G) && Z.ltb hi SB && img_cov k lo hi
                  && match img_bytes segs lo (Z.to_nat (hi - lo)) with Some _ => true | None => false end
                  && kshok_x k (ELit s) 0 (ELit (len + 1)))%bool
              then Some (mem_post cs ret (ELit len) (mem_kept cs k (nxt cs)) 0)
              else None
          | None => None
          end
      | None => None
      end
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_blkfact (args : list expr) (cs : acs) : option acs :=
  match args with
  | [b] =>
      match remove_block b (a_vis cs) with
      | Some (n, live') =>
          let k := kn cs in let fl := acs_floor (a_maps cs) in
          match xlo k n with
          | Some nlo => if (Z.leb 1 nlo && top_ok k fl (a_brk cs) (a_ylo cs) && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n
                            && bflat_x k b 0 n && live_flat cs)%bool
                        then let objs := live' ++ a_fake cs in
                             let kept0 := keep_owned 0 k (objs ++ a_ghost cs) (objs ++ ghosts_ne k (a_ghost cs)) fl (a_brk cs) (a_ylo cs) (reg cs 2) (nxt cs) in
                             Some (add_kn cs (block_place b n nlo fl (a_brk cs) (a_ylo cs)
                                              ++ disj_facts b n (objs ++ ghosts_ne k (a_ghost cs))
                                              ++ kdisj_of_factsH k b n kept0 []))
                        else None
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition XAg (id : nat) (args : list expr) (cs : acs) : option (acs * acs) :=
  match id with
  | 12 => node_malloc2 args cs
  | _ => None
  end%nat.

(* [comment removed for export] *)
Definition XBg (id : nat) (args : list expr) (cs : acs) : option (acs * acs) :=
  let _ := segs in let _ := nx0 in let _ := G in let _ := bcap in let _ := ccap in let _ := (id, args, cs) in None.

Definition XNg (id : nat) (args : list expr) (cs : acs) : option acs :=
  match id with
  | 0 => node_imgload cs
  | 1 => node_memcpy cs
  | 2 => node_memset cs
  | 3 => node_memmove cs
  | 4 => node_strlen cs
  | 5 => node_amemcpy cs
  | 6 => node_amemset cs
  | 7 => node_amemmove cs
  | 11 => node_free cs          (* [comment removed for export] *)
  | 13 => node_blkfact args cs
  | 20 => node_opnew cs
  | 21 => node_opdel cs
  | 22 => node_opdel_sized cs
  | 30 => None   (* [comment removed for export] *)
  | 50 => node_stack_malloc args cs
  | 51 => node_fake_release cs
  | 40 => node_divmagic args cs
  | 41 => node_enumrange args cs
  | 46 => node_shok segs args cs   (* [comment removed for export] *)
  | _ => None
  end%nat.


End WithTables.
