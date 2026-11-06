(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AxSymExec3.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AxSymExec3B.   (* [comment removed for export] *)
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Export AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Export AsanPlanWhile.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Module AP.
Include APC.
Include APW.   (* [comment removed for export] *)
Import AX2.

(* [comment removed for export] *)
Record ledger : Type := LG { lg_maps : list amap; lg_totsz : Z; lg_ylo : Z; lg_eager : Z;
                             lg_vis : list (expr * expr); lg_ghost : list (expr * expr); lg_abytes : Z }.
Definition ledger_of (cs : acs) : ledger :=
  LG (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs).
Definition with_ledger (L : ledger) (cs : acs) : acs :=
  ACSG (a_ss cs) (lg_maps L) (lg_totsz L) (lg_ylo L) (lg_eager L) (lg_vis L) (lg_ghost L) (lg_abytes L)
       (a_brk cs) (a_fd cs) (a_tidset cs) (a_props cs).
Lemma with_ledger_of : forall cs, with_ledger (ledger_of cs) cs = cs.
Proof. intros cs. destruct cs; reflexivity. Qed.
Lemma ledger_of_with : forall L cs, ledger_of (with_ledger L cs) = L.
Proof. intros L cs. destruct L; reflexivity. Qed.
Lemma with_ledger_twice : forall L L' cs, with_ledger L (with_ledger L' cs) = with_ledger L cs.
Proof. intros. reflexivity. Qed.
(* [comment removed for export] *)
Definition ledger_vars_lt (b : nat) (L : ledger) : bool :=
  (maps_vars_lt b (lg_maps L) && pairs_vars_lt b (lg_vis L) && pairs_vars_lt b (lg_ghost L))%bool.

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
Inductive snode : Type :=
| YMunmap      (* [comment removed for export] *)
| YBrk         (* [comment removed for export] *)
| YSetTid.     (* [comment removed for export] *)

(* [comment removed for export] *)
Inductive xnode : Type :=
| XIMemset     (* [comment removed for export] *)
| XIMemcpy     (* [comment removed for export] *)
| XMemset      (* [comment removed for export] *)
| XMemcpy      (* [comment removed for export] *)
| XMemIsZero   (* [comment removed for export] *)
| XEnvScan     (* [comment removed for export] *)
| XPnScan      (* [comment removed for export] *)
| XLayout      (* [comment removed for export] *)
| XIStrncpy    (* [comment removed for export] *)
| XPopFree     (* [comment removed for export] *)
| XSniff.      (* [comment removed for export] *)

Inductive plan : Type :=
| PRun (stops : list Z) (k : plan)           (* [comment removed for export] *)
| PSplit (e : expr) (mid : Z) (k1 k2 : plan) (* [comment removed for export] *)
| PCase2 (e : expr) (mid : Z) (k1 k2 : plan) (* [comment removed for export] *)
| PCaseDisj (b1 b2 : expr) (k1 k2 : plan)  (* [comment removed for export] *)
| PShDisj (b1 n1 b2 n2 : expr) (k : plan)  (* [comment removed for export] *)
| PContra                                    (* [comment removed for export] *)
| PFact (K : kentry) (k : plan)              (* [comment removed for export] *)
| PJoin (b : expr) (off : Z) (n : nat) (k : plan)  (* [comment removed for export] *)
| PForget (ixs : list nat) (k : plan)        (* [comment removed for export] *)
| PDropRange (b : expr) (n : expr) (k : plan) (* [comment removed for export] *)
| PGcKeep (ws : list (expr * expr)) (k : plan) (* [comment removed for export] *)
| PBump (m : nat) (k : plan)                 (* [comment removed for export] *)
| PHavoc (rs : list nat) (k : plan)          (* [comment removed for export] *)
| PHavocBig (K : nat) (k : plan)             (* [comment removed for export] *)
| PFresh (r : nat) (logc : Z) (base : option expr) (k : plan)  (* [comment removed for export] *)
| PSys (y : snode) (k : plan)                (* [comment removed for export] *)
| PMmap (kgranted : plan)                    (* [comment removed for export] *)
| PMmapIn (kok : plan)                       (* [comment removed for export] *)
| PMprotect (kgranted : plan)                (* [comment removed for export] *)
| PBrk (kgranted : plan)                     (* [comment removed for export] *)
| PX (x : xnode) (args : list expr) (k : plan)   (* [comment removed for export] *)
| PExt (id : nat) (args : list expr) (k : plan)  (* [comment removed for export] *)
| PEmit (id : nat) (args : list expr) (k : plan) (* [comment removed for export] *)
| PExt2 (id : nat) (args : list expr) (k1 k2 : plan) (* [comment removed for export] *)
| PLoop (J : nat) (N : expr) (inv : acs) (body k : plan)  (* [comment removed for export] *)
| PNext                                      (* [comment removed for export] *)
| PHandoff (h : nat)                         (* [comment removed for export] *)
| PExit                                      (* [comment removed for export] *)
| PSpin                                      (* [comment removed for export] *)
| PFog (i : nat) (sz : Z) (k : plan)          (* [comment removed for export] *)
| PFogNew (i : nat) (sz : Z) (k : plan)       (* [comment removed for export] *)
| PGhost (b n : expr) (k : plan)              (* [comment removed for export] *)
| PUnvis (b n : expr) (k : plan)              (* [comment removed for export] *)
| PHavocBrk (lo hi : Z) (k : plan)            (* [comment removed for export] *)
| PIntro (lo hi : Z) (k : plan)               (* [comment removed for export] *)
| PDiamond (joinpc : Z) (rs : list nat) (k : plan)  (* [comment removed for export] *)
| PRename (m : list (nat * nat)) (k : plan)   (* [comment removed for export] *)
| PCompact (k : plan)                         (* [comment removed for export] *)
| PVia (j : nat) (js : acs) (lo : nat) (karms k : plan)  (* [comment removed for export] *)
| PMerge (j : nat)                            (* [comment removed for export] *)
| PAbstractCell (b : expr) (n : Z) (k : plan) (* [comment removed for export] *)
| PHavocWords (bs : list expr) (k : plan)    (* [comment removed for export] *)
| PRespell (r : nat) (e : expr) (k : plan)    (* [comment removed for export] *)
  (* [comment removed for export] *)
| PWhileN (lo : nat) (heads : list (acs * plan)) (V : expr) (xs : shape) (exits : list (acs * plan))
                                              (* [comment removed for export] *)
| PNextN (h : nat) (hints : sbind)            (* [comment removed for export] *)
| PBreak (i : nat) (hints : sbind)            (* [comment removed for export] *)
  (* [comment removed for export] *)
| PUse (sid : nat) (hints : sbind) (ks : list plan)   (* [comment removed for export] *)
  (* [comment removed for export] *)
| PGIntro (g : gatom) (k : plan)              (* [comment removed for export] *)
| PGDrop (i : nat) (k : plan)                 (* [comment removed for export] *)
| PGFact (K : kentry) (k : plan)              (* [comment removed for export] *)
| PGFactT (x : bool) (i : nat) (K : kentry) (k : plan)  (* [comment removed for export] *)
  (* [comment removed for export] *)
| PHandoffS (h lo : nat) (hints : sbind)     (* [comment removed for export] *)
| PBrk2 (kgranted kfailed : plan)            (* [comment removed for export] *)
| PCaseDisjJ (b1 b2 : expr) (joinpc : Z) (rs : list nat) (k : plan).
                                             (* [comment removed for export] *)

(* [comment removed for export] *)
Definition PWhile (lo : nat) (inv : acs) (V : expr) (xs : shape) (exits : list (acs * plan)) (body : plan) : plan :=
  PWhileN lo [(inv, body)] V xs exits.
Definition PNextW (hints : sbind) : plan := PNextN 0 hints.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition node_sys (y : snode) (cs : acs) : option acs :=
  match y with
  | YMunmap => node_munmap A cs
  | YBrk => node_brk1 A cs
  | YSetTid => node_settid nx0 cs
  end.

(* [comment removed for export] *)
Definition gate0 (entry : Z) (r : option acs) : option acs := if Z.eqb entry 0 then None else r.

Definition node_x (x : xnode) (args : list expr) (cs : acs) : option acs :=
  match x with
  | XIMemset => gate0 (x_imemset A) (summary_fill A nx0 cs (x_imemset A) 256)       (* [comment removed for export] *)
  | XMemset => gate0 (x_memset A) (summary_fill A nx0 cs (x_memset A) two64)
  | XIMemcpy => gate0 (x_imemcpy A) (summary_copy segs A nx0 cs (x_imemcpy A))
  | XMemcpy => gate0 (x_memcpy A) (summary_copy segs A nx0 cs (x_memcpy A))
  | XMemIsZero => gate0 (x_memiszero A) (summary_miz A nx0 cs)
  | XEnvScan => node_envscan A cs
  | XPnScan => node_pnscan A nx0 cs
  | XLayout => node_layout cs args
  | XIStrncpy => gate0 (x_istrncpy A) (summary_istrncpy A nx0 cs)
  | XPopFree => gate0 (x_popfree A) (summary_popfree A nx0 cs args)
  | XSniff => summary_sniff segs A nx0 cs
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive cres : Type := COk (s : shape) | CErr (code : Z) (where_ : plan) (cs : acs)
  | CNeed (missing : list vc).    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition cmerge (r1 : cres) (r2 : unit -> cres) (ok : shape -> shape -> cres) : cres :=
  match r1 with
  | CErr c q x => CErr c q x
  | COk s1 => match r2 tt with COk s2 => ok s1 s2 | CNeed l2 => CNeed l2 | CErr c q x => CErr c q x end
  | CNeed l1 => match r2 tt with COk _ => CNeed l1 | CNeed l2 => CNeed (l1 ++ l2) | CErr c q x => CErr c q x end
  end.
(* [comment removed for export] *)
Definition ginst (sg : sbind) (g : gatom) : gatom := GA (g_id g) (map (esubsts sg) (g_args g)).

(* [comment removed for export] *)
Record segdef : Type := SEG {
  sg_lo : nat; sg_hi : nat;
  sg_in : acs;
  sg_w : list (saddr * expr);
  sg_outs : list acs;
  sg_shape : shape;
  sg_body : plan; sg_fuel : nat; sg_bfuel : nat }.
(* [comment removed for export] *)
Record xparams : Type := XP {
  xp_sg : nat -> option segdef;
  xp_wb : option (list (saddr * expr) * nat);
  xp_extF : nat -> bool;
  xp_gh : gparams;                 (* [comment removed for export] *)
  xp_extG : nat -> bool;           (* [comment removed for export] *)
  (* [comment removed for export] *)
  xp_sysws : snode -> acs -> option (list (saddr * expr));
  xp_xnws : nat -> list expr -> acs -> option (list (saddr * expr));
  xp_xews : nat -> list expr -> acs -> option (list (saddr * expr));
  (* [comment removed for export] *)
  xp_xws : xnode -> list expr -> acs -> option (list (saddr * expr));
  (* [comment removed for export] *)
  xp_hq : bool }.
Definition XP0 : xparams := XP (fun _ => None) None (fun _ => false) G0 (fun _ => false) (fun _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) false.
(* [comment removed for export] *)
Definition XPS : xparams := XP (fun _ => None) None (fun _ => false) G0 (fun _ => false) (fun _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) true.
(* [comment removed for export] *)
Definition XPG (G : gparams) : xparams := XP (fun _ => None) None (fun _ => false) G (fun _ => false) (fun _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) false.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xp_seg (xp : xparams) (W : list (saddr * expr)) (wlo : nat) (cur : nat) : xparams :=
  XP (fun sid => if (sid <? cur)%nat then xp_sg xp sid else None) (Some (W, wlo)) (xp_extF xp) (xp_gh xp) (fun _ => false)
     (xp_sysws xp) (xp_xnws xp) (xp_xews xp) (xp_xws xp) false.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ws_inside (fk : list kentry) (ws W : list (saddr * expr)) : bool :=
  forallb (fun w => existsb (fun w' => xinside fk (a_base (fst w)) (a_off (fst w)) (snd w) (a_base (fst w')) (a_off (fst w')) (snd w')) W) ws.

(* [comment removed for export] *)
Definition wvars_lt (b : nat) (W : list (saddr * expr)) : bool :=
  forallb (fun w => expr_vars_lt b (a_base (fst w)) && expr_vars_lt b (snd w))%bool W.
(* [comment removed for export] *)
Definition acs_frame_eqb (x y : acs) : bool :=
  (list_eqb amap_eqb (a_maps x) (a_maps y) && Z.eqb (a_totsz x) (a_totsz y) && Z.eqb (a_ylo x) (a_ylo y)
   && Z.eqb (a_eager x) (a_eager y) && list_eqb pair_eqb (a_vis x) (a_vis y)
   && list_eqb pair_eqb (a_ghost x) (a_ghost y) && Z.eqb (a_abytes x) (a_abytes y)
   && expr_eqb (a_brk x) (a_brk y) && afd_eqb (a_fd x) (a_fd y) && Bool.eqb (a_tidset x) (a_tidset y))%bool.
Definition segdef_wf (SD : segdef) : bool :=
  (Nat.leb nx0 (sg_lo SD) && Nat.leb (sg_lo SD) (sg_hi SD) && Nat.eqb (nxt (sg_in SD)) (sg_hi SD)
   && template_ok nx0 (sg_lo SD) (sg_in SD)
   && forallb (fun x => template_ok nx0 (sg_hi SD) x && acs_frame_eqb (sg_in SD) x)%bool (sg_outs SD)
   && wvars_lt (sg_hi SD) (sg_w SD)
   && shape_vars_lt nx0 (sg_shape SD)
   && no_next (sg_shape SD)                                                        (* [comment removed for export] *)
   && match a_props (sg_in SD) with [] => true | _ => false end)%bool.             (* [comment removed for export] *)

(* [comment removed for export] *)
Definition shiftb (lo top d : nat) : sbind := map (fun v => (v, EVar (v + d)%nat)) (seq lo (top - lo)).
Definition sg_top (SD : segdef) : nat := fold_left Nat.max (map nxt (sg_outs SD)) (sg_hi SD).
Definition kpure (K : kentry) : bool := match K with KAlign _ _ | KRange _ _ _ | KDisj _ _ _ _ => true | _ => false end.
Definition kfoot (K : kentry) : option (saddr * expr) :=
  match K with
  | KWord a w _ => Some (a, ELit (Z.of_nat w))
  | KZero a n | KBlob a n _ | KFill a n _ | KUnk a n | KWr a n => Some (a, n)
  | KImg lo hi => if Z.ltb (hi - lo) two64 then Some (SA (ELit 0) lo, ELit (hi - lo)) else None   (* [comment removed for export] *)
  | _ => None
  end.
Definition frame_keep (fk : list kentry) (W : list (saddr * expr)) (K : kentry) : bool :=
  (kpure K || match kfoot K with
              | Some (a, n) => forallb (fun w => ranges_apart_x fk (a_base a) (a_off a) n (a_base (fst w)) (a_off (fst w)) (snd w)) W
              | None => false
              end)%bool.
(* [comment removed for export] *)
Definition kresize (K : kentry) (kk : Z) (n : Z) : option kentry :=
  match K with
  | KZero (SA b _) _ => Some (KZero (SA b kk) (ELit n))
  | KUnk (SA b _) _ => Some (KUnk (SA b kk) (ELit n))
  | KFill (SA b _) _ c => Some (KFill (SA b kk) (ELit n) c)
  | KWr (SA b _) _ => Some (KWr (SA b kk) (ELit n))
  | _ => None
  end.
Definition opt_list {T : Type} (o : option T) : list T := match o with Some x => [x] | None => [] end.
Definition cut_by (fk : list kentry) (w : saddr * expr) (P : kentry) : list kentry :=
  match kfoot P with
  | None => []
  | Some (SA pb pk, pl) =>
      let '(SA wb wk, wl) := (fst w, snd w) in
      if ranges_apart_x fk pb pk pl wb wk wl then [P] else
      match pl with
      | ELit n =>
          if (expr_eqb pb wb && Z.leb 0 n && Z.ltb n two64)%bool then
            match xhi fk wl with
            | Some wh =>
                (if Z.ltb pk (Z.min (pk + n) wk) then opt_list (kresize P pk (Z.min (pk + n) wk - pk)) else [])
                ++ (let lo2 := Z.max pk (wk + wh) in
                    if Z.ltb lo2 (pk + n) then opt_list (kresize P lo2 (pk + n - lo2)) else [])
            | None => []
            end
          else []
      | _ => []
      end
  end.
Definition wcut (fk : list kentry) (W : list (saddr * expr)) (K : kentry) : list kentry :=
  fold_left (fun ps w => flat_map (cut_by fk w) ps) W [K].
(* [comment removed for export] *)
Definition ranges_apart_q (kn : list kentry) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match base_range kn b1, sp_rng sp with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then true
      else if in_sides kn (sp_D sp) b1 k1 m1 then true
      else lin_apart kn b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match base_range kn b1, sp_rng sp, xhi kn n1, sp_h1 sp with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else
            if match end_hi kn b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hi kn b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_x kn (sp_Dx sp) b1 k1 n1 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0 kn [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0 kn [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.
Lemma in_sides_mirror : forall allkn kn b1 k1 n1 b2 k2 n2,
  in_sides allkn (disj_sides allkn kn b2 k2 n2) b1 k1 n1 = kdisj_apart allkn kn b1 k1 n1 b2 k2 n2.
Proof.
  intros allkn kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; [reflexivity|].
  destruct K as [| | | | | | |c1 m1 c2 m2| |]; cbn [disj_sides kdisj_apart]; try exact IH.
  destruct (sub_itv allkn b2 k2 n2 c1 m1), (sub_itv allkn b2 k2 n2 c2 m2); cbn [in_sides];
    destruct (sub_itv allkn b1 k1 n1 c2 m2) eqn:E2, (sub_itv allkn b1 k1 n1 c1 m1) eqn:E1;
    rewrite ?E1, ?E2, ?IH; reflexivity.
Qed.
Lemma in_sides_x_mirror : forall allkn kn b1 k1 n1 b2 k2 n2,
  in_sides_x allkn (disj_sides_x allkn kn b2 k2 n2) b1 k1 n1 = kdisj_apart_x allkn kn b1 k1 n1 b2 k2 n2.
Proof.
  intros allkn kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; [reflexivity|].
  destruct K as [| | | | | | |c1 m1 c2 m2| |]; cbn [disj_sides_x kdisj_apart_x]; try exact IH.
  destruct (sub_itv_x allkn b2 k2 n2 c1 m1), (sub_itv_x allkn b2 k2 n2 c2 m2); cbn [in_sides_x];
    destruct (sub_itv_x allkn b1 k1 n1 c2 m2) eqn:E2, (sub_itv_x allkn b1 k1 n1 c1 m1) eqn:E1;
    rewrite ?E1, ?E2, ?IH; reflexivity.
Qed.
Lemma ranges_apart_q_eq : forall kn b1 k1 n1 b2 k2 n2,
  ranges_apart_q kn (mk_sprep kn b2 k2 n2) b1 k1 n1 b2 k2 n2 = ranges_apart_x kn b1 k1 n1 b2 k2 n2.
Proof.
  intros kn b1 k1 n1 b2 k2 n2. unfold ranges_apart_q, ranges_apart_x, mk_sprep. cbn [sp_rng sp_h1 sp_D sp_Dx].
  destruct n1; try (rewrite in_sides_x_mirror; reflexivity).
  destruct n2; try (rewrite in_sides_x_mirror; reflexivity).
  unfold ranges_apart. rewrite in_sides_mirror. reflexivity.
Qed.
Definition ranges_apart_qB (bc : AX2B.bctx) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match AX2B.base_rangeB bc b1, sp_rng sp with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then true
      else if AX2B.in_sidesB bc (sp_D sp) b1 k1 m1 then true
      else AX2B.lin_apartB bc b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match AX2B.base_rangeB bc b1, sp_rng sp, AX2B.xhiB bc n1, sp_h1 sp with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else
            if match AX2B.end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match AX2B.end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if AX2B.in_sides_xB bc (sp_Dx sp) b1 k1 n1 then true
    else if negb (shares_var b1 b2) then false
    else if AX2B.lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else AX2B.lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.
Lemma ranges_apart_qB_eqf : forall fk, ranges_apart_qB (AX2B.mkbc fk) = ranges_apart_q fk.
Proof.
  intros. AX2B.bcfe. unfold ranges_apart_qB, ranges_apart_q.
  rewrite ?AX2B.base_rangeB_eqf, ?AX2B.in_sidesB_eqf, ?AX2B.lin_apartB_eqf, ?AX2B.xhiB_eqf, ?AX2B.end_hiB_eqf, ?AX2B.in_sides_xB_eqf, ?AX2B.lin_ge0B_eqf.
  reflexivity.
Qed.
(* [comment removed for export] *)
Record ehq := EHQ { q_br : option (Z * Z); q_h1 : option Z; q_e1 : option Z }.
Definition mk_ehq (bc : AX2B.bctx) (b1 : expr) (k1 : Z) (n1 : expr) : ehq :=
  let br := AX2B.base_rangeB bc b1 in let h1 := AX2B.xhiB bc n1 in
  EHQ br h1 (match br, h1 with Some (lo1, hi1), Some h => AX2B.end_hiB bc b1 k1 n1 lo1 hi1 h | _, _ => None end).
Definition ranges_apart_qHB (bc : AX2B.bctx) (sp : sprep) (q : ehq) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match q_br q, sp_rng sp with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then true
      else if AX2B.in_sidesB bc (sp_D sp) b1 k1 m1 then true
      else AX2B.lin_apartB bc b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match q_br q, sp_rng sp, q_h1 q, sp_h1 sp with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else
            if match q_e1 q with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match AX2B.end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if AX2B.in_sides_xB bc (sp_Dx sp) b1 k1 n1 then true
    else if negb (shares_var b1 b2) then false
    else if AX2B.lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else AX2B.lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.
Lemma ranges_apart_qHB_eq : forall bc sp b1 k1 n1 b2 k2 n2,
  ranges_apart_qHB bc sp (mk_ehq bc b1 k1 n1) b1 k1 n1 b2 k2 n2 = ranges_apart_qB bc sp b1 k1 n1 b2 k2 n2.
Proof.
  intros. unfold ranges_apart_qHB, ranges_apart_qB, mk_ehq. cbn [q_br q_h1 q_e1].
  destruct (AX2B.base_rangeB bc b1) as [[lo1 hi1]|], (AX2B.xhiB bc n1) as [h1|]; reflexivity.
Qed.

Definition cut_byQ (bc : AX2B.bctx) (wp : (saddr * expr) * sprep) (P : kentry) : list kentry :=
  match kfoot P with
  | None => []
  | Some (SA pb pk, pl) =>
      let '(SA wb wk, wl) := (fst (fst wp), snd (fst wp)) in
      if ranges_apart_qB bc (snd wp) pb pk pl wb wk wl then [P] else
      match pl with
      | ELit n =>
          if (expr_eqb pb wb && Z.leb 0 n && Z.ltb n two64)%bool then
            match sp_h1 (snd wp) with
            | Some wh =>
                (if Z.ltb pk (Z.min (pk + n) wk) then opt_list (kresize P pk (Z.min (pk + n) wk - pk)) else [])
                ++ (let lo2 := Z.max pk (wk + wh) in
                    if Z.ltb lo2 (pk + n) then opt_list (kresize P lo2 (pk + n - lo2)) else [])
            | None => []
            end
          else []
      | _ => []
      end
  end.
Definition wcutQ (bc : AX2B.bctx) (wps : list ((saddr * expr) * sprep)) (K : kentry) : list kentry :=
  fold_left (fun ps wp => flat_map (cut_byQ bc wp) ps) wps [K].
(* [comment removed for export] *)
Definition wcutQ2 (bc : AX2B.bctx) (wps : list ((saddr * expr) * sprep)) (K : kentry) : list kentry :=
  match kfoot K with
  | Some (SA pb pk, pl) =>
      let q := mk_ehq bc pb pk pl in
      if forallb (fun wp : (saddr * expr) * sprep =>
                    ranges_apart_qHB bc (snd wp) q pb pk pl (a_base (fst (fst wp))) (a_off (fst (fst wp))) (snd (fst wp))) wps
      then [K] else wcutQ bc wps K
  | None => wcutQ bc wps K
  end.
Lemma wcutQ2_eq : forall bc wps K, wcutQ2 bc wps K = wcutQ bc wps K.
Proof.
  intros bc wps K. unfold wcutQ2. destruct (kfoot K) as [[[pb pk] pl]|] eqn:HF; [|reflexivity].
  destruct (forallb _ wps) eqn:HA; [|reflexivity]. unfold wcutQ. symmetry.
  induction wps as [|[[[wb wk] wl] sp] r IH]; [reflexivity|].
  cbn [forallb fst snd a_base a_off] in HA. apply andb_prop in HA as [H1 H2].
  cbn [fold_left flat_map]. rewrite app_nil_r.
  replace (cut_byQ bc (SA wb wk, wl, sp) K) with [K]; [exact (IH H2)|].
  unfold cut_byQ. rewrite HF. cbn [fst snd]. rewrite ranges_apart_qHB_eq in H1. rewrite H1. reflexivity.
Qed.
Definition frameQ (k : list kentry) (W : list (saddr * expr)) : list kentry :=
  let bc := AX2B.mkbc (facts_of k) in
  let wps := map (fun w => (w, AX2B.mk_sprepB bc (a_base (fst w)) (a_off (fst w)) (snd w))) W in
  flat_map (fun K => if kpure K then [K] else match kfoot K with Some _ => wcutQ2 bc wps K | None => [] end) k.

Lemma cut_byQ_eq : forall fk w P,
  cut_byQ (AX2B.mkbc fk) (w, AX2B.mk_sprepB (AX2B.mkbc fk) (a_base (fst w)) (a_off (fst w)) (snd w)) P = cut_by fk w P.
Proof.
  intros fk [[wb wk] wl] P. unfold cut_byQ, cut_by. cbn [fst snd a_base a_off].
  destruct (kfoot P) as [[[pb pk] pl]|]; [|reflexivity].
  rewrite ranges_apart_qB_eqf, AX2B.mk_sprepB_eqf, ranges_apart_q_eq. unfold mk_sprep. cbn [sp_h1]. reflexivity.
Qed.
Lemma wcutQ_eq : forall fk W K,
  wcutQ (AX2B.mkbc fk) (map (fun w => (w, AX2B.mk_sprepB (AX2B.mkbc fk) (a_base (fst w)) (a_off (fst w)) (snd w))) W) K = wcut fk W K.
Proof.
  intros fk W K. unfold wcutQ, wcut. generalize [K] as ps. induction W as [|w r IH]; intros ps; [reflexivity|].
  cbn [map fold_left]. rewrite <- IH. f_equal. apply flat_map_ext. intros P. apply cut_byQ_eq.
Qed.
Lemma frameQ_eq : forall k W,
  frameQ k W = flat_map (fun K => if kpure K then [K] else match kfoot K with Some _ => wcut (facts_of k) W K | None => [] end) k.
Proof.
  intros k W. unfold frameQ. cbv zeta. apply flat_map_ext. intros K. destruct (kpure K); [reflexivity|].
  destruct (kfoot K); [|reflexivity]. rewrite wcutQ2_eq. apply wcutQ_eq.
Qed.
(* [comment removed for export] *)
Definition fp_apartE (k : list kentry) (W : list (saddr * expr)) (r : expr * expr) : bool :=
  forallb (fun w => ranges_apart_x k (a_base (fst w)) (a_off (fst w)) (snd w) (fst r) 0 (snd r)) W.
Definition gkeep1E (G : gparams) (k : list kentry) (W : list (saddr * expr)) (nx : nat) (g : gatom) : bool :=
  (gvars_lt nx g && forallb (fp_apartE k W) (g_fp G (g_id g) (g_args g)))%bool.
Definition gkeepE (G : gparams) (W : list (saddr * expr)) (cs cs' : acs) : acs :=
  set_props cs' (List.filter (gkeep1E G (facts_of (kn cs)) W (nxt cs)) (a_props cs)).
(* [comment removed for export] *)
Definition fp_apartEB (bc : AX2B.bctx) (W : list (saddr * expr)) (r : expr * expr) : bool :=
  forallb (fun w => AX2B.ranges_apart_xB bc (a_base (fst w)) (a_off (fst w)) (snd w) (fst r) 0 (snd r)) W.
Definition gkeep1EB (G : gparams) (bc : AX2B.bctx) (W : list (saddr * expr)) (nx : nat) (g : gatom) : bool :=
  (gvars_lt nx g && forallb (fp_apartEB bc W) (g_fp G (g_id g) (g_args g)))%bool.
Lemma gkeep1EB_eqf : forall G k, gkeep1EB G (AX2B.mkbc k) = gkeep1E G k.
Proof.
  intros. apply functional_extensionality; intros W. apply functional_extensionality; intros nx. apply functional_extensionality; intros g.
  unfold gkeep1EB, gkeep1E, fp_apartEB, fp_apartE. rewrite AX2B.ranges_apart_xB_eqf. reflexivity.
Qed.
Lemma gkeep1E_nil : forall G fk fk' nx, gkeep1E G fk [] nx = gkeep1E G fk' [] nx.
Proof. intros. apply functional_extensionality; intros g. reflexivity. Qed.
Definition gkeepEM (G : gparams) (W : list (saddr * expr)) (cs cs' : acs) : acs :=
  match a_props cs with
  | [] => set_props cs' []
  | props =>
      match W with
      | [] => set_props cs' (List.filter (gkeep1E G [] [] (nxt cs)) props)   (* [comment removed for export] *)
      | _ => let bc := AX2B.mkbc (facts_of (kn cs)) in set_props cs' (List.filter (gkeep1EB G bc W (nxt cs)) props)
      end
  end.
Lemma gkeepEM_eq : gkeepEM = gkeepE.
Proof.
  apply functional_extensionality; intros G. apply functional_extensionality; intros W.
  apply functional_extensionality; intros cs. apply functional_extensionality; intros cs'.
  unfold gkeepEM, gkeepE. destruct (a_props cs); [reflexivity|].
  destruct W as [|w W']; [rewrite (gkeep1E_nil G [] (facts_of (kn cs))); reflexivity|].
  cbv zeta. rewrite gkeep1EB_eqf. reflexivity.
Qed.
(* [comment removed for export] *)
Definition gkeepP (G : gparams) (W : list (saddr * expr)) (cs cs' : acs) : acs :=
  set_props cs' (List.filter (gkeep1E G (facts_of (kn cs')) W (nxt cs)) (a_props cs)).
(* [comment removed for export] *)
Definition gkeepPM (G : gparams) (W : list (saddr * expr)) (cs cs' : acs) : acs :=
  match a_props cs with
  | [] => set_props cs' []
  | props => let bc := AX2B.mkbc (facts_of (kn cs')) in set_props cs' (List.filter (gkeep1EB G bc W (nxt cs)) props)
  end.
Lemma gkeepPM_eq : gkeepPM = gkeepP.
Proof.
  apply functional_extensionality; intros G. apply functional_extensionality; intros W.
  apply functional_extensionality; intros cs. apply functional_extensionality; intros cs'.
  unfold gkeepPM, gkeepP. destruct (a_props cs); [reflexivity|]. cbv zeta. rewrite gkeep1EB_eqf. reflexivity.
Qed.
(* [comment removed for export] *)
Definition mmap_win (cs' : acs) : option (list (saddr * expr)) :=
  match a_maps cs' with
  | m :: _ =>
      let nb := am_base m in let ne := am_len m in
      if plain A then Some [(SA nb 0, ne)]
      else let '(sb, sk, sn) := shadow_of A (kn cs') nb ne in
           if flat_x (kn cs') sb sk sn then Some [(SA nb 0, ne); (SA sb sk, sn)] else None
  | [] => None
  end.
Definition wsubsts (sg : sbind) (W : list (saddr * expr)) : list (saddr * expr) :=
  map (fun w => (asubsts sg (fst w), esubsts sg (snd w))) W.
Fixpoint xsplice (sh : shape) (ss : list shape) : shape :=
  match sh with
  | SHole i => nth i ss SNil
  | SEmitP fd ps s' => SEmitP fd ps (xsplice s' ss)
  | SAlt2 a b => SAlt2 (xsplice a ss) (xsplice b ss)
  | SCase e m a b => SCase e m (xsplice a ss) (xsplice b ss)
  | _ => sh
  end.
(* [comment removed for export] *)
Definition anorm (fk : list kentry) (a : saddr) : saddr :=
  match a_base a with
  | ELit c => SA (ELit 0) (zlit64 c + a_off a)
  | EAlu ALU_ADD b (ELit z) =>
      match xlo fk b, xhi fk b with
      | Some lo, Some hi => if ((0 <=? lo + z) && (hi + z <? two64))%Z then SA b (z + a_off a) else a
      | _, _ => a
      end
  | _ => a
  end.
Definition knorm (fk : list kentry) (K : kentry) : kentry :=
  match K with
  | KWord a w v => KWord (anorm fk a) w v
  | KZero a n => KZero (anorm fk a) n
  | KBlob a n k => KBlob (anorm fk a) n k
  | KWr a n => KWr (anorm fk a) n
  | KDisj a1 n1 a2 n2 => KDisj (anorm fk a1) n1 (anorm fk a2) n2
  | KFill a n c => KFill (anorm fk a) n c
  | KUnk a n => KUnk (anorm fk a) n
  | _ => K
  end.
(* [comment removed for export] *)
Definition wnorm (fk : list kentry) (w : saddr * expr) : saddr * expr := (anorm fk (fst w), snd w).
Definition use_exit (sg rho : sbind) (d : nat) (FR : list kentry) (KP : list gatom) (x : acs) : acs :=
  let xr := insts sg (insts rho x) in
  let kx0 := map (knorm (kn xr ++ FR)) (kn xr) in                                (* [comment removed for export] *)
  let kx := List.filter (fun K => negb (kpure K && fact_ok FR K)) kx0 in         (* [comment removed for export] *)
  let FR' := List.filter (fun K => negb (existsb (kentry_eqb K) kx)) FR in      (* [comment removed for export] *)
  set_props (with_ss xr (mk_ss (pc xr) (s_regs (a_ss xr)) (kx ++ FR') (nxt x + d)%nat)) KP.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition use_exitN (sg rho : sbind) (d : nat) (FR : list kentry) (KP : list gatom) (x : acs) : acs :=
  let xr := instsN sg (instsN rho x) in
  let kx0 := map (knorm (kn xr ++ FR)) (kn xr) in
  let kx := List.filter (fun K => negb (kpure K && fact_ok FR K)) kx0 in
  let FR' := List.filter (fun K => negb (existsb (kentry_eqb K) kx)) FR in
  set_props (with_ss xr (mk_ss (pc xr) (s_regs (a_ss xr)) (kx ++ FR') (nxt x + d)%nat)) KP.
Lemma use_exitN_eqf : use_exitN = use_exit.
Proof.
  apply functional_extensionality; intros sg. apply functional_extensionality; intros rho. apply functional_extensionality; intros d.
  apply functional_extensionality; intros FR. apply functional_extensionality; intros KP. apply functional_extensionality; intros x.
  unfold use_exitN, use_exit. rewrite !instsN_eq. reflexivity.
Qed.
(* [comment removed for export] *)
Definition slot_var (lo hi : nat) (e : expr) : option nat :=
  match e with EVar v => if ((lo <=? v) && (v <? hi))%nat then Some v else None | _ => None end.
Fixpoint reskel_maps (lo hi : nat) (sk : list amap) (ms : list amap) {struct sk} : option (list amap * sbind) :=
  match sk with
  | [] => match ms with [] => Some ([], []) | _ => None end
  | s :: sk' =>
      match slot_var lo hi (am_base s), slot_var lo hi (am_len s) with
      | Some b, Some l =>
          match ms with
          | [] => match reskel_maps lo hi sk' [] with
                  | Some (r, sg) => Some (r, (b, ELit 0) :: (l, ELit 0) :: sg)     (* [comment removed for export] *)
                  | None => None end
          | m :: ms' => match reskel_maps lo hi sk' ms' with
                        | Some (r, sg) => Some (AM (EVar b) (EVar l) (am_kind m) :: r, (b, am_base m) :: (l, am_len m) :: sg)
                        | None => None end
          end
      | _, _ => None
      end
  end.
Fixpoint reskel_pairs (lo hi : nat) (sk : list (expr * expr)) (ps : list (expr * expr)) {struct sk} : option (list (expr * expr) * sbind) :=
  match sk with
  | [] => match ps with [] => Some ([], []) | _ => None end
  | s :: sk' =>
      match slot_var lo hi (fst s), slot_var lo hi (snd s) with
      | Some b, Some l =>
          match ps with
          | [] => match reskel_pairs lo hi sk' [] with
                  | Some (r, sg) => Some (r, (b, ELit 0) :: (l, ELit 0) :: sg)
                  | None => None end
          | q :: ps' => match reskel_pairs lo hi sk' ps' with
                        | Some (r, sg) => Some ((EVar b, EVar l) :: r, (b, fst q) :: (l, snd q) :: sg)
                        | None => None end
          end
      | _, _ => None
      end
  end.
(* [comment removed for export] *)
Definition reskel (lo hi : nat) (SK L : ledger) : option (ledger * sbind) :=
  match reskel_maps lo hi (lg_maps SK) (lg_maps L), reskel_pairs lo hi (lg_vis SK) (lg_vis L), reskel_pairs lo hi (lg_ghost SK) (lg_ghost L) with
  | Some (ms, s1), Some (vs, s2), Some (gs, s3) =>
      Some (LG ms (lg_totsz L) (lg_ylo L) (lg_eager L) vs gs (lg_abytes L), s1 ++ s2 ++ s3)
  | _, _, _ => None
  end.
Definition reledger_sd (L : ledger) (SD : segdef) : segdef :=
  SEG (sg_lo SD) (sg_hi SD) (with_ledger L (sg_in SD)) (sg_w SD) (map (with_ledger L) (sg_outs SD))
      (sg_shape SD) (sg_body SD) (sg_fuel SD) (sg_bfuel SD).
(* [comment removed for export] *)

Definition core_vars_lt (b : nat) (x : acs) : bool :=
  (sr_vars_lt b (s_regs (a_ss x)) && kn_vars_lt b (kn x) && expr_vars_lt b (a_brk x) && fd_vars_lt b (a_fd x)
   && forallb (gvars_lt b) (a_props x))%bool.
(* [comment removed for export] *)
Fixpoint expr_vars_allb (P : nat -> bool) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => P n
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_allb P x && expr_vars_allb P y
  | EExt _ _ _ x => expr_vars_allb P x
  | EBlob _ _ _ _ => true
  end%bool.
Definition saddr_vars_allb (P : nat -> bool) (a : saddr) : bool := expr_vars_allb P (a_base a).
Definition kentry_vars_allb (P : nat -> bool) (K : kentry) : bool :=
  (match K with
   | KWord a _ v => saddr_vars_allb P a && expr_vars_allb P v
   | KZero a n => saddr_vars_allb P a && expr_vars_allb P n
   | KBlob a n _ => saddr_vars_allb P a && expr_vars_allb P n
   | KImg _ _ => true
   | KAlign e _ => expr_vars_allb P e
   | KRange e _ _ => expr_vars_allb P e
   | KWr a n => saddr_vars_allb P a && expr_vars_allb P n
   | KDisj a1 n1 a2 n2 => saddr_vars_allb P a1 && expr_vars_allb P n1 && saddr_vars_allb P a2 && expr_vars_allb P n2
   | KFill a n _ => saddr_vars_allb P a && expr_vars_allb P n
   | KUnk a n => saddr_vars_allb P a && expr_vars_allb P n
   end)%bool.
Definition fd_vars_allb (P : nat -> bool) (f : afd) : bool :=
  match f with FdFile _ l o => (expr_vars_allb P l && expr_vars_allb P o)%bool | _ => true end.
Definition core_vars_allb (P : nat -> bool) (x : acs) : bool :=
  (forallb (expr_vars_allb P) (s_regs (a_ss x)) && forallb (kentry_vars_allb P) (kn x) && expr_vars_allb P (a_brk x)
   && fd_vars_allb P (a_fd x) && forallb (fun g => forallb (expr_vars_allb P) (g_args g)) (a_props x))%bool.
(* [comment removed for export] *)
Definition vout (b hi top : nat) (v : nat) : bool := ((v <? b) || ((hi <=? v) && (v <? top)))%nat.
(* [comment removed for export] *)
Definition evar_ids (l : list expr) : list nat := flat_map (fun e => match e with EVar v => [v] | _ => [] end) l.
Definition skel_ids (L : ledger) : list nat :=
  evar_ids (flat_map (fun m => [am_base m; am_len m]) (lg_maps L))
  ++ evar_ids (flat_map (fun p => [fst p; snd p]) (lg_vis L)) ++ evar_ids (flat_map (fun p => [fst p; snd p]) (lg_ghost L)).
Definition skel_lo (L : ledger) : option nat := match skel_ids L with [] => None | v :: _ => Some v end.
Fixpoint nodup_nat (l : list nat) : bool :=
  match l with [] => true | v :: r => negb (existsb (Nat.eqb v) r) && nodup_nat r end%bool.
Definition skel_free (SD : segdef) : bool :=
  let SK := ledger_of (sg_in SD) in
  match skel_lo SK with
  | Some b => core_vars_lt b (sg_in SD) && forallb (core_vars_allb (vout b (sg_hi SD) (sg_top SD))) (sg_outs SD) && wvars_lt b (sg_w SD)
              && forallb (Nat.leb b) (skel_ids SK) && nodup_nat (skel_ids SK)      (* [comment removed for export] *)
  | None => false
  end%bool.
(* [comment removed for export] *)
Definition use_view (cs : acs) (SD : segdef) : option (segdef * sbind) :=
  if skel_free SD then
    match reskel (sg_lo SD) (sg_hi SD) (ledger_of (sg_in SD)) (ledger_of cs) with
    | Some (L, sk) => Some (reledger_sd L SD, sk)
    | None => None                                   (* [comment removed for export] *)
    end
  else Some (SD, []).
Inductive lres : Type := LOk (ss : list shape) | LErr (r : cres).
Fixpoint use_all (chk : acs -> plan -> cres) (mk : acs -> acs) (p0 : plan) (cs0 : acs) (outs : list acs) (ks : list plan) : lres :=
  match outs, ks with
  | [], [] => LOk []
  | x :: outs', k :: ks' =>
      match chk (mk x) k with
      | COk s => match use_all chk mk p0 cs0 outs' ks' with LOk ss => LOk (s :: ss) | LErr r => LErr r end
      | r => LErr r
      end
  | _, _ => LErr (CErr 3 p0 cs0)
  end.

Section Check.
Variable XN : nat -> list expr -> acs -> option acs.                      (* [comment removed for export] *)
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).  (* [comment removed for export] *)
Variable XB : nat -> list expr -> acs -> option (acs * acs).              (* [comment removed for export] *)
Variable HS : nat -> option acs.   (* [comment removed for export] *)
Variable KC : nat.                 (* [comment removed for export] *)
Variable xp : xparams.             (* [comment removed for export] *)
Variable bfuel : nat.              (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vc_at (cs : acs) (c : vconcl) : vc := VC (kn cs) (a_props cs) c (pc cs).
(* [comment removed for export] *)
Definition vc_implied (c' v : vc) : bool :=
  if vconcl_eqb (vc_concl c') (vc_concl v) then
    if forallb (fun K => existsb (kentry_eqb K) (vc_kn c')) (vc_kn v)
    then forallb (fun g => existsb (gatom_eqb g) (vc_hyps c')) (vc_hyps v) else false
  else false.
(* [comment removed for export] *)
Definition vc_list (L : list vc) (v : vc) : bool := existsb (vc_implied v) L.
Definition need1 (cs : acs) (c : vconcl) : list vc :=
  let trivial := match c with
                 | VCAtom g => existsb (gatom_eqb g) (a_props cs)
                 | VCFact K => existsb (kentry_eqb K) (kn cs)
                 end in
  if trivial then []
  else if g_vcok (xp_gh xp) (vc_at cs c) then [] else [vc_at cs c].   (* [comment removed for export] *)
Definition needs_props (cs : acs) (gs : list gatom) : list vc := flat_map (fun g => need1 cs (VCAtom g)) gs.
(* [comment removed for export] *)
Definition with_props (cs : acs) (gs : list gatom) (r : cres) : cres :=
  match needs_props cs gs with [] => r | l => CNeed l end.
Fixpoint remove_nth {T : Type} (i : nat) (l : list T) : list T :=
  match l, i with [], _ => [] | _ :: r, O => r | x :: r, S j => x :: remove_nth j r end.

(* [comment removed for export] *)
Definition WB : option (list (saddr * expr)) := match xp_wb xp with Some (W, _) => Some W | None => None end.
Definition wbb : bool := match xp_wb xp with Some _ => true | None => false end.
(* [comment removed for export] *)
Definition normT (cs : acs) (l : list (acs * plan)) : list (acs * plan) :=
  if wbb then map (fun hp => (with_ledger (ledger_of cs) (fst hp), snd hp)) l else l.
(* [comment removed for export] *)
Definition okW (ows : option (list (saddr * expr))) (cs : acs) : bool :=
  match xp_wb xp with
  | None => true
  | Some (W, _) => match ows with Some ws => ws_inside (facts_of (kn cs)) ws W | None => false end
  end.
Definition munmap_ws (cs : acs) : option (list (saddr * expr)) :=
  match reg_lit cs 17, mmap_len cs with
  | Some 215, Some (ne, _, _) => let '(bb, bk) := split_lit (reg cs 10) in Some [(SA bb bk, ne)]
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition sys_frame (y : snode) (cs : acs) : option (list (saddr * expr)) :=
  match y with YMunmap => if plain A then munmap_ws cs else None | _ => None end.
Definition sys_okW (y : snode) (cs : acs) : bool := okW (xp_sysws xp y cs) cs.
Definition ext_okW (id : nat) (args : list expr) (cs : acs) : bool := (xp_extF xp id || okW (xp_xnws xp id args cs) cs)%bool.
Definition emit_okW (id : nat) (args : list expr) (cs : acs) : bool := okW (xp_xews xp id args cs) cs.
Definition x_okW (x : xnode) (args : list expr) (cs : acs) : bool := okW (xp_xws xp x args cs) cs.
(* [comment removed for export] *)
Definition erange_any (k : list kentry) (e : expr) : option (Z * Z) :=
  match erange k e with Some r => Some r | None => Some (0%Z, (two64 - 1)%Z) end.
(* [comment removed for export] *)
Definition gsuccW (ows : option (list (saddr * expr))) (cs cs' : acs) : acs :=
  match ows with Some ws => gkeepEM (xp_gh xp) ws cs cs' | None => gpures (xp_gh xp) cs cs' end.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition check_all (chk : acs -> plan -> cres) (k : plan) (css : list acs) : cres :=
  match css with
  | [] => CErr 3 k (init_acs_of A)
  | cs0 :: rest =>
      match chk cs0 k with
      | COk s0 =>
          fold_left (fun acc cs => match acc with
                                   | COk s => match chk cs k with
                                              | COk s' => if shape_eqb s s' then COk s else CErr 6 k cs
                                              | err => err
                                              end
                                   | err => err
                                   end) rest (COk s0)
      | err => err
      end
  end.

(* [comment removed for export] *)
Inductive xres : Type := XOk (xts : list (acs * shape)) | XErr (err : cres).
Fixpoint chk_exits (chk : acs -> plan -> cres) (lo : nat) (xs : shape) (l : list (acs * plan)) : xres :=
  match l with
  | [] => XOk []
  | (x, kx) :: rest =>
      if template_ok nx0 lo x then
        match chk x kx with
        | COk sx => if (no_next sx || is_snext xs)%bool then
                      match chk_exits chk lo xs rest with XOk r => XOk ((x, sx) :: r) | XErr e => XErr e end
                    else XErr (CErr 10 kx x)         (* [comment removed for export] *)
        | err => XErr err                            (* [comment removed for export] *)
        end
      else XErr (CErr 3 kx x)                        (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
Fixpoint chk_heads (chk : option loopctx -> acs -> plan -> cres) (hs : list acs) (cur : nat) (lo : nat) (V : expr) (xs : shape)
         (xts : list (acs * shape)) (l : list (acs * plan)) : cres :=
  match l with
  | [] => COk xs
  | (T, b) :: rest =>
      match chk (Some (WC hs cur lo (nxt T) V xs xts)) T b with
      | COk sb => if shape_eqb sb xs then chk_heads chk hs (S cur) lo V xs xts rest else CErr 7 b T
      | CNeed l =>          (* [comment removed for export] *)
          match chk_heads chk hs (S cur) lo V xs xts rest with
          | CNeed l' => CNeed (l ++ l')
          | CErr c q x => CErr c q x
          | COk _ => CNeed l
          end
      | err => err
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition add_kn_end (cs : acs) (k : list kentry) : acs := set_kn cs (kn cs ++ k).
(* [comment removed for export] *)
Definition fact_okL (k : list kentry) (K : kentry) : bool :=
  match K with KRange e lo hi => krange_lin k e lo hi | _ => false end.
Definition tfact_inst (lc : option loopctx) (cs : acs) (x : bool) (i : nat) (K : kentry) : option kentry :=
  match lc with
  | Some (WC hs cur lo hi V xs xts) =>
      match (if x then match nth_error xts i with Some (T, _) => Some T | None => None end else nth_error hs i) with
      | Some T => Some (ksubsts (infer_sg lo (nxt T) [] cs T) K)
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition rerun_block (stops : list Z) (cs cs' : acs) : bool :=
  (negb (Z.eqb (pc cs') (pc cs)) && negb (existsb (Z.eqb (pc cs')) (stops ++ STOPS A))
   && match itab_lookup IT (pc cs') with Some _ => true | None => false end)%bool.

Fixpoint check (fuel : nat) (lc : option loopctx) (cs : acs) (p : plan) {struct fuel} : cres :=
  match fuel with
  | O => CErr 0 p cs
  | S f =>
  let check_in := check in
  let check (f : nat) := check_in f lc in
  (* [comment removed for export] *)
  let gcb := match lc with Some c => lc_bnd c | None => nx0 end in
  if negb match lc with Some c => Nat.leb (lc_bnd c) (nxt cs) | None => true end then CErr 9 p cs else
  match p with
  | PRun stops k =>
      match run_block_gc_wb_ws segs IT gcb WB KC bfuel (stops ++ STOPS A) cs with   (* [comment removed for export] *)
      | Some (cs', W) =>      (* [comment removed for export] *)
          if rerun_block stops cs cs' then check f (gkeepM (xp_gh xp) W cs cs') (PRun stops k)   (* [comment removed for export] *)
          else check f (gkeepM (xp_gh xp) W cs cs') k
      | None => CErr 1 p cs
      end
  | PSplit e mid k1 k2 =>
      if expr_vars_lt nx0 e then
      match erange (kn cs) e with
      | Some (lo, hi) =>
          if (Z.leb lo mid && Z.ltb mid hi)%bool then
            cmerge (check f (set_kn cs (KRange e lo mid :: kn cs)) k1)
                   (fun _ => check f (set_kn cs (KRange e (mid + 1) hi :: kn cs)) k2)
                   (fun s1 s2 => COk (SCase e mid s1 s2))
          else (* [comment removed for export] *)
            if Z.leb hi mid then check f cs k1 else check f cs k2
      | None => CErr 3 p cs
      end
      else CErr 3 p cs
  | PCase2 e mid k1 k2 =>
      match erange_any (kn cs) e with   (* [comment removed for export] *)
      | Some (lo, hi) =>
          if negb (Z.leb lo mid && Z.ltb mid hi)%bool then (if Z.leb hi mid then check f cs k1 else check f cs k2) else
          if (Z.leb lo mid && Z.ltb mid hi)%bool then
            let cs1 := set_kn cs (KRange e lo mid :: kn cs) in
            let cs2 := set_kn cs (KRange e (mid + 1) hi :: kn cs) in
            (* [comment removed for export] *)
            if kn_contra (kn cs1) then check f cs2 k2
            else if kn_contra (kn cs2) then check f cs1 k1
            else
            cmerge (check f cs1 k1) (fun _ => check f cs2 k2)
                   (fun s1 s2 => if shape_eqb s1 s2 || (xp_hq xp && shape_eqb_holes s1 s2) then COk s1 else CErr 6 p cs)   (* [comment removed for export] *)
          else CErr 3 p cs
      | None => CErr 3 p cs
      end
  | PCaseDisj b1 b2 k1 k2 =>
      match node_casedisj A cs b1 b2 with
      | Some (csa, csb) =>
          cmerge (check f csa k1) (fun _ => check f csb k2)
                 (fun s1 s2 => if shape_eqb s1 s2 || (xp_hq xp && shape_eqb_holes s1 s2) then COk s1 else CErr 6 p cs)   (* [comment removed for export] *)
      | None => CErr 3 p cs
      end
  | PShDisj b1 n1 b2 n2 k => match node_shdisj A cs b1 n1 b2 n2 with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PContra => if kn_contra (kn cs) then COk SNil else CErr 3 p cs
  | PFact K k => if (fact_ok (kn cs) K || fact_okL (kn cs) K)%bool then check f (add_kn cs [K]) k else CErr 3 p cs
  | PJoin b off n k => if wbb then CErr 11 p cs else match node_join segs cs b off n with Some cs' => check f (gkeepEM (xp_gh xp) [] cs cs') k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PForget ixs k => check f (set_kn cs (drop_ixsF ixs 0 (kn cs))) k   (* [comment removed for export] *)
  | PDropRange b n k => check f (node_droprange cs b n) k
  | PGcKeep ws k => check f (set_kn cs (kn_keep (kn cs) ws)) k
  | PBump m k => match node_bump cs m with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PHavoc rs k => match node_havoc nx0 cs rs with Some cs' => check f (gkeepEM (xp_gh xp) [] cs cs') k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PHavocBig K k => match node_havocbig nx0 cs K with Some cs' => check f (gkeepEM (xp_gh xp) [] cs cs') k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PFresh r logc base k => if wbb then CErr 11 p cs else match node_fresh nx0 cs r logc base with Some cs' => check f (gkeepEM (xp_gh xp) [] cs cs') k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PSys y k =>
      if negb (sys_okW y cs) then CErr 11 p cs else   (* [comment removed for export] *)
      if (wbb && match y with YSetTid => false | _ => true end)%bool then CErr 11 p cs else   (* [comment removed for export] *)
      if is_ecall_at segs cs then
        match node_sys y cs with
        | Some cs' => check f (match xp_sysws xp y cs, sys_frame y cs with
                               | Some ws, _ => gkeepEM (xp_gh xp) ws cs cs'              (* [comment removed for export] *)
                               | None, Some W => gkeepEM (xp_gh xp) W cs cs'          (* [comment removed for export] *)
                               | None, None => gpures (xp_gh xp) cs cs'
                               end) k
        | None => CErr 3 p cs end
      else CErr 2 p cs
  | PBrk k =>      (* [comment removed for export] *)
      if wbb then CErr 11 p cs else CErr 3 p cs
  | PBrk2 kg kf =>      (* [comment removed for export] *)
      if wbb then CErr 11 p cs else   (* [comment removed for export] *)
      if is_ecall_at segs cs then
        match node_brk2 A LIMIT cs with
        | Some (csg, csf) =>
            cmerge (check f (gpures (xp_gh xp) cs csg) kg) (fun _ => check f (gpures (xp_gh xp) cs csf) kf)
                   (fun s1 s2 => if shape_eqb s1 s2 || (xp_hq xp && shape_eqb_holes s1 s2) then COk s1 else CErr 6 p cs)
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PMmap k =>      (* [comment removed for export] *)
      if wbb then CErr 11 p cs else   (* [comment removed for export] *)
      if is_ecall_at segs cs then
        match node_mmap A nx0 LIMIT cs with
        | Some cs' => check f (match mmap_win cs' with                (* [comment removed for export] *)
                               | Some W => gkeepPM (xp_gh xp) W cs cs'  (* [comment removed for export] *)
                               | None => gpures (xp_gh xp) cs cs' end) k
        | None => CErr 3 p cs end
      else CErr 2 p cs
  | PMmapIn k =>
      if wbb then CErr 11 p cs else   (* [comment removed for export] *)
      if is_ecall_at segs cs then
        match node_mmapin A LIMIT cs with Some cs' => check f (gpures (xp_gh xp) cs cs') k | None => CErr 3 p cs end
      else CErr 2 p cs
  | PMprotect k =>
      if wbb then CErr 11 p cs else   (* [comment removed for export] *)
      if is_ecall_at segs cs then
        match node_mprotect A LIMIT cs with Some cs' => check f (gpures (xp_gh xp) cs cs') k | None => CErr 3 p cs end
      else CErr 2 p cs
  | PX x args k =>
      if negb (x_okW x args cs) then CErr 11 p cs else   (* [comment removed for export] *)
      match node_x x args cs with Some cs' => check f (gsuccW (xp_xws xp x args cs) cs cs') k | None => CErr 3 p cs end
  | PExt id args k =>
      if negb (ext_okW id args cs) then CErr 11 p cs else   (* [comment removed for export] *)
      if xp_extG xp id then        (* [comment removed for export] *)
        (if wbb then CErr 11 p cs else
         match XN id args cs with Some cs' => check f cs' k | None => CErr 3 p cs end)
      else
      match XN id args cs with
      | Some cs' => check f (if xp_extF xp id then gkeepEM (xp_gh xp) [] cs cs'          (* [comment removed for export] *)
                             else gsuccW (xp_xnws xp id args cs) cs cs') k              (* [comment removed for export] *)
      | None => CErr 3 p cs
      end
  | PEmit id args k =>
      if negb (emit_okW id args cs) then CErr 11 p cs else   (* [comment removed for export] *)
      match XE id args cs with
      | Some (fd, ps, cs') => match check f (gsuccW (xp_xews xp id args cs) cs cs') k with COk s => COk (SEmitP fd ps s) | err => err end
      | None => CErr 3 p cs
      end
  | PExt2 id args k1 k2 =>
      if wbb then CErr 11 p cs else   (* [comment removed for export] *)
      match XB id args cs with
      | Some (csa, csb) =>
          cmerge (check f (gpures (xp_gh xp) cs csa) k1) (fun _ => check f (gpures (xp_gh xp) cs csb) k2) (fun sa sb => COk (SAlt2 sa sb))
      | None => CErr 3 p cs
      end
  | PLoop J N inv body k =>
      if wbb then CErr 11 p cs else   (* [comment removed for export] *)
      if negb (match a_props inv with [] => true | _ => false end) then CErr 3 p cs else   (* [comment removed for export] *)
      match loop_ok nx0 cs J N inv with
      | Some nhi =>
          let lo := S J in let hi := nxt inv in
          if (Z.eqb (pc inv) (pc cs) && entails_hM A lo hi cs (inst inv J (ELit 0)))%bool then
            match check_in f (Some (LC (pc cs) (inst inv J (eaddz (EVar J) 1)) lo hi)) (loop_body_state J N nhi inv) body with
            | COk SNext => check f (inst inv J N) k
            | COk _ => CErr 7 p cs
            | err => err
            end
          else CErr 3 p cs
      | None => CErr 3 p cs
      end
  | PNext =>
      match lc with
      | Some (LC h nx lo hi) =>
          if (Z.eqb (pc cs) h && entails_hM A lo hi cs nx)%bool then COk SNext else CErr 3 p cs
      | Some (WC (T :: _) cur lo hi V xs _) =>      (* [comment removed for export] *)
          match (if Z.eqb (pc cs) (pc T) then entails_sM A lo (nxt T) [] cs T else None) with
          | Some sg => if (variant_ok (kn cs) sg V cur 0 && shape_vars_lt nx0 xs)%bool
                       then with_props cs (map (ginst sg) (a_props T)) (COk xs) else CErr 3 p cs
          | None => CErr 3 p cs
          end
      | _ => CErr 8 p cs
      end
  (* [comment removed for export] *)
  | PWhileN lo heads0 V xs exits0 =>
      (* [comment removed for export] *)
      let heads := normT cs heads0 in
      let exits := normT cs exits0 in
      match heads with
      | [] => CErr 3 p cs
      | (T0, _) :: _ =>
        if (while_okN nx0 cs lo (map fst heads) V xs && Z.eqb (pc cs) (pc T0))%bool then
          match entails_sM A lo (nxt T0) [] cs T0 with
          | Some sg =>
              match needs_props cs (map (ginst sg) (a_props T0)) with
              | [] =>
                match chk_exits (check f) lo xs exits with
                | XOk xts => chk_heads (check_in f) (map fst heads) 0 lo V xs xts heads
                | XErr err => err
                end
              | l => CNeed l
              end
          | None => CErr 3 p cs
          end
        else CErr 3 p cs
      end
  | PNextN h hints =>
      match lc with
      | Some (WC hs cur lo hi V xs _) =>
          match nth_error hs h with
          | Some T =>
              match (if Z.eqb (pc cs) (pc T) then entails_sM A lo (nxt T) hints cs T else None) with
              | Some sg => if (variant_ok (kn cs) sg V cur h && shape_vars_lt nx0 xs)%bool
                           then with_props cs (map (ginst sg) (a_props T)) (COk xs) else CErr 3 p cs
              | None => CErr 3 p cs
              end
          | None => CErr 4 p cs
          end
      | _ => CErr 8 p cs
      end
  | PBreak i hints =>
      match lc with
      | Some (WC hs cur lo hi V xs xts) =>
          match nth_error xts i with
          | Some (x, sx) =>
              match entails_sM A lo (nxt x) hints cs x with
              | Some sg => if shape_vars_lt nx0 sx then with_props cs (map (ginst sg) (a_props x)) (COk sx) else CErr 3 p cs
              | None => CErr 3 p cs
              end
          | None => CErr 4 p cs
          end
      (* [comment removed for export] *)
      | Some (SC outs hi) =>
          match nth_error outs i with
          | Some x =>
              match entails_sM A hi (nxt x) hints cs x with
              | Some _ => COk (SHole 0)     (* [comment removed for export] *)
              | None => CErr 3 p cs
              end
          | None => CErr 4 p cs
          end
      | _ => CErr 8 p cs
      end
  (* [comment removed for export] *)
  | PUse sid hints0 ks =>                       (* [comment removed for export] *)
      match xp_sg xp sid with
      | None => CErr 12 p cs
      | Some SD0 =>
          if negb (segdef_wf SD0) then CErr 12 p cs else   (* [comment removed for export] *)
          (* [comment removed for export] *)
          match use_view cs SD0 with
          | None => CErr 12 p cs
          | Some (SD, skh) =>
          (* [comment removed for export] *)
          if (wbb && negb (skel_free SD0))%bool then CErr 12 p cs else
          let n := Nat.max (sg_lo SD) (nxt cs) in
          let d := (n - sg_lo SD)%nat in
          let hints := map (fun ve => ((fst ve + d)%nat, snd ve)) skh ++ hints0 in   (* [comment removed for export] *)
          let rho := shiftb (sg_lo SD) (sg_top SD) d in
          match entails_sM A n (n + (sg_hi SD - sg_lo SD))%nat hints cs (instsN rho (sg_in SD)) with
          | None => CErr 3 p cs
          | Some sg =>
              if negb (fresh_ok nx0 cs && forallb (fun b => expr_vars_lt n (snd b)) sg)%bool then CErr 3 p cs else
              let Wc := map (wnorm (facts_of (kn cs))) (wsubsts sg (wsubsts rho (sg_w SD))) in   (* [comment removed for export] *)
              if negb (okW (Some Wc) cs) then CErr 11 p cs else   (* [comment removed for export] *)
              let FR := frameQ (kn cs) Wc in   (* [comment removed for export] *)
              let KP := List.filter (gkeep1E (xp_gh xp) (facts_of (kn cs)) Wc (nxt cs)) (a_props cs) in   (* [comment removed for export] *)
              match use_all (check f) (use_exitN sg rho d FR KP) p cs (sg_outs SD) ks with
              | LOk ss => if forallb (shape_eqb (nth 0 ss SNil)) ss then COk (xsplice (sg_shape SD) ss)
                         else CErr 6 p cs        (* [comment removed for export] *)
              | LErr r => r
              end
          end
          end
      end
  | PHandoff h =>
      if wbb then CErr 11 p cs else   (* [comment removed for export] *)
      match HS h with
      | Some ch => if entails cs ch then with_props cs (a_props ch) (COk (SHole h)) else CErr 3 p cs
      | None =>
          (* [comment removed for export] *)
          if Nat.leb 1000 h then
            CNeed [VC (map (fun ir : nat * expr => KWord (SA (ELit 7777777) (Z.of_nat (fst ir))) 8 (snd ir))
                            (combine (seq 0 32) (s_regs (a_ss cs)))
                       ++ KWord (SA (ELit 7777777) 32) 8 (ELit (Z.of_nat (nxt cs))) :: kn cs)
                      (a_props cs) (VCFact (KUnk (SA (ELit 7777777) (Z.of_nat h)) (ELit 0))) (pc cs)]
          else CErr 4 p cs
      end
  | PHandoffS h lo hints =>     (* [comment removed for export] *)
      if wbb then CErr 11 p cs else   (* [comment removed for export] *)
      match HS h with
      | Some ch =>
          match (if (Nat.leb nx0 lo && match s_log (a_ss ch) with [] => true | _ => false end)%bool
                 then entails_sM A lo (nxt ch) hints cs ch else None) with
          | Some sg => with_props cs (map (ginst sg) (a_props ch)) (COk (SHole h))
          | None => CErr 3 p cs
          end
      | None => CErr 4 p cs
      end
  | PExit =>
      if is_ecall_at segs cs then
        match node_exit cs with Some code => COk (SExit code) | None => CErr 3 p cs end
      else CErr 2 p cs
  | PSpin => if node_spin segs cs then COk SNil else CErr 2 p cs
  | PFog i sz k => if wbb then CErr 11 p cs else   (* [comment removed for export] *)
                   match node_fog cs i sz with Some cs' => check f (gpures (xp_gh xp) cs cs') k | None => CErr 3 p cs end
  | PFogNew i sz k => if wbb then CErr 11 p cs else   (* [comment removed for export] *)
                      match node_fognew cs i sz with Some cs' => check f (gpures (xp_gh xp) cs cs') k | None => CErr 3 p cs end
  | PGhost b n k => if wbb then CErr 11 p cs else match node_ghost LIMIT cs b n with Some cs' => check f (gpures (xp_gh xp) cs cs') k | None => CErr 3 p cs end
  | PUnvis b n k => if wbb then CErr 11 p cs else match node_unvis A cs b n with Some cs' => check f (gpures (xp_gh xp) cs cs') k | None => CErr 3 p cs end
  | PHavocBrk lo hi k => match node_havocbrk nx0 cs lo hi with Some cs' => check f (gpures (xp_gh xp) cs cs') k | None => CErr 3 p cs end
  | PIntro lo hi k => match node_intro nx0 cs lo hi with Some cs' => check f (gkeepEM (xp_gh xp) [] cs cs') k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PRename m k => if wbb then CErr 11 p cs else   (* [comment removed for export] *)
                   match node_rename gcb cs m with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PCompact k => if wbb then CErr 11 p cs else   (* [comment removed for export] *)
                  match node_compact gcb cs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PVia j js lo karms k =>
      if wbb then CErr 11 p cs else   (* [comment removed for export] *)
      if (via_ok nx0 cs js lo && forallb (gvars_lt (nxt cs)) (a_props js))%bool then   (* [comment removed for export] *)
        match check f js k with
        | COk sk => check_in f (Some (JC j js sk (nxt cs) lo)) cs karms
        | err => err
        end
      else CErr 3 p cs
  | PMerge j =>
      match lc with
      | Some (JC j' js sk b lo) =>
          if (Nat.eqb j j' && Z.eqb (pc cs) (pc js) && shape_vars_lt nx0 sk && entails_hM A lo (nxt js) cs js)%bool
          then with_props cs (a_props js) (COk sk)
          else
          (* [comment removed for export] *)
          match (if (Nat.eqb j j' && Z.eqb (pc cs) (pc js) && shape_vars_lt nx0 sk && match s_log (a_ss js) with [] => true | _ => false end)%bool
                 then entails_sM A lo (nxt js) [] cs js else None) with
          | Some sg => with_props cs (map (ginst sg) (a_props js)) (COk sk)
          | None => CErr 3 p cs
          end
      | _ => CErr 8 p cs
      end
  (* [comment removed for export] *)
  | PGIntro g k =>
      if gvars_lt (nxt cs) g then
        match need1 cs (VCAtom g) with
        | [] => check f (set_props cs (g :: a_props cs)) k
        | l =>      (* [comment removed for export] *)
            match check f (set_props cs (g :: a_props cs)) k with CErr c q x => CErr c q x | CNeed l' => CNeed (l ++ l') | COk _ => CNeed l end
        end
      else CErr 3 p cs
  | PGDrop i k => check f (set_props cs (remove_nth i (a_props cs))) k
  | PGFact K k =>
      if kentry_vars_lt (nxt cs) K then
        match need1 cs (VCFact K) with
        | [] => check f (add_kn cs [K]) k
        | l =>      (* [comment removed for export] *)
            match check f (add_kn cs [K]) k with CErr c q x => CErr c q x | CNeed l' => CNeed (l ++ l') | COk _ => CNeed l end
        end
      else CErr 3 p cs
  | PGFactT x i K0 k =>
      match tfact_inst lc cs x i K0 with
      | Some K =>
      if kentry_vars_lt (nxt cs) K then
        match need1 cs (VCFact K) with
        | [] => check f (add_kn_end cs [K]) k
        | l =>
            match check f (add_kn_end cs [K]) k with CErr c q x => CErr c q x | CNeed l' => CNeed (l ++ l') | COk _ => CNeed l end
        end
      else CErr 3 p cs
      | None => CErr 4 p cs
      end
  | PAbstractCell b n k => match node_abstractcell A cs b n with Some cs' => check f (gpures (xp_gh xp) cs cs') k | None => CErr 3 p cs end
  | PHavocWords bs k => match node_havocwords nx0 cs bs with Some cs' => check f (gpures (xp_gh xp) cs cs') k | None => CErr 3 p cs end
  | PRespell r e k => match node_respell cs r e with Some cs' => check f (gkeepEM (xp_gh xp) [] cs cs') k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PCaseDisjJ b1 b2 joinpc rs k =>   (* [comment removed for export] *)
      if wbb then CErr 11 p cs else
      match node_casedisjJ A cs b1 b2 with
      | Some (csl, None) =>
          (* [comment removed for export] *)
          match run_block_gc_wb_ws segs IT gcb WB KC bfuel (joinpc :: STOPS A) csl with
          | Some (cs', W) => if Z.eqb (pc cs') joinpc then check f (gkeepM (xp_gh xp) W cs cs') k else CErr 3 p cs'
          | None => CErr 1 p csl
          end
      | Some (csa, Some csb) =>
          match run_block_gc_wb_ws segs IT gcb WB KC bfuel (joinpc :: STOPS A) csa with
          | Some (ca, Wa) =>
              match run_block_gc_wb_ws segs IT gcb WB KC bfuel (joinpc :: STOPS A) csb with
              | Some (cb, Wb) =>
                  match node_diamond_joinM A nx0 (nxt cs) joinpc rs ca cb with
                  | Some csj => check f (gkeepM (xp_gh xp) (Wa ++ Wb) cs csj) k
                  | None => CErr 3 p ca    (* [comment removed for export] *)
                  end
              | None => CErr 1 p csb
              end
          | None => CErr 1 p csa
          end
      | None => CErr 3 p cs
      end
  | PDiamond joinpc rs k =>
      if wbb then CErr 11 p cs else   (* [comment removed for export] *)
      match branch_probe IT cs with
      | Some e =>
          match erange (kn cs) e with
          | Some (lo, hi) =>
              (* [comment removed for export] *)
              if (Z.ltb hi 1 || Z.ltb 0 lo)%bool then
                match run_block_gc_wb_ws segs IT gcb WB KC bfuel (joinpc :: STOPS A) cs with
                | Some (cs', W) => if Z.eqb (pc cs') joinpc then check f (gkeepM (xp_gh xp) W cs cs') k else CErr 3 p cs'
                | None => CErr 1 p cs
                end
              else
                let cs1 := set_kn cs (KRange e lo 0 :: kn cs) in
                let cs2 := set_kn cs (KRange e 1 hi :: kn cs) in
                match run_block_gc_wb_ws segs IT gcb WB KC bfuel (joinpc :: STOPS A) cs1 with
                | Some (ca, Wa) =>
                    match run_block_gc_wb_ws segs IT gcb WB KC bfuel (joinpc :: STOPS A) cs2 with
                    | Some (cb, Wb) =>
                        match node_diamond_joinM A nx0 (nxt cs) joinpc rs ca cb with   (* [comment removed for export] *)
                        (* [comment removed for export] *)
                        | Some csj => check f (gkeepM (xp_gh xp) (Wa ++ Wb) cs csj) k
                        | None => CErr 3 p ca    (* [comment removed for export] *)
                        end
                    | None => CErr 1 p cs2
                    end
                | None => CErr 1 p cs1
                end
          | None => CErr 3 p cs
          end
      | None => CErr 2 p cs                  (* [comment removed for export] *)
      end
  end
  end.
End Check.

(* [comment removed for export] *)
Definition seg_ok (XN : nat -> list expr -> acs -> option acs) (XE : nat -> list expr -> acs -> option (Z * list spiece * acs))
           (XB : nat -> list expr -> acs -> option (acs * acs)) (KC : nat) (xp : xparams) (sid : nat) (SD : segdef) : bool :=
  segdef_wf SD &&
  match check XN XE XB (fun _ => None) KC (xp_seg xp (sg_w SD) (sg_hi SD) sid)   (* [comment removed for export] *)
              (sg_bfuel SD) (sg_fuel SD) (Some (SC (sg_outs SD) (sg_hi SD))) (sg_in SD) (sg_body SD) with
  | COk s => shape_eqb s (sg_shape SD)
  | _ => false
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sys_ws_std (y : snode) (cs : acs) : option (list (saddr * expr)) :=
  match y with YMunmap => None | YSetTid => Some [] | YBrk => None end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition x_ws_std (x : xnode) (args : list expr) (cs : acs) : option (list (saddr * expr)) :=
  match x with
  | XMemset | XMemcpy | XIMemset | XIMemcpy => Some [(SA (reg cs 10) 0, reg cs 12)]
  | _ => None
  end.

End WithSegs.
End AP.
