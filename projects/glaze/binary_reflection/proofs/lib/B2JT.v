(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallRec OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import Esc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.


(* [comment removed for export] *)
#[local] Notation PTRHI := GlzConst.PTRHI.
Definition img_apart (x : expr) (k : Z) (n : expr) : kentry := KDisj (SA x k) n (SA (ELit 0) 0x10000) (ELit 0x97000).
Definition ENTRY : Z := 0x30738.
Definition RETPC : Z := 0x325d8.
(* [comment removed for export] *)
Definition IT_def : itab := mk_itab_ranges PSEGS [(ENTRY, 2102%nat)].
Definition IT : itab := Eval vm_compute in IT_def.
Lemma IT_eq : IT = IT_def. Proof. vm_cast_no_check (@eq_refl itab IT_def). Qed.
Lemma IT_ok : itab_sound PSEGS IT. Proof. rewrite IT_eq. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition regs0 : list expr := sr_upd (ELit 0 :: map EVar (seq 0 31)) 4 (ELit (g_tp GPLAIN)).
Definition e_sp : expr := EVar 1.
Definition G : expr := EVar 9.          (* [comment removed for export] *)
Definition OBJ : expr := EVar 12.       (* [comment removed for export] *)
Definition DEPTH : expr := EVar 14.     (* [comment removed for export] *)
Definition ITO : expr := EVar 31.       (* [comment removed for export] *)
Definition BSZ : expr := EVar 33.       (* [comment removed for export] *)
Definition IX : expr := EVar 34.
Definition INLO : expr := EVar 35.

Definition EEND : expr := eadd INLO BSZ.
Definition NXF : nat := 39.
Definition FR : Z := 192.
(* [comment removed for export] *)
Definition SK : Z := 8192 + 192.      (* [comment removed for export] *)
Definition XD : expr := eaddz (escale (- FR) DEPTH) (SK + FR * 256).
Definition XDMAX : Z := SK + FR * 256.          (* [comment removed for export] *)
Definition SLO : expr := eadd (eaddz e_sp (- XDMAX)) (escale FR DEPTH).   (* [comment removed for export] *)
Definition FLOOR : list amap := [AM SLO (ELit 0) KRW].                    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition IXMAX : Z := 32 * INSZ.                       (* [comment removed for export] *)
Definition CAPMAX : Z := 8 * INSZ.
Definition IXHI2 : Z := BIG + 2 * INSZ + 64.              (* [comment removed for export] *)
Definition iixE (ito ix err : expr) : kentry :=          (* [comment removed for export] *)
  KRange (esub (eadd (escale 24 ito) (escale IXMAX err)) ix) 0 (24 * INSZ + 256 * IXMAX).
(* [comment removed for export] *)
Definition RELHI : Z := 24 * INSZ + 256 * IXMAX.
Definition rel (ito ix : expr) (lo : Z) : kentry := KRange (esub (escale 24 (esub ito ITO)) (esub ix IX)) lo RELHI.
Definition relE (ito ix err : expr) (lo : Z) : kentry :=
  KRange (esub (eadd (escale 24 (esub ito ITO)) (escale IXMAX err)) (esub ix IX)) lo RELHI.
Definition capE (ix ito a err : expr) : kentry :=        (* [comment removed for export] *)
  KRange (esub (eaddz (eadd (eadd (escale 4 ix) (escale 8 ito)) (escale CAPMAX err)) CAPK) (escale 8 a)) 0 (4 * IXMAX + 8 * INSZ + CAPK + 256 * CAPMAX).
(* [comment removed for export] *)
Definition placement (d a : expr) : list kentry :=
  [ KRange d PTRLO (PTRHI - 24); KRange (eadd d (escale 8 a)) (PTRLO + 24) PTRHI;
    KDisj (SA d 0) (escale 8 a) (SA SLO 0) (ELit (XDMAX + WSTK)) ].   (* [comment removed for export] *)
Definition strLc (ix ito err d s a : expr) : list kentry :=
  [ KWord (SA OBJ 0) 8 (eaddz (escale 8 a) 1); KWord (SA OBJ 8) 8 s; KWord (SA OBJ 16) 8 d;
    KRange a 3 AHI; capE ix ito a err;
    KRange s 0 (8 * AHI); KRange (esub (escale 8 a) s) 1 (8 * AHI);
    KRange d PTRLO (HI47 - 24); KRange (eadd d (escale 8 a)) (PTRLO + 24) HI47; KAlign d 16;
    KWr (SA d 0) (escale 8 a); KUnk (SA d 0) (escale 8 a);
    KDisj (SA d 0) (escale 8 a) (SA G 0) (ELit 112); KDisj (SA d 0) (escale 8 a) (SA OBJ 0) (ELit 24);
    KDisj (SA d 0) (escale 8 a) (SA INLO 0) BSZ; img_apart d 0 (escale 8 a) ].
Definition strL (ix ito err d s a : expr) : list kentry := placement d a ++ strLc ix ito err d s a.
Definition strS (s : expr) : list kentry := [ KWord (SA OBJ 0) 1 (escale 2 s); KRange s 0 22 ].
Definition str (m : smode) (ix ito err : expr) (v : nat) : list kentry :=
  match m with MS => strS (EVar v) | ML => strL ix ito err (EVar v) (EVar (1 + v)) (EVar (2 + v)) end.
Definition strc (m : smode) (ix ito err : expr) (v : nat) : list kentry :=
  match m with MS => strS (EVar v) | ML => strLc ix ito err (EVar v) (EVar (1 + v)) (EVar (2 + v)) end.
(* [comment removed for export] *)
Definition n13 (t : acs) (k : plan) : plan := match a_vis t with [(b, _)] => PExt 13 [b] k | _ => k end.
Definition vis (m : smode) (v : nat) : list (expr * expr) :=
  match m with MS => [] | ML => [(EVar v, escale 8 (EVar (2 + v)))] end.

Definition kn_fixed : list kentry :=
  [ KRange G CEIL (HI47 - 112); KWr (SA G 0) (ELit 4); KWr (SA G 96) (ELit 16); KWord (SA G 88) 8 EEND;   (* [comment removed for export] *)
    KWr (SA G 32) (ELit 4); KUnk (SA G 32) (ELit 4);                                               (* [comment removed for export] *)
    KRange OBJ CEIL (HI47 - 24); KWr (SA OBJ 0) (ELit 24); KUnk (SA OBJ 0) (ELit 24);
    KRange INLO PTRLO PTRHI; KRange BSZ 1 INSZ; KRange (eadd INLO BSZ) (PTRLO + 1) PTRHI; KUnk (SA INLO 0) BSZ; img_apart INLO 0 BSZ;
    KDisj (SA G 0) (ELit 112) (SA OBJ 0) (ELit 24);
    KDisj (SA INLO 0) BSZ (SA G 0) (ELit 112); KDisj (SA INLO 0) BSZ (SA OBJ 0) (ELit 24);
    KAlign e_sp 16; KRange e_sp (CEIL + SK) HI47; KRange SLO CEIL HI47; KWr (SA SLO 0) XD;
    KRange (esub G e_sp) 0 (2 ^ 62); KRange (esub OBJ e_sp) 0 (2 ^ 62);
    KDisj (SA SLO 0) XD (SA G 0) (ELit 112); KDisj (SA SLO 0) XD (SA OBJ 0) (ELit 24); KDisj (SA INLO 0) BSZ (SA SLO 0) (ELit (XDMAX + WSTK));   (* [comment removed for export] *)
    KRange ITO 0 INSZ; KRange IX 0 BIG;            (* [comment removed for export] *)
    KWr (SA G 0) (ELit 112);    (* [comment removed for export] *)
    KImg 0x10000 0x71000 ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition posg (mlo : Z) (ito ix err : expr) (k : Z) (ixhi : Z) : list kentry :=  (* [comment removed for export] *)
  [ KWord (SA G 0) 4 err; KWord (SA G 96) 8 (eadd INLO ito); KRange ito 0 (INSZ - k); KRange (esub BSZ ito) k INSZ;
    KWord (SA G 104) 8 ix; KRange ix 0 ixhi; iixE ITO IX (ELit 0); iixE ito ix err;     (* [comment removed for export] *)
    KRange (esub ito ITO) mlo INSZ ].                           (* [comment removed for export] *)
(* [comment removed for export] *)
Definition pos0 := posg 0.
Definition pos := posg 1.
Definition kn_in (m : smode) : list kentry :=
  [ KRange DEPTH 0 256 ] ++ pos0 ITO IX (ELit 0) 0 BIG ++ strc m IX ITO (ELit 0) 36 ++ kn_fixed.   (* [comment removed for export] *)
Definition WS : list (expr * expr) := [(G, ELit 4); (eaddz G 32, ELit 4); (eaddz G 96, ELit 16); (OBJ, ELit 24); (INLO, BSZ)].   (* [comment removed for export] *)
Definition mkcs (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vs : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k nx) FLOOR 0 XDMAX 0 vs WS 0 e_sp FdStd false.   (* [comment removed for export] *)
Definition regs_in : list expr := sr_upd (sr_upd (sr_upd regs0 11 (eaddz G 96)) 12 (eaddz G 88)) 14 (eaddz G 104).
Definition tin (m : smode) : acs := mkcs ENTRY regs_in (kn_in m) NXF (vis m 36).

(* [comment removed for export] *)
Definition xERR := EVar 39. Definition xITO := EVar 40. Definition xIX := EVar 41.
Definition XSTR : nat := 42. Definition XLO : nat := 45.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_out : list expr := sr_havoc regs0 clobbered XLO.
Definition kn_out (m : smode) : list kentry :=
  [ KRange xERR 0 255; relE xITO xIX xERR 1; KRange (eadd (esub xITO ITO) xERR) 1 (INSZ + 255) ]   (* [comment removed for export] *)
  ++ pos0 xITO xIX xERR 0 IXMAX ++ strc m xIX xITO xERR XSTR ++ kn_fixed.      (* [comment removed for export] *)
Definition tout (m : smode) : acs := mkcs RETPC regs_out (kn_out m) (XLO + 15)%nat (vis m XSTR).
Definition BCAP : Z := 10 * 2 ^ 30.  Definition CCAP : Z := 4.
Definition ce2 (m : smode) : gcallee2 := GCE2 NXF (tin m) [tout MS] [tout ML] BCAP CCAP.
(* [comment removed for export] *)
Definition ceL1 : gcallee := GCE NXF (tin ML) [tout ML; tout ML] BCAP CCAP.
Definition ce (m : smode) : gcallee := match m with MS => c2_merged (ce2 MS) | ML => ceL1 end.
