(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import GpCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition B16U : Z := 0x36b48.    (* [comment removed for export] *)
Definition B16I : Z := 0x39d7c.    (* [comment removed for export] *)
Definition NINSTR : nat := 141.
Definition IT (B : Z) : itab := mk_itab_ranges PSEGS [(B, NINSTR)].
Lemma IT_ok : forall B, itab_sound PSEGS (IT B). Proof. intro. apply APS.mk_itab_ranges_sound. Qed.
Definition RETPC (B : Z) : Z := B + 0x208.
Definition JOIN1 (B : Z) : Z := B + 0x7c.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition regsW : list expr := sr_upd regs0 4 (ELit (g_tp GPLAIN)).    (* [comment removed for export] *)
Definition C : expr := EVar 9.           (* [comment removed for export] *)
Definition T : expr := eaddz C (-8).
Definition G : expr := EVar 31.          (* [comment removed for export] *)
Definition OBJ : expr := EVar 32.        (* [comment removed for export] *)
Definition INLO : expr := EVar 40.       (* [comment removed for export] *)
Definition ITO : expr := EVar 33.        (* [comment removed for export] *)
Definition IT0 : expr := eadd INLO ITO.  (* [comment removed for export] *)
Definition REM : expr := EVar 34.        (* [comment removed for export] *)
Definition IX : expr := EVar 35.         (* [comment removed for export] *)
Definition D : expr := EVar 36.  Definition S : expr := EVar 37.  Definition A : expr := EVar 38.   (* [comment removed for export] *)
Definition ERR : expr := EVar 39.        (* [comment removed for export] *)
Definition BLEN : expr := eadd ITO REM.
Definition NXF : nat := 41.
(* [comment removed for export] *)
Definition INSZ : Z := 2 ^ 26.
Definition BIG : Z := 24 * INSZ.
Definition REMHI : Z := INSZ.
Definition IXHI : Z := BIG.
Definition CAPK : Z := 1040.
Definition AHI : Z := (4 * IXHI + 8 * INSZ + CAPK) / 8.
Definition FRK : Z := 48 + 2048.         (* [comment removed for export] *)

Definition capexpr (ix it inlo a : expr) : expr := esub (eaddz (eadd (escale 4 ix) (escale 8 (esub it inlo))) CAPK) (escale 8 a).
Definition capfact (ix it inlo a : expr) : kentry := KRange (capexpr ix it inlo a) 0 (4 * IXHI + 8 * INSZ + CAPK).
Definition strL (ix it d s a : expr) : list kentry :=
  [ KWord (SA OBJ 0) 8 (eaddz (escale 8 a) 1); KWord (SA OBJ 8) 8 s; KWord (SA OBJ 16) 8 d;
    KRange a 3 AHI; capfact ix it INLO a;
    KRange s 0 (8 * AHI); KRange (esub (escale 8 a) s) 1 (8 * AHI);
    KRange d PTRLO (PTRHI - 24); KRange (eadd d (escale 8 a)) (PTRLO + 24) PTRHI; KAlign d 16;
    KWr (SA d 0) (escale 8 a); KUnk (SA d 0) (escale 8 a);                                           (* [comment removed for export] *)
    KDisj (SA d 0) (escale 8 a) (SA C (-8)) (ELit 48); KDisj (SA d 0) (escale 8 a) (SA G 0) (ELit 112);
    KDisj (SA d 0) (escale 8 a) (SA OBJ 0) (ELit 24); KDisj (SA d 0) (escale 8 a) (SA INLO 0) BLEN;
    KDisj (SA d 0) (escale 8 a) (SA e_sp (- FRK)) (ELit (FRK + WSTK)); img_apart d 0 (escale 8 a) ].
Definition kn_fixed : list kentry :=
  [ KRange C (CEIL + 16) HI47; KWord (SA C 0) 8 (eaddz G 88); KWord (SA C 8) 8 (eaddz G 96); KWord (SA C 16) 8 G;
    KWord (SA C 24) 8 OBJ; KWord (SA C 32) 8 (eaddz G 104); KWr (SA C (-8)) (ELit 2);
    KRange G CEIL (objhi 112); KWr (SA G 0) (ELit 4); KWr (SA G 96) (ELit 16); KWord (SA G 88) 8 (eadd IT0 REM);
    KRange OBJ CEIL (objhi 24); KWr (SA OBJ 0) (ELit 24);
    KRange INLO PTRLO PTRHI; KRange ITO 1 INSZ; KRange REM 0 REMHI; KRange BLEN 1 INSZ;
    KUnk (SA INLO 0) BLEN; KDisj (SA INLO 0) BLEN (SA e_sp (- FRK)) (ELit (FRK + WSTK)); img_apart INLO 0 BLEN; KRange (eadd INLO BLEN) (PTRLO + 1) PTRHI;
    KDisj (SA C (-8)) (ELit 48) (SA G 0) (ELit 112); KDisj (SA C (-8)) (ELit 48) (SA OBJ 0) (ELit 24);
    KDisj (SA G 0) (ELit 112) (SA OBJ 0) (ELit 24);
    KDisj (SA INLO 0) BLEN (SA C (-8)) (ELit 48); KDisj (SA INLO 0) BLEN (SA G 0) (ELit 112); KDisj (SA INLO 0) BLEN (SA OBJ 0) (ELit 24);
    KUnk (SA OBJ 0) (ELit 24);
    KAlign e_sp 16; KRange e_sp (CEIL + 4096) HI47; KWr (SA e_sp (- FRK)) (ELit FRK);     (* [comment removed for export] *)
    KRange (esub C e_sp) 16 (2 ^ 63); KRange (esub G e_sp) 0 (2 ^ 63); KRange (esub OBJ e_sp) 0 (2 ^ 63);   (* [comment removed for export] *)
    KDisj (SA e_sp (- FRK)) (ELit FRK) (SA C (-8)) (ELit 48); KDisj (SA e_sp (- FRK)) (ELit FRK) (SA G 0) (ELit 112);
    KDisj (SA e_sp (- FRK)) (ELit FRK) (SA OBJ 0) (ELit 24);
    KWr (SA C (-8)) (ELit 48); KWr (SA G 0) (ELit 112);    (* [comment removed for export] *)
    KImg 0x10000 0x71000 ].
(* [comment removed for export] *)
Definition str (m : smode) (ix it : expr) (v : nat) : list kentry :=
  match m with MS => strS OBJ (EVar v) | ML => strL ix it (EVar v) (EVar (1 + v)) (EVar (2 + v)) end.
Definition vis (m : smode) (v : nat) : list (expr * expr) :=
  match m with MS => [] | ML => [(EVar v, escale 8 (EVar (2 + v)))] end.
Definition kn_in (m : smode) : list kentry :=
  [ KWord (SA G 0) 4 ERR; KRange ERR 0 0; KWord (SA G 96) 8 IT0; KWord (SA G 104) 8 IX; KRange IX 0 BIG;
    KRange (esub (escale 24 (esub IT0 INLO)) IX) 0 BIG ]                          (* [comment removed for export] *)
  ++ str m IX IT0 36 ++ kn_fixed.
Definition WS : list (expr * expr) := [(T, ELit 2); (G, ELit 4); (eaddz G 96, ELit 16); (OBJ, ELit 24); (INLO, BLEN)].   (* [comment removed for export] *)
Definition mkcsV (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRK 0 vis WS 0 e_sp FdStd false.
Definition regs_in : list expr := sr_upd regsW 11 T.
Definition tin (m : smode) (B : Z) : acs := mkcsV B regs_in (kn_in m) NXF (vis m 36).

(* [comment removed for export] *)
Definition frame : list kentry :=
  [ KWord (SA e_sp (-8)) 8 (EVar 0); KWord (SA e_sp (-16)) 8 (EVar 7); KWord (SA e_sp (-24)) 8 (EVar 8);
    KWord (SA e_sp (-32)) 8 (EVar 17); KWord (SA e_sp (-40)) 8 (EVar 18) ].

(* [comment removed for export] *)
Definition xERR := EVar 41. Definition xDI := EVar 42. Definition xIX := EVar 43.



Definition XLO : nat := 47.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_out : list expr := sr_havoc regsW clobbered XLO.
Definition kn_out (m : smode) : list kentry :=
  [ KWord (SA G 0) 4 xERR; KRange xERR 0 24; KWord (SA G 96) 8 (eadd IT0 xDI); KRange xDI 0 2; KRange (esub REM xDI) 0 REMHI;
    KWord (SA G 104) 8 xIX; KRange xIX 0 IXHI; KRange (esub xIX IX) 0 5;
    KRange (esub (escale 24 (esub (eadd IT0 xDI) INLO)) xIX) 0 BIG;                   (* [comment removed for export] *)
    KRange (esub (eadd IT0 xDI) INLO) 0 INSZ;                                         (* [comment removed for export] *)
    relx xDI xERR xIX IX 8 ]                                                            (* [comment removed for export] *)
  ++ str m xIX (eadd IT0 xDI) 44 ++ kn_fixed.
Definition tout (m : smode) (B : Z) : acs := mkcsV (RETPC B) regs_out (kn_out m) (XLO + 15)%nat (vis m 44).
Definition BCAP : Z := 10 * 2 ^ 30.  Definition CCAP : Z := 2.
(* [comment removed for export] *)
Definition ce2 (m : smode) (B : Z) : gcallee2 := GCE2 NXF (tin m B) [tout MS B] [tout ML B] BCAP CCAP.
Definition ce (m : smode) (B : Z) : gcallee := c2_merged (ce2 m B).
(* [comment removed for export] *)
Definition ceL1 (B : Z) : gcallee := GCE NXF (tin ML B) [tout ML B; tout ML B] BCAP CCAP.

(* [comment removed for export] *)
Definition CT2_0 (id : nat) : option gcallee2 := None.
Definition XN (B : Z) : nat -> list expr -> acs -> option acs := XNc PSEGS (IT B) APLAIN NXF GPLAIN BCAP CCAP CT0.
Definition XB : nat -> list expr -> acs -> option (acs * acs) := XBc PSEGS APLAIN NXF GPLAIN BCAP CCAP CT2_0.
Definition FUEL16 : nat := 4000.

(* [comment removed for export] *)
Definition D1 := EVar 100. Definition S1 := EVar 101. Definition A1 := EVar 102. Definition BV := EVar 103.
Definition csregs_ra_noa0 : list nat := [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_mid (a0 : expr) (v : nat) : list expr :=
  sr_havoc (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd regsW
    2 (eaddz e_sp (-48))) 8 C) 9 T) 10 a0) 18 OBJ) 19 (eaddz G 104)) csregs_ra_noa0 v.
(* [comment removed for export] *)
Definition room (m : smode) : list kentry :=
  match m with MS => [KRange (esub (EVar 100) IX) 8 (2 ^ 40)] | ML => [KRange (esub S1 IX) 8 (2 ^ 37)] end.   (* [comment removed for export] *)
Definition JS1 (m : smode) (B : Z) : acs :=
  mkcsV (JOIN1 B) (regs_mid IX 104)
       (room m ++ [KWord (SA C (-8)) 2 BV; KRange BV 0 65535; KRange REM 2 REMHI] ++ frame ++
        [KWord (SA G 0) 4 ERR; KRange ERR 0 0; KWord (SA G 96) 8 IT0; KWord (SA G 104) 8 IX; KRange IX 0 BIG;
         KRange (esub (escale 24 (esub IT0 INLO)) IX) 0 BIG]
        ++ str m IX IT0 100 ++ kn_fixed)
       120 (vis m 100).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition PH : nat := 255.   (* [comment removed for export] *)
Definition XPH : expr := EVar PH.
Definition CAPB : expr := eaddz (eadd (escale 4 IX) (escale 8 (esub IT0 INLO))) CAPK.
(* [comment removed for export] *)
Definition RSZ (m : smode) : list expr := match m with MS => [ELit 0; D; CAPB] | ML => [ELit 1; D; A; S; CAPB] end.
   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition exit_chain (m : smode) (k : plan) : plan :=
  let cons' := esub (eaddz IT0 2) INLO in
  PFactLe cons' (eadd (esub IT0 INLO) REM) INSZ
  (PFact (KRange ITO 1 (INSZ - 2))                    (* [comment removed for export] *)
  (PFactLeX 11 PH XPH (escale 24 cons') IXHI
  (PFactLeX 11 PH (esub (escale 24 cons') XPH) (escale 24 cons') BIG
  (match m with
   | ML => PFactLeX 11 PH (capexpr XPH (eaddz IT0 2) INLO A1) (eaddz (escale 104 cons') CAPK) (4 * IXHI + 8 * INSZ + CAPK) k
   | MS => k end)))).
Definition EXITOK (m : smode) : plan := exit_chain m (PHandoffW (hole m) [(42%nat, ELit 2)]).
Definition EXITERR (m : smode) : plan := PRun [] (PHandoffW (hole m) [(42%nat, ELit 0)]).       (* [comment removed for export] *)

Definition xl (k : plan) : plan := PRun [] (PExt 0 [] k).         (* [comment removed for export] *)
Definition fin (m : smode) : plan := PRun [] (EXITOK m).
Definition armA (m : smode) : plan := xl (xl (fin m)).                                                           (* [comment removed for export] *)
Definition armB (m : smode) : plan := divfact BV (q100 BV) 100 (zfact BV (q100 BV) 100 (xl (xl (xl (fin m))))).  (* [comment removed for export] *)
Definition q4 : expr := EMd M_MULHU BV (ELit 0x68db8bac710cc).
Definition r4 : expr := rem BV q4 10000.
Definition armC (m : smode) : plan :=                                                                            (* [comment removed for export] *)
  divfact BV q4 10000 (divfact r4 (q100w r4) 100 (zfact r4 (q100w r4) 100 (xl (xl (fin m))))).
Definition digits (m : smode) : plan :=
  PCase2 BV 9 (armA m) (PCase2 BV 99 (armA m) (PCase2 BV 999 (armB m) (PCase2 BV 9999 (armB m) (armC m)))).
Definition after1 (m : smode) : plan :=
  match m with ML => PFactVia (esub (escale 8 A1) IX) (esub S1 IX) 9 (2 ^ 40) (digits ML) | MS => digits MS end.
(* [comment removed for export] *)
Definition okArm (m : smode) (B : Z) : plan :=
  PRun [] (PRun [] (PViaM 1 (match m with MS => [(JS1 MS B, after1 MS); (JS1 ML B, after1 ML)] | ML => [(JS1 ML B, after1 ML)] end) 100
     (PBranch (PRun [JOIN1 B] (PMerge 1))                                                        (* [comment removed for export] *)
              (PRun [] (PExt2 31 (RSZ m) (PRun [JOIN1 B] (PMerge 1)) (PRun [JOIN1 B] (PMerge 1))))))).  (* [comment removed for export] *)
Definition PLAN (m : smode) (B : Z) : plan := PCase2 REM 1 (EXITERR m) (okArm m B).

Lemma w16_gplan : forall m B, gplan_ok (PLAN m B) = true. Proof. intros [|] B; reflexivity. Qed.

(* [comment removed for export] *)
