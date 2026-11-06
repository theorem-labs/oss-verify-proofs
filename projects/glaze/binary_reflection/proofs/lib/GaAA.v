(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GcFlush.F72_001.   (* [comment removed for export] *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GaPsub.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section PSub.
Variable sJ : nat.
Variable se : expr.



End PSub.
(* [comment removed for export] *)
Section PTAdd.
Variable ks : list kentry.

End PTAdd.
(* [comment removed for export] *)
Section PNW.
Variable w0 : list (nat * expr).

End PNW.
End GaPsub.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPw OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Record acfg := ACFG {
  c_entry : Z; c_ninstr : nat;
  c_fr : Z;                      (* [comment removed for export] *)
  c_K : Z;                       (* [comment removed for export] *)
  c_hr : Z;                      (* [comment removed for export] *)
  c_wmx : Z;                     (* [comment removed for export] *)
  c_head : Z; c_join1 : Z; c_ret : Z;
  c_jreg : nat;                  (* [comment removed for export] *)
  c_vol0 : list nat;             (* [comment removed for export] *)
  c_vol1 : list nat;             (* [comment removed for export] *)
  c_vw : nat;                    (* [comment removed for export] *)
  c_vhi : Z;                     (* [comment removed for export] *)
  c_ixpc : Z; c_ixreg : nat;     (* [comment removed for export] *)
  c_ix2pc : Z; c_ix2reg : nat    (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition regsW : list expr := sr_upd regs0 4 (ELit (g_tp GASAN)).    (* [comment removed for export] *)
Definition C : expr := EVar 9.
Definition T : expr := eaddz C 56.
Definition G : expr := EVar 31.   Definition OBJ : expr := EVar 32.
Definition ITO : expr := EVar 33.       (* [comment removed for export] *)
Definition REM : expr := EVar 34. Definition IX : expr := EVar 35.
   Definition S : expr := EVar 37.    Definition A : expr := EVar 38.
Definition ERR : expr := EVar 39.
Definition INLO : expr := EVar 40.      (* [comment removed for export] *)
Definition NV : expr := EVar 41.        (* [comment removed for export] *)
Definition PN : expr := EVar 42.        (* [comment removed for export] *)
Definition PEND : expr := EVar 43.      (* [comment removed for export] *)
Definition PIT : expr := EVar 44.       (* [comment removed for export] *)
Definition PIX : expr := EVar 45.       (* [comment removed for export] *)
Definition SZ0 : expr := EVar 46.       (* [comment removed for export] *)
Definition e_mtr : expr := EVar 47.     (* [comment removed for export] *)
Definition e_fb : expr := EVar 48.      (* [comment removed for export] *)
Definition IT0 : expr := eadd INLO ITO. (* [comment removed for export] *)
Definition BLEN : expr := eadd ITO REM.  (* [comment removed for export] *)
Definition NXF : nat := 49.
Definition INSZ : Z := 2 ^ 26.
Definition BIG : Z := 24 * INSZ.
Definition REMHI : Z := INSZ.
Definition IXHI : Z := BIG.
Definition CAPK : Z := 1040.
Definition CAPHI : Z := 4 * IXHI + 8 * INSZ + CAPK.
Definition AHI : Z := CAPHI / 8.
Definition NVHI : Z := 2 ^ 48.              (* [comment removed for export] *)
Definition two62 : Z := 2 ^ 62.
Definition FRK (c : acfg) : Z := c_fr c + AzStrResizeT.FRK.   (* [comment removed for export] *)
Definition RFRK : Z := AzStrResizeT.FRK.
Definition flo (c : acfg) (x : expr) (n : expr) : kentry := KDisj (SA x 0) n (SA e_sp (- FRK c)) (ELit (FRK c + WSTK)).   (* [comment removed for export] *)
Definition NB : Z := 3 * 2^30 + 16.         (* [comment removed for export] *)
(* [comment removed for export] *)
Definition GEV : Z := 2 * EVT + 8.
Definition MTRJ : Z := MTRMAX NB.                          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition CPW : expr := EVar 3.
Definition CMAX : Z := MTRJ - pwtop (8 * AHI).      (* [comment removed for export] *)
Definition MTRIN : Z := MTRJ.
Definition GROWMAX : Z := kcost (2 * NB + 8) + KFREE.

Definition mP (j sz mtr : expr) : list kentry := pw_facts CPW sz mtr.                    (* [comment removed for export] *)
Definition mE (sz1 sz0 mtr1 mtr0 : expr) : list kentry := pw_facts CPW sz1 mtr1.       (* [comment removed for export] *)
Definition mX (c : acfg) (sz' di mtr' : expr) : list kentry := pw_facts CPW sz' mtr'.  (* [comment removed for export] *)

Definition capexpr (ix it inlo a : expr) : expr := esub (eaddz (eadd (escale 4 ix) (escale 8 (esub it inlo))) CAPK) (escale 8 a).
Definition capfact (ix it inlo a : expr) : kentry := KRange (capexpr ix it inlo a) 0 CAPHI.
Definition strL (c : acfg) (ix it d s a : expr) : list kentry :=
  [ KWord (SA OBJ 0) 8 (eaddz (escale 8 a) 1); KWord (SA OBJ 8) 8 s; KWord (SA OBJ 16) 8 d;
    KRange a 3 AHI; capfact ix it INLO a;
    KRange s 0 (8 * AHI); KRange (esub (escale 8 a) s) 1 (8 * AHI);
    KRange d PTRLO (PTRHI - 24); KRange (eadd d (escale 8 a)) (PTRLO + 24) PTRHI; KAlign d 16;
    KWr (SA d 0) (escale 8 a); KUnk (SA d 0) (escale 8 a); KShOk (SA d 0) (escale 8 a);                 (* [comment removed for export] *)
    KDisj (SA d 0) (escale 8 a) (SA C 0) (ELit 64); KDisj (SA d 0) (escale 8 a) (SA G 0) (ELit 4);
    KDisj (SA d 0) (escale 8 a) (SA PN 0) (ELit 8); KDisj (SA d 0) (escale 8 a) (SA PEND 0) (ELit 8);
    KDisj (SA d 0) (escale 8 a) (SA PIT 0) (ELit 8); KDisj (SA d 0) (escale 8 a) (SA PIX 0) (ELit 8);
    KDisj (SA d 0) (escale 8 a) (SA OBJ 0) (ELit 24); KDisj (SA d 0) (escale 8 a) (SA INLO 0) BLEN;
    KDisj (SA d 0) (escale 8 a) (SA e_sp (- FRK c)) (ELit (RFRK + WSTK)); img_apart d 0 (escale 8 a); shmap_apart d 0 (escale 8 a) ].
(* [comment removed for export] *)
Definition str (c : acfg) (m : smode) (ix it : expr) (v : nat) : list kentry :=
  match m with MS => strS OBJ (EVar v) | ML => strL c ix it (EVar v) (EVar (1 + v)) (EVar (2 + v)) end.
Definition vis (m : smode) (v : nat) : list (expr * expr) :=
  match m with MS => [] | ML => [(EVar v, escale 8 (EVar (2 + v)))] end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tbl_shadow : list kentry := GLZ_LOWSH.   (* [comment removed for export] *)        (* [comment removed for export] *)
Definition kn_fixed (c : acfg) : list kentry :=
  [ KRange C (CEIL + 16) (HI47 - 64); KAlign C 8; KShOk (SA C 0) (ELit 64);
    KWord (SA C 0) 8 PN; KWord (SA C 8) 8 PEND; KWord (SA C 16) 8 PIT; KWord (SA C 24) 8 G; KWord (SA C 32) 8 OBJ; KWord (SA C 40) 8 PIX;
    KWr (SA C 56) (ELit 8);
    KRange PN PTRLO (objhi 8); KWord (SA PN 0) 8 NV; KShOk (SA PN 0) (ELit 8); KAlign PN 8; KRange NV 0 NVHI;
    KRange G PTRLO (objhi 4); KWr (SA G 0) (ELit 4); KShOk (SA G 0) (ELit 4); KAlign G 4;
    KRange PEND PTRLO (objhi 8); KWord (SA PEND 0) 8 (eadd IT0 REM); KShOk (SA PEND 0) (ELit 8); KAlign PEND 8;
    KRange PIT PTRLO (objhi 8); KWr (SA PIT 0) (ELit 8); KShOk (SA PIT 0) (ELit 8); KAlign PIT 8;
    KRange PIX PTRLO (objhi 8); KWr (SA PIX 0) (ELit 8); KShOk (SA PIX 0) (ELit 8); KAlign PIX 8;
    KRange OBJ PTRLO (objhi 24); KWr (SA OBJ 0) (ELit 24); KShOk (SA OBJ 0) (ELit 24); KAlign OBJ 8; KUnk (SA OBJ 0) (ELit 24);
    KRange INLO PTRLO PTRHI; KRange ITO 1 INSZ; KRange REM 0 REMHI; KRange BLEN 1 INSZ;
    KUnk (SA INLO 0) BLEN; KShOk (SA INLO 0) BLEN; KRange (eadd INLO BLEN) (PTRLO + 1) PTRHI;
    KDisj (SA C 0) (ELit 64) (SA OBJ 0) (ELit 24); KDisj (SA e_sp (- FRK c)) (ELit (FRK c)) (SA OBJ 0) (ELit 24);   (* [comment removed for export] *)
    KDisj (SA G 0) (ELit 4) (SA OBJ 0) (ELit 24); KDisj (SA PN 0) (ELit 8) (SA OBJ 0) (ELit 24); KDisj (SA PEND 0) (ELit 8) (SA OBJ 0) (ELit 24);
    KDisj (SA PIT 0) (ELit 8) (SA OBJ 0) (ELit 24); KDisj (SA PIX 0) (ELit 8) (SA OBJ 0) (ELit 24);
    KDisj (SA G 0) (ELit 4) (SA PN 0) (ELit 8); KDisj (SA G 0) (ELit 4) (SA PEND 0) (ELit 8);
    KDisj (SA G 0) (ELit 4) (SA PIT 0) (ELit 8); KDisj (SA G 0) (ELit 4) (SA PIX 0) (ELit 8);
    KDisj (SA PN 0) (ELit 8) (SA PIT 0) (ELit 8); KDisj (SA PN 0) (ELit 8) (SA PIX 0) (ELit 8); KDisj (SA PN 0) (ELit 8) (SA PEND 0) (ELit 8);
    KDisj (SA PEND 0) (ELit 8) (SA PIT 0) (ELit 8); KDisj (SA PEND 0) (ELit 8) (SA PIX 0) (ELit 8); KDisj (SA PIT 0) (ELit 8) (SA PIX 0) (ELit 8);
    KDisj (SA INLO 0) BLEN (SA G 0) (ELit 4); KDisj (SA INLO 0) BLEN (SA OBJ 0) (ELit 24); KDisj (SA INLO 0) BLEN (SA PN 0) (ELit 8);
    KDisj (SA INLO 0) BLEN (SA PEND 0) (ELit 8); KDisj (SA INLO 0) BLEN (SA PIT 0) (ELit 8); KDisj (SA INLO 0) BLEN (SA PIX 0) (ELit 8);
    KAlign e_sp 16; KRange e_sp (CEIL + 8192) (two47 - 16); KWr (SA e_sp (- FRK c)) (ELit (FRK c));
    KDisj (SA INLO 0) BLEN (SA e_sp (- FRK c)) (ELit (FRK c));                                          (* [comment removed for export] *)
    KRange (esub C e_sp) 16 (2 ^ 62); KDisj (SA e_sp (- FRK c)) (ELit (FRK c)) (SA C 0) (ELit 64);   (* [comment removed for export] *)
    KRange e_mtr 0 MTRIN; KRange SZ0 0 (8 * AHI); KRange CPW 0 CMAX; (* [comment removed for export] *)
    flo c G (ELit 4); flo c PN (ELit 8); flo c PEND (ELit 8); flo c PIT (ELit 8); flo c PIX (ELit 8); flo c OBJ (ELit 24); flo c INLO BLEN;
    img_apart G 0 (ELit 4); shmap_apart G 0 (ELit 4); img_apart PIT 0 (ELit 8); shmap_apart PIT 0 (ELit 8);
    img_apart PIX 0 (ELit 8); shmap_apart PIX 0 (ELit 8); img_apart OBJ 0 (ELit 24); shmap_apart OBJ 0 (ELit 24);
    img_apart PN 0 (ELit 8); img_apart PEND 0 (ELit 8); img_apart INLO 0 BLEN; shmap_apart INLO 0 BLEN;
    KDisj (SA C 0) (ELit 64) (SA G 0) (ELit 4); KDisj (SA C 0) (ELit 64) (SA PN 0) (ELit 8); KDisj (SA C 0) (ELit 64) (SA PEND 0) (ELit 8);
    KDisj (SA C 0) (ELit 64) (SA PIT 0) (ELit 8); KDisj (SA C 0) (ELit 64) (SA PIX 0) (ELit 8); KDisj (SA C 0) (ELit 64) (SA INLO 0) BLEN;   (* [comment removed for export] *)
    KIMGA; fb_fact e_fb ] ++ pw_facts CPW SZ0 e_mtr ++ NEWH ++ RTC ++ tbl_shadow.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition szin (m : smode) : expr := match m with MS => EVar 36 | ML => S end.
Definition kn_in (c : acfg) (m : smode) : list kentry :=
  [ KWord (SA G 0) 4 ERR; KRange ERR 0 0; KWord (SA PIT 0) 8 IT0; KWord (SA PIX 0) 8 IX; KRange IX 0 BIG;
    KRange (esub (escale 24 (esub IT0 INLO)) IX) 0 BIG; KRange (esub SZ0 (szin m)) 0 0 ]
  ++ str c m IX IT0 36 ++ kn_fixed c.
Definition WS : list (expr * expr) :=
  [(C, ELit 64); (G, ELit 4); (PN, ELit 8); (PEND, ELit 8); (PIT, ELit 8); (PIX, ELit 8); (OBJ, ELit 24); (INLO, BLEN)].   (* [comment removed for export] *)
Definition mkcsV (c : acfg) (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) (mtr : expr) : acs :=
  ACS (mk_ss p regs k nx) [] 0 (FRK c) 0 vis WS 0 e_sp FdStd false mtr [] e_fb.   (* [comment removed for export] *)
Definition regs_in : list expr := sr_upd regsW 11 T.
Definition tin (c : acfg) (m : smode) : acs := mkcsV c (c_entry c) regs_in (kn_in c m) NXF (vis m 36) e_mtr.
Definition IT (c : acfg) : itab := mk_itab_ranges ASEGS [(c_entry c, c_ninstr c)].
Lemma IT_ok : forall c, itab_sound ASEGS (IT c). Proof. intro. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition xERR := EVar 49. Definition xDI := EVar 50. Definition xIX := EVar 51.
Definition DISLOT : nat := 50.
 Definition xS := EVar 53.

Definition xMTR := EVar 55.
Definition XLO : nat := 56.
Definition szx (m : smode) : expr := match m with MS => EVar 52 | ML => xS end.   (* [comment removed for export] *)
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_out : list expr := sr_havoc regsW clobbered XLO.
Definition IXMAX : Z := 40.  Definition RELHI : Z := 2 ^ 62.
Definition relx (di err ix ix0 : expr) (lo : Z) : kentry :=                (* [comment removed for export] *)
  KRange (esub (eadd (escale 24 di) (escale IXMAX err)) (esub ix ix0)) lo RELHI.
Definition kn_out (c : acfg) (m : smode) : list kentry :=
  [ KWord (SA G 0) 4 xERR; KRange xERR 0 22; KWord (SA PIT 0) 8 (eadd IT0 xDI); KRange xDI 0 REMHI; KRange (esub REM xDI) 0 REMHI;
    KWord (SA PIX 0) 8 xIX; KRange xIX 0 IXHI; KRange (esub xIX IX) 0 two62;
    KRange (esub (escale 24 (esub (eadd IT0 xDI) INLO)) xIX) 0 BIG;
    KRange (esub (eadd IT0 xDI) INLO) 0 INSZ;
    relx xDI xERR xIX IX 0;                                                            (* [comment removed for export] *)
    KRange (esub xMTR e_mtr) 0 MTRJ; KRange xMTR 0 MTRJ ] ++ mX c (szx m) xDI xMTR        (* [comment removed for export] *)
  ++ str c m xIX (eadd IT0 xDI) 52 ++ no_cbound CPW (kn_fixed c).
Definition tout (c : acfg) (m : smode) : acs := mkcsV c (c_ret c) regs_out (kn_out c m) (XLO + 15)%nat (vis m 52) xMTR.
Definition BCAP : Z := 10 * 2 ^ 30.  Definition CCAP : Z := 2.
Definition ce2 (c : acfg) (m : smode) : gcallee2 := GCE2 NXF (tin c m) [tout c MS] [tout c ML] BCAP CCAP.
Definition ce (c : acfg) (m : smode) : gcallee := c2_merged (ce2 c m).
(* [comment removed for export] *)
Definition ceL1 (c : acfg) : gcallee := GCE NXF (tin c ML) [tout c ML; tout c ML] BCAP CCAP.


Definition XB : nat -> list expr -> acs -> option (acs * acs) := XBc ASEGS AASAN NXF GASAN BCAP CCAP CT2_resize.
Definition FUELA : nat := 4000.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition own_entry (i : nat) (e : expr) : bool :=
  match e with EVar j => (Nat.eqb (Datatypes.S j) i && negb (Nat.eqb i 3))%bool | _ => false end.
Fixpoint gen_regs (bound : nat) (vol : list nat) (jreg : nat) (Jx : expr) (i : nat) (rs : list expr) (v : nat) : list expr * nat :=
  match rs with
  | [] => ([], v)
  | e :: r =>
      let ev := if Nat.eqb i jreg then (Jx, v)
                else if (existsb (Nat.eqb i) vol || own_entry i e || negb (expr_vars_lt bound e))%bool then (EVar v, Datatypes.S v) else (e, v) in
      let rv := gen_regs bound vol jreg Jx (Datatypes.S i) r (snd ev) in
      (fst ev :: fst rv, snd rv)
  end.
(* [comment removed for export] *)
Fixpoint rdiff (i : nat) (r1 r2 : list expr) : list nat :=
  match r1, r2 with
  | e1 :: t1, e2 :: t2 => (if expr_eqb e1 e2 then [] else [i]) ++ rdiff (Datatypes.S i) t1 t2
  | _, _ => []
  end.
(* [comment removed for export] *)
Definition frame_of (bound : nat) (k : list kentry) (ks : list (list kentry)) : list kentry :=
  List.filter (fun K => match K with
                        | KWord (SA b _) _ val => (expr_eqb b e_sp && expr_vars_lt bound val && forallb (fun k2 => existsb (kentry_eqb K) k2) ks)%bool
                        | _ => false end) k.

(* [comment removed for export] *)
Definition JV : nat := 80.
Definition J : expr := EVar JV.
Definition IXv := EVar 81. Definition Dv := EVar 82. Definition Sv := EVar 83. Definition Av := EVar 84. Definition MTRI := EVar 85.
Definition V0 : nat := 86.
Definition itK (c : acfg) (j : expr) : expr := eadd IT0 (escale (c_K c) j).       (* [comment removed for export] *)
Definition remK (c : acfg) (j : expr) : expr := esub REM (escale (c_K c) j).     (* [comment removed for export] *)
Definition relJe (c : acfg) (j ix : expr) : expr := esub (escale (24 * c_K c) j) (esub ix IX).
Definition relJ (c : acfg) (j ix : expr) (lo : Z) : kentry := KRange (relJe c j ix) lo BIG.
(* [comment removed for export] *)
Definition stri (c : acfg) (m : smode) (ix it : expr) (v : nat) : list kentry :=
  match m with MS => strS OBJ (EVar (1 + v)) | ML => strL c ix it (EVar v) (EVar (1 + v)) (EVar (2 + v)) end.
Definition kn_loop (c : acfg) (m : smode) (ix : expr) (v : nat) : list kentry :=
  [ KRange NV 1 NVHI; KRange (esub NV J) 1 NVHI; KWord (SA PIT 0) 8 (itK c J); KRange (remK c J) 0 REMHI;
    KWord (SA G 0) 4 ERR; KRange ERR 0 0; KWord (SA PIX 0) 8 ix; KRange ix 0 IXHI; KRange IX 0 BIG; KRange (esub ix IX) 0 two62;
    KRange (esub (escale 24 (esub (itK c J) INLO)) ix) 0 BIG; KRange (esub (itK c J) INLO) 0 INSZ;
    relJ c J ix 0;                                                                      (* [comment removed for export] *)
    KRange MTRI 0 MTRJ; KRange (esub MTRI e_mtr) 0 MTRJ ] ++ mP J Sv MTRI                (* [comment removed for export] *)
  ++ stri c m ix (itK c J) v ++ kn_fixed c.
(* [comment removed for export] *)
Definition LO1 : nat := 150.
Definition D1 := EVar 150. Definition S1 := EVar 151. Definition A1 := EVar 152. Definition VAL := EVar 153. Definition MTR1 := EVar 154.
Definition V1 : nat := 155.
(* [comment removed for export] *)
Definition room (c : acfg) (m : smode) : list kentry :=
  [KRange (esub S1 IXv) (c_hr c) (match m with MS => 2 ^ 40 | ML => 2 ^ 37 end)].
Definition kn_js1 (c : acfg) (m : smode) (fr : list kentry) : list kentry :=
  room c m ++ [ KRange J 0 (NVHI - 1); KRange (remK c J) (c_K c) REMHI ]
  ++ (match c_vw c with O => [] | w => [KWord (SA C 56) w VAL] end)
  ++ (if Z.eqb (c_vhi c) 0 then [] else [KRange VAL 0 (c_vhi c)])
  ++ [ KRange NV 1 NVHI; KRange (esub NV J) 1 NVHI; KWord (SA PIT 0) 8 (itK c J); KRange (remK c J) 0 REMHI;
       KWord (SA G 0) 4 ERR; KRange ERR 0 0; KWord (SA PIX 0) 8 IXv; KRange IXv 0 IXHI; KRange IX 0 BIG; KRange (esub IXv IX) 0 two62;
       KRange (esub (escale 24 (esub (itK c J) INLO)) IXv) 0 BIG; KRange (esub (itK c J) INLO) 0 INSZ;
       relJ c J IXv 0;
       KRange (esub MTR1 MTRI) 0 GROWMAX; KRange MTR1 0 MTRJ; KRange Sv 0 (8 * AHI);   (* [comment removed for export] *)
       KRange MTRI 0 MTRJ; KRange (esub MTRI e_mtr) 0 MTRJ ] ++ mE S1 Sv MTR1 MTRI ++ mP J Sv MTRI             (* [comment removed for export] *)
  ++ fr ++ stri c m IXv (itK c J) 150 ++ kn_fixed c.
(* [comment removed for export] *)
Definition RSZID (m : smode) : nat := match m with MS => 104%nat | ML => 114%nat end.
Definition RSZ (m : smode) : list expr :=
  match m with MS => resize_args_S Sv MTRI e_fb | ML => resize_args_L Dv Sv Av MTRI e_fb end.

Section Templates.
  Variable c : acfg.
  (* [comment removed for export] *)
  Variable XNi : nat -> list expr -> acs -> option acs.
  Variable epaths : smode -> expr -> expr -> expr -> list (list dstep).



  Variable SH : smode -> acs.
  Definition INVx (m : smode) (vol : list nat) (fr : list kentry) : acs :=
    let rv := gen_regs NXF vol (c_jreg c) J 0 (s_regs (a_ss (SH m))) V0 in
    mkcsV c (c_head c) (fst rv) (kn_loop c m IXv 82 ++ fr) (snd rv) (vis m 82) MTRI.





   (* [comment removed for export] *)
  Variable SJ1z : acs.
  Variable SJ2z : bool -> acs.
  (* [comment removed for export] *)
  Definition JS1g (bnd : smode -> nat) (sj1 : smode -> acs) (sj2 : smode -> bool -> acs) (m : smode) : acs :=
    let vol1 := c_vol1 c ++ rdiff 0 (s_regs (a_ss (sj1 ML))) (s_regs (a_ss (sj2 ML false)))
                         ++ rdiff 0 (s_regs (a_ss (sj1 ML))) (s_regs (a_ss (sj2 ML true))) in
    let fr := frame_of (bnd ML) (kn (sj1 ML)) [kn (sj2 ML false); kn (sj2 ML true)] in
    let rv := gen_regs (bnd m) vol1 99 J 0 (s_regs (a_ss (sj1 m))) V1 in
    mkcsV c (c_join1 c) (fst rv) (kn_js1 c m fr) (snd rv) (vis m 150) MTR1.



   (* [comment removed for export] *)
  Variable SH2s : list acs.
  Definition vol0 : list nat := c_vol0 c ++ flat_map (fun s2 => rdiff 0 (s_regs (a_ss (SH ML))) (s_regs (a_ss s2))) SH2s.
  Definition frame0 : list kentry := frame_of NXF (kn (SH ML)) (map kn SH2s).
  Definition INV (m : smode) : acs := INVx m vol0 frame0.
  Variable INVm : smode -> acs.
  Definition GCL (m : smode) : nat := nxt (INVm m).




     (* [comment removed for export] *)
  Variable SJ1 : smode -> acs.
  Variable SJ2 : smode -> bool -> acs.
  Definition JS1 (m : smode) : acs := JS1g GCL SJ1 SJ2 m.
End Templates.
(* [comment removed for export] *)
Section TemplatesI.
  Variable c : acfg.
  Variable itc : itab.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable XNi : nat -> list expr -> acs -> option acs.
  Variable epaths : smode -> expr -> expr -> expr -> list (list dstep).   (* [comment removed for export] *)
  Definition DPi_I (gcb : nat) (cs : acs) (steps : list dstep) : acs := snd (dpath ASEGS itc AASAN XNi XB BFUEL gcb cs steps 0).


  (* [comment removed for export] *)
  Definition S_head_I (m : smode) : acs := DPi_I NXF (tin c m) [DHi NV 0; DRun [c_head c]].
  Variable SH : smode -> acs.
  Definition INVx_I (m : smode) (vol : list nat) (fr : list kentry) : acs :=
    let rv := gen_regs NXF vol (c_jreg c) J 0 (s_regs (a_ss (SH m))) V0 in
    mkcsV c (c_head c) (fst rv) (kn_loop c m IXv 82 ++ fr) (snd rv) (vis m 82) MTRI.
  (* [comment removed for export] *)
  Definition p_join1_I : list dstep := [DHi (remK c J) (c_K c - 1); DRun []; DBrF; DRun [c_join1 c]].
  Definition p_rsz_I (m : smode) (grown : bool) : list dstep :=
    [DHi (remK c J) (c_K c - 1); DRun []; DBrT; DRun []; (if grown then DX2b (RSZID m) (RSZ m) else DX2a (RSZID m) (RSZ m)); DRun [c_join1 c]].
  (* [comment removed for export] *)
  Definition INV0_I : acs := INVx_I ML (c_vol0 c) (frame_of NXF (kn (SH ML)) []).
  Definition S_j1z_I : acs := DPi_I (nxt INV0_I) (loop_body_state JV NV NVHI INV0_I) p_join1_I.
  Definition S_j2z_I (grown : bool) : acs := DPi_I (nxt INV0_I) (loop_body_state JV NV NVHI INV0_I) (p_rsz_I ML grown).
   (* [comment removed for export] *)
  Variable SJ1z : acs.
  Variable SJ2z : bool -> acs.
  (* [comment removed for export] *)
  Definition JS1g_I (bnd : smode -> nat) (sj1 : smode -> acs) (sj2 : smode -> bool -> acs) (m : smode) : acs :=
    let vol1 := c_vol1 c ++ rdiff 0 (s_regs (a_ss (sj1 ML))) (s_regs (a_ss (sj2 ML false)))
                         ++ rdiff 0 (s_regs (a_ss (sj1 ML))) (s_regs (a_ss (sj2 ML true))) in
    let fr := frame_of (bnd ML) (kn (sj1 ML)) [kn (sj2 ML false); kn (sj2 ML true)] in
    let rv := gen_regs (bnd m) vol1 99 J 0 (s_regs (a_ss (sj1 m))) V1 in
    mkcsV c (c_join1 c) (fst rv) (kn_js1 c m fr) (snd rv) (vis m 150) MTR1.
  Definition JS1z_I : acs := JS1g_I (fun _ => nxt INV0_I) (fun _ => SJ1z) (fun _ g => SJ2z g) ML.
  Definition p_iters_I (m : smode) : list (list dstep) :=
    map (fun es => es ++ [DHi (esub NV J) 1; DRun [c_ix2pc c]; DRun [c_head c]]) (epaths m D1 IXv MTR1).
  Definition S_head2s_I : list acs := map (fun p => DPi_I (nxt JS1z_I) JS1z_I p) (p_iters_I ML).
   (* [comment removed for export] *)
  Variable SH2s : list acs.



  Variable INVm : smode -> acs.
  Definition GCL_I (m : smode) : nat := nxt (INVm m).
  Definition BODY0_I (m : smode) : acs := loop_body_state JV NV NVHI (INVm m).
  (* [comment removed for export] *)
  Definition S_j1_I (m : smode) : acs := DPi_I (GCL_I m) (BODY0_I m) p_join1_I.
  Definition S_j2_I (m : smode) (grown : bool) : acs := DPi_I (GCL_I m) (BODY0_I m) (p_rsz_I m grown).

     (* [comment removed for export] *)
  Variable SJ1 : smode -> acs.
  Variable SJ2 : smode -> bool -> acs.

End TemplatesI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition PH : nat := 255.
Definition XPH : expr := EVar PH.

Section Plan.
  Variable c : acfg.
  Variable INVT JS1T : smode -> acs.            (* [comment removed for export] *)
  Variable elem : smode -> plan -> plan.        (* [comment removed for export] *)
(* [comment removed for export] *)
Definition capA (m : smode) (r : nat) (itn cons' : expr) (k : plan) : plan :=
  match m with ML => PFactLeX r PH (capexpr XPH itn INLO A1) (eaddz (escale 104 cons') CAPK) CAPHI k | MS => k end.
(* [comment removed for export] *)
Definition chainM (k : plan) : plan :=
  PFactLe J REM REMHI                                   (* [comment removed for export] *)
  (PFactLe MTR1 (pwtop_e CPW S1) MTRJ                              (* [comment removed for export] *)
  (PFact (KRange (esub MTR1 e_mtr) 0 MTRJ) k)).
Definition chainA (m : smode) (r : nat) (k : plan) : plan :=
  let itn := itK c (eaddz J 1) in let cons' := esub itn INLO in
  PFactLe cons' (eadd (esub IT0 INLO) REM) INSZ
  (PFactLe (escale (c_K c) (eaddz J 1)) REM REMHI
  (PFactLeX r PH XPH (escale 24 cons') IXHI
  (PFactLeX r PH (esub (escale 24 cons') XPH) (escale 24 cons') BIG
  (PFactLeX r PH (esub XPH IX) XPH two62
  (PFactX r PH (relJe c (eaddz J 1) XPH) 1 BIG                  (* [comment removed for export] *)
  (capA m r itn cons' (chainM k))))))).
(* [comment removed for export] *)
Definition chainB (m : smode) (r : nat) (k : plan) : plan :=
  let itn := itK c (eaddz J 1) in let cons' := esub itn INLO in
  PFactLe (remK c (eaddz J 1)) (remK c J) REMHI
  (PFactLeX r PH XPH (escale 24 cons') IXHI
  (PFactLeX r PH (esub (escale 24 cons') XPH) (escale 24 cons') BIG
  (PFactLeX r PH (esub XPH IX) XPH two62
  (PFactX r PH (relJe c (eaddz J 1) XPH) 0 BIG                  (* [comment removed for export] *)
  (capA m r itn cons' k))))).

Definition EXIT0 (m : smode) : plan := PRun [] (PHandoffW (hole m) [(DISLOT, ELit 0)]).                   (* [comment removed for export] *)
Definition errJ (m : smode) : plan :=                                                         (* [comment removed for export] *)
  PRun [] (PFactLe (escale (c_K c) J) REM REMHI (PHandoffW (hole m) [(DISLOT, escale (c_K c) J)])).
Definition after_elem (m : smode) : plan :=
  chainA m (c_ixreg c)
    (PCase2 (esub NV J) 1
       (PRun [] (PHandoffW (hole m) [(DISLOT, escale (c_K c) (eaddz J 1))]))                           (* [comment removed for export] *)
       (PRun [c_ix2pc c] (chainB m (c_ix2reg c) (PRun [c_head c] PNext)))).                           (* [comment removed for export] *)
(* [comment removed for export] *)
Definition after1 (m : smode) : plan :=
  match m with
  | ML => PFactVia (esub (escale 8 A1) IXv) (esub S1 IXv) (c_hr c + 1) (2 ^ 40) (elem ML (after_elem ML))
  | MS => elem MS (after_elem MS)
  end.                                                                (* [comment removed for export] *)
(* [comment removed for export] *)
Definition NEWSZ : expr := eaddz (escale 2 IXv) (2 * c_hr c).        (* [comment removed for export] *)
Definition PWK (k : plan) : plan := PExt 49 [MTRI; Sv; NEWSZ; CPW; ELit 1] k.     (* [comment removed for export] *)
Definition PWG (k : plan) : plan := PExt 49 [MTRI; Sv; NEWSZ; CPW; ELit 0] k.     (* [comment removed for export] *)
Definition diamondL : plan :=
  PBranch (PRun [c_join1 c] (PMerge 1))
          (PRun [] (PExt2 (RSZID ML) (RSZ ML) (PWK (PRun [c_join1 c] (PMerge 1))) (PWG (PRun [c_join1 c] (PMerge 1))))).
Definition diamondS : plan :=
  if Z.leb 23 (c_hr c) then PExt2 (RSZID MS) (RSZ MS) (PContraH 0) (PWG (PRun [c_join1 c] (PMerge 1)))
  else PBranch (PRun [c_join1 c] (PMerge 1))
               (PRun [] (PExt2 (RSZID MS) (RSZ MS) (if Z.leb 12 (c_hr c) then PContraH 0 else PWK (PRun [c_join1 c] (PMerge 1)))
                                                    (PWG (PRun [c_join1 c] (PMerge 1))))).
Definition alts1 (m : smode) : list (acs * plan) :=
  match m with
  | ML => [(JS1T ML, after1 ML)]
  | MS => if Z.leb 23 (c_hr c) then [(JS1T ML, after1 ML)] else [(JS1T MS, after1 MS); (JS1T ML, after1 ML)]
  end.
Definition body (m : smode) : plan :=
  PCase2 (remK c J) (c_K c - 1) (errJ m)
    (PRun [] (PViaM 1 (alts1 m) LO1 (match m with ML => diamondL | MS => diamondS end))).

End Plan.

