(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgJT.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS. Import APC.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Fixpoint assocn (l : list (nat * expr)) (i : nat) : option expr :=
  match l with [] => None | (j, x) :: r => if Nat.eqb i j then Some x else assocn r i end.
Fixpoint jregs (rss : list (list expr)) (i n : nat) (ov : list (nat * expr)) (keep v : nat) : list expr :=
  match n with
  | O => []
  | Datatypes.S n' =>
      let col := map (fun rs => nth i rs (ELit 0)) rss in
      match assocn ov i with
      | Some x => x :: jregs rss (Datatypes.S i) n' ov keep v
      | None =>
          match col with
          | e :: r => if (forallb (expr_eqb e) r && expr_vars_lt keep e)%bool then e :: jregs rss (Datatypes.S i) n' ov keep v
                      else EVar v :: jregs rss (Datatypes.S i) n' ov keep (Datatypes.S v)
          | [] => EVar v :: jregs rss (Datatypes.S i) n' ov keep (Datatypes.S v)
          end
      end
  end.
(* [comment removed for export] *)
Definition is_frame_word (fr : Z) (keep : nat) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w x => (expr_eqb b e_sp && Z.leb (- fr) o && Z.ltb o 0) && expr_vars_lt keep x
  | _ => false
  end.
Definition jframe (fr : Z) (ss : list acs) (keep : nat) : list kentry :=
  match ss with
  | [] => []
  | s0 :: r => List.filter (fun K => is_frame_word fr keep K && forallb (fun s => existsb (kentry_eqb K) (kn s)) r)%bool (kn s0)
  end.
Fixpoint maxvar_regs (rs : list expr) (acc : nat) : nat :=
  match rs with [] => acc | EVar i :: r => maxvar_regs r (Nat.max acc (Datatypes.S i)) | _ :: r => maxvar_regs r acc end.


End BgJT.
Require LinuxProcessSemantics.Riscv.Instr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgVecT.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ANNOT : Z := 0x70fc4.       (* [comment removed for export] *)
Definition SZHI : Z := 2 ^ 26 - 1.

Module Ctor.
Definition ENTRY : Z := 0x9e5ec.
Definition RETPC : Z := 0x9e654.
Definition NXF : nat := 33.
Definition V : expr := EVar 9.  Definition FIRST : expr := EVar 10.  Definition SZ : expr := EVar 12.
Definition e_mtr : expr := EVar 31.  Definition e_fb : expr := EVar 32.
Definition regsT : list expr := sr_upd (sr_upd regs0 4 (ELit (g_tp GBOTH))) 12 (eadd FIRST SZ).
Definition FRS : Z := 64 + 32 + MSTK_N.      (* [comment removed for export] *)
Definition MTRIN : Z := GKCAP - kcost (SZHI + 1).
Definition vobj : list kentry :=
  [ KRange V PTRLO (objhi 32); KAlign V 8; KWr (SA V 0) (ELit 24); shok V 0 24;
    KDisj (SA V 0) (ELit 24) (SA e_sp (- FRS)) (ELit (FRS + WSTK)); img_apart V 0 (ELit 24); shmap_apart V 0 (ELit 24) ].
Definition payload : list kentry :=
  [ KRange SZ 1 SZHI; KRange FIRST PTRLO (PTRHI - 1); KRange (eadd FIRST SZ) (PTRLO + 1) PTRHI; KAlign FIRST 16;
    KWr (SA FIRST 0) SZ; KUnk (SA FIRST 0) SZ; KShOk (SA FIRST 0) SZ;
    KDisj (SA FIRST 0) SZ (SA e_sp (- FRS)) (ELit (FRS + WSTK)); img_apart FIRST 0 SZ; shmap_apart FIRST 0 SZ;
    KDisj (SA FIRST 0) SZ (SA V 0) (ELit 24) ].
Definition stk_facts : list kentry := [ KAlign e_sp 32; KRange e_sp (CEIL + FRS) HI47; KWr (SA e_sp (- FRS)) (ELit FRS) ].
(* [comment removed for export] *)
Definition kn_fixed : list kentry := vobj ++ payload ++ NEWH ++ RTC ++ [KIMGA] ++ GLZ_LOWSH.
Definition kn_in : list kentry := kn_fixed ++ stk_facts ++ [ KShOk (SA e_sp (- FRS)) (ELit FRS); fb_fact e_fb; KRange e_mtr 0 MTRIN ].
Definition WS : list (expr * expr) := [(V, ELit 24)].
Definition mkcsV (vis : list (expr * expr)) (mtr : expr) (p : Z) (regs : list expr) (k : list kentry) (nx : nat) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRS 0 vis WS 0 e_sp FdStd false mtr [] e_fb.
Definition tin : acs := mkcsV [(FIRST, SZ)] e_mtr ENTRY regsT kn_in NXF.
(* [comment removed for export] *)
Definition P : expr := EVar 33.
Definition XLO : nat := 34.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_out : list expr := sr_havoc (sr_upd regs0 4 (ELit (g_tp GBOTH))) clobbered XLO.
Definition blkP (p n : expr) : list kentry :=
  [ KRange p PTRLO (PTRHI - 1); KRange (eadd n p) (PTRLO + 1) PTRHI; KAlign p 16; KWr (SA p 0) n; KUnk (SA p 0) n; KShOk (SA p 0) n;
    KDisj (SA p 0) n (SA e_sp (- FRS)) (ELit (FRS + WSTK)); img_apart p 0 n; shmap_apart p 0 n;
    KDisj (SA p 0) n (SA FIRST 0) SZ; KDisj (SA p 0) n (SA V 0) (ELit 24) ].
Definition kn_out : list kentry :=
  [ KWord (SA V 0) 8 P; KWord (SA V 8) 8 (eadd SZ P); KWord (SA V 16) 8 (eadd SZ P) ] ++ blkP P SZ ++ kn_fixed.
Definition MTRX : expr := eaddz e_mtr EVT.      (* [comment removed for export] *)
Definition tout : acs := mkcsV [(P, SZ); (FIRST, SZ)] MTRX RETPC regs_out kn_out (XLO + 15)%nat.
Definition BCAP : Z := 3 * 2 ^ 26.   (* [comment removed for export] *)
Definition CCAP : Z := 2.
Definition ce : gcallee := GCE NXF tin [tout] BCAP CCAP.
End Ctor.

(* [comment removed for export] *)
Module Push.
Definition ENTRY : Z := 0x9e538.
Definition RETPC : Z := 0x9e5cc.
Definition NXF : nat := 35.
Definition V : expr := EVar 9.  Definition C : expr := EVar 10.
Definition D : expr := EVar 31.  Definition SZ : expr := EVar 32.
Definition e_mtr : expr := EVar 33.  Definition e_fb : expr := EVar 34.
Definition regsT : list expr := sr_upd regs0 4 (ELit (g_tp GBOTH)).
Definition FRS : Z := 32 + 96 + 64 + MSTK_N.   (* [comment removed for export] *)      (* [comment removed for export] *)
Definition MTRIN : Z := GKCAP - kcost (2 * SZHI + 2) - KFREE.
Definition vobj : list kentry :=
  [ KRange V PTRLO (objhi 32); KAlign V 8; KWr (SA V 0) (ELit 24); shok V 0 24;
    KDisj (SA V 0) (ELit 24) (SA e_sp (- FRS)) (ELit (FRS + WSTK)); img_apart V 0 (ELit 24); shmap_apart V 0 (ELit 24) ].
(* [comment removed for export] *)
Definition cobj : list kentry :=
  [ KRange C (CEIL + FRS) (HI47 - 8); KUnk (SA C 0) (ELit 1); shok C 0 1; KDisj (SA C 0) (ELit 1) (SA V 0) (ELit 24);
    KDisj (SA C 0) (ELit 1) (SA e_sp (- FRS)) (ELit FRS) ].
Definition blk (p n : expr) : list kentry :=
  [ KRange p PTRLO (PTRHI - 1); KRange (eadd n p) (PTRLO + 1) PTRHI; KAlign p 16; KWr (SA p 0) n; KUnk (SA p 0) n; KShOk (SA p 0) n;
    KDisj (SA p 0) n (SA e_sp (- FRS)) (ELit (FRS + WSTK)); img_apart p 0 n; shmap_apart p 0 n;
    KDisj (SA p 0) n (SA V 0) (ELit 24) ].
Definition stk_facts : list kentry := [ KAlign e_sp 16; KRange e_sp (CEIL + FRS) HI47; KWr (SA e_sp (- FRS)) (ELit FRS) ].
Definition SZLO : Z := 1.      (* [comment removed for export] *)
Definition kn_fixed : list kentry := vobj ++ [KRange SZ SZLO SZHI] ++ NEWH ++ RTC ++ [KIMGA] ++ GLZ_LOWSH.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition kn_in : list kentry :=
  [ KWord (SA V 0) 8 D; KWord (SA V 8) 8 (eadd SZ D); KWord (SA V 16) 8 (eadd SZ D) ] ++ blk D SZ ++ kn_fixed ++ cobj ++ stk_facts
  ++ [ KShOk (SA e_sp (- FRS)) (ELit FRS); fb_fact e_fb; KRange e_mtr 0 MTRIN ].
Definition WS : list (expr * expr) := [(V, ELit 24); (C, ELit 1)].
Definition mkcsV (vis : list (expr * expr)) (mtr : expr) (p : Z) (regs : list expr) (k : list kentry) (nx : nat) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRS 0 vis WS 0 e_sp FdStd false mtr [] e_fb.
Definition tin : acs := mkcsV [(D, SZ)] e_mtr ENTRY regsT kn_in NXF.
(* [comment removed for export] *)
Definition P2 : expr := EVar 35.
Definition XLO : nat := 36.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_out : list expr := sr_havoc regsT clobbered XLO.
Definition CAP2 : expr := escale 2 SZ.
Definition blk2 (p : expr) (cap used : expr) (nlo : Z) : list kentry :=
  [ KRange p PTRLO (PTRHI - nlo); KRange (eadd cap p) (PTRLO + nlo) PTRHI; KAlign p 16; KWr (SA p 0) cap; KUnk (SA p 0) cap; KShOk (SA p 0) used;
    KDisj (SA p 0) cap (SA e_sp (- FRS)) (ELit (FRS + WSTK)); img_apart p 0 cap; shmap_apart p 0 cap;
    KDisj (SA p 0) cap (SA V 0) (ELit 24) ].
Definition kn_out : list kentry :=
  [ KWord (SA V 0) 8 P2; KWord (SA V 8) 8 (eaddz (eadd SZ P2) 1); KWord (SA V 16) 8 (eadd CAP2 P2) ] ++ blk2 P2 CAP2 (eaddz SZ 1) 2
  ++ [ KRange (eaddz (eadd SZ P2) 1) (PTRLO + 2) PTRHI ]      (* [comment removed for export] *)
  ++ kn_fixed.
Definition MTRX : expr := eaddz e_mtr (EVT + KFREE).      (* [comment removed for export] *)
Definition tout : acs := mkcsV [(P2, CAP2)] MTRX RETPC regs_out kn_out (XLO + 15)%nat.
(* [comment removed for export] *)
Definition kn_out1 : list kentry :=
  [ KWord (SA V 0) 8 P2; KWord (SA V 8) 8 (eaddz P2 2); KWord (SA V 16) 8 (eaddz P2 2) ] ++ blk2 P2 (ELit 2) (ELit 2) 2 ++ [KRange SZ 1 1] ++ kn_fixed.
Definition tout1 : acs := mkcsV [(P2, ELit 2)] (eaddz e_mtr (EVT + KFREE)) RETPC regs_out kn_out1 (XLO + 15)%nat.
Definition BCAP : Z := 4 * 2 ^ 26.  Definition CCAP : Z := 2.
Definition ce2 : gcallee2 := GCE2 NXF tin [tout] [tout1] BCAP CCAP.
Definition ce : gcallee := c2_merged ce2.

(* [comment removed for export] *)
Definition NXFE : nat := 33.
Definition e_mtrE : expr := EVar 31.  Definition e_fbE : expr := EVar 32.
Definition kn_fixedE : list kentry := vobj ++ NEWH ++ RTC ++ [KIMGA] ++ GLZ_LOWSH.
Definition kn_inE : list kentry :=
  [ KWord (SA V 0) 8 (ELit 0); KWord (SA V 8) 8 (ELit 0); KWord (SA V 16) 8 (ELit 0) ] ++ kn_fixedE ++ cobj ++ stk_facts
  ++ [ KShOk (SA e_sp (- FRS)) (ELit FRS); fb_fact e_fbE; KRange e_mtrE 0 MTRIN ].
Definition mkcsE (vis : list (expr * expr)) (mtr : expr) (p : Z) (regs : list expr) (k : list kentry) (nx : nat) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRS 0 vis WS 0 e_sp FdStd false mtr [] e_fbE.
Definition tinE : acs := mkcsE [] e_mtrE ENTRY regsT kn_inE NXFE.
Definition P2E : expr := EVar 33.
Definition regs_outE : list expr := sr_havoc regsT clobbered 34.
Definition kn_outE : list kentry :=
  [ KWord (SA V 0) 8 P2E; KWord (SA V 8) 8 (eaddz P2E 1); KWord (SA V 16) 8 (eaddz P2E 1) ] ++ blk2 P2E (ELit 1) (ELit 1) 1 ++ kn_fixedE.
Definition toutE : acs := mkcsE [(P2E, ELit 1)] (eaddz e_mtrE EVT) RETPC regs_outE kn_outE 49.
Definition BCAPE : Z := 2 ^ 21.
Definition ceE : gcallee := GCE NXFE tinE [toutE] BCAPE 1.
End Push.
End BgVecT.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw BgJT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Record ncfg := NCFG {
  n_ninstr : nat;
  n_K : Z;                (* [comment removed for export] *)
  n_hr : Z;               (* [comment removed for export] *)
  n_wmx : Z;              (* [comment removed for export] *)
  n_vhi : Z;              (* [comment removed for export] *)
  n_join1 : Z;            (* [comment removed for export] *)
  n_ret : Z;              (* [comment removed for export] *)
  n_stix : Z;             (* [comment removed for export] *)
  n_ixreg : nat;          (* [comment removed for export] *)
  n_more : list (Z * nat) (* [comment removed for export] *)
}.
Definition IT (c : ncfg) (B : Z) : itab := mk_itab_ranges BSEGS ((B, n_ninstr c) :: n_more c).
Lemma IT_ok : forall c B, itab_sound BSEGS (IT c B). Proof. intros. apply APS.mk_itab_ranges_sound. Qed.
Definition RETPC (c : ncfg) (B : Z) : Z := B + n_ret c.
Definition JOIN1 (c : ncfg) (B : Z) : Z := B + n_join1 c.
Definition STIX (c : ncfg) (B : Z) : Z := B + n_stix c.
Definition FR : Z := 96.                 (* [comment removed for export] *)

(* [comment removed for export] *)
Definition regsW : list expr := sr_upd regs0 4 (ELit (g_tp GBOTH)).    (* [comment removed for export] *)
Definition C : expr := EVar 9.           (* [comment removed for export] *)
Definition T : expr := eaddz C (-8).
Definition G : expr := EVar 31.          (* [comment removed for export] *)
Definition OBJ : expr := EVar 32.        (* [comment removed for export] *)
Definition ITO : expr := EVar 33.        (* [comment removed for export] *)
Definition REM : expr := EVar 34.        (* [comment removed for export] *)
Definition IX : expr := EVar 35.         (* [comment removed for export] *)
Definition D : expr := EVar 36.  Definition S : expr := EVar 37.  Definition A : expr := EVar 38.   (* [comment removed for export] *)
Definition ERR : expr := EVar 39.        (* [comment removed for export] *)
Definition INLO : expr := EVar 40.       (* [comment removed for export] *)
Definition PEND : expr := EVar 41.       (* [comment removed for export] *)
Definition PIT : expr := EVar 42.        (* [comment removed for export] *)
Definition PIX : expr := EVar 43.        (* [comment removed for export] *)
Definition e_mtr : expr := EVar 44.      (* [comment removed for export] *)
Definition e_fb : expr := EVar 45.       (* [comment removed for export] *)
Definition IT0 : expr := eadd INLO ITO.  (* [comment removed for export] *)
Definition BLEN : expr := eadd ITO REM.
Definition NXF : nat := 46.

Definition INSZ : Z := 2 ^ 26.
Definition BIG : Z := 24 * INSZ.
Definition REMHI : Z := INSZ.
Definition IXHI : Z := BIG.
Definition CAPK : Z := 1040.
Definition AHI : Z := (4 * IXHI + 8 * INSZ + CAPK) / 8.
Definition FRK : Z := FR + 3680.         (* [comment removed for export] *)
Definition RFRK : Z := 3680.
Definition flo (x : expr) (n : expr) : kentry := KDisj (SA x 0) n (SA e_sp (- FRK)) (ELit (FRK + WSTK)).   (* [comment removed for export] *)
Definition NB : Z := 3 * 2^30 + 16.

Definition MTRJ : Z := MTRMAX NB.
(* [comment removed for export] *)
Definition CPW : expr := EVar 3.
Definition CMAX : Z := MTRJ - pwtop (8 * AHI).   (* [comment removed for export] *)
Definition MTRIN : Z := MTRJ.
Definition GROWMAX : Z := kcost (2 * NB + 8) + KFREE.

(* [comment removed for export] *)
Definition szin (m0 : smode) : expr := match m0 with MS => EVar 36 | ML => S end.
(* [comment removed for export] *)
Definition capexpr (ix it inlo a : expr) : expr := esub (eaddz (eadd (escale 4 ix) (escale 8 (esub it inlo))) CAPK) (escale 8 a).
Definition capfact (ix it inlo a : expr) : kentry := KRange (capexpr ix it inlo a) 0 (4 * IXHI + 8 * INSZ + CAPK).
Definition strL (ix it d s a : expr) : list kentry :=
  [ KWord (SA OBJ 0) 8 (eaddz (escale 8 a) 1); KWord (SA OBJ 8) 8 s; KWord (SA OBJ 16) 8 d;
    KRange a 3 AHI; capfact ix it INLO a;
    KRange s 0 (8 * AHI); KRange (esub (escale 8 a) s) 1 (8 * AHI);
    KRange d PTRLO (PTRHI - 24); KRange (eadd d (escale 8 a)) (PTRLO + 24) PTRHI; KAlign d 16;
    KWr (SA d 0) (escale 8 a); KUnk (SA d 0) (escale 8 a); KShOk (SA d 0) (escale 8 a);                 (* [comment removed for export] *)
    KDisj (SA d 0) (escale 8 a) (SA C (-8)) (ELit 48); KDisj (SA d 0) (escale 8 a) (SA G 0) (ELit 4);
    KDisj (SA d 0) (escale 8 a) (SA PEND 0) (ELit 8); KDisj (SA d 0) (escale 8 a) (SA PIT 0) (ELit 8); KDisj (SA d 0) (escale 8 a) (SA PIX 0) (ELit 8);
    KDisj (SA d 0) (escale 8 a) (SA OBJ 0) (ELit 24); KDisj (SA d 0) (escale 8 a) (SA INLO 0) BLEN;
    KDisj (SA d 0) (escale 8 a) (SA e_sp (- FRK)) (ELit (RFRK + WSTK)); img_apart d 0 (escale 8 a); shmap_apart d 0 (escale 8 a) ].


Definition tbl_shadow : list kentry := GLZ_LOWSH.   (* [comment removed for export] *)
Definition kn_fixed : list kentry :=
  [ KRange C (CEIL + 16) (HI47 - 40); KAlign C 8; KShOk (SA C (-8)) (ELit 48); KWord (SA C 0) 8 PEND; KWord (SA C 8) 8 PIT; KWord (SA C 16) 8 G;
    KWord (SA C 24) 8 OBJ; KWord (SA C 32) 8 PIX; KWr (SA C (-8)) (ELit 8);   (* [comment removed for export] *)
    KRange G PTRLO (objhi 4); KWr (SA G 0) (ELit 4); KShOk (SA G 0) (ELit 4); KAlign G 8;   (* [comment removed for export] *)
    KRange PEND PTRLO (objhi 8); KWord (SA PEND 0) 8 (eadd IT0 REM); KShOk (SA PEND 0) (ELit 8); KAlign PEND 8;
    KRange PIT PTRLO (objhi 8); KWr (SA PIT 0) (ELit 8); KShOk (SA PIT 0) (ELit 8); KAlign PIT 8;
    KRange PIX PTRLO (objhi 8); KWr (SA PIX 0) (ELit 8); KShOk (SA PIX 0) (ELit 8); KAlign PIX 8;
    KRange OBJ PTRLO (objhi 24); KWr (SA OBJ 0) (ELit 24); KShOk (SA OBJ 0) (ELit 24); KAlign OBJ 8;
    KRange INLO PTRLO PTRHI; KRange ITO 1 INSZ; KRange REM 0 REMHI; KRange BLEN 1 INSZ;
    KUnk (SA INLO 0) BLEN; KShOk (SA INLO 0) BLEN; KRange (eadd INLO BLEN) (PTRLO + 1) PTRHI;
    KDisj (SA C (-8)) (ELit 48) (SA OBJ 0) (ELit 24); KDisj (SA e_sp (- FRK)) (ELit FRK) (SA OBJ 0) (ELit 24);   (* [comment removed for export] *)
    KDisj (SA G 0) (ELit 4) (SA OBJ 0) (ELit 24); KDisj (SA PEND 0) (ELit 8) (SA OBJ 0) (ELit 24);
    KDisj (SA PIT 0) (ELit 8) (SA OBJ 0) (ELit 24); KDisj (SA PIX 0) (ELit 8) (SA OBJ 0) (ELit 24);
    KDisj (SA G 0) (ELit 4) (SA PIT 0) (ELit 8); KDisj (SA G 0) (ELit 4) (SA PIX 0) (ELit 8); KDisj (SA G 0) (ELit 4) (SA PEND 0) (ELit 8);
    KDisj (SA PIT 0) (ELit 8) (SA PIX 0) (ELit 8); KDisj (SA PEND 0) (ELit 8) (SA PIT 0) (ELit 8); KDisj (SA PEND 0) (ELit 8) (SA PIX 0) (ELit 8);
    KDisj (SA INLO 0) BLEN (SA G 0) (ELit 4); KDisj (SA INLO 0) BLEN (SA OBJ 0) (ELit 24);
    KDisj (SA INLO 0) BLEN (SA PEND 0) (ELit 8); KDisj (SA INLO 0) BLEN (SA PIT 0) (ELit 8); KDisj (SA INLO 0) BLEN (SA PIX 0) (ELit 8);
    KUnk (SA OBJ 0) (ELit 24);
    KAlign e_sp 16; KRange e_sp (CEIL + FRK + 416) (two47 - 16); KWr (SA e_sp (- FRK)) (ELit FRK);
    KRange (esub C e_sp) 16 (2 ^ 63); KDisj (SA e_sp (- FRK)) (ELit FRK) (SA C (-8)) (ELit 48);   (* [comment removed for export] *)
    KRange e_mtr 0 MTRIN; KRange CPW 0 CMAX;
    flo G (ELit 4); flo PEND (ELit 8); flo PIT (ELit 8); flo PIX (ELit 8); flo OBJ (ELit 24); flo INLO BLEN;
    img_apart G 0 (ELit 4); shmap_apart G 0 (ELit 4); img_apart PIT 0 (ELit 8); shmap_apart PIT 0 (ELit 8);
    img_apart PIX 0 (ELit 8); shmap_apart PIX 0 (ELit 8); img_apart OBJ 0 (ELit 24); shmap_apart OBJ 0 (ELit 24);
    img_apart PEND 0 (ELit 8); img_apart INLO 0 BLEN; shmap_apart INLO 0 BLEN;
    KDisj (SA C (-8)) (ELit 48) (SA G 0) (ELit 4); KDisj (SA C (-8)) (ELit 48) (SA PEND 0) (ELit 8); KDisj (SA C (-8)) (ELit 48) (SA PIT 0) (ELit 8);
    KDisj (SA C (-8)) (ELit 48) (SA PIX 0) (ELit 8); KDisj (SA C (-8)) (ELit 48) (SA INLO 0) BLEN;   (* [comment removed for export] *)
    KIMGA; fb_fact e_fb ] ++ NEWH ++ RTC ++ tbl_shadow.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition str (m : smode) (ix it : expr) (v : nat) : list kentry :=
  match m with MS => strS OBJ (EVar v) | ML => strL ix it (EVar v) (EVar (1 + v)) (EVar (2 + v)) end.
Definition vis (m : smode) (v : nat) : list (expr * expr) :=
  match m with MS => [] | ML => [(EVar v, escale 8 (EVar (2 + v)))] end.
Definition kn_in (m : smode) : list kentry :=
  [ KWord (SA G 0) 4 ERR; KRange ERR 0 0; KWord (SA PIT 0) 8 IT0; KWord (SA PIX 0) 8 IX; KRange IX 0 BIG;
    KRange (esub (escale 24 (esub IT0 INLO)) IX) 0 BIG ]                          (* [comment removed for export] *)
  ++ pw_facts CPW (szin m) e_mtr ++ str m IX IT0 36 ++ kn_fixed.
Definition WS : list (expr * expr) := [(eaddz C (-8), ELit 48); (G, ELit 4); (PEND, ELit 8); (PIT, ELit 8); (PIX, ELit 8); (OBJ, ELit 24); (INLO, BLEN)].   (* [comment removed for export] *)
Definition mkcsV (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRK 0 vis WS 0 e_sp FdStd false e_mtr [] e_fb.
Definition regs_in : list expr := sr_upd regsW 11 T.
Definition tin (m : smode) (B : Z) : acs := mkcsV B regs_in (kn_in m) NXF (vis m 36).

(* [comment removed for export] *)
Definition xERR := EVar 46. Definition xDI := EVar 47. Definition xIX := EVar 48.
 Definition xS := EVar 50.

Definition xMTR := EVar 52.
Definition XLO : nat := 53.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_out : list expr := sr_havoc regsW clobbered XLO.
Definition szx (m : smode) : expr := match m with MS => EVar 49 | ML => xS end.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition kn_out (c : ncfg) (m0 m : smode) : list kentry :=
  [ KWord (SA G 0) 4 xERR; KRange xERR 0 24; KWord (SA PIT 0) 8 (eadd IT0 xDI); KRange xDI 0 (n_K c); KRange (esub REM xDI) 0 REMHI;
    KWord (SA PIX 0) 8 xIX; KRange xIX 0 IXHI; KRange (esub xIX IX) 0 (n_wmx c);
    KRange (esub (escale 24 (esub (eadd IT0 xDI) INLO)) xIX) 0 BIG;                   (* [comment removed for export] *)
    KRange (esub (eadd IT0 xDI) INLO) 0 INSZ                                         (* [comment removed for export] *)
    ] ++ pw_facts CPW (szx m) xMTR ++ [                       (* [comment removed for export] *)
    KRange (esub xMTR e_mtr) 0 MTRJ; KRange xMTR 0 MTRJ;
    relx xDI xERR xIX IX 8 ]                                                          (* [comment removed for export] *)
  ++ str m xIX (eadd IT0 xDI) 49 ++ no_cbound CPW kn_fixed.
Definition mkcsX (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRK 0 vis WS 0 e_sp FdStd false xMTR [] e_fb.
Definition tout (c : ncfg) (m0 m : smode) (B : Z) : acs := mkcsX (RETPC c B) regs_out (kn_out c m0 m) (XLO + 15)%nat (vis m 49).
Definition BCAP : Z := 10 * 2 ^ 30.  Definition CCAP : Z := 2.
(* [comment removed for export] *)
Definition ce2 (c : ncfg) (m : smode) (B : Z) : gcallee2 := GCE2 NXF (tin m B) [tout c m MS B] [tout c m ML B] BCAP CCAP.
Definition ce (c : ncfg) (m : smode) (B : Z) : gcallee := c2_merged (ce2 c m B).
(* [comment removed for export] *)
Definition ceL1 (c : ncfg) (B : Z) : gcallee := GCE NXF (tin ML B) [tout c ML ML B; tout c ML ML B] BCAP CCAP.

(* [comment removed for export] *)
Definition XNg (c : ncfg) (CT : nat -> option gcallee) (B : Z) : nat -> list expr -> acs -> option acs := XNw (XNc BSEGS (IT c B) ABOTH NXF GBOTH BCAP CCAP CT).   (* [comment removed for export] *)
Definition XB : nat -> list expr -> acs -> option (acs * acs) := XBc BSEGS ABOTH NXF GBOTH BCAP CCAP CT2_resize.
Definition FUEL16 : nat := 4000.

(* [comment removed for export] *)
Definition D1 := EVar 100. Definition S1 := EVar 101. Definition A1 := EVar 102. Definition BV := EVar 103. Definition MTR1 := EVar 104.
Definition csregs_ra : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition room (c : ncfg) (m : smode) : list kentry :=
  match m with MS => [KRange (esub (EVar 100) IX) (n_hr c) (2 ^ 40)] | ML => [KRange (esub S1 IX) (n_hr c) (2 ^ 37)] end.
(* [comment removed for export] *)
Definition sz1 (m : smode) : expr := match m with MS => EVar 100 | ML => S1 end.
Definition mfacts1 (m0 m : smode) : list kentry :=
  [ ] ++ pw_facts CPW (sz1 m) MTR1 ++ [
    KRange (esub MTR1 e_mtr) 0 GROWMAX; KRange MTR1 0 MTRJ ].
Definition mkcsJ (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRK 0 vis WS 0 e_sp FdStd false MTR1 [] e_fb.
Definition JS1 (c : ncfg) (rm : list expr) (fw : list kentry) (m0 m : smode) (B : Z) : acs :=
  mkcsJ (JOIN1 c B) rm
       (room c m ++ mfacts1 m0 m ++ [KWord (SA C (-8)) (Z.to_nat (n_K c)) BV] ++ (if Z.eqb (n_vhi c) 0 then [] else [KRange BV 0 (n_vhi c)])
        ++ [KRange REM (n_K c) REMHI] ++ fw
        ++ [KWord (SA G 0) 4 ERR; KRange ERR 0 0; KWord (SA PIT 0) 8 IT0; KWord (SA PIX 0) 8 IX; KRange IX 0 BIG;
            KRange (esub (escale 24 (esub IT0 INLO)) IX) 0 BIG]
        ++ str m IX IT0 100 ++ kn_fixed)
       140 (vis m 100).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition PH : nat := 255.   (* [comment removed for export] *)
Definition XPH : expr := EVar PH.
(* [comment removed for export] *)
Definition RSZID (m : smode) : nat := match m with MS => 104%nat | ML => 114%nat end.
Definition RSZ (m : smode) : list expr :=
  match m with MS => resize_args_S D e_mtr e_fb | ML => resize_args_L D S A e_mtr e_fb end.

(* [comment removed for export] *)
Definition exit_chain (c : ncfg) (m : smode) (k : plan) : plan :=
  let r := n_ixreg c in let K := n_K c in
  let cons' := esub (eaddz IT0 K) INLO in
  PFactLe cons' (eadd (esub IT0 INLO) REM) INSZ
  (PFact (KRange ITO 1 (INSZ - K))
  (PFactLeX r PH XPH (escale 24 cons') IXHI
  (PFactLeX r PH (esub (escale 24 cons') XPH) (escale 24 cons') BIG
  (match m with
   | ML => PFactLeX r PH (capexpr XPH (eaddz IT0 K) INLO A1) (eaddz (escale 104 cons') CAPK) (4 * IXHI + 8 * INSZ + CAPK) k
   | MS => k end)))).
Definition NEWSZ (c : ncfg) : expr := eaddz (escale 2 IX) (2 * n_hr c).        (* [comment removed for export] *)
Definition EXITOK (c : ncfg) (m : smode) : plan := exit_chain c m (PRun [] (PHandoffW (hole m) [(47%nat, ELit (n_K c))])).
Definition EXITERR (m : smode) : plan := PRun [] (PHandoffW (hole m) [(47%nat, ELit 0)]).       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition fin (c : ncfg) (B : Z) (m : smode) : plan := PRun [STIX c B] (EXITOK c m).

Section Plan.
Variable c : ncfg.
Variable elem : smode -> plan -> plan.      (* [comment removed for export] *)
Variable rm : list expr.                    (* [comment removed for export] *)
Variable fw : list kentry.
Variable B : Z.
(* [comment removed for export] *)
Definition after1 (m : smode) : plan :=
  match m with ML => PFactVia (esub (escale 8 A1) IX) (esub S1 IX) (n_hr c + 1) (2 ^ 40) (elem ML (fin c B ML)) | MS => elem MS (fin c B MS) end.
(* [comment removed for export] *)
Definition mrg : plan := PRun [JOIN1 c B] (PMerge 1).
Definition PWK (m : smode) (k : plan) : plan := PExt 49 [e_mtr; szin m; NEWSZ c; CPW; ELit 1] k.     (* [comment removed for export] *)
Definition PWG (m : smode) (k : plan) : plan := PExt 49 [e_mtr; szin m; NEWSZ c; CPW; ELit 0] k.     (* [comment removed for export] *)
Definition diamond (m : smode) : plan :=
  match m with
  | ML => PBranch mrg (PRun [] (PExt2 (RSZID ML) (RSZ ML) (PWK ML mrg) (PWG ML mrg)))
  | MS => if Z.leb 23 (n_hr c) then PExt2 (RSZID MS) (RSZ MS) (PContraH 0) (PWG MS mrg)
          else PBranch mrg (PRun [] (PExt2 (RSZID MS) (RSZ MS) (if Z.leb 12 (n_hr c) then PContraH 0 else PWK MS mrg) (PWG MS mrg)))
  end.
Definition alts (m : smode) : list (acs * plan) :=
  match m with
  | ML => [(JS1 c rm fw ML ML B, after1 ML)]
  | MS => if Z.leb 23 (n_hr c) then [(JS1 c rm fw MS ML B, after1 ML)] else [(JS1 c rm fw MS MS B, after1 MS); (JS1 c rm fw MS ML B, after1 ML)]
  end.
Definition okArm (m : smode) : plan := PRun [] (PRun [] (PViaM 1 (alts m) 100 (diamond m))).
Definition PLAN (m : smode) : plan := PCase2 REM (n_K c - 1) (EXITERR m) (okArm m).
End Plan.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Templates.
Variable c : ncfg.
Variable B : Z.
Variable XNi : nat -> list expr -> acs -> option acs.
Definition DPi (cs : acs) (steps : list dstep) : nat * acs := dpath BSEGS (IT c B) ABOTH XNi XB BFUEL NXF cs steps 0.
(* [comment removed for export] *)
Definition p_join1 : list dstep := [DHi REM (n_K c - 1); DRun []; DRun []; DBrF; DRun [JOIN1 c B]].
Definition p_rsz (m : smode) (grown : bool) : list dstep :=
  [DHi REM (n_K c - 1); DRun []; DRun []] ++ (if (Z.leb 23 (n_hr c) && (match m with MS => true | ML => false end))%bool then [] else [DBrT; DRun []])
  ++ [(if grown then DX2b (RSZID m) (RSZ m) else DX2a (RSZID m) (RSZ m)); DRun [JOIN1 c B]].
Definition reps : list (nat * acs) :=
  (if Z.leb 23 (n_hr c) then [] else [DPi (tin MS B) p_join1]) ++ [DPi (tin ML B) p_join1; DPi (tin ML B) (p_rsz ML false); DPi (tin ML B) (p_rsz ML true); DPi (tin MS B) (p_rsz MS true)].
        (* [comment removed for export] *)
Definition RM : list expr := jregs (map (fun x => s_regs (a_ss (snd x))) reps) 0 32 [] NXF 105.
Definition FW : list kentry := jframe FR (map snd reps) NXF.
End Templates.

