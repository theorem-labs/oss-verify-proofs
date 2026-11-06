(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Instr OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GaDedup.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS. Import APC.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ID_DEDUP : nat := 48.
Fixpoint lmem (K : kentry) (l : list kentry) : bool :=
  match l with [] => false | K' :: r => if kentry_eqb K K' then true else lmem K r end.
(* [comment removed for export] *)
Fixpoint dedup_acc (seen l : list kentry) : list kentry :=
  match l with
  | [] => []
  | K :: r => if lmem K seen then dedup_acc seen r else K :: dedup_acc (K :: seen) r
  end.
(* [comment removed for export] *)
Fixpoint lmemH (h : PrimInt63.int) (K : kentry) (l : list (PrimInt63.int * kentry)) : bool :=
  match l with [] => false | (h', K') :: r => if (if PrimInt63.eqb h h' then kentry_eqb K K' else false) then true else lmemH h K r end.
Fixpoint dedup_accH (seen : list (PrimInt63.int * kentry)) (l : list kentry) : list kentry :=
  match l with
  | [] => []
  | K :: r => let h := AzHashK.AHK.khash K in if lmemH h K seen then dedup_accH seen r else K :: dedup_accH ((h, K) :: seen) r
  end.
Lemma lmemH_eq : forall K seen, lmemH (AzHashK.AHK.khash K) K (khl seen) = lmem K seen.
Proof.
  intros K seen. unfold khl. induction seen as [|K' r IH]; [reflexivity|]. cbn [map lmemH lmem].
  rewrite (AzHashK.AHK.hash_guard kentry AzHashK.AHK.khash kentry_eqb kentry_eqbT K K'), IH. reflexivity.
Qed.
Lemma dedup_accH_eq : forall l seen, dedup_accH (khl seen) l = dedup_acc seen l.
Proof.
  induction l as [|K r IH]; intros seen; [reflexivity|]. cbn [dedup_accH dedup_acc]. cbv zeta. rewrite lmemH_eq.
  destruct (lmem K seen); [apply IH|]. change ((AzHashK.AHK.khash K, K) :: khl seen) with (khl (K :: seen)). rewrite IH. reflexivity.
Qed.
Lemma dedup_accH_nil : forall l, dedup_accH [] l = dedup_acc [] l.
Proof. intros l. exact (dedup_accH_eq l []). Qed.
Lemma dedup_acc_In : forall l seen K, In K (dedup_acc seen l) -> In K l.
Proof.
  induction l as [|K0 r IH]; intros seen K H; [exact H|]. cbn [dedup_acc] in H.
  destruct (lmem K0 seen).
  - right. exact (IH _ _ H).
  - destruct H as [<-|H]; [left; reflexivity | right; exact (IH _ _ H)].
Qed.
Definition node_dedup (args : list expr) (cs : acs) : option acs := Some (set_kn cs (dedup_accH [] (kn cs))).   (* [comment removed for export] *)

Definition XNd (XN0 : nat -> list expr -> acs -> option acs) (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id ID_DEDUP then node_dedup args cs else XN0 id args cs.

Section Sound.
Context {RC : run_ceil}.
Variable NXF : nat.
Variable RZ : GPS.rz_t.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable VSHc : list (Z * Z).
Variable AINVc : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable FTOPc : Z.
Variable UINV : env -> Prop.
Variable XN0 : nat -> list expr -> acs -> option acs.

Theorem XNd_sound :
  GPS.ext_stmt ASEGS NXF XN0 PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ ->
  GPS.ext_stmt ASEGS NXF (XNd XN0) PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ.
Proof.
  intros H0 id args. unfold XNd. destruct (Nat.eqb id ID_DEDUP); [|exact (H0 id args)].
  intros cs cs' E fx R M model T HT HC _ Hn Hk. unfold node_dedup in Hn. rewrite dedup_accH_nil in Hn. injection Hn as <-.
  apply (Hk E fx R M model).
  - split; apply APS.env_agree_refl.
  - apply cs_ok_set_kn; [exact HC|]. pose proof (co_know HC) as HK. unfold know_ok in *.
    apply Forall_forall. intros K Hin. exact (proj1 (Forall_forall _ _) HK K (dedup_acc_In _ _ _ Hin)).
  - reflexivity.
Qed.
End Sound.
End GaDedup.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPrune OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPw OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ENTRY : Z := 0xa3c60.
Definition NINSTR : nat := 6522.
(* [comment removed for export] *)
Definition IT_def : itab := mk_itab_ranges ASEGS [(ENTRY, NINSTR)].
Definition IT : itab := Eval vm_compute in IT_def.
Lemma IT_eq : IT = IT_def. Proof. vm_cast_no_check (@eq_refl itab IT_def). Qed.
Lemma IT_ok : itab_sound ASEGS IT. Proof. rewrite IT_eq. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition regsW : list expr := sr_upd regs0 4 (ELit (g_tp GASAN)).
Definition G : expr := EVar 9.     Definition PIT : expr := EVar 10.  Definition PEND : expr := EVar 11.
Definition OBJ : expr := EVar 12.  Definition PIX : expr := EVar 13.  Definition DEPTH : expr := EVar 14.
Definition ITO : expr := EVar 31.  Definition BSZ : expr := EVar 33.  Definition IX : expr := EVar 34.  Definition INLO : expr := EVar 35.
Definition e_mtr : expr := EVar 39.  Definition e_fb : expr := EVar 40.
Definition NXF : nat := 41.

Definition EEND : expr := eadd INLO BSZ.
Definition INSZ : Z := 2 ^ 26.
Definition BIG : Z := 24 * INSZ.
Definition IXMAX : Z := 32 * INSZ.
Definition CAPK : Z := 1040.
Definition CAPMAX : Z := 8 * INSZ.
Definition AHI : Z := (4 * BIG + 8 * INSZ + CAPK) / 8.
Definition FR : Z := 320.
Definition SK : Z := 8192 + FR.                 (* [comment removed for export] *)
Definition XDMAX : Z := SK + FR * 256.
Definition XD : expr := eaddz (escale (- FR) DEPTH) XDMAX.
Definition SLO : expr := eadd (eaddz e_sp (- XDMAX)) (escale FR DEPTH).   (* [comment removed for export] *)
Definition FLOOR : list amap := [AM SLO (ELit 0) KRW].
Definition flo (x : expr) (k : Z) (n : expr) : kentry := KDisj (SA x k) n (SA SLO 0) (ELit (XDMAX + WSTK)).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition GEV : Z := 2 * EVT + 8.
Definition CG : Z := 4 * GEV.
Definition SZMAX : Z := 8 * AHI.
(* [comment removed for export] *)
Definition CPX : expr := EVar 3.
Definition NBE : Z := 13 * 2 ^ 28 + 80.                  (* [comment removed for export] *)
Definition CMAXB : Z := MTRMAX NBE - pwtop NBE - pwtop (8 * AHI) - 2 ^ 24.   (* [comment removed for export] *)
Definition MTRTOP : Z := CMAXB + pwtop (8 * AHI).

Definition szin (m : smode) : expr := match m with MS => EVar 36 | ML => EVar 37 end.


(* [comment removed for export] *)
Definition iixE (ito ix err : expr) : kentry := KRange (esub (eadd (escale 24 ito) (escale IXMAX err)) ix) 0 (24 * INSZ + 256 * IXMAX).
Definition RELHI : Z := 24 * INSZ + 256 * IXMAX.
Definition rel (ito ix : expr) (lo : Z) : kentry := KRange (esub (escale 24 (esub ito ITO)) (esub ix IX)) lo RELHI.
Definition relE (ito ix err : expr) (lo : Z) : kentry := KRange (esub (eadd (escale 24 (esub ito ITO)) (escale IXMAX err)) (esub ix IX)) lo RELHI.
Definition capE (ix ito a err : expr) : kentry :=
  KRange (esub (eaddz (eadd (eadd (escale 4 ix) (escale 8 ito)) (escale CAPMAX err)) CAPK) (escale 8 a)) 0 (4 * IXMAX + 8 * INSZ + CAPK + 256 * CAPMAX).
(* [comment removed for export] *)
Definition strL (ix ito err d s a : expr) : list kentry :=
  [ KWord (SA OBJ 0) 8 (eaddz (escale 8 a) 1); KWord (SA OBJ 8) 8 s; KWord (SA OBJ 16) 8 d;
    KRange a 3 AHI; capE ix ito a err;
    KRange s 0 (8 * AHI); KRange (esub (escale 8 a) s) 1 (8 * AHI);
    KRange d PTRLO (PTRHI - 24); KRange (eadd d (escale 8 a)) (PTRLO + 24) PTRHI; KAlign d 16;
    KWr (SA d 0) (escale 8 a); KUnk (SA d 0) (escale 8 a); KShOk (SA d 0) (escale 8 a);
    KDisj (SA d 0) (escale 8 a) (SA G 0) (ELit 4); KDisj (SA d 0) (escale 8 a) (SA G 32) (ELit 4); KDisj (SA d 0) (escale 8 a) (SA PEND 0) (ELit 8);
    KDisj (SA d 0) (escale 8 a) (SA PIT 0) (ELit 8); KDisj (SA d 0) (escale 8 a) (SA PIX 0) (ELit 8);
    KDisj (SA d 0) (escale 8 a) (SA OBJ 0) (ELit 24); KDisj (SA d 0) (escale 8 a) (SA INLO 0) BSZ;
    flo d 0 (escale 8 a); img_apart d 0 (escale 8 a); shmap_apart d 0 (escale 8 a) ].
Definition str (m : smode) (ix ito err : expr) (v : nat) : list kentry :=
  match m with MS => strS OBJ (EVar v) | ML => strL ix ito err (EVar v) (EVar (1 + v)) (EVar (2 + v)) end.
Definition vis (m : smode) (v : nat) : list (expr * expr) := match m with MS => [] | ML => [(EVar v, escale 8 (EVar (2 + v)))] end.

Definition obj (x : expr) (n al : Z) (wr : bool) : list kentry :=
  [ KRange x PTRLO (objhi n); KShOk (SA x 0) (ELit n); KAlign x al; flo x 0 (ELit n); img_apart x 0 (ELit n); shmap_apart x 0 (ELit n) ]
  ++ (if wr then [KWr (SA x 0) (ELit n)] else []).
(* [comment removed for export] *)
Definition gind : list kentry :=
  [ KRange (eaddz G 36) (PTRLO + 36) HI47;       (* [comment removed for export] *)
    KShOk (SA G 32) (ELit 4); KWr (SA G 32) (ELit 4); KUnk (SA G 32) (ELit 4);
    flo G 32 (ELit 4); img_apart G 32 (ELit 4); shmap_apart G 32 (ELit 4);
    KDisj (SA G 32) (ELit 4) (SA OBJ 0) (ELit 24); KDisj (SA G 32) (ELit 4) (SA PIT 0) (ELit 8); KDisj (SA G 32) (ELit 4) (SA PIX 0) (ELit 8);
    KDisj (SA G 32) (ELit 4) (SA PEND 0) (ELit 8); KDisj (SA INLO 0) BSZ (SA G 32) (ELit 4) ].
Definition kn_fixed : list kentry :=
  (KRange G PTRLO (objhi 36) :: tl (obj G 4 4 true)) ++ gind ++          (* [comment removed for export] *)
  obj PEND 8 8 false ++ [KWord (SA PEND 0) 8 EEND] ++ obj PIT 8 8 true ++ obj PIX 8 8 true ++ obj OBJ 24 8 true ++ [KUnk (SA OBJ 0) (ELit 24)]
  ++ [ KRange INLO PTRLO PTRHI; KRange BSZ 1 INSZ; KRange (eadd INLO BSZ) (PTRLO + 1) PTRHI; KUnk (SA INLO 0) BSZ; KShOk (SA INLO 0) BSZ;
       flo INLO 0 BSZ; img_apart INLO 0 BSZ; shmap_apart INLO 0 BSZ;
       KDisj (SA G 0) (ELit 4) (SA OBJ 0) (ELit 24); KDisj (SA PEND 0) (ELit 8) (SA OBJ 0) (ELit 24);
       KDisj (SA PIT 0) (ELit 8) (SA OBJ 0) (ELit 24); KDisj (SA PIX 0) (ELit 8) (SA OBJ 0) (ELit 24);
       KDisj (SA G 0) (ELit 4) (SA PIT 0) (ELit 8); KDisj (SA G 0) (ELit 4) (SA PIX 0) (ELit 8); KDisj (SA G 0) (ELit 4) (SA PEND 0) (ELit 8);
       KDisj (SA PIT 0) (ELit 8) (SA PIX 0) (ELit 8); KDisj (SA PEND 0) (ELit 8) (SA PIT 0) (ELit 8); KDisj (SA PEND 0) (ELit 8) (SA PIX 0) (ELit 8);
       KDisj (SA INLO 0) BSZ (SA G 0) (ELit 4); KDisj (SA INLO 0) BSZ (SA OBJ 0) (ELit 24);
       KDisj (SA INLO 0) BSZ (SA PEND 0) (ELit 8); KDisj (SA INLO 0) BSZ (SA PIT 0) (ELit 8); KDisj (SA INLO 0) BSZ (SA PIX 0) (ELit 8);
       KAlign e_sp 32; KRange e_sp (CEIL + SK) (two47 - 16); KRange SLO CEIL HI47; KWr (SA SLO 0) XD;
       KRange ITO 0 INSZ; KRange IX 0 BIG; KRange DEPTH 0 256;
       KRange e_fb 2 FBMAX; KRange (eadd e_fb DEPTH) 258 (FBMAX + 256);
       KRange e_mtr 0 MTRTOP; KRange CPX 0 CMAXB;
       KIMGA ] ++ NEWH ++ RTC ++ GLZ_LOWSH.
(* [comment removed for export] *)
Definition stk_shok : kentry := KShOk (SA SLO 0) XD.
Definition posg (mlo : Z) (ito ix err : expr) (k : Z) (ixhi : Z) : list kentry :=
  [ KWord (SA G 0) 4 err; KWord (SA PIT 0) 8 (eadd INLO ito); KRange ito 0 (INSZ - k); KRange (esub BSZ ito) k INSZ;
    KWord (SA PIX 0) 8 ix; KRange ix 0 ixhi; iixE ITO IX (ELit 0); iixE ito ix err;
    KRange (esub ito ITO) mlo INSZ ].
Definition pos0 := posg 0.
Definition pos := posg 1.
Definition kn_in (m : smode) : list kentry :=
  [ stk_shok ] ++ pw_facts CPX (szin m) e_mtr ++ pos0 ITO IX (ELit 0) 0 BIG ++ str m IX ITO (ELit 0) 36 ++ kn_fixed.
Definition WS : list (expr * expr) := [(G, ELit 4); (eaddz G 32, ELit 4); (PEND, ELit 8); (PIT, ELit 8); (PIX, ELit 8); (OBJ, ELit 24); (INLO, BSZ)].
Definition mkcs (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vs : list (expr * expr)) (mtr : expr) (fk : list (expr * expr)) (fb : expr) : acs :=
  ACS (mk_ss p regs k nx) FLOOR 0 XDMAX 0 vs WS 0 e_sp FdStd false mtr fk fb.
Definition tin (m : smode) : acs := mkcs ENTRY regsW (kn_in m) NXF (vis m 36) e_mtr [] e_fb.

(* [comment removed for export] *)
Definition RETPC : Z := 0xa7f88.
Definition xERR := EVar 41. Definition xITO := EVar 42. Definition xIX := EVar 43.
Definition XSTR : nat := 44. Definition xMTR := EVar 47. Definition XLO : nat := 48.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_out : list expr := sr_havoc regsW clobbered XLO.
Definition szx (m : smode) : expr := match m with MS => EVar 44 | ML => EVar 45 end.

Definition kn_out (m0 m : smode) : list kentry :=
  [ KRange xERR 0 255; relE xITO xIX xERR 1; KRange (eadd (esub xITO ITO) xERR) 1 (INSZ + 255)      (* [comment removed for export] *)
    ] ++ pw_facts CPX (szx m) xMTR ++ [     (* [comment removed for export] *)
    KRange xMTR 0 MTRTOP ]
  ++ pos0 xITO xIX xERR 0 IXMAX ++ str m xIX xITO xERR XSTR ++ no_cbound CPX kn_fixed.
Definition tout (m0 m : smode) : acs := mkcs RETPC regs_out (kn_out m0 m) (XLO + 15)%nat (vis m XSTR) xMTR [] e_fb.
Definition BCAP : Z := 10 * 2 ^ 30.  Definition CCAP : Z := 4.
Definition ce2 (m : smode) : gcallee2 := GCE2 NXF (tin m) [tout m MS] [tout m ML] BCAP CCAP.
(* [comment removed for export] *)
Definition ceL1 : gcallee := GCE NXF (tin ML) [tout ML ML; tout ML ML] BCAP CCAP.
Definition ce (m : smode) : gcallee := match m with MS => c2_merged (ce2 MS) | ML => ceL1 end.

(* [comment removed for export] *)
Definition F : expr := EVar 41.
Definition shF : expr := EAlu ALU_SRL F (ELit 3).
