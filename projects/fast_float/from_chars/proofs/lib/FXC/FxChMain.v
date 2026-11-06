(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Znumtheory List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs Fs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEntM FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChStart.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChStart FxChain FxChEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChWv FxChSubst.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEntM OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.FxChBrk OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart.FxChLoop OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChWv OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSubst.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxWvG FxWvC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChUnmap FxChBlob.   (* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDir.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC.FxChDirDefs OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDir.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Instance chm_fx : FPState := fx0.

(* [comment removed for export] *)
Inductive fstate : Type :=
| FSClosed
| FSOpen (off FL : lin)
| FSDone
| FSDir    (* [comment removed for export] *)
| FSOpenLB (off B : lin).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition FLT : Z := 4611686018427387903.
Definition flen_of (n : nat) : Z := Z.min (Z.of_nat n) FLT.

Definition fs_wf (n : positive) (FS : fstate) : bool :=
  match FS with FSOpen off FL => (lwf n off && lwf n FL)%bool | FSOpenLB off B => (lwf n off && lwf n B)%bool | _ => true end.

(* [comment removed for export] *)
Fixpoint all_some {A B} (f : A -> option (list B)) (l : list A) : option (list B) :=
  match l with
  | [] => Some []
  | x :: r => match f x, all_some f r with Some f1, Some f2 => Some (f1 ++ f2) | _, _ => None end
  end.

Lemma all_some_spec : forall {A B} (f : A -> option (list B)) l out, all_some f l = Some out ->
  forall x, In x l -> exists o, f x = Some o /\ (forall y, In y o -> In y out).
Proof.
  intros A B f l. induction l as [|x r IH]; intros out H y Hy; cbn [all_some In] in *; [destruct Hy|].
  destruct (f x) as [o1|] eqn:H1; [|discriminate]. destruct (all_some f r) as [o2|] eqn:H2; [|discriminate].
  injection H as <-. destruct Hy as [<-|Hy].
  - exists o1. split; [exact H1|]. intros z Hz. apply in_or_app. left. exact Hz.
  - destruct (IH o2 eq_refl y Hy) as (o & Ho & Hsub). exists o. split; [exact Ho|]. intros z Hz. apply in_or_app. right. exact (Hsub z Hz).
Qed.

Definition is_ecall (t : tree xi) (pc : Z) : bool := match tlookup t pc with XEcall => true | _ => false end.
Lemma is_ecall_ok : forall t pc, is_ecall t pc = true -> tlookup t pc = XEcall.
Proof. intros t pc H. unfold is_ecall in H. destruct (tlookup t pc); try discriminate; reflexivity. Qed.

(* [comment removed for export] *)
Definition AT_FDCWD_Z : Z := bv_unsigned AT_FDCWD.
Definition open_args_ok (S : sst) (pv : lin) : bool :=
  match a7c S, arg S 0, arg S 2 with
  | Some c7, Some c0, Some fl => (Z.eqb c7 56 && bv_eqb (fd32 (Z_to_bv 64 c0)) AT_FDCWD32 &&
                                  Z.eqb (Z.ldiff (bv_unsigned (Z_to_bv 64 fl)) open_ignored_flags) 0 &&
                                  lin_eqb (rget (s_regs S) (rkey a1r)) pv)%bool
  | _, _, _ => false
  end.
Definition close_args_ok (S : sst) : bool :=
  match a7c S, arg S 0 with Some c7, Some c0 => (Z.eqb c7 57 && Z.eqb c0 3)%bool | _, _ => false end.
Definition ioctl_args_ok (S : sst) (fd cmd : Z) : bool :=
  match a7c S, arg S 0, arg S 1 with
  | Some c7, Some c0, Some c1 => (Z.eqb c7 29 && Z.eqb c0 fd && (Z.eqb fd 1 || Z.eqb fd 2) && Z.eqb c1 cmd && tty_only_request (cmd32 (Z_to_bv 64 cmd)))%bool
  | _, _, _ => false
  end.
Definition errno_lin (e : Z) : lin := lconst (bv_unsigned (errno_ret e)).
(* [comment removed for export] *)
Definition ERRLO : Z := 18446744073709547521.
Definition ERRHI : Z := 18446744073709551615.
Lemma errno_in_range : forall e, In e openat_errnos -> ERRLO <= bv_unsigned (errno_ret e) <= ERRHI.
Proof.
  intros e He. cbn [openat_errnos In] in He.
  destruct He as [<-|[<-|[<-|[<-|[]]]]]; split; apply Z.leb_le; vm_compute; reflexivity.
Qed.
Fixpoint frz_eqb (a b : list (lin * lin)) : bool :=
  match a, b with
  | [], [] => true
  | (x, y) :: a', (x', y') :: b' => (lin_eqb x x' && lin_eqb y y' && frz_eqb a' b')%bool
  | _, _ => false
  end.
Lemma frz_eqb_eq : forall a b, frz_eqb a b = true -> a = b.
Proof.
  induction a as [|[x y] a IH]; intros [|[x' y'] b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply lin_eqb_eq in H1, H2. subst. f_equal. exact (IH b H3).
Qed.


(* [comment removed for export] *)
Inductive src : Type :=
| SLit (bs : list Z)
| SArgs (pre : list Z) (j : nat) (lj : lin) (suf : list Z).   (* [comment removed for export] *)
Record pend : Type := PD { pd_ch : Z ; pd_src : src ; pd_off : lin }.
Inductive shp : Type :=
| ShEmit (po : list pend) (kc : Z)      (* [comment removed for export] *)
| ShAlt2 (a b : shp)                   (* [comment removed for export] *)
| ShIf (l : lin) (lo hi : Z) (a b : shp)   (* [comment removed for export] *)
| ShBit (l : lin) (j : Z) (a b : shp).     (* [comment removed for export] *)

Definition src_len (s : src) : Z := match s with SLit bs => Z.of_nat (length bs) | SArgs pre _ _ suf => Z.of_nat (length pre + length suf) end.
Definition pend_wf (n : positive) (p : pend) : bool :=
  match pd_src p with SLit _ => lwf n (pd_off p) | SArgs _ _ lj _ => (lwf n (pd_off p) && lwf n lj)%bool end.
Fixpoint shp_wf (n : positive) (sh : shp) : bool :=
  match sh with
  | ShEmit po _ => forallb (pend_wf n) po
  | ShAlt2 a b => (shp_wf n a && shp_wf n b)%bool
  | ShIf l _ _ a b => (lwf n l && shp_wf n a && shp_wf n b)%bool
  | ShBit l _ a b => (lwf n l && shp_wf n a && shp_wf n b)%bool
  end.
Fixpoint zlist_eqb (a b : list Z) : bool :=
  match a, b with [], [] => true | x :: a', y :: b' => (Z.eqb x y && zlist_eqb a' b')%bool | _, _ => false end.
Lemma zlist_eqb_eq : forall a b, zlist_eqb a b = true -> a = b.
Proof. induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. subst y. f_equal. exact (IH b H2). Qed.
Definition src_ent (a b : src) (σ : tree lin) : bool :=
  match a, b with
  | SLit x, SLit y => zlist_eqb x y
  | SArgs p j l s, SArgs p' j' l' s' => (zlist_eqb p p' && Nat.eqb j j' && lin_eqb l (lsubst σ l') && zlist_eqb s s')%bool
  | _, _ => false
  end.
Definition pend_ent (p q : pend) (σ : tree lin) : bool :=
  (Z.eqb (pd_ch p) (pd_ch q) && src_ent (pd_src p) (pd_src q) σ && lin_eqb (pd_off p) (lsubst σ (pd_off q)))%bool.
Fixpoint pends_ent (a b : list pend) (σ : tree lin) : bool :=
  match a, b with [], [] => true | p :: a', q :: b' => (pend_ent p q σ && pends_ent a' b' σ)%bool | _, _ => false end.
Fixpoint shp_ent (a b : shp) (σ : tree lin) : bool :=
  match a, b with
  | ShEmit po kc, ShEmit po' kc' => (Z.eqb kc kc' && pends_ent po po' σ)%bool
  | ShAlt2 a1 a2, ShAlt2 b1 b2 => (shp_ent a1 b1 σ && shp_ent a2 b2 σ)%bool
  | ShIf l lo hi a1 a2, ShIf l' lo' hi' b1 b2 =>
      (lin_eqb l (lsubst σ l') && Z.eqb lo lo' && Z.eqb hi hi' && shp_ent a1 b1 σ && shp_ent a2 b2 σ)%bool
  | ShBit l j a1 a2, ShBit l' j' b1 b2 => (lin_eqb l (lsubst σ l') && Z.eqb j j' && shp_ent a1 b1 σ && shp_ent a2 b2 σ)%bool
  | _, _ => false
  end.
Definition fs_ent (FS FP : fstate) (σ : tree lin) : bool :=
  match FS, FP with
  | FSClosed, FSClosed | FSDone, FSDone | FSDir, FSDir => true
  | FSOpen o f, FSOpen o' f' => (lin_eqb o (lsubst σ o') && lin_eqb f (lsubst σ f'))%bool
  | FSOpenLB o b, FSOpenLB o' b' => (lin_eqb o (lsubst σ o') && lin_eqb b (lsubst σ b'))%bool
  | _, _ => false
  end.

Inductive mchain {N : Type} : Type :=
| MEnd
| MChain (ch : chain) (k : mchain)
| MSegK (depth : nat) (p : plan) (ks : mks)
| MOpen (kerr kok : mchain)
| MRead (i : nat) (o : Z) (ka kb : mchain)
| MClose (k : mchain)
| MIoctl (fd cmd : Z) (k : mchain)
| MWritev (B0 : Z) (k : mchain)
| MExit
| MWeaken (P : sst) (n0 : positive) (FP : fstate) (shP : shp) (k : mchain)
| MLoop (P : sst) (n0 : positive) (FP : fstate) (shP : shp) (meas : lin) (body : mchain) (ks : mks)
| MCall (nk : N) (k : mchain)          (* [comment removed for export] *)
| MVoid                                (* [comment removed for export] *)
| MJoin (body : mchain) (jpc : Z) (k : mchain)   (* [comment removed for export] *)
| MLoopW (zk : Z) (body : mchain) (ks : mks)      (* [comment removed for export] *)
| MPop (k : mchain)                               (* [comment removed for export] *)
| MAlt (k1 k2 : mchain)                           (* [comment removed for export] *)
| MOpenDir (kerr kok : mchain)       (* [comment removed for export] *)
| MReadDir (k : mchain)              (* [comment removed for export] *)
| MWritev2 (B0 : lin) (k : mchain)   (* [comment removed for export] *)
| MWritevC (F0 F1 : wsrc) (k : mchain)   (* [comment removed for export] *)
| MWritev0 (k : mchain)                  (* [comment removed for export] *)
| MSel (ka kb : mchain)               (* [comment removed for export] *)
| MReadH (i : nat) (o : Z) (k : nat) (ka kb : mchain)    (* [comment removed for export] *)
| MSep (op : templop) (k : mchain)             (* [comment removed for export] *)
| MSplit (l : lin) (c : Z) (ka kb : mchain)     (* [comment removed for export] *)
| MSplitB (l : lin) (k r0 : Z) (ka kb : mchain)  (* [comment removed for export] *)
| MSelB (ka kb : mchain)                        (* [comment removed for export] *)
| MSplitG (j : nat) (c : Z) (ka kb : mchain)    (* [comment removed for export] *)
| MConcR (k : mchain)                          (* [comment removed for export] *)
| MReadB (b o : Z) (ka kb : mchain)             (* [comment removed for export] *)
| MReadHB (b o : Z) (k : nat) (ka kb : mchain)  (* [comment removed for export] *)
| MSplitR (r : Z) (c : Z) (ka kb : mchain)     (* [comment removed for export] *)
| MConcF (k : mchain)                          (* [comment removed for export] *)
| MJoinS (body : mchain) (jpc : Z) (shj : shp) (k : mchain)   (* [comment removed for export] *)
| MWritevL (Pn : nat) (F0 F1 : wsrc) (k : mchain)   (* [comment removed for export] *)
| MSplitP (n : nat) (k : mchain)                    (* [comment removed for export] *)
| MOpenLB (kerr kok : mchain)   (* [comment removed for export] *)
| MReadLB (b o : Z) (k : mchain)   (* [comment removed for export] *)
| MGc (nk : positive) (xs : list positive) (k : mchain)   (* [comment removed for export] *)
| MLoopW0 (zk : Z) (body : mchain) (ks : mks)   (* [comment removed for export] *)
| MJoinL (body : mchain) (jpc : Z) (k : mchain)   (* [comment removed for export] *)
| MLoopG (gen : sst -> sst -> fstate -> fstate -> shp -> shp -> option (sst * positive * fstate * shp * lin)) (body : mchain) (ks : mks)
    (* [comment removed for export] *)
| MUse (j : nat) (nb : positive) (k : mchain)
    (* [comment removed for export] *)
| MCont (j : nat) (nb : positive)
    (* [comment removed for export] *)
| MJoinG (gen : list (sst * smodel) -> list (list lin) -> option (sst * smodel * list lin)) (body : mchain) (jpc : Z) (k : mchain)
    (* [comment removed for export] *)
| MBlobNil (i : nat) (k : mchain)     (* [comment removed for export] *)
| MBlobAdd (i : nat) (k : mchain)     (* [comment removed for export] *)
| MAllowW (j : nat) (z : Z) (k : mchain)   (* [comment removed for export] *)
| MRgFront (i : nat) (k : mchain)          (* [comment removed for export] *)
| MAllowFront (i : nat) (k : mchain)       (* [comment removed for export] *)
| MRegEq (t : lin) (k : mchain)            (* [comment removed for export] *)
with mks {N : Type} : Type :=
| KNil
| KCons (a sys : Z) (k : mchain) (r : mks).
Scheme mchain_mut := Induction for mchain Sort Prop with mks_mut := Induction for mks Sort Prop.
(* [comment removed for export] *)
Definition is_mvoid {N : Type} (k : @mchain N) : bool := match k with MVoid => true | _ => false end.


(* [comment removed for export] *)
Definition rk_is_rwz (k : rkind) : bool := match k with RW | RZ => true | _ => false end.
Definition read_args_ok (S : sst) (i : nat) (o : Z) : option Z :=
  match a7c S, arg S 0, nth_error (s_rgs S) i with
  | Some c7, Some c0, Some R =>
      let '(clo, chi) := irange (s_facts S) (argl S 2) in
      match is_const (rg_base R), is_const (rg_size R) with
      | Some b, Some sz =>
          if (Z.eqb c7 63 && Z.eqb c0 3 && Z.ltb 0 clo && Z.leb chi 65536 && rk_is_rwz (rg_kind R) && Z.leb 0 o &&
              Z.leb (o + chi) sz && Z.leb 0x10000 b && Z.leb (b + sz) 0x61a000 && lwf (s_next S) (argl S 2) &&
              lin_eqb (argl S 1) (lconst (b + o)))%bool then Some chi else None
      | _, _ => None
      end
  | _, _, _ => None
  end.

(* [comment removed for export] *)
Fixpoint bytes_ok (img : tree Z) (fs : list fact) (rgs : list region) (B0 : Z) (bs : list Z) (j : Z) : bool :=
  match bs with
  | [] => true
  | x :: r => match load_at img fs rgs (lconst (B0 + j)) SZ1 false with
              | Some (Some l) => (lin_eqb l (lconst x) && bytes_ok img fs rgs B0 r (j + 1))%bool
              | _ => false
              end
  end.
Definition writev_ok (img : tree Z) (S : sst) (B0 : Z) (p : pend) : option lin :=
  let fs := s_facts S in let rgs := s_rgs S in
  match p with
  | PD ch (SLit bs) off =>
      match a7c S, arg S 0, arg S 2, load_at img fs rgs (argl S 1) SZ8 false, load_at img fs rgs (laddc (argl S 1) 8) SZ8 false with
      | Some c7, Some c0, Some c2, Some (Some b), Some (Some len) =>
          let n := Z.of_nat (length bs) in
          if (Z.eqb c7 66 && Z.eqb c0 ch && (Z.eqb ch 1 || Z.eqb ch 2) && Z.eqb c2 1 &&
              lin_eqb b (laddc off B0) && lin_eqb len (laddc (lneg off) n) && bytes_ok img fs rgs B0 bs 0 &&
              Z.leb 0 (fst (irange fs off)) && Z.ltb (snd (irange fs off)) n && Z.leb 1 n && Z.leb n 1073741824 &&
              Z.leb 0 B0 && Z.leb (B0 + n) TASK_SIZE && Z.leb (snd (irange fs (argl S 1)) + 16) TASK_SIZE &&
              lwf (s_next S) off && lwf (s_next S) (argl S 1))%bool
          then Some len else None
      | _, _, _, _, _ => None
      end
  | PD _ (SArgs _ _ _ _) _ => None
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition writev2_ok (img : tree Z) (S : sst) (B0 : lin) (p : pend) : option lin :=
  let fs := s_facts S in let rgs := s_rgs S in
  match p with
  | PD ch (SLit bs) off =>
      match a7c S, arg S 0, arg S 2, load_at img fs rgs (argl S 1) SZ8 false, load_at img fs rgs (laddc (argl S 1) 8) SZ8 false,
            load_at img fs rgs (laddc (argl S 1) 16) SZ8 false, load_at img fs rgs (laddc (argl S 1) 24) SZ8 false with
      | Some c7, Some c0, Some c2, Some (Some b), Some (Some len), Some (Some z1), Some (Some z2) =>
          let n := Z.of_nat (length bs) in
          if (Z.eqb c7 66 && Z.eqb c0 ch && (Z.eqb ch 1 || Z.eqb ch 2) && Z.eqb c2 2 &&
              lin_eqb b (ladd off B0) && lin_eqb len (laddc (lneg off) n) && lin_eqb z1 (lconst 0) && lin_eqb z2 (lconst 0) &&
              lbytes_ok img fs rgs B0 bs 0 &&
              Z.leb 0 (fst (irange fs off)) && Z.ltb (snd (irange fs off)) n && Z.leb 1 n && Z.leb n 1073741824 &&
              Z.leb (snd (irange fs B0) + n) TASK_SIZE && Z.leb (snd (irange fs (argl S 1)) + 32) TASK_SIZE &&
              lwf (s_next S) off && lwf (s_next S) (argl S 1) && lwf (s_next S) B0)%bool
          then Some len else None
      | _, _, _, _, _, _, _ => None
      end
  | PD _ (SArgs _ _ _ _) _ => None
  end.
Definition pend_done (fs : list fact) (p : pend) : bool :=
  match pd_src p with
  | SLit bs => Z.leb (Z.of_nat (length bs)) (fst (irange fs (pd_off p)))
  | SArgs pre _ lj suf =>     (* [comment removed for export] *)
      let '(dlo, dhi) := irange fs (lsub (pd_off p) lj) in
      (Z.leb (Z.of_nat (length pre + length suf)) dlo && Z.leb dhi 9223372036854775808 && Z.leb (snd (irange fs lj)) 4611686018427387904)%bool
  end.
Definition exit_args_ok (S : sst) (kc : Z) : bool :=
  match a7c S, arg S 0 with
  | Some c7, Some c0 => ((Z.eqb c7 94 || Z.eqb c7 93) && Z.eqb c0 kc && Z.leb 0 kc && Z.leb kc 255)%bool
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition gk_eqb (a b : gkind) : bool := gkind_eqb a b.
Fixpoint maps_eqb (a b : list (lin * lin * gkind)) : bool :=
  match a, b with
  | [], [] => true
  | (x, n, k) :: a', (y, m, k') :: b' => (lin_eqb x y && lin_eqb n m && gkind_eqb k k' && maps_eqb a' b')%bool
  | _, _ => false
  end.
Fixpoint allow_eqb (a b : list (lin * Z)) : bool :=
  match a, b with [], [] => true | (x, n) :: a', (y, m) :: b' => (lin_eqb x y && Z.eqb n m && allow_eqb a' b')%bool | _, _ => false end.
Fixpoint zr_eqb (a b : list (Z * Z)) : bool :=
  match a, b with [], [] => true | (x, n) :: a', (y, m) :: b' => (Z.eqb x y && Z.eqb n m && zr_eqb a' b')%bool | _, _ => false end.
Definition otid_eqb (a b : option lin) : bool := match a, b with None, None => true | Some x, Some y => lin_eqb x y | _, _ => false end.
Definition sm_eqb (a b : smodel) : bool :=
  (maps_eqb (sm_maps a) (sm_maps b) && allow_eqb (sm_allow a) (sm_allow b) && zr_eqb (sm_zr a) (sm_zr b) &&
   otid_eqb (sm_tid a) (sm_tid b) && lin_eqb (sm_brk a) (sm_brk b) && lin_eqb (sm_sbrk a) (sm_sbrk b) &&
   lin_eqb (sm_sp a) (sm_sp b) && frz_eqb (sm_frz a) (sm_frz b) && frz_eqb (sm_own a) (sm_own b))%bool.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fs_rem_iv (F : sst) (FS : fstate) : Z * Z :=
  let iv := fun l => let r := irange (s_facts F) l in if (Z.eqb (fst r) 0 && Z.eqb (snd r) M64)%bool then irange_x (s_facts F) l else r in
  match FS with FSOpen o f => iv (lsub f o) | FSOpenLB o b => iv (lsub b o) | _ => (0, M64) end.
(* [comment removed for export] *)
Definition fs_len_iv (F : sst) (FS : fstate) : Z * Z :=
  let iv := fun l => let r := irange (s_facts F) l in if (Z.eqb (fst r) 0 && Z.eqb (snd r) M64)%bool then irange_x (s_facts F) l else r in
  match FS with FSOpen o f => iv f | _ => (0, M64) end.
Definition join_fs_hull {X Y Z0 : Type} (P : sst) (FS0 : fstate) (J : list (sst * X * fstate * Y * Z0)) : sst :=
  match FS0 with
  | FSOpen o f =>
      let r := List.fold_left (fun r '(F, _, FSF, _, _) => let r' := fs_rem_iv F FSF in (Z.min (fst r) (fst r'), Z.max (snd r) (snd r'))) J (M64, 0) in
      let P1 := if (Z.leb (fst r) (snd r) && negb (Z.eqb (fst r) 0 && Z.eqb (snd r) M64))%bool then add_fact P (FRange (lsub f o) (fst r) (snd r)) else P in
      match is_const f with
      | Some _ => P1
      | None =>
          let q := List.fold_left (fun q '(F, _, FSF, _, _) => let q' := fs_len_iv F FSF in (Z.min (fst q) (fst q'), Z.max (snd q) (snd q'))) J (M64, 0) in
          if (Z.leb (fst q) (snd q) && negb (Z.eqb (fst q) 0 && Z.eqb (snd q) M64))%bool then add_fact P1 (FRange f (fst q) (snd q)) else P1
      end
  | FSOpenLB o b =>
      let r := List.fold_left (fun r '(F, _, FSF, _, _) => let r' := fs_rem_iv F FSF in (Z.min (fst r) (fst r'), Z.max (snd r) (snd r'))) J (M64, 0) in
      if (Z.leb (fst r) (snd r) && negb (Z.eqb (fst r) 0 && Z.eqb (snd r) M64))%bool then add_fact P (FRange (lsub b o) (fst r) (snd r)) else P
  | _ => P
  end.
(* [comment removed for export] *)
Definition lmeas_dec (F : sst) (σ : tree lin) (m : lin) : bool :=
  let '(lo, hi) := irange (s_facts F) (lsub m (lsubst σ m)) in (Z.leb 1 lo && Z.leb hi 4611686018427387904)%bool.
(* [comment removed for export] *)
Definition went (n0 : positive) (S : sst) (M : smodel) (FS : fstate) (sh : shp) (P : sst) (FP : fstate) (shP : shp) : bool :=
  let σ := match_st S P in
  (ent_ok n0 S P M && Pos.leb (s_next S) n0 && fs_ent FS FP σ && shp_ent sh shP σ)%bool.
(* [comment removed for export] *)
Definition ent_okN (σ : tree lin) (n0 : positive) (S P : sst) (M : smodel) : bool :=
  (entails S P σ && fixed_below σ n0 && sm_wf n0 M && Pos.leb n0 (s_next P))%bool.
Definition wentN (n0 : positive) (S : sst) (M : smodel) (FS : fstate) (sh : shp) (P : sst) (FP : fstate) (shP : shp) : bool :=
  let σ := match_st S P in
  (ent_okN σ n0 S P M && Pos.leb (s_next S) n0 && fs_ent FS FP σ && shp_ent sh shP σ)%bool.
Definition sm_eqbm (σ : tree lin) (MP MF : smodel) : bool := (sm_eqb (msubst σ MP) MF && marks_ok σ (sm_maps MP))%bool.

(* [comment removed for export] *)
Definition wdelta (D zd v0 v1 : lin) : option lin :=
  if lin_eqb v1 v0 then Some v0 else
  let d := lsub v1 v0 in
  if lin_eqb d D then Some (ladd v0 zd) else if lin_eqb d (lneg D) then Some (lsub v0 zd) else None.
Fixpoint gen_wregs (R0 R1 : tree lin) (n0 : positive) (zk : positive) (zv D zd : lin) (k : nat) (acc : tree lin) : tree lin :=
  match k with
  | O => acc
  | Datatypes.S k' => let key := Pos.of_succ_nat k in
            let v0 := rget R0 key in let v1 := rget R1 key in
            let v' := if Pos.eqb key zk then zv
                      else match wdelta D zd v0 v1 with Some v => v | None => lvar (n0 + key) end in
            gen_wregs R0 R1 n0 zk zv D zd k' (rset acc key v')
  end.
Definition wbyte (D zd : lin) (x y : bval) : option bval :=
  match x, y with
  | BV l0 j0, BV l1 j1 => if Z.eqb j0 j1 then match wdelta D zd l0 l1 with Some l => Some (BV l j0) | None => None end else None
  | _, _ => if bval_eqb x y then Some x else None
  end.
Fixpoint cinterW (D zd : lin) (t u : tree bval) : tree bval :=
  match t with
  | TEmpty => TEmpty
  | TNode l v r =>
      let '(ul, uv, ur) := tsplit u in
      TNode (cinterW D zd l ul) (match v, uv with Some x, Some y => wbyte D zd x y | _, _ => None end) (cinterW D zd r ur)
  end.
Fixpoint gen_wrgs (D zd : lin) (r0 r1 : list region) : list region :=
  match r0, r1 with
  | R0 :: r0', R1 :: r1' =>
      let c := cinterW D zd (rg_cont R0) (rg_cont R1) in
      let R' := RG (rg_base R0) (rg_size R0) (rg_kind R0) c in
      (* [comment removed for export] *)
      RG (rg_base R0) (rg_size R0) (if (rkind_eqb (rg_kind R0) (rg_kind R1) && rz_extra_ok R0 R')%bool then rg_kind R0 else RW) c
        :: gen_wrgs D zd r0' r1'
  | _, _ => r0
  end.
Fixpoint gen_wpends (D zd : lin) (a b : list pend) : option (list pend) :=
  match a, b with
  | [], [] => Some []
  | PD c s o0 :: a', PD c' s' o1 :: b' => match wdelta D zd o0 o1, gen_wpends D zd a' b' with Some o, Some r => Some (PD c s o :: r) | _, _ => None end
  | _, _ => None
  end.
Fixpoint gen_wshp (D zd : lin) (a b : shp) : option shp :=
  match a, b with
  | ShEmit po kc, ShEmit po' kc' => if Z.eqb kc kc' then match gen_wpends D zd po po' with Some p => Some (ShEmit p kc) | None => None end else None
  | ShAlt2 x y, ShAlt2 x' y' => match gen_wshp D zd x x', gen_wshp D zd y y' with Some p, Some q => Some (ShAlt2 p q) | _, _ => None end
  | ShIf l lo hi x y, ShIf l' lo' hi' x' y' =>
      if (lin_eqb l l' && Z.eqb lo lo' && Z.eqb hi hi')%bool then
        match gen_wshp D zd x x', gen_wshp D zd y y' with Some p, Some q => Some (ShIf l lo hi p q) | _, _ => None end
      else None
  | ShBit l j x y, ShBit l' j' x' y' =>
      if (lin_eqb l l' && Z.eqb j j')%bool then
        match gen_wshp D zd x x', gen_wshp D zd y y' with Some p, Some q => Some (ShBit l j p q) | _, _ => None end
      else None
  | _, _ => None
  end.
Definition gen_wfs (D zd : lin) (a b : fstate) : option fstate :=
  match a, b with
  | FSOpen o0 f0, FSOpen o1 f1 => match wdelta D zd o0 o1, wdelta D zd f0 f1 with Some o, Some f => Some (FSOpen o f) | _, _ => None end
  | FSClosed, FSClosed => Some FSClosed
  | FSDone, FSDone => Some FSDone
  | FSDir, FSDir => Some FSDir      (* [comment removed for export] *)
  | FSOpenLB o0 b0, FSOpenLB o1 b1 => if lin_eqb b1 b0 then match wdelta D zd o0 o1 with Some o => Some (FSOpenLB o b0) | None => None end else None
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition irange2 (fs : list fact) (l : lin) : Z * Z :=
  (* [comment removed for export] *)
  let fs' := List.filter (fun f => match f with FCond _ _ _ _ => false | _ => true end) fs ++
             List.filter (fun f => match f with FCond _ _ _ _ => true | _ => false end) fs in
  let r := irange fs' l in irange (FRange l (fst r) (snd r) :: fs') l.
Definition wgen (st : bool) (S F1 : sst) (FS FS1 : fstate) (sh sh1 : shp) (zk : Z) : option (sst * positive * fstate * shp * lin) :=
  let zp := Z.to_pos (zk + 1) in    (* [comment removed for export] *)
  let n0 := Pos.max (s_next S) (s_next F1) in
  let z0 := rget (s_regs S) zp in let z1 := rget (s_regs F1) zp in
  let D := lsub z1 z0 in
  (* [comment removed for export] *)
  let W := lvar (n0 + zp) in
  let '(Zv, zd) := match (if st then is_const D else None) with Some c => (ladd z0 (lscale c W), lscale c W) | None => (W, lsub W z0) end in
  let '(lo0, hi0) := irange2 (s_facts S) z0 in let '(lo1, hi1) := irange2 (s_facts F1) z1 in
  (* [comment removed for export] *)
  let lo := match is_const D with Some c => if Z.leb 9223372036854775808 c then Z.min (Z.min lo0 lo1) (18446744073709551616 - c) else Z.min lo0 lo1
                                | None => Z.min lo0 lo1 end in
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  let kal := match is_const D with Some c => Z.min (Z.min (lalign (s_facts S) z0) (ctz64 c)) 16 | None => 0 end in
  let fal := if Z.ltb 0 kal then [FMod Zv kal 0] else [] in
  let fs := FRange Zv lo (Z.max hi0 hi1) :: FRange (lsub z0 Zv) 0 (hi0 - lo) :: fal ++ common_suffix (s_facts S) (s_facts F1) in
  let P := SST (s_pc S) (gen_wregs (s_regs S) (s_regs F1) n0 zp Zv D zd 31 TEmpty) (gen_wrgs D zd (s_rgs S) (s_rgs F1)) fs (n0 + 33)
               (if rsv_eqb (s_resv F1) (s_resv S) then s_resv S else RUnk) in
  match gen_wfs D zd FS FS1, gen_wshp D zd sh sh1 with
  | Some FP, Some shP =>
      (* [comment removed for export] *)
      Some ((match FP with FSOpenLB _ _ => P | _ => join_fs_hull P FP [(S, tt, FS, tt, tt); (F1, tt, FS1, tt, tt)] end), n0, FP, shP, Zv)
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition cfilt (σ : tree lin) (tp tf : tree bval) : tree bval :=
  tfilter (fun k => match tget k tp, tget k tf with Some v, Some v' => bval_eqb v' (bsubst σ v) | _, _ => false end) tp.
Fixpoint wref_rgs (σ : tree lin) (rp rf : list region) : list region :=
  match rp, rf with
  | R :: rp', RF :: rf' =>
      let c := cfilt σ (rg_cont R) (rg_cont RF) in
      RG (rg_base R) (rg_size R) (if rz_extra_ok R (RG (rg_base R) (rg_size R) (rg_kind R) c) then rg_kind R else RW) c :: wref_rgs σ rp' rf'
  | _, _ => rp
  end.
Definition wref (P F : sst) : sst :=
  if Nat.eqb (List.length (s_rgs P)) (List.length (s_rgs F)) then
    SST (s_pc P) (s_regs P) (wref_rgs (match_st F P) (s_rgs P) (s_rgs F)) (s_facts P) (s_next P) (s_resv P)
  else P.

(* [comment removed for export] *)
Definition concr_lin (fs : list fact) (l : lin) : lin := let '(lo, hi) := irange fs l in if Z.eqb lo hi then lconst lo else l.
Definition concr (S : sst) : sst := SST (s_pc S) (tmap (concr_lin (s_facts S)) (s_regs S)) (s_rgs S) (s_facts S) (s_next S) (s_resv S).
(* [comment removed for export] *)
Definition eqv_lin (fs : list fact) (t l : lin) : lin := let '(lo, hi) := irange fs (lsub l t) in if (Z.eqb lo 0 && Z.eqb hi 0)%bool then t else l.
Definition regeqv (S : sst) (t : lin) : sst := SST (s_pc S) (tmap (eqv_lin (s_facts S) t) (s_regs S)) (s_rgs S) (s_facts S) (s_next S) (s_resv S).
(* [comment removed for export] *)
Definition concr_fs (fs : list fact) (FS : fstate) : fstate :=
  match FS with FSOpen off FL => FSOpen (concr_lin fs off) FL | FSOpenLB off B => FSOpenLB (concr_lin fs off) B | _ => FS end.

(* [comment removed for export] *)
Fixpoint rg_index (rs : list region) (b : Z) (i : nat) : nat :=
  match rs with [] => i | R :: r => if lin_eqb (rg_base R) (lconst b) then i else rg_index r b (Datatypes.S i) end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition empty_rng (fs : list fact) (f : fact) : bool :=
  match f with FRange l _ _ => let '(lo, hi) := irange fs l in Z.ltb hi lo | _ => false end.
Definition fact_ts (f : fact) : list (positive * Z) :=
  match f with FCond _ a b _ => l_t a ++ l_t b | FRange l _ _ => l_t l | _ => [] end.
Definition fx_contra (fs : list fact) : bool :=
  match fs with
  | [] => false
  | f0 :: _ =>
      let t0 := fact_ts f0 in
      if existsb_lz (fun f => match f with FRange l _ _ => if shares (l_t l) t0 then empty_rng fs f else false | _ => false end) fs then true
      (* [comment removed for export] *)
      else existsb_lz (fun f => match f with FRange l _ _ => if shares (l_t l) t0 then false else empty_rng fs f | _ => false end) fs
  end.
Lemma existsb_split2 : forall {A} (e q q' : A -> bool) l, (forall x, e x = (q x || q' x)%bool) ->
  (if existsb q l then true else existsb q' l) = existsb e l.
Proof.
  intros A e q q' l H. induction l as [|x l IH]; [reflexivity|]. cbn [existsb]. rewrite H.
  destruct (q x), (q' x); cbn [orb]; try reflexivity; try exact IH.
  destruct (existsb q l); reflexivity.
Qed.
Lemma fx_contra_eq : forall fs, fx_contra fs = existsb (empty_rng fs) fs.
Proof.
  intros fs. unfold fx_contra. destruct fs as [|f0 r]; [reflexivity|]. cbv zeta.
  rewrite !existsb_lz_eq. apply existsb_split2. intros f. destruct f; try reflexivity.
  destruct (shares (l_t l) (fact_ts f0)); [rewrite orb_false_r | ]; reflexivity.
Qed.
(* [comment removed for export] *)
Definition fx_contra1 (fs : list fact) : bool :=
  match fs with
  | [] => false
  | f0 :: _ =>
      let t0 := fact_ts f0 in
      existsb_lz (fun f => match f with FRange l _ _ => if shares (l_t l) t0 then empty_rng fs f else false | _ => false end) fs
  end.
Lemma fx_contra1_contra : forall fs, fx_contra1 fs = true -> fx_contra fs = true.
Proof. intros fs H. unfold fx_contra. unfold fx_contra1 in H. destruct fs as [|f0 r]; [discriminate|]. cbv zeta in H |- *. rewrite H. reflexivity. Qed.
(* [comment removed for export] *)
Definition meas_ok (fs : list fact) (m : lin) : bool := let '(lo, hi) := irange fs m in (Z.leb 0 lo && Z.leb hi 4611686018427387904)%bool.

(* [comment removed for export] *)
Definition dvar (h : positive) (i : nat) : positive := Pos.of_nat (Pos.to_nat h + i).
Definition hdr_bvs (h : positive) (k : nat) : list bval := List.map (fun j => BV (lvar (dvar h j)) 0) (List.seq 0 k).
Definition track_hdr (S : sst) (i : nat) (o : Z) (h : positive) (k : nat) : sst := put_rg S i o (hdr_bvs h k).
Definition hv_okb (hv : option positive) (n : positive) : bool := match hv with Some h => Pos.leb (dvar h 18) n | None => true end.

(* [comment removed for export] *)
Definition writevC_ok (img : tree Z) (S : sst) (M : smodel) (recs : list srec) (F0 F1 : wsrc) (p : pend) : option lin :=
  let fs := s_facts S in let rgs := s_rgs S in
  match p with
  | PD ch (SArgs pre j lj suf) off =>
      let P := Z.of_nat (length pre) in let Sl := Z.of_nat (length suf) in
      match a7c S, arg S 0, arg S 2, load_at img fs rgs (argl S 1) SZ8 false, load_at img fs rgs (laddc (argl S 1) 8) SZ8 false with
      | Some c7, Some c0, Some c2, Some (Some b0), Some (Some l0) =>
          if (Z.eqb c7 66 && Z.eqb c0 ch && (Z.eqb ch 1 || Z.eqb ch 2) && wsrc_ok img S M recs pre suf j lj F0 &&
              len_rec recs lj j && Z.ltb (snd (irange fs lj)) (2 ^ 62) && Z.ltb P 1048576 && Z.ltb Sl 1048576 &&
              iov_src_ok fs recs P Sl lj b0 l0 off F0 &&
              lwf (s_next S) off && lwf (s_next S) (argl S 1) && lwf (s_next S) lj && lwf (s_next S) l0)%bool then
            if Z.eqb c2 1 then
              if (Z.leb 1 (fst (irange fs l0)) && Z.leb (snd (irange fs l0)) 1073741824 &&
                  Z.leb (snd (irange fs (argl S 1)) + 16) TASK_SIZE)%bool then Some l0 else None
            else if Z.eqb c2 2 then
              match load_at img fs rgs (laddc (argl S 1) 16) SZ8 false, load_at img fs rgs (laddc (argl S 1) 24) SZ8 false with
              | Some (Some b1), Some (Some l1) =>
                  if (wsrc_ok img S M recs pre suf j lj F1 && iov_src_ok fs recs P Sl lj b1 l1 (ladd off l0) F1 && lwf (s_next S) l1 &&
                      Z.leb 1 (fst (irange fs (ladd l0 l1))) && Z.leb (snd (irange fs (ladd l0 l1))) 1073741824 &&
                      Z.leb (snd (irange fs (argl S 1)) + 32) TASK_SIZE)%bool then Some (ladd l0 l1) else None
              | _, _ => None
              end
            else None
          else None
      | _, _, _, _, _ => None
      end
  | PD _ (SLit _) _ => None
  end.
(* [comment removed for export] *)
Definition writevL_core (img : tree Z) (S : sst) (M : smodel) (recs : list srec) (F0 F1 : wsrc) (p : pend) : option lin :=
  let fs := s_facts S in let rgs := s_rgs S in
  match p with
  | PD ch (SArgs pre j lj suf) off =>
      let P := Z.of_nat (length pre) in let Sl := Z.of_nat (length suf) in
      match a7c S, arg S 0, arg S 2, load_at img fs rgs (argl S 1) SZ8 false, load_at img fs rgs (laddc (argl S 1) 8) SZ8 false with
      | Some c7, Some c0, Some c2, Some (Some b0), Some (Some l0) =>
          if (Z.eqb c7 66 && Z.eqb c0 ch && (Z.eqb ch 1 || Z.eqb ch 2) && wsrc_ok img S M recs pre suf j lj F0 &&
              Z.ltb (snd (irange fs lj)) (2 ^ 62) && Z.ltb P 1048576 && Z.ltb Sl 1048576 &&
              iov_src_ok fs recs P Sl lj b0 l0 off F0 &&
              lwf (s_next S) off && lwf (s_next S) (argl S 1) && lwf (s_next S) lj && lwf (s_next S) l0)%bool then
            if Z.eqb c2 1 then
              if (Z.leb 1 (fst (irange fs l0)) && Z.leb (snd (irange fs l0)) 1073741824 &&
                  Z.leb (snd (irange fs (argl S 1)) + 16) TASK_SIZE)%bool then Some l0 else None
            else if Z.eqb c2 2 then
              match load_at img fs rgs (laddc (argl S 1) 16) SZ8 false, load_at img fs rgs (laddc (argl S 1) 24) SZ8 false with
              | Some (Some b1), Some (Some l1) =>
                  if (wsrc_ok img S M recs pre suf j lj F1 && iov_src_ok fs recs P Sl lj b1 l1 (ladd off l0) F1 && lwf (s_next S) l1 &&
                      Z.leb 1 (fst (irange fs (ladd l0 l1))) && Z.leb (snd (irange fs (ladd l0 l1))) 1073741824 &&
                      Z.leb (snd (irange fs (argl S 1)) + 32) TASK_SIZE)%bool then Some (ladd l0 l1) else None
              | _, _ => None
              end
            else None
          else None
      | _, _, _, _, _ => None
      end
  | PD _ (SLit _) _ => None
  end.
Definition writevL_ok (img : tree Z) (S : sst) (M : smodel) (Pn : nat) (F0 F1 : wsrc) (p : pend) : option lin :=
  match p with
  | PD ch (SLit bs) off => writevL_core img S M [] F0 F1 (PD ch (SArgs (firstn Pn bs) O (lconst 0) (skipn Pn bs)) off)
  | PD _ (SArgs _ _ _ _) _ => None
  end.
(* [comment removed for export] *)
Definition wv_l0 (img : tree Z) (S : sst) (F1 : wsrc) : option lin :=
  match F1 with
  | WEmpty => None
  | _ => match arg S 2 with
         | Some c2 => if Z.eqb c2 2 then
                        match load_at img (s_facts S) (s_rgs S) (laddc (argl S 1) 8) SZ8 false with Some (Some l0) => Some l0 | _ => None end
                      else None
         | None => None
         end
  end.
Definition wv_lo (S : sst) (len l0 : lin) : sst := add_fact (wv_post S len 1073741824) (FRange (lsub l0 (lvar (s_next S))) 0 1073741824).
Definition wv_hi (S : sst) (len l0 : lin) : sst := add_fact (wv_post S len 1073741824) (FRange (lsub (lvar (s_next S)) (laddc l0 1)) 0 1073741824).
(* [comment removed for export] *)
Definition writev0_ok (img : tree Z) (S : sst) : bool :=
  let fs := s_facts S in let rgs := s_rgs S in
  match a7c S, arg S 0, arg S 2, load_at img fs rgs (argl S 1) SZ8 false, load_at img fs rgs (laddc (argl S 1) 8) SZ8 false with
  | Some c7, Some c0, Some c2, Some (Some b), Some (Some l) =>
      (Z.eqb c7 66 && (Z.eqb c0 1 || Z.eqb c0 2) && Z.eqb c2 1 && lin_eqb l (lconst 0) && Z.leb (snd (irange fs b)) TASK_SIZE &&
       Z.leb (snd (irange fs (argl S 1)) + 16) TASK_SIZE)%bool
  | _, _, _, _, _ => false
  end.

(* [comment removed for export] *)
Definition asub_id {A : Type} (σ : tree lin) (a : A) : A := a.
Definition agok_t {A : Type} (M : smodel) (a : A) : bool := true.
Definition alins_nil {A : Type} (a : A) : list lin := [].
Definition aset_id {A : Type} (a : A) (ls : list lin) : A := a.
Definition amod_t {A : Type} (M M' : smodel) (a : A) : bool := true.   (* [comment removed for export] *)

Section Check.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable t : tree xi.
Variable img : tree Z.
Variable pv : lin.          (* [comment removed for export] *)
Variables FLlo FLhi : Z.    (* [comment removed for export] *)
Variable dr : bool.         (* [comment removed for export] *)
Variable hv : option positive.  (* [comment removed for export] *)
Definition pv_okb (n0 : positive) : bool := (lwf n0 pv && hv_okb hv n0)%bool.
(* [comment removed for export] *)
Context {N A : Type}.
Variable apost : N -> sst -> smodel -> A -> option (sst * smodel * A).
Variable anil : A -> bool.
Variable aeqb : A -> A -> bool.
Variable awf : positive -> A -> bool.
Variable acopy : A -> list srec.   (* [comment removed for export] *)
Variable asub : tree lin -> A -> A.   (* [comment removed for export] *)
Variable agok : smodel -> A -> bool.   (* [comment removed for export] *)
Variable alins : A -> list lin.        (* [comment removed for export] *)
Variable aset : A -> list lin -> A.    (* [comment removed for export] *)
Variable amod : smodel -> smodel -> A -> bool.   (* [comment removed for export] *)
Variable subs : list (sst * smodel * A * list (sst * smodel * A)).   (* [comment removed for export] *)
Variable conts : list (sst * smodel * fstate * shp * A).   (* [comment removed for export] *)

Definition open_post (S : sst) : sst := add_fact (bump (ret_post S (lconst 3)) (Pos.succ (s_next S))) (FRange (lvar (s_next S)) FLlo FLhi).
(* [comment removed for export] *)
Definition flv (S : sst) : lin := match hv with Some h => lvar (dvar h 16) | None => lvar (s_next S) end.
(* [comment removed for export] *)
Definition open_postH (S : sst) : sst :=
  match hv with
  | Some h => add_fact (open_post S) (FRange (lsub (lvar (s_next S)) (lvar (dvar h 16))) 0 0)
  | None => open_post S
  end.
Definition wv_shp (sh : shp) (S : sst) : shp :=
  match sh with
  | ShEmit (PD ch s off :: rest) kc => ShEmit (PD ch s (ladd off (lvar (s_next S))) :: rest) kc
  | _ => sh
  end.

(* [comment removed for export] *)
Definition tadd_lin (t : tree unit) (l : lin) : tree unit := List.fold_left (fun t p => tset (fst p) tt t) (l_t l) t.
Fixpoint tvals_acc {X} (t : tree X) (acc : list X) : list X :=
  match t with TEmpty => acc | TNode l v r => tvals_acc l (match v with Some x => x :: tvals_acc r acc | None => tvals_acc r acc end) end.
Definition bval_lin (v : bval) : lin := match v with BK _ => lconst 0 | BV l _ => l end.
Definition live_rg (t : tree unit) (R : region) : tree unit :=
  List.fold_left (fun t v => tadd_lin t (bval_lin v)) (tvals_acc (rg_cont R) []) (tadd_lin (tadd_lin t (rg_base R)) (rg_size R)).
Definition live_M (t : tree unit) (M : smodel) : tree unit :=
  let t := List.fold_left (fun t g => tadd_lin (tadd_lin t (fst (fst g))) (snd (fst g))) (sm_maps M) t in
  let t := List.fold_left (fun t p => tadd_lin t (fst p)) (sm_allow M) t in
  let t := List.fold_left (fun t p => tadd_lin (tadd_lin t (fst p)) (snd p)) (sm_frz M ++ sm_own M) t in
  let t := match sm_tid M with Some l => tadd_lin t l | None => t end in
  tadd_lin (tadd_lin (tadd_lin t (sm_brk M)) (sm_sbrk M)) (sm_sp M).
Definition live_FS (t : tree unit) (FS : fstate) : tree unit :=
  match FS with FSOpen a b | FSOpenLB a b => tadd_lin (tadd_lin t a) b | _ => t end.
Fixpoint live_sh (t : tree unit) (sh : shp) : tree unit :=
  match sh with
  | ShEmit po _ => List.fold_left (fun t p => match pd_src p with SArgs _ _ lj _ => tadd_lin (tadd_lin t (pd_off p)) lj | _ => tadd_lin t (pd_off p) end) po t
  | ShAlt2 a b => live_sh (live_sh t a) b
  | ShIf l _ _ a b => live_sh (live_sh (tadd_lin t l) a) b
  | ShBit l _ a b => live_sh (live_sh (tadd_lin t l) a) b
  end.
Definition lin_vars (l : lin) : list positive := List.map fst (l_t l).
Definition fact_vars (f : fact) : list positive :=
  match f with
  | FCond _ a b _ => lin_vars a ++ lin_vars b
  | FRange l _ _ | FMod l _ _ | FBits l _ _ => lin_vars l
  | FByte x v _ => lin_vars x ++ lin_vars v
  | FBytes x bs => lin_vars x ++ List.concat (List.map (fun p => lin_vars (fst p)) bs)
  end.
Definition fact_live (nk : positive) (t : tree unit) (f : fact) : bool :=
  List.existsb (fun x => (Pos.ltb x nk || match tget x t with Some _ => true | None => false end)%bool) (fact_vars f).
Definition live_set (S : sst) (M : smodel) (FS : fstate) (sh : shp) (xs : list positive) : tree unit :=
  live_sh (live_FS (live_M (List.fold_left live_rg (s_rgs S) (List.fold_left tadd_lin (tvals_acc (s_regs S) [])
    (List.fold_left (fun t x => tset x tt t) xs TEmpty))) M) FS) sh.
(* [comment removed for export] *)
Fixpoint fdedup (seen : list fact) (fs : list fact) : list fact :=
  match fs with [] => [] | f :: r => if List.existsb (fact_eqb f) seen then fdedup seen r else f :: fdedup (f :: seen) r end.
Definition gc_post (nk : positive) (xs : list positive) (S : sst) (M : smodel) (FS : fstate) (sh : shp) : sst :=
  SST (s_pc S) (s_regs S) (s_rgs S) (fdedup [] (List.filter (fact_live nk (live_set S M FS sh xs)) (s_facts S))) (s_next S) (s_resv S).

(* [comment removed for export] *)
Fixpoint lall2 (f : lin -> lin -> bool) (a b : list lin) : bool :=
  match a, b with [], [] => true | x :: a', y :: b' => (f x y && lall2 f a' b')%bool | _, _ => false end.
Definition gq : Type := (lin * list lin)%type.
Fixpoint glink (ys : list lin) (cs : list gq) : option lin :=
  match cs with
  | [] => None
  | (tx, xs) :: cs' =>
      match ys, xs with
      | y0 :: _, x0 :: _ =>
          match is_const (lsub y0 x0) with
          | Some c => if lall2 (fun y x => lin_eqb (lsub y x) (lconst c)) ys xs then Some (laddc tx c) else glink ys cs'
          | None => glink ys cs'
          end
      | _, _ => glink ys cs'
      end
  end.
Fixpoint zconsts (ls : list lin) : option (list Z) :=
  match ls with [] => Some [] | l :: r => match is_const l, zconsts r with Some c, Some cs => Some (c :: cs) | _, _ => None end end.
Fixpoint zall2 (f : Z -> Z -> bool) (a b : list Z) : bool :=
  match a, b with [], [] => true | x :: a', y :: b' => (f x y && zall2 f a' b')%bool | _, _ => false end.
Definition sdiv8 (tx : lin) : option lin :=
  match tx with LIN 0 [(v, k)] => if (Z.ltb 0 k && Z.eqb (Z.land k 7) 0 && Z.ltb k 4294967296)%bool then Some (LIN 0 [(v, k / 8)]) else None | _ => None end.
Fixpoint glink8 (ys : list lin) (cs : list gq) : option lin :=
  match cs with
  | [] => None
  | (tx, xs) :: cs' =>
      match sdiv8 tx, zconsts ys, zconsts xs with
      | Some t8, Some (y0 :: yr), Some (x0 :: xr) =>
          let c := y0 - x0 / 8 in
          if (Z.eqb (Z.land x0 7) 0 && zall2 (fun y x => Z.eqb (Z.land x 7) 0 && Z.eqb (y - x / 8) c) yr xr)%bool
          then Some (laddc t8 c) else glink8 ys cs'
      | _, _, _ => glink8 ys cs'
      end
  end.
Fixpoint ctz12 (x : Z) (k : nat) : Z := match k with O => 0 | Datatypes.S k' => if Z.eqb (Z.land x 1) 0 then 1 + ctz12 (Z.shiftr x 1) k' else 0 end.
Definition zmin_l (a : list Z) (d : Z) : Z := List.fold_left Z.min a d.
Definition zmax_l (a : list Z) (d : Z) : Z := List.fold_left Z.max a d.
(* [comment removed for export] *)
Definition gfresh (v : positive) (ys : list lin) (fss : list (list fact)) : lin * list fact :=
  match zconsts ys with
  | Some (c0 :: cr) =>
      let k := List.fold_left (fun k c => Z.min k (ctz12 c 12)) cr (ctz12 c0 12) in
      let s := 2 ^ k in
      (lscale s (lvar v), [FRange (lvar v) (zmin_l cr c0 / s) (zmax_l cr c0 / s)])
  | _ =>
      let rs := List.map (fun '(y, fs) => irange fs y) (List.combine ys fss) in
      let lo := zmin_l (List.map fst rs) M64 in let hi := zmax_l (List.map snd rs) 0 in
      (lvar v, if (Z.leb lo hi && negb (Z.eqb lo 0 && Z.eqb hi M64))%bool then [FRange (lvar v) lo hi] else [])
  end.
(* [comment removed for export] *)
Record gst : Type := GST { g_v : positive ; g_cs : list gq ; g_fs : list fact }.
Definition gq_gen (g : gst) (ys : list lin) (fss : list (list fact)) : lin * gst :=
  match ys with
  | [] => (lconst 0, g)
  | y0 :: yr =>
      if forallb (lin_eqb y0) yr then (y0, g)
      else match glink ys (g_cs g) with
           | Some t => (t, g)
           | None => match glink8 ys (g_cs g) with
                     | Some t => (t, g)
                     | None => let '(t, fs) := gfresh (g_v g) ys fss in (t, GST (Pos.succ (g_v g)) ((t, ys) :: g_cs g) (fs ++ g_fs g))
                     end
           end
  end.
Fixpoint gen_regsL (Ls : list sst) (fss : list (list fact)) (k : nat) (g : gst) (acc : tree lin) : tree lin * gst :=
  match k with
  | O => (acc, g)
  | Datatypes.S k' => let key := Pos.of_succ_nat k in
      let '(t, g') := gq_gen g (List.map (fun L => rget (s_regs L) key) Ls) fss in
      gen_regsL Ls fss k' g' (rset acc key t)
  end.
(* [comment removed for export] *)
Fixpoint telems {X} (t : tree X) (k : positive -> positive) (acc : list (positive * X)) : list (positive * X) :=
  match t with
  | TEmpty => acc
  | TNode l v r => telems l (fun p => k (xO p)) (match v with Some x => (k xH, x) :: telems r (fun p => k (xI p)) acc | None => telems r (fun p => k (xI p)) acc end)
  end.
(* [comment removed for export] *)
Definition gen_contL (c0 : tree bval) (cr : list (tree bval)) (fss : list (list fact)) (g : gst) : tree bval * gst :=
  List.fold_left (fun '(acc, g) '(key, v0) =>
      let vs := List.map (fun t => tget key t) cr in
      if forallb (fun o => match o with Some v => bval_eqb v v0 | None => false end) vs then (tset key v0 acc, g)
      else match v0 with
           | BV l0 j0 =>
               match List.fold_right (fun o accl => match o, accl with Some (BV l j), Some ls => if Z.eqb j j0 then Some (l :: ls) else None | _, _ => None end) (Some []) vs with
               | Some ls => let '(t, g') := gq_gen g (l0 :: ls) fss in (tset key (BV t j0) acc, g')
               | None => (acc, g)
               end
           | BK _ => (acc, g)
           end) (telems c0 (fun p => p) []) (@TEmpty bval, g).
(* [comment removed for export] *)
Definition gen_kindL (R0 : region) (Rr : list region) (c : tree bval) : rkind :=
  let k0 := rg_kind R0 in
  let P0 := RG (rg_base R0) (rg_size R0) k0 c in
  if (forallb (fun R => rkind_eqb (rg_kind R) k0) Rr && forallb (fun R => rz_extra_ok R P0) (R0 :: Rr))%bool then k0 else RW.
(* [comment removed for export] *)
Definition match_contL (cp cs : tree bval) (σ : tree lin) : tree lin :=
  List.fold_left (fun σ '(key, v) => match v, tget key cs with BV l j, Some (BV l' j') => if Z.eqb j j' then bind_any l l' σ else σ | _, _ => σ end)
    (telems cp (fun p => p) []) σ.
(* [comment removed for export] *)
Definition mc_step (vp vs : option bval) (σ : tree lin) : tree lin :=
  match vp, vs with Some (BV l j), Some (BV l' j') => if Z.eqb j j' then bind_any l l' σ else σ | _, _ => σ end.
Fixpoint match_contP (cp cs : tree bval) (σ : tree lin) : tree lin :=
  match cp with
  | TEmpty => σ
  | TNode lp vp rp =>
      match cs with
      | TEmpty => σ
      | TNode ls vs rs => match_contP rp rs (mc_step vp vs (match_contP lp ls σ))
      end
  end.
Definition mc_g (cs0 : tree bval) : tree lin -> positive * bval -> tree lin :=
  fun σ '(key, v) => match v, tget key cs0 with BV l j, Some (BV l' j') => if Z.eqb j j' then bind_any l l' σ else σ | _, _ => σ end.
#[using="Type"] Lemma mc_none : forall cs0 (cp : tree bval) (k : positive -> positive) acc σ, (forall p, tget (k p) cs0 = None) ->
  fold_left (mc_g cs0) (telems cp k acc) σ = fold_left (mc_g cs0) acc σ.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros cs0 cp. induction cp as [|lp IHl vp rp IHr]; intros k acc σ Hk; cbn [telems]; [reflexivity|].
  rewrite IHl by (intros p; apply Hk).
  destruct vp as [x|].
  - cbn [fold_left]. assert (E : mc_g cs0 σ (k 1%positive, x) = σ) by (unfold mc_g; rewrite Hk; destruct x; reflexivity).
    rewrite E. apply IHr. intros p; apply Hk.
  - apply IHr. intros p; apply Hk.
Qed.
#[using="Type"] Lemma match_contP_gen : forall cs0 (cp cs : tree bval) (k : positive -> positive) acc σ, (forall p, tget (k p) cs0 = tget p cs) ->
  fold_left (mc_g cs0) (telems cp k acc) σ = fold_left (mc_g cs0) acc (match_contP cp cs σ).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros cs0 cp. induction cp as [|lp IHl vp rp IHr]; intros cs k acc σ Hk; [reflexivity|].
  destruct cs as [|ls vs rs].
  - cbn [match_contP]. apply mc_none. intros p. rewrite Hk. destruct p; reflexivity.
  - cbn [telems match_contP].
    rewrite (IHl ls (fun p => k (xO p)) _ σ) by (intros p; rewrite Hk; reflexivity).
    assert (Hn : tget (k 1%positive) cs0 = vs) by (rewrite Hk; reflexivity).
    destruct vp as [x|].
    + cbn [fold_left].
      assert (E : mc_g cs0 (match_contP lp ls σ) (k 1%positive, x) = mc_step (Some x) vs (match_contP lp ls σ)) by (unfold mc_g, mc_step; rewrite Hn; reflexivity).
      rewrite E. apply (IHr rs (fun p => k (xI p))). intros p; rewrite Hk; reflexivity.
    + assert (E : mc_step None vs (match_contP lp ls σ) = match_contP lp ls σ) by reflexivity. rewrite E.
      apply (IHr rs (fun p => k (xI p))). intros p; rewrite Hk; reflexivity.
Qed.
#[using="Type"] Lemma match_contP_eq : forall cp cs σ, match_contP cp cs σ = match_contL cp cs σ.
Proof. LiaFast.lf_pins LiaFast.u0. intros cp cs σ. unfold match_contL. symmetry. exact (match_contP_gen cs cp cs (fun p => p) [] σ (fun p => eq_refl)). Qed.
Fixpoint match_rgs_contL_ref (rs rp : list region) (σ : tree lin) : tree lin :=
  match rs, rp with
  | R :: rs', R' :: rp' => match_rgs_contL_ref rs' rp' (match_contL (rg_cont R') (rg_cont R) σ)
  | _, _ => σ
  end.
Fixpoint match_rgs_contL (rs rp : list region) (σ : tree lin) : tree lin :=
  match rs, rp with
  | R :: rs', R' :: rp' => match_rgs_contL rs' rp' (match_contP (rg_cont R') (rg_cont R) σ)
  | _, _ => σ
  end.
#[using="Type"] Lemma match_rgs_contL_eq : forall rs rp σ, match_rgs_contL rs rp σ = match_rgs_contL_ref rs rp σ.
Proof. LiaFast.lf_pins LiaFast.u0. induction rs as [|R rs IH]; intros [|R' rp] σ; cbn [match_rgs_contL match_rgs_contL_ref]; try reflexivity. rewrite match_contP_eq. apply IH. Qed.
(* [comment removed for export] *)
Fixpoint treq_g {X} (f : X -> X -> bool) (t u : tree X) : bool :=
  match t, u with
  | TEmpty, TEmpty => true
  | TNode l v r, TNode l' v' r' =>
      if match v, v' with Some x, Some y => f x y | None, None => true | _, _ => false end then (if treq_g f l l' then treq_g f r r' else false) else false
  | _, _ => false
  end.
Fixpoint nodead_g {X} (t : tree X) : bool :=
  match t with
  | TEmpty => true
  | TNode l v r => if nodead_g l then (if nodead_g r then match v, l, r with None, TEmpty, TEmpty => false | _, _, _ => true end else false) else false
  end.
Fixpoint gen_rgsL (rss : list (list region)) (fss : list (list fact)) (n : nat) (g : gst) : option (list region * gst) :=
  match n with
  | O => Some ([], g)
  | Datatypes.S n' =>
      match List.map (fun rs => List.hd_error rs) rss with
      | hs => match List.fold_right (fun o acc => match o, acc with Some R, Some l => Some (R :: l) | _, _ => None end) (Some []) hs with
              | Some (R0 :: Rr) =>
                  let '(b, g1) := gq_gen g (List.map rg_base (R0 :: Rr)) fss in
                  let '(z, g2) := gq_gen g1 (List.map rg_size (R0 :: Rr)) fss in
                  let same := if forallb (fun R => treq_g bval_eqb (rg_cont R0) (rg_cont R)) Rr then nodead_g (rg_cont R0) else false in
                  let '(c, g2') := if same then (rg_cont R0, g2) else gen_contL (rg_cont R0) (List.map rg_cont Rr) fss g2 in
                  match gen_rgsL (List.map (@List.tl region) rss) fss n' g2' with
                  | Some (rs', g3) =>
                      let k := if same then (if forallb (fun R => rkind_eqb (rg_kind R) (rg_kind R0)) Rr then rg_kind R0 else RW) else gen_kindL R0 Rr c in
                      Some (RG b z k c :: rs', g3)
                  | None => None
                  end
              | _ => None
              end
      end
  end.
Fixpoint gen_mapsL (mss : list (list (lin * lin * gkind))) (fss : list (list fact)) (n : nat) (g : gst) : option (list (lin * lin * gkind) * gst) :=
  match n with
  | O => Some ([], g)
  | Datatypes.S n' =>
      match List.fold_right (fun o acc => match o, acc with Some x, Some l => Some (x :: l) | _, _ => None end) (Some []) (List.map (fun ms => List.hd_error ms) mss) with
      | Some ((g0 :: gr) as gs) =>
          if forallb (fun x => gkind_eqb (snd x) (snd g0)) gr then
            let '(b, g1) := gq_gen g (List.map (fun x => fst (fst x)) gs) fss in
            let '(z, g2) := gq_gen g1 (List.map (fun x => snd (fst x)) gs) fss in
            match gen_mapsL (List.map (@List.tl _) mss) fss n' g2 with
            | Some (ms', g3) => Some ((b, z, snd g0) :: ms', g3)
            | None => None
            end
          else None
      | _ => None
      end
  end.
Fixpoint gen_pairsL (pss : list (list (lin * lin))) (fss : list (list fact)) (n : nat) (g : gst) : option (list (lin * lin) * gst) :=
  match n with
  | O => Some ([], g)
  | Datatypes.S n' =>
      match List.fold_right (fun o acc => match o, acc with Some x, Some l => Some (x :: l) | _, _ => None end) (Some []) (List.map (fun ps => List.hd_error ps) pss) with
      | Some (p0 :: pr) =>
          let '(b, g1) := gq_gen g (List.map fst (p0 :: pr)) fss in
          let '(z, g2) := gq_gen g1 (List.map snd (p0 :: pr)) fss in
          match gen_pairsL (List.map (@List.tl _) pss) fss n' g2 with
          | Some (ps', g3) => Some ((b, z) :: ps', g3)
          | None => None
          end
      | _ => None
      end
  end.
Fixpoint gen_allowL (pss : list (list (lin * Z))) (fss : list (list fact)) (n : nat) (g : gst) : option (list (lin * Z) * gst) :=
  match n with
  | O => Some ([], g)
  | Datatypes.S n' =>
      match List.fold_right (fun o acc => match o, acc with Some x, Some l => Some (x :: l) | _, _ => None end) (Some []) (List.map (fun ps => List.hd_error ps) pss) with
      | Some (p0 :: pr) =>
          if forallb (fun p => Z.eqb (snd p) (snd p0)) pr then
            let '(b, g1) := gq_gen g (List.map fst (p0 :: pr)) fss in
            match gen_allowL (List.map (@List.tl _) pss) fss n' g1 with
            | Some (ps', g2) => Some ((b, snd p0) :: ps', g2)
            | None => None
            end
          else None
      | _ => None
      end
  end.
Fixpoint gen_linsL (lss : list (list lin)) (fss : list (list fact)) (n : nat) (g : gst) : option (list lin * gst) :=
  match n with
  | O => Some ([], g)
  | Datatypes.S n' =>
      match List.fold_right (fun o acc => match o, acc with Some x, Some l => Some (x :: l) | _, _ => None end) (Some []) (List.map (fun ls => List.hd_error ls) lss) with
      | Some (l0 :: lr) =>
          let '(t, g1) := gq_gen g (l0 :: lr) fss in
          match gen_linsL (List.map (@List.tl _) lss) fss n' g1 with
          | Some (ls', g2) => Some (t :: ls', g2)
          | None => None
          end
      | _ => None
      end
  end.
(* [comment removed for export] *)
Definition genLA (L : list (sst * smodel)) (As : list (list lin)) : option (sst * smodel * list lin) :=
  match L with
  | [] => None
  | (F0, M0) :: Lrst =>
      let Lsts := List.map fst L in let Msts := List.map snd L in let fss := List.map s_facts Lsts in
      let n0 := max_next (List.map fst Lrst) (s_next F0) in
      let nR := List.length (s_rgs F0) in
      if (forallb (fun F => Nat.eqb (List.length (s_rgs F)) nR) Lsts &&
          forallb (fun M => Nat.eqb (List.length (sm_maps M)) (List.length (sm_maps M0)) && Nat.eqb (List.length (sm_allow M)) (List.length (sm_allow M0)) &&
                            Nat.eqb (List.length (sm_frz M)) (List.length (sm_frz M0)) && Nat.eqb (List.length (sm_own M)) (List.length (sm_own M0)) &&
                            zr_eqb (sm_zr M) (sm_zr M0)) Msts)%bool then
      let '(regs', g1) := gen_regsL Lsts fss 31 (GST n0 [] []) TEmpty in
      match gen_rgsL (List.map s_rgs Lsts) fss nR g1 with
      | Some (rgs', g2) =>
          match gen_mapsL (List.map sm_maps Msts) fss (List.length (sm_maps M0)) g2 with
          | Some (maps', g3) =>
              match gen_allowL (List.map sm_allow Msts) fss (List.length (sm_allow M0)) g3 with
              | Some (allow', g4) =>
                  match gen_pairsL (List.map sm_frz Msts) fss (List.length (sm_frz M0)) g4 with
                  | Some (frz', g5) =>
                      match gen_pairsL (List.map sm_own Msts) fss (List.length (sm_own M0)) g5 with
                      | Some (own', g6) =>
                          let '(brk', g7) := gq_gen g6 (List.map sm_brk Msts) fss in
                          let '(sbrk', g8) := gq_gen g7 (List.map sm_sbrk Msts) fss in
                          let '(sp', g9a) := gq_gen g8 (List.map sm_sp Msts) fss in
                          let nA := List.length (List.hd [] As) in
                          match (if forallb (fun ls => Nat.eqb (List.length ls) nA) As then gen_linsL As fss nA g9a else None) with
                          | Some (als', g9) =>
                          let tid' := sm_tid M0 in
                          if forallb (fun M => match sm_tid M, tid' with Some a, Some b => lin_eqb a b | None, None => true | _, _ => false end) Msts then
                          let fs := g_fs g9 ++ List.fold_left (fun fs L => common_suffix fs (s_facts L)) (List.map fst Lrst) (s_facts F0) in
                          Some (SST (s_pc F0) regs' rgs' fs (g_v g9)
                                    (if forallb (fun F => rsv_eqb (s_resv F) (s_resv F0)) Lsts then s_resv F0 else RUnk),
                                SM maps' allow' (sm_zr M0) tid' brk' sbrk' sp' frz' own', als')
                          else None
                          | None => None
                          end
                      | None => None
                      end
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | None => None
      end
      else None
  end.
Definition genL (L : list (sst * smodel)) : option (sst * smodel) :=
  match genLA L (List.map (fun _ => []) L) with Some (P, MP, _) => Some (P, MP) | None => None end.
(* [comment removed for export] *)
Fixpoint match_maps (ms mp : list (lin * lin * gkind)) (σ : tree lin) : tree lin :=
  match ms, mp with
  | x :: ms', y :: mp' => match_maps ms' mp' (bind_any (snd (fst y)) (snd (fst x)) (bind_any (fst (fst y)) (fst (fst x)) σ))
  | _, _ => σ
  end.
Fixpoint match_pairs (ps pp : list (lin * lin)) (σ : tree lin) : tree lin :=
  match ps, pp with
  | x :: ps', y :: pp' => match_pairs ps' pp' (bind_any (snd y) (snd x) (bind_any (fst y) (fst x) σ))
  | _, _ => σ
  end.
Fixpoint match_allow (ps pp : list (lin * Z)) (σ : tree lin) : tree lin :=
  match ps, pp with
  | x :: ps', y :: pp' => match_allow ps' pp' (bind_any (fst y) (fst x) σ)
  | _, _ => σ
  end.
Fixpoint match_lins (ls lp : list lin) (σ : tree lin) : tree lin :=
  match ls, lp with
  | x :: ls', y :: lp' => match_lins ls' lp' (bind_any y x σ)
  | _, _ => σ
  end.
(* [comment removed for export] *)
Definition matchLA (F : sst) (MF : smodel) (lsF : list lin) (P : sst) (MP : smodel) (lsP : list lin) : tree lin :=
  let σ := match_maps (sm_maps MF) (sm_maps MP) (match_st F P) in
  let σ := match_allow (sm_allow MF) (sm_allow MP) σ in
  let σ := match_pairs (sm_frz MF) (sm_frz MP) σ in
  let σ := match_pairs (sm_own MF) (sm_own MP) σ in
  let σ := bind_any (sm_sp MP) (sm_sp MF) (bind_any (sm_sbrk MP) (sm_sbrk MF) (bind_any (sm_brk MP) (sm_brk MF) σ)) in
  let σ := match_lins lsF lsP σ in
  match_rgs_contL (s_rgs F) (s_rgs P) σ.
Definition matchL (F : sst) (MF : smodel) (P : sst) (MP : smodel) : tree lin := matchLA F MF [] P MP [].

(* [comment removed for export] *)
Definition sep_post (op : templop) (S : sst) (M : smodel) : option sst :=
  match op with
  | TSepG i j => sepg_post S M i j
  | TSepW i j => sepw_post S M i j
  | TSepR j lo hi => sepr_post segs S M j lo hi
  | TSepS j => seps_post S M j
  | _ => None
  end.

Fixpoint mcheck (ch : @mchain N) (S : sst) (M : smodel) (FS : fstate) (sh : shp) (a : A) : option (list (sst * smodel * fstate * shp * A)) :=
  match ch with
  | MEnd => Some [(S, M, FS, sh, a)]
  | MChain c k =>
      if anil a then
      match check_chain segs LIMIT t img c S M with
      | Some fins => all_some (fun '(S', M') => if (Pos.leb (s_next S) (s_next S') && fs_wf (s_next S') FS && frz_eqb (sm_frz M') (sm_frz M))%bool
                                                then mcheck k S' M' FS sh a else None) fins
      | None => None
      end
      else None
  | MSegK depth p ks =>
      if bases_below (s_next S) (s_rgs S) then
        match checkB t img (s_next S) depth p S with
        | Some Ls => all_some (fun L => if (sm_wf (s_next L) M && Pos.leb (s_next S) (s_next L) && fs_wf (s_next L) FS)%bool
                                        then mfind ks L M FS sh a else None) Ls
        | None => None
        end
      else None
  | MOpen kerr kok =>
      match FS, sh with
      | FSClosed, ShAlt2 sa sb =>
          if (negb dr && is_ecall t (s_pc S) && open_args_ok S pv && Z.leb FLlo FLhi)%bool then
            match mcheck kerr (ret_gen S ERRLO ERRHI) M FSClosed sa a,
                  mcheck kok (open_postH S) M (FSOpen (lconst 0) (flv S)) sb a with
            | Some f1, Some f2 => Some (f1 ++ f2)
            | _, _ => None
            end
          else None
      | _, _ => None
      end
  | MRead i o ka kb =>
      match FS with
      | FSOpen off FL =>
          if (negb dr && is_ecall t (s_pc S))%bool then
            match read_args_ok S i o with
            | Some chi =>
                let c := argl S 2 in
                let rem := lsub FL off in
                let '(lo, hi) := irange (s_facts S) rem in
                let '(clo, _) := irange (s_facts S) c in
                match (if Z.leb lo chi then mcheck ka (add_fact (read_post S i o (o + chi) rem) (FRange (lsub c rem) 0 65536)) M (FSOpen FL FL) sh a else Some []),
                      (if Z.ltb clo hi then mcheck kb (add_fact (read_post S i o (o + chi) c) (FRange (lsub rem c) 1 hi)) M (FSOpen (ladd off c) FL) sh a
                       else Some []) with
                | Some f1, Some f2 => if (Z.leb 0 lo && Z.ltb hi 4611686018427387904 && Z.ltb (snd (irange (s_facts S) off) + chi) FLT)%bool then Some (f1 ++ f2) else None
                | _, _ => None
                end
            | None => None
            end
          else None
      | _ => None
      end
  | MClose k =>
      match FS with
      | FSOpen _ _ | FSOpenLB _ _ => if (is_ecall t (s_pc S) && close_args_ok S)%bool then mcheck k (ret_post S (lconst 0)) M FSDone sh a else None
      | _ => None
      end
  | MIoctl fd cmd k =>
      if (is_ecall t (s_pc S) && ioctl_args_ok S fd cmd)%bool then mcheck k (ret_post S (errno_lin ENOTTY)) M FS sh a else None
  | MWritev B0 k =>
      match sh with
      | ShEmit (p :: _) _ =>
          if is_ecall t (s_pc S) then
            match writev_ok img S B0 p with
            | Some len => mcheck k (wv_post S len (src_len (pd_src p))) M FS (wv_shp sh S) a
            | None => None
            end
          else None
      | _ => None
      end
  | MExit =>
      match sh with
      | ShEmit po kc => if (is_ecall t (s_pc S) && exit_args_ok S kc && forallb (pend_done (s_facts S)) po)%bool then Some [] else None
      | _ => None
      end
  | MWeaken P n0 FP shP k =>
      if (went n0 S M FS sh P FP shP && fs_wf (s_next P) FP && shp_wf (s_next P) shP && pv_okb n0 && awf n0 a)%bool then mcheck k P M FP shP a else None
  | MLoop P n0 FP shP meas body ks =>
      if (went n0 S M FS sh P FP shP && fs_wf (s_next P) FP && shp_wf (s_next P) shP && pv_okb n0 && lwf (s_next P) meas &&
          meas_ok (s_facts P) meas && awf n0 a)%bool then
        match mcheck body P M FP shP a with
        | Some fb => all_some (fun '(F, MF, FSF, shF, aF) =>
                        if Z.eqb (s_pc F) (s_pc P) then
                          let σ := match_st F P in
                          if (ent_okN σ n0 F P MF && fs_ent FSF FP σ && shp_ent shF shP σ && sm_eqb MF M && aeqb aF a && lmeas_dec F σ meas)%bool
                          then Some [] else None
                        else if Pos.leb n0 (s_next F) then mfind ks F MF FSF shF aF else None) fb
        | None => None
        end
      else None
  | MVoid => if fx_contra (s_facts S) then Some [] else None
  | MLoopW zk body ks =>
      match mcheck body S M FS sh a with
      | Some fb1 =>
          match List.find (fun '(F, _, _, _, _) => Z.eqb (s_pc F) (s_pc S)) fb1 with
          | Some (F1, _, FS1, sh1, _) =>
              match wgen false S F1 FS FS1 sh sh1 zk with
              | Some (P0, n0, FP, shP, meas) =>
      (* [comment removed for export] *)
      let P := match mcheck body P0 M FP shP a with
               | Some fb0 => match List.find (fun '(F, _, _, _, _) => Z.eqb (s_pc F) (s_pc P0)) fb0 with
                             | Some (F0, _, _, _, _) => wref P0 F0
                             | None => P0
                             end
               | None => P0
               end in
      if (went n0 S M FS sh P FP shP && fs_wf (s_next P) FP && shp_wf (s_next P) shP && pv_okb n0 && lwf (s_next P) meas &&
                    meas_ok (s_facts P) meas && awf n0 a)%bool then
                  match mcheck body P M FP shP a with
                  | Some fb => all_some (fun '(F, MF, FSF, shF, aF) =>
                                  if Z.eqb (s_pc F) (s_pc P) then
                                    let σ := match_st F P in
                                    if (ent_okN σ n0 F P MF && fs_ent FSF FP σ && shp_ent shF shP σ && sm_eqb MF M && aeqb aF a && lmeas_dec F σ meas)%bool
                                    then Some [] else None
                                  else if Pos.leb n0 (s_next F) then mfind ks F MF FSF shF aF else None) fb
                  | None => None
                  end
                else None
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | MPop k =>
      match sh with
      | ShEmit (p :: rest) kc => if pend_done (s_facts S) p then mcheck k S M FS (ShEmit rest kc) a else None
      | _ => None
      end
  | MAlt k1 k2 => if is_mvoid k1 then (if fx_contra1 (s_facts S) then Some [] else mcheck k2 S M FS sh a)      (* [comment removed for export] *)
                 else match mcheck k1 S M FS sh a with Some f => Some f | None => mcheck k2 S M FS sh a end
  | MOpenDir kerr kok =>
      match FS, sh with
      | FSClosed, ShAlt2 sa sb =>
          if (dr && is_ecall t (s_pc S) && open_args_ok S pv && lbytes_ok img (s_facts S) (s_rgs S) pv dot_z 0)%bool then
            match mcheck kerr (ret_gen S ERRLO ERRHI) M FSClosed sa a,
                  mcheck kok (ret_post S (lconst 3)) M FSDir sb a with
            | Some f1, Some f2 => Some (f1 ++ f2)
            | _, _ => None
            end
          else None
      | _, _ => None
      end
  | MReadDir k =>
      match FS with
      | FSDir => if (is_ecall t (s_pc S) && readdir_args_ok S)%bool then mcheck k (ret_post S (errno_lin EISDIR)) M FS sh a else None
      | _ => None
      end
  | MWritev2 B0 k =>
      match sh with
      | ShEmit (p :: _) _ =>
          if is_ecall t (s_pc S) then
            match writev2_ok img S B0 p with
            | Some len => mcheck k (wv_post S len (src_len (pd_src p))) M FS (wv_shp sh S) a
            | None => None
            end
          else None
      | _ => None
      end
  | MWritevC F0 F1 k =>
      match sh with
      | ShEmit (p :: _) _ =>
          if is_ecall t (s_pc S) then
            match writevC_ok img S M (acopy a) F0 F1 p with
            | Some len =>
                match wv_l0 img S F1 with
                | Some l0 => match mcheck k (wv_lo S len l0) M FS (wv_shp sh S) a, mcheck k (wv_hi S len l0) M FS (wv_shp sh S) a with
                             | Some f1, Some f2 => Some (f1 ++ f2)
                             | _, _ => None
                             end
                | None => mcheck k (wv_post S len 1073741824) M FS (wv_shp sh S) a
                end
            | None => None
            end
          else None
      | _ => None
      end
  | MWritevL Pn F0 F1 k =>
      match sh with
      | ShEmit (p :: _) _ =>
          if is_ecall t (s_pc S) then
            match writevL_ok img S M Pn F0 F1 p with
            | Some len =>
                match wv_l0 img S F1 with
                | Some l0 => match mcheck k (wv_lo S len l0) M FS (wv_shp sh S) a, mcheck k (wv_hi S len l0) M FS (wv_shp sh S) a with
                             | Some f1, Some f2 => Some (f1 ++ f2)
                             | _, _ => None
                             end
                | None => mcheck k (wv_post S len 1073741824) M FS (wv_shp sh S) a
                end
            | None => None
            end
          else None
      | _ => None
      end
  | MSplitP n k =>
      match sh with
      | ShEmit (PD ch (SLit bs) off :: rest) kc =>
          if lin_eqb off (lconst 0) then mcheck k S M FS (ShEmit (PD ch (SLit (firstn n bs)) (lconst 0) :: PD ch (SLit (skipn n bs)) (lconst 0) :: rest) kc) a
          else None
      | _ => None
      end
  | MWritev0 k => if (is_ecall t (s_pc S) && writev0_ok img S)%bool then mcheck k (ret_post S (lconst 0)) M FS sh a else None
  | MJoin body jpc k =>
      match mcheck body S M FS sh a with
      | Some fb =>
          let J := List.filter (fun '(F, _, _, _, _) => Z.eqb (s_pc F) jpc) fb in
          let O := List.filter (fun '(F, _, _, _, _) => negb (Z.eqb (s_pc F) jpc)) fb in
          match J with
          | [] => Some O
          | (F0, M0, FS0, sh0, a0) :: Jr =>
              let n0 := max_next (List.map (fun '(F, _, _, _, _) => F) Jr) (s_next F0) in
              let P := join_fs_hull (fst (gen2 F0 (List.map (fun '(F, _, _, _, _) => F) Jr))) FS0 J in
              if (forallb (fun '(F, MF, FSF, shF, aF) => wentN n0 F MF FSF shF P FS0 sh0 && sm_eqb MF M0 && aeqb aF a0) J && state_wf P &&
                  Pos.leb (s_next S) n0 && fs_wf (s_next P) FS0 && shp_wf (s_next P) sh0 && pv_okb n0 && awf n0 a0)%bool
              then match mcheck k P M0 FS0 sh0 a0 with Some fk => Some (fk ++ O) | None => None end
              else None
          end
      | None => None
      end
  | MCall nk k =>
      match apost nk S M a with
      | Some (S', M', a') =>
          if (Pos.leb (s_next S) (s_next S') && fs_wf (s_next S') FS && frz_eqb (sm_frz M') (sm_frz M) && awf (s_next S') a')%bool
          then mcheck k S' M' FS sh a' else None
      | None => None
      end
  | MReadH i o k ka kb =>
      match FS, hv with
      | FSOpen off FL, Some h =>
          if (negb dr && is_ecall t (s_pc S) && lin_eqb off (lconst 0) && Pos.leb (dvar h 16) (s_next S) && Nat.leb k 16)%bool then
            match read_args_ok S i o with
            | Some chi =>
                let c := argl S 2 in
                let rem := lsub FL off in
                let '(lo, hi) := irange (s_facts S) rem in
                let '(clo, _) := irange (s_facts S) c in
                match (if Z.leb lo chi then if Z.leb (Z.of_nat k) lo then mcheck ka (track_hdr (add_fact (read_post S i o (o + chi) rem) (FRange (lsub c rem) 0 65536)) i o h k) M (FSOpen FL FL) sh a else None else Some []),
                      (if Z.ltb clo hi then if Z.leb (Z.of_nat k) clo then mcheck kb (track_hdr (add_fact (read_post S i o (o + chi) c) (FRange (lsub rem c) 1 hi)) i o h k) M (FSOpen (ladd off c) FL) sh a else None
                       else Some []) with
                | Some f1, Some f2 => if (Z.leb 0 lo && Z.ltb hi 4611686018427387904 && Z.ltb (snd (irange (s_facts S) off) + chi) FLT)%bool then Some (f1 ++ f2) else None
                | _, _ => None
                end
            | None => None
            end
          else None
      | _, _ => None
      end
  | MSel ka kb =>
      match sh with
      | ShIf l lo hi sa sb =>
          let r := irange (s_facts S) l in
          if (Z.leb lo (fst r) && Z.leb (snd r) hi)%bool then mcheck ka S M FS sa a
          else if (Z.ltb hi (fst r) || Z.ltb (snd r) lo)%bool then mcheck kb S M FS sb a
          else None
      | _ => None
      end
  | MSep op k => match sep_post op S M with Some S' => mcheck k S' M FS sh a | None => None end
  | MSplit l c ka kb =>
      if lwf (s_next S) l then
        let r := irange (s_facts S) l in
        match (if Z.leb (fst r) c then mcheck ka (add_fact S (FRange l (fst r) (Z.min c (snd r)))) M FS sh a else Some []),
              (if Z.ltb c (snd r) then mcheck kb (add_fact S (FRange l (Z.max (c + 1) (fst r)) (snd r))) M FS sh a else Some []) with
        | Some f1, Some f2 => Some (f1 ++ f2)
        | _, _ => None
        end
      else None
  | MSplitB l k r0 ka kb =>
      if (lwf (s_next S) l && Z.leb 0 k && Z.ltb k 64 && (Z.eqb k 0 && Z.eqb r0 0 || match lowb (s_facts S) l k with Some r => Z.eqb r r0 | None => false end))%bool then
        match mcheck ka (add_fact S (FMod l (k + 1) r0)) M FS sh a, mcheck kb (add_fact S (FMod l (k + 1) (r0 + 2 ^ k))) M FS sh a with
        | Some f1, Some f2 => Some (f1 ++ f2)
        | _, _ => None
        end
      else None
  | MSplitG j c ka kb =>
      match nth_error (sm_maps M) j with
      | Some g =>
          let l := fst (fst g) in
          if lwf (s_next S) l then
            let r := irange (s_facts S) l in
            match (if Z.leb (fst r) c then mcheck ka (add_fact S (FRange l (fst r) (Z.min c (snd r)))) M FS sh a else Some []),
                  (if Z.ltb c (snd r) then mcheck kb (add_fact S (FRange l (Z.max (c + 1) (fst r)) (snd r))) M FS sh a else Some []) with
            | Some f1, Some f2 => Some (f1 ++ f2)
            | _, _ => None
            end
          else None
      | None => None
      end
  | MConcR k => mcheck k (concr S) M FS sh a
  | MConcF k => mcheck k S M (concr_fs (s_facts S) FS) sh a
  | MOpenLB kerr kok =>
      match FS, sh with
      | FSClosed, ShAlt2 sa sb =>
          if (negb dr && is_ecall t (s_pc S) && open_args_ok S pv && Z.leb 0 FLlo && Z.ltb FLlo 4611686018427387904)%bool then
            match mcheck kerr (ret_gen S ERRLO ERRHI) M FSClosed sa a,
                  mcheck kok (ret_post S (lconst 3)) M (FSOpenLB (lconst 0) (lconst FLlo)) sb a with
            | Some f1, Some f2 => Some (f1 ++ f2)
            | _, _ => None
            end
          else None
      | _, _ => None
      end
  | MReadLB b o k =>
      match FS with
      | FSOpenLB off B =>
          if (negb dr && is_ecall t (s_pc S))%bool then
            let i := rg_index (s_rgs S) b O in
            match read_args_ok S i o with
            | Some chi => if Z.leb chi (fst (irange (s_facts S) (lsub B off))) then
                            mcheck k (read_post S i o (o + chi) (argl S 2)) M (FSOpenLB (ladd off (argl S 2)) B) sh a
                          else None
            | None => None
            end
          else None
      | _ => None
      end
  | MJoinS body jpc shj k =>
      match mcheck body S M FS sh a with
      | Some fb =>
          let J := List.filter (fun '(F, _, _, shF, _) => (Z.eqb (s_pc F) jpc && shp_ent shF shj TEmpty)%bool) fb in
          let O := List.filter (fun '(F, _, _, shF, _) => negb (Z.eqb (s_pc F) jpc && shp_ent shF shj TEmpty)%bool) fb in
          match J with
          | [] => Some O
          | (F0, M0, FS0, sh0, a0) :: Jr =>
              let n0 := max_next (List.map (fun '(F, _, _, _, _) => F) Jr) (s_next F0) in
              let P := join_fs_hull (fst (gen2 F0 (List.map (fun '(F, _, _, _, _) => F) Jr))) FS0 J in
              if (forallb (fun '(F, MF, FSF, shF, aF) => wentN n0 F MF FSF shF P FS0 sh0 && sm_eqb MF M0 && aeqb aF a0) J && state_wf P &&
                  Pos.leb (s_next S) n0 && fs_wf (s_next P) FS0 && shp_wf (s_next P) sh0 && pv_okb n0 && awf n0 a0)%bool
              then match mcheck k P M0 FS0 sh0 a0 with Some fk => Some (fk ++ O) | None => None end
              else None
          end
      | None => None
      end
  | MSplitR r c ka kb =>
      let l := rget (s_regs S) (Z.to_pos (r + 1)) in
      if lwf (s_next S) l then
        let r := irange (s_facts S) l in
        match (if Z.leb (fst r) c then mcheck ka (add_fact S (FRange l (fst r) (Z.min c (snd r)))) M FS sh a else Some []),
              (if Z.ltb c (snd r) then mcheck kb (add_fact S (FRange l (Z.max (c + 1) (fst r)) (snd r))) M FS sh a else Some []) with
        | Some f1, Some f2 => Some (f1 ++ f2)
        | _, _ => None
        end
      else None
  | MReadB b o ka kb =>
      let i := rg_index (s_rgs S) b O in
      match FS with
      | FSOpen off FL =>
          if (negb dr && is_ecall t (s_pc S))%bool then
            match read_args_ok S i o with
            | Some chi =>
                let c := argl S 2 in
                let rem := lsub FL off in
                let '(lo, hi) := irange (s_facts S) rem in
                let '(clo, _) := irange (s_facts S) c in
                match (if Z.leb lo chi then mcheck ka (add_fact (read_post S i o (o + chi) rem) (FRange (lsub c rem) 0 65536)) M (FSOpen FL FL) sh a else Some []),
                      (if Z.ltb clo hi then mcheck kb (add_fact (read_post S i o (o + chi) c) (FRange (lsub rem c) 1 hi)) M (FSOpen (ladd off c) FL) sh a
                       else Some []) with
                | Some f1, Some f2 => if (Z.leb 0 lo && Z.ltb hi 4611686018427387904 && Z.ltb (snd (irange (s_facts S) off) + chi) FLT)%bool then Some (f1 ++ f2) else None
                | _, _ => None
                end
            | None => None
            end
          else None
      | _ => None
      end
  | MReadHB b o k ka kb =>
      let i := rg_index (s_rgs S) b O in
      match FS, hv with
      | FSOpen off FL, Some h =>
          if (negb dr && is_ecall t (s_pc S) && lin_eqb off (lconst 0) && Pos.leb (dvar h 16) (s_next S) && Nat.leb k 16)%bool then
            match read_args_ok S i o with
            | Some chi =>
                let c := argl S 2 in
                let rem := lsub FL off in
                let '(lo, hi) := irange (s_facts S) rem in
                let '(clo, _) := irange (s_facts S) c in
                match (if Z.leb lo chi then if Z.leb (Z.of_nat k) lo then mcheck ka (track_hdr (add_fact (read_post S i o (o + chi) rem) (FRange (lsub c rem) 0 65536)) i o h k) M (FSOpen FL FL) sh a else None else Some []),
                      (if Z.ltb clo hi then if Z.leb (Z.of_nat k) clo then mcheck kb (track_hdr (add_fact (read_post S i o (o + chi) c) (FRange (lsub rem c) 1 hi)) i o h k) M (FSOpen (ladd off c) FL) sh a else None
                       else Some []) with
                | Some f1, Some f2 => if (Z.leb 0 lo && Z.ltb hi 4611686018427387904 && Z.ltb (snd (irange (s_facts S) off) + chi) FLT)%bool then Some (f1 ++ f2) else None
                | _, _ => None
                end
            | None => None
            end
          else None
      | _, _ => None
      end
  | MSelB ka kb =>
      match sh with
      | ShBit l j sa sb =>
          if Z.leb 0 j then
            match lowb (s_facts S) l (j + 1) with
            | Some r => if Z.testbit r j then mcheck ka S M FS sa a else mcheck kb S M FS sb a
            | None => None
            end
          else None
      | _ => None
      end
  | MJoinL body jpc k =>
      match mcheck body S M FS sh a with
      | Some fb =>
          let J := List.filter (fun '(F, _, _, _, _) => Z.eqb (s_pc F) jpc) fb in
          let O := List.filter (fun '(F, _, _, _, _) => negb (Z.eqb (s_pc F) jpc)) fb in
          match J with
          | [] => Some O
          | (F0, M0, FS0, sh0, a0) :: Jr =>
              let n0 := max_next (List.map (fun '(F, _, _, _, _) => F) Jr) (s_next F0) in
              match genLA (List.map (fun '(F, MF, _, _, _) => (F, MF)) J) (List.map (fun '(_, _, _, _, aF) => alins aF) J) with
              | Some (P0, MP, als) =>
                  let P := join_fs_hull P0 FS0 J in
                  let aP := aset a0 als in
                  if (forallb (fun '(F, MF, FSF, shF, aF) => let σ := matchLA F MF (alins aF) P MP (alins aP) in
                                 entails F P σ && fixed_below σ n0 && Pos.leb (s_next F) n0 && fs_ent FSF FS0 σ && shp_ent shF sh0 σ &&
                                 sm_eqbm σ MP MF && aeqb (asub σ aP) aF) J &&
                      state_wf P && sm_wf (s_next P) MP && Pos.leb n0 (s_next P) && agok MP aP &&
                      Pos.leb (s_next S) n0 && fs_wf (s_next P) FS0 && shp_wf (s_next P) sh0 && pv_okb n0 && awf (s_next P) aP)%bool
                  then match mcheck k P MP FS0 sh0 aP with Some fk => Some (fk ++ O) | None => None end
                  else None
              | None => None
              end
          end
      | None => None
      end
  | MGc nk xs k => mcheck k (gc_post nk (xs ++ List.concat (List.map lin_vars (alins a))) S M FS sh) M FS sh a
  | MLoopW0 zk body ks =>
      match mcheck body S M FS sh a with
      | Some fb1 =>
          match List.find (fun '(F, _, _, _, _) => Z.eqb (s_pc F) (s_pc S)) fb1 with
          | Some (F1, _, FS1, sh1, _) =>
              match wgen false S F1 FS FS1 sh sh1 zk with
              | Some (P0, n0, FP, shP, meas) =>
      (* [comment removed for export] *)
      let P := P0 in
      if (went n0 S M FS sh P FP shP && fs_wf (s_next P) FP && shp_wf (s_next P) shP && pv_okb n0 && lwf (s_next P) meas &&
                    meas_ok (s_facts P) meas && awf n0 a)%bool then
                  match mcheck body P M FP shP a with
                  | Some fb => all_some (fun '(F, MF, FSF, shF, aF) =>
                                  if Z.eqb (s_pc F) (s_pc P) then
                                    let σ := match_st F P in
                                    if (ent_okN σ n0 F P MF && fs_ent FSF FP σ && shp_ent shF shP σ && sm_eqb MF M && aeqb aF a && lmeas_dec F σ meas)%bool
                                    then Some [] else None
                                  else if Pos.leb n0 (s_next F) then mfind ks F MF FSF shF aF else None) fb
                  | None => None
                  end
                else None
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | MLoopG gen body ks =>
      match mcheck body S M FS sh a with
      | Some fb1 =>
          match List.find (fun '(F, _, _, _, _) => Z.eqb (s_pc F) (s_pc S)) fb1 with
          | Some (F1, _, FS1, sh1, _) =>
              match gen S F1 FS FS1 sh sh1 with
              | Some (P0, n0, FP, shP, meas) =>
      (* [comment removed for export] *)
      let P := P0 in
      if (went n0 S M FS sh P FP shP && fs_wf (s_next P) FP && shp_wf (s_next P) shP && pv_okb n0 && lwf (s_next P) meas &&
                    meas_ok (s_facts P) meas && awf n0 a)%bool then
                  match mcheck body P M FP shP a with
                  | Some fb => all_some (fun '(F, MF, FSF, shF, aF) =>
                                  if Z.eqb (s_pc F) (s_pc P) then
                                    let σ := match_st F P in
                                    if (ent_okN σ n0 F P MF && fs_ent FSF FP σ && shp_ent shF shP σ && sm_eqb MF M && aeqb aF a && lmeas_dec F σ meas)%bool
                                    then Some [] else None
                                  else if Pos.leb n0 (s_next F) then mfind ks F MF FSF shF aF else None) fb
                  | None => None
                  end
                else None
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | MUse j nb k =>
      match nth_error subs j with
      | Some (T, MT, aT, fins) =>
          let σ := matchLA S M (alins a) T MT (alins aT) in
          if (entails S T σ && state_wf T && sm_wf (s_next T) MT && agok MT aT && sm_eqbm σ MT M && aeqb (asub σ aT) a &&
              Pos.leb nb (s_next T) && Pos.leb nb (s_next S) && fixed_below σ nb && use_bwf σ nb (s_next T) (s_next S) &&
              awf (s_next T) aT)%bool then
            all_some (fun '(F, MF, aF) =>
              let σ' := use_sig σ nb (s_next T) (s_next F) (s_next S) in
              let nx := use_next nb (s_next F) (s_next S) in
              if (Pos.leb (s_next T) (s_next F) && awf nx (asub σ' aF) && marks_ok σ' (sm_maps MF))%bool
              then mcheck k (ssubst σ' nx F) (msubst σ' MF) FS sh (asub σ' aF) else None) fins
          else None
      | None => None
      end
  | MCont j nb =>
      match nth_error conts j with
      | Some (T, MT, FST, shT, aT) =>
          let σ := matchLA S M (alins a) T MT (alins aT) in
          if (entails S T σ && state_wf T && sm_wf (s_next T) MT && agok MT aT && sm_eqbm σ MT M && aeqb (asub σ aT) a &&
              fixed_below σ nb && Pos.leb nb (s_next T) && pv_okb nb && fs_ent FS FST σ && fs_wf (s_next T) FST &&
              shp_ent sh shT σ && shp_wf (s_next T) shT && awf (s_next T) aT)%bool
          then Some [] else None
      | None => None
      end
  | MJoinG gen body jpc k =>
      match mcheck body S M FS sh a with
      | Some fb =>
          let J := List.filter (fun '(F, _, _, _, _) => Z.eqb (s_pc F) jpc) fb in
          let O := List.filter (fun '(F, _, _, _, _) => negb (Z.eqb (s_pc F) jpc)) fb in
          match J with
          | [] => Some O
          | (F0, M0, FS0, sh0, a0) :: Jr =>
              let n0 := max_next (List.map (fun '(F, _, _, _, _) => F) Jr) (s_next F0) in
              match gen (List.map (fun '(F, MF, _, _, _) => (F, MF)) J) (List.map (fun '(_, _, _, _, aF) => alins aF) J) with
              | Some (P0, MP, als) =>
                  let P := join_fs_hull P0 FS0 J in
                  let aP := aset a0 als in
                  if (forallb (fun '(F, MF, FSF, shF, aF) => let σ := matchLA F MF (alins aF) P MP (alins aP) in
                                 entails F P σ && fixed_below σ n0 && Pos.leb (s_next F) n0 && fs_ent FSF FS0 σ && shp_ent shF sh0 σ &&
                                 sm_eqbm σ MP MF && aeqb (asub σ aP) aF) J &&
                      state_wf P && sm_wf (s_next P) MP && Pos.leb n0 (s_next P) && agok MP aP &&
                      Pos.leb (s_next S) n0 && fs_wf (s_next P) FS0 && shp_wf (s_next P) sh0 && pv_okb n0 && awf (s_next P) aP)%bool
                  then match mcheck k P MP FS0 sh0 aP with Some fk => Some (fk ++ O) | None => None end
                  else None
              | None => None
              end
          end
      | None => None
      end
  | MBlobNil i k =>
      let M' := with_maps M (ins_mark i (lvar (s_next S)) (sm_maps M)) in
      if nomark (sm_maps M) &&& amod M M' a
      then mcheck k (add_fact (bump S (Pos.succ (s_next S))) (FRange (lvar (s_next S)) 4096 4096)) M' FS sh a else None
  | MBlobAdd i k =>
      match blobadd LIMIT (segments_reserved segs) S M i with
      | Some (S', M') => if amod M M' a then mcheck k S' M' FS sh a else None
      | None => None
      end
  | MAllowW j z k =>
      let M' := with_allow M (widen_nth j z (sm_allow M)) in
      if widen_ok LIMIT S M j z &&& amod M M' a then mcheck k S M' FS sh a else None
  | MRgFront i k => mcheck k (with_rgs' S (nth_front i (s_rgs S))) M FS sh a
  | MAllowFront i k =>
      let M' := with_allow M (nth_front i (sm_allow M)) in
      if front_ok LIMIT S M i &&& amod M M' a then mcheck k S M' FS sh a else None
  | MRegEq tq k => if lwf (s_next S) tq then mcheck k (regeqv S tq) M FS sh a else None
  end
with mfind (ks : @mks N) (L : sst) (M : smodel) (FS : fstate) (sh : shp) (a : A) : option (list (sst * smodel * fstate * shp * A)) :=
  match ks with
  | KNil => Some [(L, M, FS, sh, a)]
  | KCons b sys k r => if (Z.eqb b (s_pc L) && (Z.eqb sys 0 || match a7c L with Some c => Z.eqb c sys | None => false end))%bool
                       then mcheck k L M FS sh a else mfind r L M FS sh a
  end.
End Check.

(* [comment removed for export] *)
Lemma read_cstr_aux_ok : forall mp (bs : list byte) a k,
  (length bs < k)%nat -> Forall (fun b => b <> Z_to_bv 8 0) bs ->
  (forall j, (j <= length bs)%nat -> mp (woff a j) = Some (nth j (bs ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))) ->
  read_cstr_aux mp a k = CstrOk bs.
Proof.
  intros mp bs. induction bs as [|b bs IH]; intros a k Hk Hnz Hm; destruct k as [|k]; cbn [length] in Hk; try lia; cbn [read_cstr_aux].
  - rewrite <- (woff_0 a). rewrite (Hm O ltac:(cbn; lia)). cbn [nth app]. rewrite bv_eqb_refl. reflexivity.
  - rewrite <- (woff_0 a). rewrite (Hm O ltac:(cbn; lia)). cbn [nth app].
    inversion Hnz as [|? ? Hb Hnz']; subst.
    destruct (bv_eqb b (Z_to_bv 8 0)) eqn:Eb; [apply bv_eqb_eq in Eb; exfalso; exact (Hb Eb)|].
    rewrite woff_0. rewrite (IH (a + 1)%bv k ltac:(lia) Hnz'); [reflexivity|].
    intros j Hj. rewrite woff_succ. exact (Hm (Datatypes.S j) ltac:(cbn; lia)).
Qed.

Section Sound.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable t : tree xi.
Variable img : tree Z.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegb : segs_below_b segs 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hfs : sc_fs cfg = true.
Hypothesis Hrespos : Forall (fun p => 0 < bv_unsigned (snd p)) (segments_reserved segs).
Hypothesis Hreswf : ivs_wf (segments_reserved segs).
Hypothesis Ht : tbl_ok segs t.
Hypothesis Himg : img_ok segs img.
Hypothesis Hect : ecall_ok segs t.
Variables (pv : lin) (path0 : path) (data0 : list byte) (fs0 : Fs.Fs) (FLlo FLhi : Z).
Variable argv0 : list byte.   (* [comment removed for export] *)
Variable dr : bool.   (* [comment removed for export] *)
Variable hv : option positive.   (* [comment removed for export] *)
Hypothesis Hp1 : path_eqb path0 [] = false.
Hypothesis Hp2 : path_has_slash path0 = false.
Hypothesis Hp3 : dr = false -> path_is_dirref path0 = false.
Hypothesis Hp4 : (length path0 < path_max)%nat.
Hypothesis Hp5 : Forall (fun b => b <> Z_to_bv 8 0) path0.
(* [comment removed for export] *)
Hypothesis HFL : FLlo <= Z.of_nat (length data0) /\ (FLlo <= FLhi -> FLhi < FLT -> Z.of_nat (length data0) <= FLhi).
Hypothesis HFLhi : FLhi < 4611686018427387904.
(* [comment removed for export] *)
Definition flen : Z := flen_of (length data0).
#[using="path0 Hp4"] Lemma flen_le : flen <= Z.of_nat (length data0). Proof. LiaFast.lf_pins (fun (path0 Hp4 : LiaFast.U) => LiaFast.u0). unfold flen, flen_of. lia. Qed.
#[using="path0 Hp4"] Lemma flen_range : 0 <= flen <= FLT. Proof. LiaFast.lf_pins (fun (path0 Hp4 : LiaFast.U) => LiaFast.u0). unfold flen, flen_of, FLT. lia. Qed.
#[using="path0 Hp4"] Lemma flen_exact : flen < FLT -> flen = Z.of_nat (length data0). Proof. LiaFast.lf_pins (fun (path0 Hp4 : LiaFast.U) => LiaFast.u0). unfold flen, flen_of. lia. Qed.
#[using="path0 Hp4 HFL HFLhi"] Lemma flen_class : FLlo <= FLhi -> FLlo <= flen <= FLhi.
Proof. LiaFast.lf_pins (fun (path0 Hp4 HFL HFLhi : LiaFast.U) => LiaFast.u0). intros H. destruct HFL as [H1 H2]. unfold flen, flen_of, FLT in *. lia. Qed.
(* [comment removed for export] *)
Hypothesis Hseg : forall x, 0x10000 <= x < 0x61a000 -> find_segment segs x 1 <> None.

(* [comment removed for export] *)
Context {N A : Type}.
Variable apost : N -> sst -> smodel -> A -> option (sst * smodel * A).
Variables (anil : A -> bool) (aeqb : A -> A -> bool) (awf : positive -> A -> bool).
Variable HA : valu -> smodel -> A -> (word -> option byte) -> Prop.
Variable acopy : A -> list srec.
Variable asub : tree lin -> A -> A.
Variable agok : smodel -> A -> bool.
Variable alins : A -> list lin.
Variable aset : A -> list lin -> A.
Variable amod : smodel -> smodel -> A -> bool.
Variable subs : list (sst * smodel * A * list (sst * smodel * A)).   (* [comment removed for export] *)
Variable conts : list (sst * smodel * fstate * shp * A).   (* [comment removed for export] *)
Hypothesis awf_mono : forall n n' a, (n <= n')%positive -> awf n a = true -> awf n' a = true.
Hypothesis aeqb_eq : forall x y, aeqb x y = true -> x = y.
Hypothesis HA_nil : forall E M a m0, anil a = true -> HA E M a m0.
Hypothesis HA_agree : forall n E E' M a m0, sm_wf n M = true -> awf n a = true -> agree n E E' -> HA E M a m0 -> HA E' M a m0.
(* [comment removed for export] *)
Definition frz_same (E : valu) (M : smodel) (m0 m0' : word -> option byte) : Prop :=
  forall p, In p (sm_frz M) -> forall w, uE E (fst p) <= w < uE E (fst p) + uE E (snd p) -> m0' (Z_to_bv 64 w) = m0 (Z_to_bv 64 w).
(* [comment removed for export] *)
Definition anode_ok (nk : N) : Prop :=
  forall S M a S' M' a', apost nk S M a = Some (S', M', a') ->
  forall model0 mem0 E ms model T, DEN segs LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN segs LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Hypothesis Hanode : forall nk, anode_ok nk.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sarg (j : nat) : list byte := match j with O => argv0 | _ => path0 end.
(* [comment removed for export] *)
Hypothesis HA_copy : forall E M a m0, HA E M a m0 -> Forall (sbytes_ok sarg E m0) (acopy a).
(* [comment removed for export] *)
Hypothesis HA_msub : forall E σ M a m0, agok M a = true -> HA E (msubst σ M) (asub σ a) m0 -> HA (ecomp E σ) M a m0.
(* [comment removed for export] *)
Hypothesis HA_mod : forall E M M' a m0, amod M M' a = true -> HA E M a m0 -> HA E M' a m0.
(* [comment removed for export] *)
Definition sub_ok (T : sst) (MT : smodel) (aT : A) (fins : list (sst * smodel * A)) : Prop :=
  forall model0 mem0 E ms model (Tg : TSet), DEN segs LIMIT model0 mem0 E T MT ms model -> awf (s_next T) aT = true -> HA E MT aT mem0 ->
  (forall F MF aF mem0' E' ms' model', In (F, MF, aF) fins -> DEN segs LIMIT model0 mem0' E' F MF ms' model' ->
     awf (s_next F) aF = true -> HA E' MF aF mem0' -> agree (s_next T) E E' -> frz_covs E MT E' MF -> frz_same E MT mem0 mem0' ->
     realizes_cfg segs cfg (mkCfg ms' model') Tg) ->
  realizes_cfg segs cfg (mkCfg ms model) Tg.
Hypothesis HMUse : forall j T MT aT fins, nth_error subs j = Some (T, MT, aT, fins) -> sub_ok T MT aT fins.
(* [comment removed for export] *)
Hypothesis HA_use : subs <> [] -> forall E σ M a m0, HA (ecomp E σ) M a m0 -> HA E (msubst σ M) (asub σ a) m0.
Definition src_bytes (E : valu) (s : src) : list byte :=
  match s with
  | SLit bs => List.map (Z_to_bv 8) bs
  | SArgs pre j lj suf => List.map (Z_to_bv 8) pre ++ firstn (Z.to_nat (uE E lj)) (sarg j) ++ List.map (Z_to_bv 8) suf
  end.
Definition pend_evs (E : valu) (p : pend) : list event :=
  List.map (WriteEv (Z_to_bv 64 (pd_ch p))) (skipn (Z.to_nat (uE E (pd_off p))) (src_bytes E (pd_src p))).
#[using="Type"] Lemma pend_wf_off : forall n p, pend_wf n p = true -> lwf n (pd_off p) = true.
Proof. LiaFast.lf_pins LiaFast.u0. intros n [ch [bs|pre j lj suf] off] H; cbn [pend_wf pd_src pd_off] in *; [exact H|]. apply andb_prop in H as [H _]. exact H. Qed.
#[using="Type"] Lemma pend_wf_mono : forall n n' p, (n <= n')%positive -> pend_wf n p = true -> pend_wf n' p = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n n' [ch [bs|pre j lj suf] off] Hle H; cbn [pend_wf pd_src pd_off] in *; [exact (lwf_mono _ _ _ Hle H)|].
  apply andb_prop in H as [H1 H2]. rewrite (lwf_mono _ _ _ Hle H1), (lwf_mono _ _ _ Hle H2). reflexivity.
Qed.
#[using="Type"] Lemma pend_evs_agree : forall n E E' p, pend_wf n p = true -> agree n E E' -> pend_evs E' p = pend_evs E p.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n E E' [ch [bs|pre j lj suf] off] Hw Ha; cbn [pend_wf pd_src pd_off] in Hw; unfold pend_evs; cbn [pd_src pd_off pd_ch src_bytes]; unfold uE.
  - rewrite (lden_agree_wf n E E' _ Hw Ha). reflexivity.
  - apply andb_prop in Hw as [Hw1 Hw2]. rewrite (lden_agree_wf n E E' _ Hw1 Ha), (lden_agree_wf n E E' _ Hw2 Ha). reflexivity.
Qed.
#[using="Type"] Lemma src_ent_bytes : forall E s s' σ, src_ent s s' σ = true -> src_bytes (ecomp E σ) s' = src_bytes E s.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E [x|p j l s] [y|p' j' l' s'] σ H; cbn [src_ent] in H; try discriminate; cbn [src_bytes].
  - apply zlist_eqb_eq in H. subst. reflexivity.
  - apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply zlist_eqb_eq in H1, H4. apply Nat.eqb_eq in H2. apply lin_eqb_eq in H3. subst p' j' s'.
    unfold uE. rewrite <- lden_lsubst, <- H3. reflexivity.
Qed.
Fixpoint shp_den (E : valu) (sh : shp) : TSet :=
  match sh with
  | ShEmit po kc => t_emit (concat (List.map (pend_evs E) po)) (t_exit (Z_to_bv 64 kc) fs0)
  | ShAlt2 a b => t_alt2 (shp_den E a) (shp_den E b)
  | ShIf l lo hi a b => if (Z.leb lo (uE E l) && Z.leb (uE E l) hi)%bool then shp_den E a else shp_den E b
  | ShBit l j a b => if Z.testbit (uE E l) j then shp_den E a else shp_den E b
  end.

#[using="Type"] Lemma shp_den_agree : forall n E E' sh, shp_wf n sh = true -> agree n E E' -> shp_den E' sh = shp_den E sh.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n E E' sh. induction sh as [po kc|a IHa b IHb|l lo hi a IHa b IHb|l jb a IHa b IHb]; intros Hw Ha; cbn [shp_den shp_wf] in *.
  - f_equal. f_equal. apply map_ext_in. intros p Hp. rewrite forallb_forall in Hw. specialize (Hw p Hp).
    exact (pend_evs_agree n E E' p Hw Ha).
  - apply andb_prop in Hw as [Hw1 Hw2]. rewrite (IHa Hw1 Ha), (IHb Hw2 Ha). reflexivity.
  - apply andb_prop in Hw as [Hw Hw2]. apply andb_prop in Hw as [Hwl Hw1].
    unfold uE. rewrite (lden_agree_wf n E E' _ Hwl Ha), (IHa Hw1 Ha), (IHb Hw2 Ha). reflexivity.
  - apply andb_prop in Hw as [Hw Hw2]. apply andb_prop in Hw as [Hwl Hw1].
    unfold uE. rewrite (lden_agree_wf n E E' _ Hwl Ha), (IHa Hw1 Ha), (IHb Hw2 Ha). reflexivity.
Qed.
#[using="Type"] Lemma shp_den_ent : forall E sh shP σ, shp_ent sh shP σ = true -> shp_den (ecomp E σ) shP = shp_den E sh.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E sh. induction sh as [po kc|a IHa b IHb|l lo hi a IHa b IHb|l jb a IHa b IHb]; intros [po' kc'|a' b'|l' lo' hi' a' b'|l' jb' a' b'] σ He; cbn [shp_ent] in He;
    try discriminate; cbn [shp_den].
  - apply andb_prop in He as [Hk Hp]. apply Z.eqb_eq in Hk. subst kc'. f_equal. f_equal.
    revert po' Hp. induction po as [|p po IH]; intros [|q po'] Hp; cbn in Hp; try discriminate; [reflexivity|].
    apply andb_prop in Hp as [Hq Hr]. cbn [List.map concat]. f_equal; [|exact (IH po' Hr)].
    unfold pend_ent in Hq. apply andb_prop in Hq as [Hq Ho]. apply andb_prop in Hq as [Hc Hs]. apply Z.eqb_eq in Hc.
    apply lin_eqb_eq in Ho. unfold pend_evs, uE. rewrite Hc, (src_ent_bytes E _ _ σ Hs), Ho, lden_lsubst. reflexivity.
  - apply andb_prop in He as [H1 H2]. rewrite (IHa a' σ H1), (IHb b' σ H2). reflexivity.
  - apply andb_prop in He as [He H2]. apply andb_prop in He as [He H1]. apply andb_prop in He as [He Hh]. apply andb_prop in He as [Hl Hlo].
    apply lin_eqb_eq in Hl. apply Z.eqb_eq in Hlo, Hh. subst lo' hi'. unfold uE. rewrite <- lden_lsubst, <- Hl.
    rewrite (IHa a' σ H1), (IHb b' σ H2). reflexivity.
  - apply andb_prop in He as [He H2]. apply andb_prop in He as [He H1]. apply andb_prop in He as [Hl Hj].
    apply lin_eqb_eq in Hl. apply Z.eqb_eq in Hj. subst jb'. unfold uE. rewrite <- lden_lsubst, <- Hl.
    rewrite (IHa a' σ H1), (IHb b' σ H2). reflexivity.
Qed.

#[using="Type"] Lemma fd_lookup_filter_other : forall T fd fd', fd <> fd' ->
  fd_lookup (List.filter (fun p => negb (bv_eqb (fst p) fd)) T) fd' = fd_lookup T fd'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros T fd fd' Hne. induction T as [|[k e] r IH]; [reflexivity|]. cbn [List.filter fst].
  destruct (bv_eqb k fd) eqn:Ek; cbn [negb fd_lookup].
  - apply bv_eqb_eq in Ek. subst k. destruct (bv_eqb fd fd') eqn:E2; [apply bv_eqb_eq in E2; exfalso; exact (Hne E2) | exact IH].
  - destruct (bv_eqb k fd'); [reflexivity | exact IH].
Qed.
#[using="Type"] Lemma fd_lookup_insert_same : forall T fd e, fd_lookup (fd_insert T fd e) fd = Some e.
Proof. LiaFast.lf_pins LiaFast.u0. intros T fd e. unfold fd_insert. cbn [fd_lookup]. rewrite bv_eqb_refl. reflexivity. Qed.
#[using="Type"] Lemma fd_lookup_insert_other : forall T fd fd' e, fd <> fd' -> fd_lookup (fd_insert T fd e) fd' = fd_lookup T fd'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros T fd fd' e Hne. unfold fd_insert. cbn [fd_lookup].
  destruct (bv_eqb fd fd') eqn:E1; [apply bv_eqb_eq in E1; exfalso; exact (Hne E1)|]. exact (fd_lookup_filter_other T fd fd' Hne).
Qed.
#[using="Type"] Lemma fd_lookup_remove_other : forall T fd fd', fd <> fd' -> fd_lookup (fd_remove T fd) fd' = fd_lookup T fd'.
Proof. LiaFast.lf_pins LiaFast.u0. intros T fd fd' Hne. unfold fd_remove. exact (fd_lookup_filter_other T fd fd' Hne). Qed.
#[using="Type"] Lemma w3_ne1 : Z_to_bv 64 3 <> Z_to_bv 64 1. Proof. LiaFast.lf_pins LiaFast.u0. intros H. apply (f_equal bv_unsigned) in H. discriminate. Qed.
#[using="Type"] Lemma w3_ne2 : Z_to_bv 64 3 <> Z_to_bv 64 2. Proof. LiaFast.lf_pins LiaFast.u0. intros H. apply (f_equal bv_unsigned) in H. discriminate. Qed.

#[using="path0 data0 Hp4"] Lemma length_file_read : forall data (off count : word), bv_unsigned off <= Z.of_nat (length data) ->
  Z.of_nat (length (file_read data off count)) = Z.min (bv_unsigned count) (Z.of_nat (length data) - bv_unsigned off).
Proof. LiaFast.lf_pins (fun (path0 data0 Hp4 : LiaFast.U) => LiaFast.u0).
  intros data off count Ho. rewrite file_read_unguarded. rewrite length_firstn, length_skipn. unfold word_to_nat.
  pose proof (bv_unsigned_in_range _ off). pose proof (bv_unsigned_in_range _ count). lia.
Qed.

#[using="path0 data0 Hp4"] Lemma cstr_access_len_ok : forall mp (bs : list byte) a k,
  (length bs < k)%nat -> Forall (fun b => b <> Z_to_bv 8 0) bs ->
  (forall j, (j <= length bs)%nat -> mp (woff a j) = Some (nth j (bs ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))) ->
  cstr_access_len_aux mp a k = Datatypes.S (length bs).
Proof. LiaFast.lf_pins (fun (path0 data0 Hp4 : LiaFast.U) => LiaFast.u0).
  intros mp bs. induction bs as [|b bs IH]; intros a k Hk Hnz Hm; destruct k as [|k]; cbn [length] in Hk; try lia; cbn [cstr_access_len_aux].
  - rewrite <- (woff_0 a). rewrite (Hm O ltac:(cbn; lia)). cbn [nth app]. rewrite bv_eqb_refl. reflexivity.
  - rewrite <- (woff_0 a). rewrite (Hm O ltac:(cbn; lia)). cbn [nth app].
    inversion Hnz as [|? ? Hb Hnz']; subst.
    destruct (bv_eqb b (Z_to_bv 8 0)) eqn:Eb; [apply bv_eqb_eq in Eb; exfalso; exact (Hb Eb)|].
    rewrite woff_0. rewrite (IH (a + 1)%bv k ltac:(lia) Hnz'); [reflexivity|].
    intros j Hj. rewrite woff_succ. exact (Hm (Datatypes.S j) ltac:(cbn; lia)).
Qed.

#[using="data0 FLlo FLhi HFL"] Lemma t_alt2_same : forall T, t_eq (t_alt2 T T) T.
Proof. LiaFast.lf_pins (fun (data0 FLlo FLhi HFL : LiaFast.U) => LiaFast.u0). intros T tr. unfold t_alt2. tauto. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hv_inv (E : valu) (S : sst) : Prop :=
  match hv with
  | None => True
  | Some h => (dvar h 18 <= s_next S)%positive /\
              (forall i, (i < 16)%nat -> (i < length data0)%nat -> E (dvar h i) = Z_to_bv 64 (bv_unsigned (nth i data0 (Z_to_bv 8 0)))) /\
              bv_unsigned (E (dvar h 16)) = flen /\    (* [comment removed for export] *)
              bv_unsigned (E (dvar h 17)) = Z.of_nat (length path0)        (* [comment removed for export] *)
  end.
#[using="path0 data0 Hp4"] Lemma dvar_lt : forall h i j, (i < j)%nat -> (dvar h i < dvar h j)%positive.
Proof. LiaFast.lf_pins (fun (path0 data0 Hp4 : LiaFast.U) => LiaFast.u0). intros h i j H. unfold dvar. apply Pos2Nat.inj_lt. rewrite !Nat2Pos.id by lia. lia. Qed.
#[using="Hp4"] Lemma hv_inv_agree : forall n E E' S S', hv_inv E S -> agree n E E' -> hv_okb hv n = true -> (n <= s_next S')%positive -> hv_inv E' S'.
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros n E E' S S' Hi Ha Hok Hle. unfold hv_inv, hv_okb in *. destruct hv as [h|]; [|exact I].
  apply Pos.leb_le in Hok. destruct Hi as (H1 & H2 & H3 & H4). split; [lia|]. split; [|split].
  - intros i Hi Hl. rewrite <- (Ha (dvar h i) ltac:(pose proof (dvar_lt h i 18 ltac:(lia)); lia)). exact (H2 i Hi Hl).
  - rewrite <- (Ha (dvar h 16) ltac:(pose proof (dvar_lt h 16 18 ltac:(lia)); lia)). exact H3.
  - rewrite <- (Ha (dvar h 17) ltac:(pose proof (dvar_lt h 17 18 ltac:(lia)); lia)). exact H4.
Qed.
#[using="Hp4"] Lemma flv_ok : forall E S, hv_inv E S -> forall v, bv_unsigned v = flen ->
  lwf (Pos.succ (s_next S)) (flv hv S) = true /\ bv_unsigned (lden (upd E (s_next S) v) (flv hv S)) = flen.
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros E S H v Hv. unfold flv, hv_inv in *. destruct hv as [h|].
  - destruct H as (H1 & _ & H3 & _). pose proof (dvar_lt h 16 18 ltac:(lia)) as Hlt. split.
    + unfold lwf, lvar. cbn. rewrite andb_true_r. apply Pos.ltb_lt. lia.
    + rewrite lden_lvar. unfold upd. destruct (Pos.eqb_spec (dvar h 16) (s_next S)) as [He|Hne]; [lia|]. exact H3.
  - split.
    + unfold lwf, lvar. cbn. rewrite andb_true_r. apply Pos.ltb_lt. lia.
    + rewrite lden_lvar. unfold upd. rewrite Pos.eqb_refl. exact Hv.
Qed.
#[using="Type"] Lemma hv_inv_ok : forall E S, hv_inv E S -> hv_okb hv (s_next S) = true.
Proof. LiaFast.lf_pins LiaFast.u0. intros E S H. unfold hv_inv, hv_okb in *. destruct hv as [h|]; [|reflexivity]. apply Pos.leb_le. exact (proj1 H). Qed.
#[using="Hp4"] Lemma hv_inv_step : forall E E' S S', hv_inv E S -> agree (s_next S) E E' -> (s_next S <= s_next S')%positive -> hv_inv E' S'.
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0). intros E E' S S' Hi Ha Hle. exact (hv_inv_agree (s_next S) E E' S S' Hi Ha (hv_inv_ok E S Hi) Hle). Qed.

Definition INV (mem0 : word -> option byte) (E : valu) (S : sst) (M : smodel) (FS : fstate) (model0 : Model) : Prop :=
  lwf (s_next S) pv = true /\ fs_wf (s_next S) FS = true /\
  (dr = false -> forall k, (k <= length path0)%nat -> exists p, In p (sm_frz M) /\
     uE E (fst p) <= bv_unsigned (lden E pv) + Z.of_nat k < uE E (fst p) + uE E (snd p)) /\
  ((dr = false -> forall k, (k <= length path0)%nat ->
      mem0 (Z_to_bv 64 (bv_unsigned (lden E pv) + Z.of_nat k)) = Some (nth k (path0 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))) /\
   (* [comment removed for export] *)
   (dr = false -> forall w, bv_unsigned (lden E pv) <= w < 8 * ((bv_unsigned (lden E pv) + Z.of_nat (length path0)) / 8 + 1) ->
      (exists p, In p (sm_frz M) /\ uE E (fst p) <= w < uE E (fst p) + uE E (snd p)) /\ mem0 (Z_to_bv 64 w) <> None)) /\
  bv_unsigned (lden E pv) + Z.of_nat (length path0) < 0x800000000000 /\
  (dr = false -> fs_lookup (m_fs model0) path0 = Some data0) /\ m_fs model0 = fs0 /\
  match FS with
  | FSClosed => alloc_fd (m_fds model0) = Z_to_bv 64 3 /\ fd_lookup (m_fds model0) (Z_to_bv 64 3) = None
  | FSOpen off FL => fd_lookup (m_fds model0) (Z_to_bv 64 3) = Some (FdFile path0 (lden E off)) /\
                     bv_unsigned (lden E FL) = flen /\ bv_unsigned (lden E off) <= flen
  | FSDone => True
  | FSDir => fd_lookup (m_fds model0) (Z_to_bv 64 3) = Some FdDir
  | FSOpenLB off B => fd_lookup (m_fds model0) (Z_to_bv 64 3) = Some (FdFile path0 (lden E off)) /\
                      bv_unsigned (lden E off) <= bv_unsigned (lden E B) /\ bv_unsigned (lden E B) <= Z.of_nat (length data0)
  end /\
  fd_lookup (m_fds model0) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) /\
  fd_lookup (m_fds model0) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) /\
  hv_inv E S.

(* [comment removed for export] *)
#[using="Hp4"] Lemma INV_agree : forall mem0 E E' S S' M M' FS model0,
  INV mem0 E S M FS model0 -> agree (s_next S) E E' -> (s_next S <= s_next S')%positive -> sm_frz M' = sm_frz M ->
  sm_wf (s_next S) M = true -> INV mem0 E' S' M' FS model0.
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros mem0 E E' S S' M M' FS model0 Hi Ha Hle Hfz Hwf.
  destruct Hi as (Hpv & Hfsw & Hfr & Hm0 & Hlen & Hlk & Hfs0 & Hfds & Hc1 & Hc2 & Hdv).
  assert (Hpv' : lden E' pv = lden E pv) by exact (lden_agree_wf _ E E' pv Hpv Ha).
  pose proof (sm_wf_frz _ M Hwf) as Hwz.
  split; [exact (lwf_mono _ _ _ Hle Hpv)|]. split.
  { destruct FS as [|off FL| | |off FL]; [reflexivity| |reflexivity|reflexivity|]; (cbn [fs_wf] in Hfsw |- *; apply andb_prop in Hfsw as [H1 H2];
    apply andb_true_intro; split; [exact (lwf_mono _ _ _ Hle H1) | exact (lwf_mono _ _ _ Hle H2)]). }
  split.
  { intros Hdr k Hk. destruct (Hfr Hdr k Hk) as (p & Hp & Hr). exists p. rewrite Hfz. split; [exact Hp|].
    rewrite Forall_forall in Hwz. destruct (Hwz p Hp) as [W1 W2]. unfold uE in *.
    rewrite (lden_agree_wf _ E E' _ W1 Ha), (lden_agree_wf _ E E' _ W2 Ha), Hpv'. exact Hr. }
  split.
  { split; [intros Hdr k Hk; rewrite Hpv'; exact (proj1 Hm0 Hdr k Hk)|].
    intros Hdr w Hw. rewrite Hpv' in Hw. destruct (proj2 Hm0 Hdr w Hw) as [(p & Hp & Hr) Hne]. split; [|exact Hne].
    exists p. rewrite Hfz. split; [exact Hp|].
    rewrite Forall_forall in Hwz. destruct (Hwz p Hp) as [W1 W2]. unfold uE in *.
    rewrite (lden_agree_wf _ E E' _ W1 Ha), (lden_agree_wf _ E E' _ W2 Ha). exact Hr. }
  split; [rewrite Hpv'; exact Hlen|]. split; [exact Hlk|]. split; [exact Hfs0|].
  split; [|split; [exact Hc1 | split; [exact Hc2 | exact (hv_inv_step E E' S S' Hdv Ha Hle)]]].
  destruct FS as [|off FL| | |off FL]; [exact Hfds| |exact I|exact Hfds|];
  cbn [fs_wf] in Hfsw; apply andb_prop in Hfsw as [W1 W2];
  rewrite (lden_agree_wf _ E E' _ W1 Ha), (lden_agree_wf _ E E' _ W2 Ha); exact Hfds.
Qed.
#[using="Type"] Lemma INV_same : forall mem0 E S S' M FS model0, INV mem0 E S M FS model0 -> s_next S' = s_next S -> INV mem0 E S' M FS model0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem0 E S S' M FS model0 Hi Hn. destruct Hi as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  split; [rewrite Hn; exact H1|]. split; [rewrite Hn; exact H2|]. repeat (split; [assumption|]).
  unfold hv_inv in *. destruct hv as [h|]; [rewrite Hn; exact H11 | exact I].
Qed.

(* [comment removed for export] *)
Definition HAX (E : valu) (S : sst) (M : smodel) (a : A) (mem0 : word -> option byte) : Prop :=
  awf (s_next S) a = true /\ HA E M a mem0.
#[using="awf_mono HA_agree"] Lemma HAX_step : forall E E' S S' M a mem0, HAX E S M a mem0 -> sm_wf (s_next S) M = true -> agree (s_next S) E E' ->
  (s_next S <= s_next S')%positive -> HAX E' S' M a mem0.
Proof. LiaFast.lf_pins (fun (awf_mono HA_agree : LiaFast.U) => LiaFast.u0). intros E E' S S' M a mem0 [Hw Hh] Hwf Ha Hle. split; [exact (awf_mono _ _ a Hle Hw) | exact (HA_agree _ E E' M a mem0 Hwf Hw Ha Hh)]. Qed.
#[using="Type"] Lemma HAX_same : forall E S S' M a mem0, HAX E S M a mem0 -> s_next S' = s_next S -> HAX E S' M a mem0.
Proof. LiaFast.lf_pins LiaFast.u0. intros E S S' M a mem0 [Hw Hh] Hn. split; [rewrite Hn; exact Hw | exact Hh]. Qed.

(* [comment removed for export] *)
Definition cont_ok (c : sst * smodel * fstate * shp * A) : Prop :=
  forall model0 mem0 E ms model, DEN segs LIMIT model0 mem0 E (fst (fst (fst (fst c)))) (snd (fst (fst (fst c)))) ms model ->
  INV mem0 E (fst (fst (fst (fst c)))) (snd (fst (fst (fst c)))) (snd (fst (fst c))) model0 ->
  HAX E (fst (fst (fst (fst c)))) (snd (fst (fst (fst c)))) (snd c) mem0 ->
  shp_wf (s_next (fst (fst (fst (fst c))))) (snd (fst c)) = true ->
  realizes_cfg segs cfg (mkCfg ms model) (shp_den E (snd (fst c))).
Hypothesis HCont : forall j c, nth_error conts j = Some c -> cont_ok c.

Definition Pm (ch : @mchain N) : Prop :=
  forall S M FS sh a finals, mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts ch S M FS sh a = Some finals ->
  forall model0 mem0 E ms model, DEN segs LIMIT model0 mem0 E S M ms model -> INV mem0 E S M FS model0 -> HAX E S M a mem0 ->
  shp_wf (s_next S) sh = true ->
  (forall S' M' FS' sh' a' model0' mem0' E' ms' model', In (S', M', FS', sh', a') finals -> DEN segs LIMIT model0' mem0' E' S' M' ms' model' ->
     INV mem0' E' S' M' FS' model0' -> HAX E' S' M' a' mem0' -> shp_wf (s_next S') sh' = true -> agree (s_next S) E E' ->
     realizes_cfg segs cfg (mkCfg ms' model') (shp_den E' sh')) ->
  realizes_cfg segs cfg (mkCfg ms model) (shp_den E sh).
Definition Qm (ks : @mks N) : Prop :=
  forall L M FS sh a finals, mfind segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts ks L M FS sh a = Some finals ->
  forall model0 mem0 E ms model, DEN segs LIMIT model0 mem0 E L M ms model -> INV mem0 E L M FS model0 -> HAX E L M a mem0 ->
  shp_wf (s_next L) sh = true ->
  (forall S' M' FS' sh' a' model0' mem0' E' ms' model', In (S', M', FS', sh', a') finals -> DEN segs LIMIT model0' mem0' E' S' M' ms' model' ->
     INV mem0' E' S' M' FS' model0' -> HAX E' S' M' a' mem0' -> shp_wf (s_next S') sh' = true -> agree (s_next L) E E' ->
     realizes_cfg segs cfg (mkCfg ms' model') (shp_den E' sh')) ->
  realizes_cfg segs cfg (mkCfg ms model) (shp_den E sh).

#[using="Type"] Lemma Qm_nil : Qm KNil.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mfind] in Hck. injection Hck as <-.
  exact (Hk L M FS sh a model0 mem0 E ms model (or_introl eq_refl) Hd Hi HX Hw (agree_refl _ _)).
Qed.
#[using="Type"] Lemma Qm_cons : forall b sys k r, Pm k -> Qm r -> Qm (KCons b sys k r).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros b sys k r IHk IHr L M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mfind] in Hck.
  destruct (Z.eqb b (s_pc L) && (Z.eqb sys 0 || match a7c L with Some c => Z.eqb c sys | None => false end))%bool;
    [exact (IHk L M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk) | exact (IHr L M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk)].
Qed.
#[using="Type"] Lemma Pm_end : Pm MEnd.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck. injection Hck as <-.
  exact (Hk S M FS sh a model0 mem0 E ms model (or_introl eq_refl) Hd Hi HX Hw (agree_refl _ _)).
Qed.

#[using="Type"] Lemma shp_wf_mono : forall n n' sh, (n <= n')%positive -> shp_wf n sh = true -> shp_wf n' sh = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n n' sh Hle. induction sh as [po kc|a IHa b IHb|l lo hi a IHa b IHb|l jb a IHa b IHb]; cbn [shp_wf]; intros Hw.
  - rewrite forallb_forall in *. intros p Hp. exact (pend_wf_mono _ _ _ Hle (Hw p Hp)).
  - apply andb_prop in Hw as [W1 W2]. rewrite (IHa W1), (IHb W2). reflexivity.
  - apply andb_prop in Hw as [W W2]. apply andb_prop in W as [W0 W1]. rewrite (lwf_mono _ _ _ Hle W0), (IHa W1), (IHb W2). reflexivity.
  - apply andb_prop in Hw as [W W2]. apply andb_prop in W as [W0 W1]. rewrite (lwf_mono _ _ _ Hle W0), (IHa W1), (IHb W2). reflexivity.
Qed.

#[using="Hwx Hsegb Hoff Hrespos Hreswf Ht Himg Hect Hp4 awf_mono HA_nil"] Lemma Pm_chain : forall c k, Pm k -> Pm (MChain c k).
Proof. LiaFast.lf_pins (fun (Hwx Hsegb Hoff Hrespos Hreswf Ht Himg Hect Hp4 awf_mono HA_nil : LiaFast.U) => LiaFast.u0).
  intros c k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (anil a) eqn:Han; [|discriminate].
  destruct (check_chain segs LIMIT t img c S M) as [fins|] eqn:Hc; [|discriminate].
  apply (chain_sound_ag segs cfg LIMIT model0 mem0 t img Hwx Hsegb Hoff Hrespos Hreswf Ht Himg Hect c S M fins Hc E ms model _ Hd).
  intros S' M' E' ms' model' Hin Hd' Ha'.
  destruct (all_some_spec _ _ _ Hck (S', M') Hin) as (o & Ho & Hsub). cbv beta in Ho.
  destruct (Pos.leb (s_next S) (s_next S') && fs_wf (s_next S') FS && frz_eqb (sm_frz M') (sm_frz M))%bool eqn:Hb; [|discriminate].
  apply andb_prop in Hb as [Hb Hfz]. apply andb_prop in Hb as [Hle Hfsw]. apply Pos.leb_le in Hle. apply frz_eqb_eq in Hfz.
  assert (Hwf : sm_wf (s_next S) M = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ Hd).
  rewrite <- (shp_den_agree (s_next S) E E' sh Hw Ha').
  apply (IH S' M' FS sh a o Ho model0 mem0 E' ms' model' Hd' (INV_agree mem0 E E' S S' M M' FS model0 Hi Ha' Hle Hfz Hwf)
           (conj (awf_mono _ _ a Hle (proj1 HX)) (HA_nil E' M' a mem0 Han)) (shp_wf_mono _ _ sh Hle Hw)).
  intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' Hx'' Hw'' Ha''.
  exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (Hsub _ Hin'') Hd'' Hi'' Hx'' Hw'' (agree_trans _ E E' E'' Ha' (agree_mono _ _ E' E'' Hle Ha''))).
Qed.

#[using="Hwx Ht Himg Hp4 awf_mono HA_agree"] Lemma Pm_segk : forall depth p ks, Qm ks -> Pm (MSegK depth p ks).
Proof. LiaFast.lf_pins (fun (Hwx Ht Himg Hp4 awf_mono HA_agree : LiaFast.U) => LiaFast.u0).
  intros depth p ks IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (bases_below (s_next S) (s_rgs S)) eqn:Hbi; [|discriminate]. rewrite bases_below_eq in Hbi.
  rewrite checkB_pos_below in Hck.
  destruct (check t img (pos_below (s_next S)) depth p S) as [Ls|] eqn:Hc; [|discriminate].
  apply (den_seg segs cfg LIMIT model0 mem0 Hwx t img (pos_below (s_next S)) depth p S Ls E M ms model _ Ht Himg Hc Hd Hbi
           (pos_below_In (s_next S))).
  intros L E' ms' model' HL Hd' Ha'.
  destruct (all_some_spec _ _ _ Hck L HL) as (o & Ho & Hsub). cbv beta in Ho.
  destruct (sm_wf (s_next L) M && Pos.leb (s_next S) (s_next L) && fs_wf (s_next L) FS)%bool eqn:Hb; [|discriminate].
  apply andb_prop in Hb as [Hb Hfsw]. apply andb_prop in Hb as [Hwl Hle]. apply Pos.leb_le in Hle.
  assert (Hwf : sm_wf (s_next S) M = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ Hd).
  rewrite <- (shp_den_agree (s_next S) E E' sh Hw Ha').
  apply (IH L M FS sh a o Ho model0 mem0 E' ms' model' Hd' (INV_agree mem0 E E' S L M M FS model0 Hi Ha' Hle eq_refl Hwf)
           (HAX_step E E' S L M a mem0 HX Hwf Ha' Hle) (shp_wf_mono _ _ sh Hle Hw)).
  intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' Hx'' Hw'' Ha''.
  exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (Hsub _ Hin'') Hd'' Hi'' Hx'' Hw'' (agree_trans _ E E' E'' Ha' (agree_mono _ _ E' E'' Hle Ha''))).
Qed.

(* [comment removed for export] *)
#[using="Hp3 Hp4 Hp5"] Lemma open_path_ok : forall mem0 model0 E S M ms model model1 FS, dr = false ->
  DEN segs LIMIT model0 mem0 E S M ms model -> DEN segs LIMIT model0 mem0 E S M ms model1 -> INV mem0 E S M FS model0 ->
  read_cstr (in_mem (sys_input segs (svc_set ms) (ms_reg ms 17))) (lden E pv) = CstrOk path0 /\
  ranges_avoid (Hof E M model1) [(lden E pv, cstr_access_len_aux (in_mem (sys_input segs (svc_set ms) (ms_reg ms 17))) (lden E pv) path_max)].
Proof. LiaFast.lf_pins (fun (Hp3 Hp4 Hp5 : LiaFast.U) => LiaFast.u0).
  intros mem0 model0 E S M ms model model1 FS Hdr Hd Hd1 Hi.
  destruct Hi as (Hpv & Hfsw & Hfr & Hm0 & Hlen & _).
  pose proof (dn_frz _ _ _ _ _ _ _ _ _ Hd) as Hfrz.
  assert (Hmp : forall j, (j <= length path0)%nat ->
            in_mem (sys_input segs (svc_set ms) (ms_reg ms 17)) (woff (lden E pv) j) = Some (nth j (path0 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))).
  { intros j Hj. destruct (Hfr Hdr j Hj) as (p & Hp & Hr). destruct (Hfrz p Hp _ Hr) as (_ & _ & Hm).
    unfold woff. cbn [in_mem sys_input]. unfold ms_read_byte. cbn [svc_set ms_mem]. rewrite Hm, (proj1 Hm0 Hdr j Hj). reflexivity. }
  split.
  - unfold read_cstr. exact (read_cstr_aux_ok _ path0 (lden E pv) path_max Hp4 Hp5 Hmp).
  - rewrite (cstr_access_len_ok _ path0 (lden E pv) path_max Hp4 Hp5 Hmp).
    apply ranges_avoid_cons; [|apply ranges_avoid_nil]. intros k Hk.
    assert (Hk' : (k <= length path0)%nat) by lia.
    destruct (Hfr Hdr k Hk') as (p & Hp & Hr). destruct (dn_frz _ _ _ _ _ _ _ _ _ Hd1 p Hp _ Hr) as (Htp & _ & _).
    unfold woff. eapply frz_hidden_false; [exact Hd1 | exact Htp].
Qed.

#[using="Hwx Hfs Hect Hp1 Hp2 Hp3 Hp4 Hp5 HFL HFLhi awf_mono HA_agree"] Lemma Pm_open : forall kerr kok, Pm kerr -> Pm kok -> Pm (MOpen kerr kok).
Proof. LiaFast.lf_pins (fun (Hwx Hfs Hect Hp1 Hp2 Hp3 Hp4 Hp5 HFL HFLhi awf_mono HA_agree : LiaFast.U) => LiaFast.u0).
  intros kerr kok IHe IHo S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct FS as [|off FL| | |off FL]; try discriminate. destruct sh as [po kc|sa sb|lq loq hiq sa sb|lq jq sa sb]; try discriminate.
  destruct (negb dr && is_ecall t (s_pc S) && open_args_ok S pv && Z.leb FLlo FLhi)%bool eqn:Hb; [|discriminate].
  apply andb_prop in Hb as [Hb Hlh]. apply Z.leb_le in Hlh. pose proof (flen_class Hlh) as HFLx. pose proof flen_range as Hflr.
  apply andb_prop in Hb as [Hb Hoa]. apply andb_prop in Hb as [Hdr Hx]. apply negb_true_iff in Hdr. apply is_ecall_ok in Hx.
  destruct (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts kerr (ret_gen S ERRLO ERRHI) M FSClosed sa a) as [f1|] eqn:H1;
    [|discriminate].
  destruct (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts kok (open_postH FLlo FLhi hv S) M (FSOpen (lconst 0) (flv hv S)) sb a) as [f2|] eqn:H2; [|discriminate].
  injection Hck as <-. cbn [shp_wf] in Hw. apply andb_prop in Hw as [Hwa Hwb]. cbn [shp_den].
  unfold open_args_ok in Hoa.
  destruct (a7c S) as [c7|] eqn:H7; [|discriminate]. destruct (arg S 0) as [c0|] eqn:H0; [|discriminate].
  destruct (arg S 2) as [fl|] eqn:H2a; [|discriminate].
  apply andb_prop in Hoa as [Hoa Hpvl]. apply andb_prop in Hoa as [Hoa Hldiff]. apply andb_prop in Hoa as [H56 Hdfd].
  apply Z.eqb_eq in H56, Hldiff. apply bv_eqb_eq in Hdfd. apply lin_eqb_eq in Hpvl. subst c7.
  pose proof Hi as Hi0.
  destruct Hi0 as (Hpv & Hfsw & Hfr & Hm0 & Hlen & Hlk & Hfs0 & (Hal & Hfree) & Hc1 & Hc2 & Hdv).
  apply (den_ecall segs cfg LIMIT model0 mem0 Hwx t E S M ms model _ Hect Hx Hd). intros model1 Hd1.
  destruct (open_path_ok mem0 model0 E S M ms model model1 FSClosed Hdr Hd Hd1 Hi) as [Hcstr Hav].
  rewrite <- Hpvl in Hcstr, Hav.
  apply (den_openat_file segs cfg LIMIT mem0 Hfs model0 E S M ms model1 _ _ c0 fl path0 data0 (Z_to_bv 64 3) Hd1 H7 H0 Hdfd H2a Hldiff
           Hcstr Hp1 Hp2 (Hp3 Hdr) (Hlk Hdr) Hal Hfree ltac:(rewrite u_small64 by (unfold two64; lia); lia) Hav).
  - intros e He ms' m'' Hd''.
    pose proof (errno_in_range e He) as Hcr.
    assert (Hc64 : 0 <= bv_unsigned (errno_ret e) < two64) by (unfold ERRLO, ERRHI, two64 in *; lia).
    pose proof (den_gen_ret segs LIMIT model0 mem0 E S M ms' m'' (bv_unsigned (errno_ret e)) ERRLO ERRHI Hd'' Hc64 Hcr) as Hd3.
    set (E1 := upd E (s_next S) (Z_to_bv 64 (bv_unsigned (errno_ret e)))) in *.
    assert (Ha : agree (s_next S) E E1) by exact (agree_upd (s_next S) E _).
    assert (Hle : (s_next S <= s_next (ret_gen S ERRLO ERRHI))%positive) by (cbn [ret_gen add_fact bump ret_post s_next]; lia).
    pose proof (dn_wf _ _ _ _ _ _ _ _ _ Hd) as Hwf0.
    rewrite <- (shp_den_agree (s_next S) E E1 sa Hwa Ha).
    apply (IHe _ _ _ _ _ f1 H1 model0 mem0 E1 ms' m'' Hd3
             (INV_agree mem0 E E1 S (ret_gen S ERRLO ERRHI) M M FSClosed model0 Hi Ha Hle eq_refl Hwf0)
             (HAX_step E E1 S (ret_gen S ERRLO ERRHI) M a mem0 HX Hwf0 Ha Hle) (shp_wf_mono _ _ sa Hle Hwa)).
    intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd''' Hi'' Hx'' Hw'' Ha''.
    exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (in_or_app _ _ _ (or_introl Hin'')) Hd''' Hi'' Hx'' Hw''
             (agree_trans _ E E1 E'' Ha (agree_mono _ _ E1 E'' Hle Ha''))).
  - intros ms' m'' Hd''.
    set (model0' := with_fds (fd_insert (m_fds model0) (Z_to_bv 64 3) (FdFile path0 (Z_to_bv 64 0))) model0) in *.
    set (E' := upd E (s_next S) (Z_to_bv 64 flen)).
    assert (Ha : agree (s_next S) E E') by exact (agree_upd (s_next S) E _).
    assert (HE' : E' (s_next S) = Z_to_bv 64 flen) by (unfold E', upd; rewrite Pos.eqb_refl; reflexivity).
    assert (HuFL : bv_unsigned (E' (s_next S)) = flen) by (rewrite HE', u_small64 by (unfold two64, FLT in *; lia); reflexivity).
    assert (Hn1 : s_next (open_postH FLlo FLhi hv S) = Pos.succ (s_next S)) by (unfold open_postH; destruct hv; reflexivity).
    assert (Hv64 : bv_unsigned (Z_to_bv 64 flen) = flen) by (rewrite u_small64 by (unfold two64, FLT in *; lia); reflexivity).
    change (lconst (bv_unsigned (Z_to_bv 64 3))) with (lconst 3) in Hd''.
    assert (Hd2 : DEN segs LIMIT model0' mem0 E' (open_postH FLlo FLhi hv S) M ms' m'').
    { assert (Hd2a : DEN segs LIMIT model0' mem0 E' (open_post FLlo FLhi S) M ms' m'').
      { unfold open_post. apply den_addfact.
        - apply den_bump; [|cbn [ret_post s_next]; lia].
          exact (den_agree segs LIMIT model0' mem0 E E' _ M ms' m'' Hd'' Ha).
        - intros E2 Ha2. cbn [fact_ok]. rewrite lden_lvar. rewrite <- (Ha2 (s_next S) ltac:(cbn [bump add_fact s_next ret_post]; lia)).
          rewrite HuFL. exact HFLx. }
      unfold open_postH. destruct hv as [h|] eqn:Hhv; [|exact Hd2a].
      apply den_addfact; [exact Hd2a|]. intros E2 Ha2. cbn [fact_ok].
      unfold hv_inv in Hdv. rewrite Hhv in Hdv. destruct Hdv as (Hdl & _ & HdL & _).
      assert (Hlt : (dvar h 16 < s_next S)%positive) by (pose proof (dvar_lt h 16 18 ltac:(lia)); lia).
      rewrite lden_lsub, !lden_lvar, bv_sub_unsigned.
      rewrite <- (Ha2 (s_next S) ltac:(cbn [bump add_fact s_next ret_post open_post]; lia)).
      rewrite <- (Ha2 (dvar h 16) ltac:(cbn [bump add_fact s_next ret_post open_post]; lia)).
      rewrite HuFL. unfold E', upd. destruct (Pos.eqb_spec (dvar h 16) (s_next S)) as [He|Hne]; [lia|]. rewrite HdL.
      rewrite Z.sub_diag. unfold bv_wrap. rewrite Z.mod_0_l; [lia|]. change (bv_modulus 64) with two64. unfold two64. lia. }
    assert (Hi' : INV mem0 E' (open_postH FLlo FLhi hv S) M (FSOpen (lconst 0) (flv hv S)) model0').
    { unfold INV. rewrite Hn1.
      split; [exact (lwf_mono (s_next S) (Pos.succ (s_next S)) pv ltac:(lia) Hpv)|]. split.
      { cbn [fs_wf]. apply andb_true_intro. split; [reflexivity|]. exact (proj1 (flv_ok E S Hdv _ Hv64)). }
      assert (Hpv' : lden E' pv = lden E pv) by exact (lden_agree_wf _ E E' pv Hpv Ha).
      pose proof (sm_wf_frz _ M (dn_wf _ _ _ _ _ _ _ _ _ Hd)) as Hwz.
      split.
      { intros Hdr' k Hk'. destruct (Hfr Hdr' k Hk') as (q & Hq & Hr). exists q. split; [exact Hq|].
        rewrite Forall_forall in Hwz. destruct (Hwz q Hq) as [W1 W2]. unfold uE in *.
        rewrite (lden_agree_wf _ E E' _ W1 Ha), (lden_agree_wf _ E E' _ W2 Ha), Hpv'. exact Hr. }
      split.
      { split; [intros Hdr' k Hk'; rewrite Hpv'; exact (proj1 Hm0 Hdr' k Hk')|].
        intros Hdr' w Hw. rewrite Hpv' in Hw. destruct (proj2 Hm0 Hdr' w Hw) as [(q & Hq & Hr) Hne]. split; [|exact Hne].
        exists q. split; [exact Hq|].
        rewrite Forall_forall in Hwz. destruct (Hwz q Hq) as [W1 W2]. unfold uE in *.
        rewrite (lden_agree_wf _ E E' _ W1 Ha), (lden_agree_wf _ E E' _ W2 Ha). exact Hr. }
      split; [rewrite Hpv'; exact Hlen|].
      split; [intros Hdr'; unfold model0'; rewrite with_fds_fs; exact (Hlk Hdr')|]. split; [unfold model0'; rewrite with_fds_fs; exact Hfs0|].
      split; [|split; [unfold model0'; rewrite with_fds_fds, fd_lookup_insert_other by (first [exact w3_ne1 | exact w3_ne2]); assumption|]].
      2: { split; [unfold model0'; rewrite with_fds_fds, fd_lookup_insert_other by (first [exact w3_ne1 | exact w3_ne2]); assumption|].
           exact (hv_inv_step E E' S (open_postH FLlo FLhi hv S) Hdv Ha ltac:(rewrite Hn1; lia)). }
      unfold model0'. rewrite with_fds_fds, fd_lookup_insert_same. rewrite lden_lconst. split; [reflexivity|]. split; [exact (proj2 (flv_ok E S Hdv _ Hv64))|].
      rewrite u_small64 by (unfold two64; lia). lia. }
    rewrite <- (shp_den_agree (s_next S) E E' sb Hwb Ha).
    apply (IHo _ _ _ _ _ f2 H2 model0' mem0 E' ms' m'' Hd2 Hi'
             (HAX_step E E' S (open_postH FLlo FLhi hv S) M a mem0 HX (dn_wf _ _ _ _ _ _ _ _ _ Hd) Ha ltac:(rewrite Hn1; lia))
             (shp_wf_mono (s_next S) (s_next (open_postH FLlo FLhi hv S)) sb ltac:(rewrite Hn1; lia) Hwb)).
    intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd''' Hi'' Hx'' Hw'' Ha''.
    exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (in_or_app _ _ _ (or_intror Hin'')) Hd''' Hi'' Hx'' Hw''
             (agree_trans _ E E' E'' Ha (agree_mono (s_next S) (s_next (open_postH FLlo FLhi hv S)) E' E'' ltac:(rewrite Hn1; lia) Ha''))).
Qed.

#[using="Type"] Lemma fd32_3 : fd32 (Z_to_bv 64 3) = Z_to_bv 64 3. Proof. LiaFast.lf_pins LiaFast.u0. apply fd32_id. rewrite u_small64 by (unfold two64; lia). lia. Qed.

#[using="Hwx Hect Hp4"] Lemma Pm_close : forall k, Pm k -> Pm (MClose k).
Proof. LiaFast.lf_pins (fun (Hwx Hect Hp4 : LiaFast.U) => LiaFast.u0).
  intros k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct FS as [|off FL| | |off FL]; try discriminate.
  all: destruct (is_ecall t (s_pc S) && close_args_ok S)%bool eqn:Hb; [|discriminate].
  all: apply andb_prop in Hb as [Hx Hca]; apply is_ecall_ok in Hx.
  all: unfold close_args_ok in Hca; destruct (a7c S) as [c7|] eqn:H7; [|discriminate]; destruct (arg S 0) as [c0|] eqn:H0; [|discriminate].
  all: apply andb_prop in Hca as [H57 H3]; apply Z.eqb_eq in H57, H3; subst c7 c0.
  all: pose proof Hi as Hi0; destruct Hi0 as (Hpv & Hfsw & Hfr & Hm0 & Hlen & Hlk & Hfs0 & (Hfd & HFL' & Hoff') & Hc1 & Hc2 & Hdv).
  all: apply (den_ecall segs cfg LIMIT model0 mem0 Hwx t E S M ms model _ Hect Hx Hd); intros model1 Hd1.
  all: apply (den_close segs cfg LIMIT mem0 model0 E S M ms model1 _ 3 (FdFile path0 (lden E off)) Hd1 H7 H0 ltac:(rewrite fd32_3; exact Hfd)).
  all: intros ms' m'' Hd''.
  all: assert (Hi' : INV mem0 E (ret_post S (lconst 0)) M FSDone (with_fds (fd_remove (m_fds model0) (fd32 (Z_to_bv 64 3))) model0))
         by (split; [exact Hpv|]; split; [reflexivity|]; split; [exact Hfr|]; split; [exact Hm0|]; split; [exact Hlen|];
             split; [intros Hdr'; rewrite with_fds_fs; exact (Hlk Hdr')|]; split; [rewrite with_fds_fs; exact Hfs0|]; split; [exact I|];
             rewrite fd32_3; split; [rewrite with_fds_fds, fd_lookup_remove_other by (first [exact w3_ne1 | exact w3_ne2]); assumption|];
             split; [rewrite with_fds_fds, fd_lookup_remove_other by (first [exact w3_ne1 | exact w3_ne2]); assumption|];
             exact (hv_inv_step E E S (ret_post S (lconst 0)) Hdv (agree_refl _ _) ltac:(cbn [ret_post s_next]; lia))).
  all: apply (IH _ _ _ _ _ finals Hck _ mem0 E ms' m'' Hd'' Hi' (HAX_same E S _ M a mem0 HX eq_refl) Hw); exact Hk.
Qed.

#[using="Hwx Hect"] Lemma Pm_ioctl : forall fd cmd k, Pm k -> Pm (MIoctl fd cmd k).
Proof. LiaFast.lf_pins (fun (Hwx Hect : LiaFast.U) => LiaFast.u0).
  intros fd cmd k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (is_ecall t (s_pc S) && ioctl_args_ok S fd cmd)%bool eqn:Hb; [|discriminate].
  apply andb_prop in Hb as [Hx Hia]. apply is_ecall_ok in Hx.
  unfold ioctl_args_ok in Hia. destruct (a7c S) as [c7|] eqn:H7; [|discriminate]. destruct (arg S 0) as [c0|] eqn:H0; [|discriminate].
  destruct (arg S 1) as [c1|] eqn:H1; [|discriminate].
  apply andb_prop in Hia as [Hia Htty]. apply andb_prop in Hia as [Hia Hc1']. apply andb_prop in Hia as [Hia H12].
  apply andb_prop in Hia as [H29 Hc0']. apply Z.eqb_eq in H29, Hc0', Hc1'. subst c7 c0 c1.
  pose proof Hi as Hi0. destruct Hi0 as (_ & _ & _ & _ & _ & _ & _ & _ & Hch1 & Hch2 & Hdv).
  assert (Hch : fd_lookup (m_fds model0) (fd32 (Z_to_bv 64 fd)) = Some (FdChannel (Z_to_bv 64 fd))).
  { apply orb_prop in H12 as [H12|H12]; apply Z.eqb_eq in H12; subst fd; rewrite fd32_id by (rewrite u_small64 by (unfold two64; lia); lia); assumption. }
  apply (den_ecall segs cfg LIMIT model0 mem0 Hwx t E S M ms model _ Hect Hx Hd). intros model1 Hd1.
  apply (den_ioctl_notty segs cfg LIMIT mem0 model0 E S M ms model1 _ fd cmd (Z_to_bv 64 fd) Hd1 H7 H0 H1 Hch Htty).
  intros ms' m'' Hd''.
  apply (IH _ _ _ _ _ finals Hck model0 mem0 E ms' m'' Hd'' (INV_same mem0 E S _ M FS model0 Hi eq_refl) (HAX_same E S _ M a mem0 HX eq_refl) Hw). exact Hk.
Qed.

#[using="Type"] Lemma add_fact_next : forall S f, s_next (add_fact S f) = s_next S. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma lwf_lsub : forall n a b, lwf n a = true -> lwf n b = true -> lwf n (lsub a b) = true.
Proof. LiaFast.lf_pins LiaFast.u0. intros n a b Ha Hb. unfold lsub. rewrite lneg_eq. apply lwf_ladd; [exact Ha | apply lwf_lscale; exact Hb]. Qed.
#[using="Type"] Lemma rsz_is_const : forall E R n, is_const (rg_size R) = Some n -> rsz E R = n.
Proof. LiaFast.lf_pins LiaFast.u0. intros E R n H. unfold rsz. exact (is_const_u E _ n H). Qed.
#[using="Type"] Lemma read_post_next : forall S i lo hi v, s_next (read_post S i lo hi v) = s_next S.
Proof. LiaFast.lf_pins LiaFast.u0. intros S i lo hi v. unfold read_post. destruct (nth_error (s_rgs S) i); reflexivity. Qed.

#[using="Hwx Hect Hp3 Hp4 HFLhi Hseg"] Lemma Pm_read : forall i o ka kb, Pm ka -> Pm kb -> Pm (MRead i o ka kb).
Proof. LiaFast.lf_pins (fun (Hwx Hect Hp3 Hp4 HFLhi Hseg : LiaFast.U) => LiaFast.u0).
  intros i o ka kb IHa IHb S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct FS as [|off FL| | |off FL]; try discriminate.
  destruct (negb dr && is_ecall t (s_pc S))%bool eqn:Hx; [|discriminate]. apply andb_prop in Hx as [Hdr Hx]. apply negb_true_iff in Hdr. apply is_ecall_ok in Hx.
  destruct (read_args_ok S i o) as [chi|] eqn:Hra; [|discriminate].
  set (c := argl S 2) in *. set (rem := lsub FL off) in *.
  destruct (irange (s_facts S) rem) as [lo hi] eqn:Hir.
  destruct (irange (s_facts S) c) as [clo chi0] eqn:Hic.
  destruct (if Z.leb lo chi then mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts ka (add_fact (read_post S i o (o + chi) rem) (FRange (lsub c rem) 0 65536)) M (FSOpen FL FL) sh a
            else Some []) as [f1|] eqn:H1; [|discriminate].
  destruct (if Z.ltb clo hi then mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts kb (add_fact (read_post S i o (o + chi) c) (FRange (lsub rem c) 1 hi)) M (FSOpen (ladd off c) FL) sh a
            else Some []) as [f2|] eqn:H2; [|discriminate].
  destruct (Z.leb 0 lo && Z.ltb hi 4611686018427387904 && Z.ltb (snd (irange (s_facts S) off) + chi) FLT)%bool eqn:Hlh; [|discriminate].
  injection Hck as <-. apply andb_prop in Hlh as [Hlh HoffT]. apply Z.ltb_lt in HoffT.
  apply andb_prop in Hlh as [Hlo0 Hhi62]. apply Z.leb_le in Hlo0. apply Z.ltb_lt in Hhi62.
  (* [comment removed for export] *)
  unfold read_args_ok in Hra. fold c in Hra. rewrite Hic in Hra.
  destruct (a7c S) as [c7|] eqn:H7; [|discriminate]. destruct (arg S 0) as [c0|] eqn:H0; [|discriminate].
  destruct (nth_error (s_rgs S) i) as [R|] eqn:HR; [|discriminate].
  destruct (is_const (rg_base R)) as [b|] eqn:Hb0; [|discriminate].
  destruct (is_const (rg_size R)) as [sz|] eqn:Hs0; [|discriminate].
  destruct (Z.eqb c7 63 && Z.eqb c0 3 && Z.ltb 0 clo && Z.leb chi0 65536 && rk_is_rwz (rg_kind R) && Z.leb 0 o &&
            Z.leb (o + chi0) sz && Z.leb 0x10000 b && Z.leb (b + sz) 0x61a000 && lwf (s_next S) c &&
            lin_eqb (argl S 1) (lconst (b + o)))%bool eqn:Hck; [|discriminate].
  injection Hra as Hchi. subst chi0.
  repeat match type of Hck with ((_ && _)%bool = true) => apply andb_prop in Hck as [Hck ?Hc] end.
  repeat match goal with
         | Hx' : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in Hx'
         | Hx' : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx'
         | Hx' : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hx'
         | Hx' : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in Hx'
         end.
  subst c7 c0.
  assert (Hwc : lwf (s_next S) c = true) by assumption.
  pose proof Hi as Hi0. destruct Hi0 as (Hpv & Hfsw & Hfr & Hm0 & Hlen & Hlk & Hfs0 & (Hfd & HFL' & Hoff') & Hch1 & Hch2 & Hdv).
  pose proof (bv_unsigned_in_range _ (lden E FL)) as XFL. unfold bv_modulus in XFL. change (2 ^ Z.of_N 64) with two64 in XFL. rewrite HFL' in XFL.
  cbn [fs_wf] in Hfsw. apply andb_prop in Hfsw as [Hwoff HwFL].
  assert (Hkd : rg_kind R = RW \/ rg_kind R = RZ).
  { match goal with Hk' : rk_is_rwz (rg_kind R) = true |- _ => destruct (rg_kind R); try discriminate; auto end. }
  destruct (is_const_sound E _ b Hb0) as [HbE Hb64].
  (* [comment removed for export] *)
  pose proof flen_le as Hfle. pose proof flen_range as Hflr.
  set (remz := flen - bv_unsigned (lden E off)).      (* [comment removed for export] *)
  assert (Hrem : bv_unsigned (lden E rem) = remz).
  { unfold rem. rewrite lden_lsub, bv_sub_unsigned, HFL'. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
    pose proof (bv_unsigned_in_range _ (lden E FL)) as X. unfold bv_modulus in X. change (2 ^ Z.of_N 64) with two64 in X.
    rewrite HFL' in X. pose proof (bv_unsigned_in_range _ (lden E off)) as Y. unfold bv_modulus in Y. change (2 ^ Z.of_N 64) with two64 in Y.
    apply Z.mod_small. unfold remz. lia. }
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF0 & _).
  pose proof (irange_sound E _ rem HF0) as Hirs. rewrite Hir in Hirs. cbn [fst snd] in Hirs. rewrite Hrem in Hirs.
  pose proof (irange_sound E _ c HF0) as Hics. rewrite Hic in Hics. cbn [fst snd] in Hics.
  set (cnt := bv_unsigned (lden E c)) in *.
  assert (Hcw : lden E c = Z_to_bv 64 cnt) by (unfold cnt; symmetry; apply Z_to_bv_bv_unsigned).
  assert (Hwrem : lwf (s_next S) rem = true) by (unfold rem, lsub; rewrite lneg_eq; apply lwf_ladd; [exact HwFL | apply lwf_lscale; exact Hwoff]).
  apply (den_ecall segs cfg LIMIT model0 mem0 Hwx t E S M ms model _ Hect Hx Hd). intros model1 Hd1.
  (* [comment removed for export] *)
  assert (Hbuf : lden E (rget (s_regs S) (rkey a1r)) = Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)).
  { change (rget (s_regs S) (rkey a1r)) with (argl S 1).
    match goal with Hq : argl S 1 = lconst (b + o) |- _ => rewrite Hq end. rewrite lden_lconst, HbE, u_small64 by exact Hb64. reflexivity. }
  assert (Hsz : forall E', agree (s_next S) E E' -> o + chi <= rsz E' R) by (intros E' _; rewrite (rsz_is_const E' R sz Hs0); lia).
  assert (Hub : bv_unsigned (lden E (rg_base R)) = b) by (rewrite HbE; apply u_small64; exact Hb64).
  assert (Hok : access_okb (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) cnt = true).
  { unfold access_okb. rewrite Hub, u_small64 by (unfold two64; lia). apply andb_true_intro. split; apply Z.leb_le; unfold TASK_SIZE; lia. }
  assert (Hav : range_avoids (Hof E M model1) (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) (Z.to_nat cnt)).
  { intros kk Hkk. assert (Hkk' : Z.of_nat kk < cnt) by (apply Nat2Z.inj_lt in Hkk; rewrite Z2Nat.id in Hkk by lia; exact Hkk).
    destruct (Hof E M model1 (woff (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) kk)) eqn:Hh; [|reflexivity].
    exfalso. apply (dn_hoff _ _ _ _ _ _ _ _ _ Hd1) in Hh. unfold woff in Hh. rewrite Hub in Hh.
    rewrite (u_small64 (b + o)) in Hh by (unfold two64; lia). rewrite u_small64 in Hh by (unfold two64; lia).
    apply (Hseg (b + o + Z.of_nat kk)); [lia | exact Hh]. }
  assert (Hfd3 : fd_lookup (m_fds model0) (fd32 (Z_to_bv 64 3)) = Some (FdFile path0 (lden E off))) by (rewrite fd32_3; exact Hfd).
  assert (Hlfr : Z.of_nat (length (file_read data0 (lden E off) (Z_to_bv 64 cnt))) = Z.min cnt remz).
  { rewrite length_file_read by lia. rewrite u_small64 by (unfold two64; lia).
    (* [comment removed for export] *)
    pose proof (irange_sound E _ off HF0) as Hiof. unfold remz, flen, flen_of. lia. }
  assert (Hc2' : lden E (argl S 2) = Z_to_bv 64 cnt) by exact Hcw.
  destruct (Z_le_gt_dec remz cnt) as [Hca|Hcb].
  - (* [comment removed for export] *)
    assert (Hl : Z.leb lo chi = true) by (apply Z.leb_le; lia). rewrite Hl in H1.
    assert (Hv : lden E rem = len_word (file_read data0 (lden E off) (Z_to_bv 64 cnt))).
    { apply bv_eq. unfold len_word. rewrite Hrem, u_small64 by (rewrite Hlfr; unfold two64; lia). rewrite Hlfr. lia. }
    apply (den_read_file2 segs cfg LIMIT mem0 model0 E S M ms model1 _ 3 cnt path0 (lden E off) data0 i R o rem
             Hd1 H7 H0 Hc2' ltac:(lia) chi ltac:(lia) HR Hkd ltac:(lia) Hbuf Hsz Hfd3 (Hlk Hdr) Hwrem Hv Hok Hav).
    intros ms' m'' Hd'' _.
    set (S1 := read_post S i o (o + chi) rem) in *.
    assert (Hn1 : s_next S1 = s_next S) by apply read_post_next.
    assert (Hd2 : DEN segs LIMIT (with_fds (fd_insert (m_fds model0) (fd32 (Z_to_bv 64 3)) (FdFile path0 (lden E off + lden E rem))) model0)
                      mem0 E (add_fact S1 (FRange (lsub c rem) 0 65536)) M ms' m'').
    { eapply den_addfact; [exact Hd''|].
      intros E' Ha'. cbn [fact_ok]. rewrite Hn1 in Ha'. rewrite (lden_agree_wf _ E E' _ (lwf_lsub _ _ _ Hwc Hwrem) Ha').
      rewrite lden_lsub, bv_sub_unsigned. fold cnt. rewrite Hrem. unfold bv_wrap.
      rewrite Z.mod_small by (change (bv_modulus 64) with two64; unfold two64; lia). lia. }
    assert (Hi' : INV mem0 E (add_fact S1 (FRange (lsub c rem) 0 65536)) M (FSOpen FL FL)
                    (with_fds (fd_insert (m_fds model0) (fd32 (Z_to_bv 64 3)) (FdFile path0 (lden E off + lden E rem))) model0)).
    { unfold INV. rewrite add_fact_next, Hn1. split; [exact Hpv|]. split; [cbn [fs_wf]; rewrite HwFL; reflexivity|].
      split; [exact Hfr|]. split; [exact Hm0|]. split; [exact Hlen|]. split; [intros Hdr'; rewrite with_fds_fs; exact (Hlk Hdr')|]. split; [rewrite with_fds_fs; exact Hfs0|].
      rewrite fd32_3.
      split; [|split; [rewrite with_fds_fds, fd_lookup_insert_other by (first [exact w3_ne1 | exact w3_ne2]); exact Hch1|]].
      2: { split; [rewrite with_fds_fds, fd_lookup_insert_other by (first [exact w3_ne1 | exact w3_ne2]); exact Hch2|].
           exact (hv_inv_step E E S _ Hdv (agree_refl _ _) ltac:(rewrite add_fact_next, Hn1; lia)). }
      rewrite with_fds_fds, fd_lookup_insert_same. split; [|split; [exact HFL' | lia]].
      f_equal. f_equal. unfold rem. rewrite lden_lsub. apply bv_eq. rewrite bv_add_unsigned, bv_sub_unsigned. unfold bv_wrap.
      rewrite Zplus_mod_idemp_r.
      replace (bv_unsigned (lden E off) + (bv_unsigned (lden E FL) - bv_unsigned (lden E off))) with (bv_unsigned (lden E FL)) by ring.
      apply Z.mod_small. apply bv_unsigned_in_range. }
    apply (IHa _ _ _ _ _ f1 H1 _ mem0 E ms' m'' Hd2 Hi' (HAX_same E S _ M a mem0 HX ltac:(rewrite add_fact_next, Hn1; reflexivity))
             ltac:(rewrite add_fact_next, Hn1; exact Hw)).
    intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd''' Hi'' Hx'' Hw'' Ha''.
    rewrite add_fact_next, Hn1 in Ha''.
    exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (in_or_app _ _ _ (or_introl Hin'')) Hd''' Hi'' Hx'' Hw'' Ha'').
  - (* [comment removed for export] *)
    assert (Hl : Z.ltb clo hi = true) by (apply Z.ltb_lt; lia). rewrite Hl in H2.
    assert (Hv : lden E c = len_word (file_read data0 (lden E off) (Z_to_bv 64 cnt))).
    { apply bv_eq. unfold len_word. fold cnt. rewrite u_small64 by (rewrite Hlfr; unfold two64; lia). rewrite Hlfr. lia. }
    apply (den_read_file2 segs cfg LIMIT mem0 model0 E S M ms model1 _ 3 cnt path0 (lden E off) data0 i R o c
             Hd1 H7 H0 Hc2' ltac:(lia) chi ltac:(lia) HR Hkd ltac:(lia) Hbuf Hsz Hfd3 (Hlk Hdr) Hwc Hv Hok Hav).
    intros ms' m'' Hd'' _.
    set (S1 := read_post S i o (o + chi) c) in *.
    assert (Hn1 : s_next S1 = s_next S) by apply read_post_next.
    assert (Hd2 : DEN segs LIMIT (with_fds (fd_insert (m_fds model0) (fd32 (Z_to_bv 64 3)) (FdFile path0 (lden E off + lden E c))) model0)
                      mem0 E (add_fact S1 (FRange (lsub rem c) 1 hi)) M ms' m'').
    { eapply den_addfact; [exact Hd''|].
      intros E' Ha'. cbn [fact_ok]. rewrite Hn1 in Ha'. rewrite (lden_agree_wf _ E E' _ (lwf_lsub _ _ _ Hwrem Hwc) Ha').
      rewrite lden_lsub, bv_sub_unsigned. fold cnt. rewrite Hrem. unfold bv_wrap.
      rewrite Z.mod_small by (change (bv_modulus 64) with two64; unfold two64; lia). lia. }
    assert (Hi' : INV mem0 E (add_fact S1 (FRange (lsub rem c) 1 hi)) M (FSOpen (ladd off c) FL)
                    (with_fds (fd_insert (m_fds model0) (fd32 (Z_to_bv 64 3)) (FdFile path0 (lden E off + lden E c))) model0)).
    { unfold INV. rewrite add_fact_next, Hn1. split; [exact Hpv|].
      split; [cbn [fs_wf]; rewrite HwFL, andb_true_r; exact (lwf_ladd _ _ _ Hwoff Hwc)|].
      split; [exact Hfr|]. split; [exact Hm0|]. split; [exact Hlen|]. split; [intros Hdr'; rewrite with_fds_fs; exact (Hlk Hdr')|]. split; [rewrite with_fds_fs; exact Hfs0|].
      rewrite fd32_3.
      split; [|split; [rewrite with_fds_fds, fd_lookup_insert_other by (first [exact w3_ne1 | exact w3_ne2]); exact Hch1|]].
      2: { split; [rewrite with_fds_fds, fd_lookup_insert_other by (first [exact w3_ne1 | exact w3_ne2]); exact Hch2|].
           exact (hv_inv_step E E S _ Hdv (agree_refl _ _) ltac:(rewrite add_fact_next, Hn1; lia)). }
      rewrite with_fds_fds, fd_lookup_insert_same. rewrite lden_ladd.
      split; [reflexivity|]. split; [exact HFL'|].
      rewrite bv_add_unsigned. fold cnt. unfold bv_wrap.
      pose proof (bv_unsigned_in_range _ (lden E off)) as Y. unfold bv_modulus in Y. change (2 ^ Z.of_N 64) with two64 in Y.
      rewrite Z.mod_small by (change (bv_modulus 64) with two64; unfold two64 in *; unfold remz in Hcb; lia). unfold remz in Hcb. lia. }
    apply (IHb _ _ _ _ _ f2 H2 _ mem0 E ms' m'' Hd2 Hi' (HAX_same E S _ M a mem0 HX ltac:(rewrite add_fact_next, Hn1; reflexivity))
             ltac:(rewrite add_fact_next, Hn1; exact Hw)).
    intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd''' Hi'' Hx'' Hw'' Ha''.
    rewrite add_fact_next, Hn1 in Ha''.
    exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (in_or_app _ _ _ (or_intror Hin'')) Hd''' Hi'' Hx'' Hw'' Ha'').
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma put_rg_next : forall S i o bvs, s_next (put_rg S i o bvs) = s_next S.
Proof. LiaFast.lf_pins LiaFast.u0. intros S i o bvs. unfold put_rg. destruct (nth_error (s_rgs S) i); reflexivity. Qed.
#[using="path0 data0 Hp4"] Lemma wtm_nth : forall m X bs j, 0 <= X -> X + Z.of_nat (length bs) <= two64 -> (j < length bs)%nat ->
  write_to_mem m (Z_to_bv 64 X) bs (Z_to_bv 64 (X + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (path0 data0 Hp4 : LiaFast.U) => LiaFast.u0).
  intros m X bs j HX Hn Hj. rewrite write_to_mem_spec by lia.
  rewrite u_small64 by (unfold two64 in *; lia).
  replace (Z.leb X (X + Z.of_nat j) && Z.ltb (X + Z.of_nat j) (X + Z.of_nat (length bs)))%bool with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  replace (Z.to_nat (X + Z.of_nat j - X)) with j by lia.
  destruct (nth_error bs j) as [x|] eqn:Hx; [rewrite (nth_error_nth _ _ _ Hx); reflexivity|].
  exfalso. apply nth_error_None in Hx. lia.
Qed.
#[using="path0 Hp4"] Lemma hdr_link : forall E h (k : nat) (off : lin) (cnt : Z), off = lconst 0 -> (k <= 16)%nat ->
  (forall j, (j < 16)%nat -> (j < length data0)%nat -> E (dvar h j) = Z_to_bv 64 (bv_unsigned (nth j data0 (Z_to_bv 8 0)))) ->
  Z.of_nat k <= Z.min cnt (Z.of_nat (length data0)) -> 0 <= cnt < two64 ->
  forall j, (j < k)%nat -> E (dvar h j) = Z_to_bv 64 (bv_unsigned (nth j (file_read data0 (lden E off) (Z_to_bv 64 cnt)) (Z_to_bv 8 0))).
Proof. LiaFast.lf_pins (fun (path0 Hp4 : LiaFast.U) => LiaFast.u0).
  intros E h k off cnt -> Hk16 Hd Hm Hc j Hj. rewrite (Hd j ltac:(lia) ltac:(lia)). f_equal. f_equal.
  rewrite file_read_unguarded. rewrite lden_lconst. unfold word_to_nat. rewrite !u_small64 by (unfold two64 in *; lia).
  cbn [Z.to_nat skipn]. rewrite nth_firstn. replace (Nat.ltb j (Z.to_nat cnt)) with true; [reflexivity|].
  symmetry. apply Nat.ltb_lt. lia.
Qed.
#[using="path0 data0 Hp4"] Lemma den_track_hdr : forall model0 mem0 E S1 M ms' m'' i R o h (k : nat) b sz (bs : list byte),
  DEN segs LIMIT model0 mem0 E S1 M ms' m'' -> (k <= 16)%nat ->
  nth_error (s_rgs S1) i = Some R -> rg_kind R = RW -> is_const (rg_base R) = Some b -> is_const (rg_size R) = Some sz ->
  0 <= o -> o + Z.of_nat k <= sz -> (dvar h 16 <= s_next S1)%positive -> 0 <= b -> b + sz <= two64 ->
  (forall j, (j < k)%nat -> ms_mem ms' (Z_to_bv 64 (b + o + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0))) ->
  (forall j, (j < k)%nat -> E (dvar h j) = Z_to_bv 64 (bv_unsigned (nth j bs (Z_to_bv 8 0)))) ->
  DEN segs LIMIT model0 mem0 E (track_hdr S1 i o h k) M ms' m''.
Proof. LiaFast.lf_pins (fun (path0 data0 Hp4 : LiaFast.U) => LiaFast.u0).
  intros model0 mem0 E S1 M ms' m'' i R o h k b sz bs Hd Hk16 HR Hk Hb Hs Ho Hos Hh Hb0 Hbs Hm HE.
  unfold track_hdr. apply (den_put segs LIMIT mem0 model0 E S1 M ms' m'' i R o (hdr_bvs h k) Hd HR ltac:(rewrite Hk; discriminate) Ho).
  - intros E' _. rewrite (rsz_is_const E' R sz Hs). unfold hdr_bvs. rewrite length_map, length_seq. lia.
  - intros E' Ha' j x Hx.
    assert (Hj : (j < k)%nat).
    { assert (Hne : nth_error (hdr_bvs h k) j <> None) by (rewrite Hx; discriminate).
      apply nth_error_Some in Hne. unfold hdr_bvs in Hne. rewrite length_map, length_seq in Hne. exact Hne. }
    assert (Hx' : x = BV (lvar (dvar h j)) 0).
    { unfold hdr_bvs in Hx. rewrite nth_error_map in Hx. destruct (nth_error (List.seq 0 k) j) as [k'|] eqn:Hk'; [|discriminate].
      cbn [option_map] in Hx. injection Hx as <-. pose proof (nth_error_nth _ _ 0%nat Hk') as X. rewrite seq_nth in X by exact Hj.
      cbn in X. subst k'. reflexivity. }
    subst x.
    assert (HuB : uE E' (rg_base R) = b) by (unfold uE; exact (is_const_u E' _ b Hb)).
    rewrite HuB.
    destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & HG & _).
    pose proof (proj1 (Forall_nth' _ _) HG i R HR) as HRok.
    assert (Hsz' : rsz E R = sz) by exact (rsz_is_const E R sz Hs).
    pose proof (rg_ok_visible segs (Hof E M m'') (ms_mem ms') E R (dn_hoff _ _ _ _ _ _ _ _ _ Hd) HRok (o + Z.of_nat j) ltac:(lia)) as Hv.
    assert (HuB0 : uE E (rg_base R) = b) by (unfold uE; exact (is_const_u E _ b Hb)).
    rewrite HuB0 in Hv. replace (b + (o + Z.of_nat j)) with (b + o + Z.of_nat j) in Hv by lia.
    unfold rd1, mrestrict. rewrite Hv, (Hm j Hj). f_equal.
    unfold bden. rewrite lden_lvar. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
    rewrite <- (Ha' (dvar h j) ltac:(pose proof (dvar_lt h j 16 ltac:(lia)); lia)). rewrite (HE j Hj).
    rewrite u_small64 by (pose proof (bv_unsigned_in_range _ (nth j bs (Z_to_bv 8 0))) as X; unfold bv_modulus in X;
                          change (2 ^ Z.of_N 8) with 256 in X; unfold two64; lia).
    symmetry. apply Z_to_bv_bv_unsigned.
Qed.

#[using="Hwx Hect Hp3 Hp4 HFLhi Hseg"] Lemma Pm_readH : forall i o k ka kb, Pm ka -> Pm kb -> Pm (MReadH i o k ka kb).
Proof. LiaFast.lf_pins (fun (Hwx Hect Hp3 Hp4 HFLhi Hseg : LiaFast.U) => LiaFast.u0).
  intros i o k ka kb IHa IHb S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct FS as [|off FL| | |off FL]; try discriminate.
  remember hv as hv0 eqn:Hhv in Hck. destruct hv0 as [h|]; [|discriminate]. cbv beta iota in Hck. rewrite Hhv in Hck.
  destruct (negb dr && is_ecall t (s_pc S) && lin_eqb off (lconst 0) && Pos.leb (dvar h 16) (s_next S) && Nat.leb k 16)%bool eqn:Hx; [|discriminate].
  apply andb_prop in Hx as [Hx Hk16]. apply Nat.leb_le in Hk16.
  apply andb_prop in Hx as [Hx Hh16]. apply andb_prop in Hx as [Hx Hoff0]. apply Pos.leb_le in Hh16. apply lin_eqb_eq in Hoff0.
  apply andb_prop in Hx as [Hdr Hx]. apply negb_true_iff in Hdr. apply is_ecall_ok in Hx.
  destruct (read_args_ok S i o) as [chi|] eqn:Hra; [|discriminate].
  set (c := argl S 2) in *. set (rem := lsub FL off) in *.
  destruct (irange (s_facts S) rem) as [lo hi] eqn:Hir.
  destruct (irange (s_facts S) c) as [clo chi0] eqn:Hic.
  destruct (if Z.leb lo chi then if Z.leb (Z.of_nat k) lo then mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts ka (track_hdr (add_fact (read_post S i o (o + chi) rem) (FRange (lsub c rem) 0 65536)) i o h k) M (FSOpen FL FL) sh a else None
            else Some []) as [f1|] eqn:H1; [|discriminate].
  destruct (if Z.ltb clo hi then if Z.leb (Z.of_nat k) clo then mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts kb (track_hdr (add_fact (read_post S i o (o + chi) c) (FRange (lsub rem c) 1 hi)) i o h k) M (FSOpen (ladd off c) FL) sh a else None
            else Some []) as [f2|] eqn:H2; [|discriminate].
  destruct (Z.leb 0 lo && Z.ltb hi 4611686018427387904 && Z.ltb (snd (irange (s_facts S) off) + chi) FLT)%bool eqn:Hlh; [|discriminate].
  injection Hck as <-. apply andb_prop in Hlh as [Hlh HoffT]. apply Z.ltb_lt in HoffT.
  apply andb_prop in Hlh as [Hlo0 Hhi62]. apply Z.leb_le in Hlo0. apply Z.ltb_lt in Hhi62.
  (* [comment removed for export] *)
  unfold read_args_ok in Hra. fold c in Hra. rewrite Hic in Hra.
  destruct (a7c S) as [c7|] eqn:H7; [|discriminate]. destruct (arg S 0) as [c0|] eqn:H0; [|discriminate].
  destruct (nth_error (s_rgs S) i) as [R|] eqn:HR; [|discriminate].
  destruct (is_const (rg_base R)) as [b|] eqn:Hb0; [|discriminate].
  destruct (is_const (rg_size R)) as [sz|] eqn:Hs0; [|discriminate].
  destruct (Z.eqb c7 63 && Z.eqb c0 3 && Z.ltb 0 clo && Z.leb chi0 65536 && rk_is_rwz (rg_kind R) && Z.leb 0 o &&
            Z.leb (o + chi0) sz && Z.leb 0x10000 b && Z.leb (b + sz) 0x61a000 && lwf (s_next S) c &&
            lin_eqb (argl S 1) (lconst (b + o)))%bool eqn:Hck; [|discriminate].
  injection Hra as Hchi. subst chi0.
  repeat match type of Hck with ((_ && _)%bool = true) => apply andb_prop in Hck as [Hck ?Hc] end.
  repeat match goal with
         | Hx' : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in Hx'
         | Hx' : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx'
         | Hx' : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hx'
         | Hx' : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in Hx'
         end.
  subst c7 c0.
  assert (Hwc : lwf (s_next S) c = true) by assumption.
  pose proof Hi as Hi0. destruct Hi0 as (Hpv & Hfsw & Hfr & Hm0 & Hlen & Hlk & Hfs0 & (Hfd & HFL' & Hoff') & Hch1 & Hch2 & Hdv).
  pose proof (bv_unsigned_in_range _ (lden E FL)) as XFL. unfold bv_modulus in XFL. change (2 ^ Z.of_N 64) with two64 in XFL. rewrite HFL' in XFL.
  assert (Hdv' : forall j, (j < 16)%nat -> (j < length data0)%nat -> E (dvar h j) = Z_to_bv 64 (bv_unsigned (nth j data0 (Z_to_bv 8 0)))).
  { unfold hv_inv in Hdv. rewrite <- Hhv in Hdv. exact (proj1 (proj2 Hdv)). }
  cbn [fs_wf] in Hfsw. apply andb_prop in Hfsw as [Hwoff HwFL].
  assert (Hkd : rg_kind R = RW \/ rg_kind R = RZ).
  { match goal with Hk' : rk_is_rwz (rg_kind R) = true |- _ => destruct (rg_kind R); try discriminate; auto end. }
  destruct (is_const_sound E _ b Hb0) as [HbE Hb64].
  (* [comment removed for export] *)
  pose proof flen_le as Hfle. pose proof flen_range as Hflr.
  set (remz := flen - bv_unsigned (lden E off)).      (* [comment removed for export] *)
  assert (Hrem : bv_unsigned (lden E rem) = remz).
  { unfold rem. rewrite lden_lsub, bv_sub_unsigned, HFL'. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
    pose proof (bv_unsigned_in_range _ (lden E FL)) as X. unfold bv_modulus in X. change (2 ^ Z.of_N 64) with two64 in X.
    rewrite HFL' in X. pose proof (bv_unsigned_in_range _ (lden E off)) as Y. unfold bv_modulus in Y. change (2 ^ Z.of_N 64) with two64 in Y.
    apply Z.mod_small. unfold remz. lia. }
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF0 & _).
  pose proof (irange_sound E _ rem HF0) as Hirs. rewrite Hir in Hirs. cbn [fst snd] in Hirs. rewrite Hrem in Hirs.
  pose proof (irange_sound E _ c HF0) as Hics. rewrite Hic in Hics. cbn [fst snd] in Hics.
  set (cnt := bv_unsigned (lden E c)) in *.
  assert (Hcw : lden E c = Z_to_bv 64 cnt) by (unfold cnt; symmetry; apply Z_to_bv_bv_unsigned).
  assert (Hwrem : lwf (s_next S) rem = true) by (unfold rem, lsub; rewrite lneg_eq; apply lwf_ladd; [exact HwFL | apply lwf_lscale; exact Hwoff]).
  apply (den_ecall segs cfg LIMIT model0 mem0 Hwx t E S M ms model _ Hect Hx Hd). intros model1 Hd1.
  (* [comment removed for export] *)
  assert (Hbuf : lden E (rget (s_regs S) (rkey a1r)) = Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)).
  { change (rget (s_regs S) (rkey a1r)) with (argl S 1).
    match goal with Hq : argl S 1 = lconst (b + o) |- _ => rewrite Hq end. rewrite lden_lconst, HbE, u_small64 by exact Hb64. reflexivity. }
  assert (Hsz : forall E', agree (s_next S) E E' -> o + chi <= rsz E' R) by (intros E' _; rewrite (rsz_is_const E' R sz Hs0); lia).
  assert (Hub : bv_unsigned (lden E (rg_base R)) = b) by (rewrite HbE; apply u_small64; exact Hb64).
  assert (Hok : access_okb (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) cnt = true).
  { unfold access_okb. rewrite Hub, u_small64 by (unfold two64; lia). apply andb_true_intro. split; apply Z.leb_le; unfold TASK_SIZE; lia. }
  assert (Hav : range_avoids (Hof E M model1) (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) (Z.to_nat cnt)).
  { intros kk Hkk. assert (Hkk' : Z.of_nat kk < cnt) by (apply Nat2Z.inj_lt in Hkk; rewrite Z2Nat.id in Hkk by lia; exact Hkk).
    destruct (Hof E M model1 (woff (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) kk)) eqn:Hh; [|reflexivity].
    exfalso. apply (dn_hoff _ _ _ _ _ _ _ _ _ Hd1) in Hh. unfold woff in Hh. rewrite Hub in Hh.
    rewrite (u_small64 (b + o)) in Hh by (unfold two64; lia). rewrite u_small64 in Hh by (unfold two64; lia).
    apply (Hseg (b + o + Z.of_nat kk)); [lia | exact Hh]. }
  assert (Hfd3 : fd_lookup (m_fds model0) (fd32 (Z_to_bv 64 3)) = Some (FdFile path0 (lden E off))) by (rewrite fd32_3; exact Hfd).
  assert (Hlfr : Z.of_nat (length (file_read data0 (lden E off) (Z_to_bv 64 cnt))) = Z.min cnt remz).
  { rewrite length_file_read by lia. rewrite u_small64 by (unfold two64; lia).
    (* [comment removed for export] *)
    pose proof (irange_sound E _ off HF0) as Hiof. unfold remz, flen, flen_of. lia. }
  assert (Hc2' : lden E (argl S 2) = Z_to_bv 64 cnt) by exact Hcw.
  destruct (Z_le_gt_dec remz cnt) as [Hca|Hcb].
  - (* [comment removed for export] *)
    assert (Hl : Z.leb lo chi = true) by (apply Z.leb_le; lia). rewrite Hl in H1.
    destruct (Z.leb (Z.of_nat k) lo) eqn:H16; [|discriminate]. apply Z.leb_le in H16.
    assert (Hv : lden E rem = len_word (file_read data0 (lden E off) (Z_to_bv 64 cnt))).
    { apply bv_eq. unfold len_word. rewrite Hrem, u_small64 by (rewrite Hlfr; unfold two64; lia). rewrite Hlfr. lia. }
    apply (den_read_file2 segs cfg LIMIT mem0 model0 E S M ms model1 _ 3 cnt path0 (lden E off) data0 i R o rem
             Hd1 H7 H0 Hc2' ltac:(lia) chi ltac:(lia) HR Hkd ltac:(lia) Hbuf Hsz Hfd3 (Hlk Hdr) Hwrem Hv Hok Hav).
    intros ms' m'' Hd'' Hcont.
    set (S1 := read_post S i o (o + chi) rem) in *.
    assert (Hn1 : s_next S1 = s_next S) by apply read_post_next.
    assert (Hd2 : DEN segs LIMIT (with_fds (fd_insert (m_fds model0) (fd32 (Z_to_bv 64 3)) (FdFile path0 (lden E off + lden E rem))) model0)
                      mem0 E (add_fact S1 (FRange (lsub c rem) 0 65536)) M ms' m'').
    { eapply den_addfact; [exact Hd''|].
      intros E' Ha'. cbn [fact_ok]. rewrite Hn1 in Ha'. rewrite (lden_agree_wf _ E E' _ (lwf_lsub _ _ _ Hwc Hwrem) Ha').
      rewrite lden_lsub, bv_sub_unsigned. fold cnt. rewrite Hrem. unfold bv_wrap.
      rewrite Z.mod_small by (change (bv_modulus 64) with two64; unfold two64; lia). lia. }
    assert (Hi' : INV mem0 E (add_fact S1 (FRange (lsub c rem) 0 65536)) M (FSOpen FL FL)
                    (with_fds (fd_insert (m_fds model0) (fd32 (Z_to_bv 64 3)) (FdFile path0 (lden E off + lden E rem))) model0)).
    { unfold INV. rewrite add_fact_next, Hn1. split; [exact Hpv|]. split; [cbn [fs_wf]; rewrite HwFL; reflexivity|].
      split; [exact Hfr|]. split; [exact Hm0|]. split; [exact Hlen|]. split; [intros Hdr'; rewrite with_fds_fs; exact (Hlk Hdr')|]. split; [rewrite with_fds_fs; exact Hfs0|].
      rewrite fd32_3.
      split; [|split; [rewrite with_fds_fds, fd_lookup_insert_other by (first [exact w3_ne1 | exact w3_ne2]); exact Hch1|]].
      2: { split; [rewrite with_fds_fds, fd_lookup_insert_other by (first [exact w3_ne1 | exact w3_ne2]); exact Hch2|].
           exact (hv_inv_step E E S _ Hdv (agree_refl _ _) ltac:(rewrite add_fact_next, Hn1; lia)). }
      rewrite with_fds_fds, fd_lookup_insert_same. split; [|split; [exact HFL' | lia]].
      f_equal. f_equal. unfold rem. rewrite lden_lsub. apply bv_eq. rewrite bv_add_unsigned, bv_sub_unsigned. unfold bv_wrap.
      rewrite Zplus_mod_idemp_r.
      replace (bv_unsigned (lden E off) + (bv_unsigned (lden E FL) - bv_unsigned (lden E off))) with (bv_unsigned (lden E FL)) by ring.
      apply Z.mod_small. apply bv_unsigned_in_range. }
    assert (Hd3 : DEN segs LIMIT (with_fds (fd_insert (m_fds model0) (fd32 (Z_to_bv 64 3)) (FdFile path0 (lden E off + lden E rem))) model0)
                      mem0 E (track_hdr (add_fact S1 (FRange (lsub c rem) 0 65536)) i o h k) M ms' m'').
    { apply (den_track_hdr _ mem0 E (add_fact S1 (FRange (lsub c rem) 0 65536)) M ms' m'' i
               (RG (rg_base R) (rg_size R) RW (havoc_range (rg_cont R) o (o + chi))) o h k b sz (file_read data0 (lden E off) (Z_to_bv 64 cnt)) Hd2 Hk16
               ltac:(cbn [add_fact s_rgs]; unfold S1, read_post; rewrite HR; cbn [s_rgs]; exact (nth_upd_same _ _ _ _ HR))
               eq_refl Hb0 Hs0 ltac:(lia) ltac:(lia) ltac:(rewrite add_fact_next, Hn1; exact Hh16) ltac:(lia) ltac:(unfold two64; lia)).
      - intros j Hj. rewrite Hcont, Hub. apply wtm_nth; [lia | rewrite Hlfr; unfold two64; lia | apply Nat2Z.inj_lt; rewrite Hlfr; lia].
      - assert (Hoffz : bv_unsigned (lden E off) = 0) by (rewrite Hoff0; reflexivity).
        exact (hdr_link E h k off cnt Hoff0 Hk16 Hdv' ltac:(unfold remz in *; lia) ltac:(unfold two64; lia)). }
    apply (IHa _ _ _ _ _ f1 H1 _ mem0 E ms' m'' Hd3 (INV_same _ _ _ _ _ _ _ Hi' (put_rg_next _ i o (hdr_bvs h k))) (HAX_same E S _ M a mem0 HX ltac:(unfold track_hdr; rewrite put_rg_next, add_fact_next, Hn1; reflexivity))
             ltac:(unfold track_hdr; rewrite put_rg_next, add_fact_next, Hn1; exact Hw)).
    intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd''' Hi'' Hx'' Hw'' Ha''.
    unfold track_hdr in Ha''. rewrite put_rg_next, add_fact_next, Hn1 in Ha''.
    exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (in_or_app _ _ _ (or_introl Hin'')) Hd''' Hi'' Hx'' Hw'' Ha'').
  - (* [comment removed for export] *)
    assert (Hl : Z.ltb clo hi = true) by (apply Z.ltb_lt; lia). rewrite Hl in H2.
    destruct (Z.leb (Z.of_nat k) clo) eqn:H16; [|discriminate]. apply Z.leb_le in H16.
    assert (Hv : lden E c = len_word (file_read data0 (lden E off) (Z_to_bv 64 cnt))).
    { apply bv_eq. unfold len_word. fold cnt. rewrite u_small64 by (rewrite Hlfr; unfold two64; lia). rewrite Hlfr. lia. }
    apply (den_read_file2 segs cfg LIMIT mem0 model0 E S M ms model1 _ 3 cnt path0 (lden E off) data0 i R o c
             Hd1 H7 H0 Hc2' ltac:(lia) chi ltac:(lia) HR Hkd ltac:(lia) Hbuf Hsz Hfd3 (Hlk Hdr) Hwc Hv Hok Hav).
    intros ms' m'' Hd'' Hcont.
    set (S1 := read_post S i o (o + chi) c) in *.
    assert (Hn1 : s_next S1 = s_next S) by apply read_post_next.
    assert (Hd2 : DEN segs LIMIT (with_fds (fd_insert (m_fds model0) (fd32 (Z_to_bv 64 3)) (FdFile path0 (lden E off + lden E c))) model0)
                      mem0 E (add_fact S1 (FRange (lsub rem c) 1 hi)) M ms' m'').
    { eapply den_addfact; [exact Hd''|].
      intros E' Ha'. cbn [fact_ok]. rewrite Hn1 in Ha'. rewrite (lden_agree_wf _ E E' _ (lwf_lsub _ _ _ Hwrem Hwc) Ha').
      rewrite lden_lsub, bv_sub_unsigned. fold cnt. rewrite Hrem. unfold bv_wrap.
      rewrite Z.mod_small by (change (bv_modulus 64) with two64; unfold two64; lia). lia. }
    assert (Hi' : INV mem0 E (add_fact S1 (FRange (lsub rem c) 1 hi)) M (FSOpen (ladd off c) FL)
                    (with_fds (fd_insert (m_fds model0) (fd32 (Z_to_bv 64 3)) (FdFile path0 (lden E off + lden E c))) model0)).
    { unfold INV. rewrite add_fact_next, Hn1. split; [exact Hpv|].
      split; [cbn [fs_wf]; rewrite HwFL, andb_true_r; exact (lwf_ladd _ _ _ Hwoff Hwc)|].
      split; [exact Hfr|]. split; [exact Hm0|]. split; [exact Hlen|]. split; [intros Hdr'; rewrite with_fds_fs; exact (Hlk Hdr')|]. split; [rewrite with_fds_fs; exact Hfs0|].
      rewrite fd32_3.
      split; [|split; [rewrite with_fds_fds, fd_lookup_insert_other by (first [exact w3_ne1 | exact w3_ne2]); exact Hch1|]].
      2: { split; [rewrite with_fds_fds, fd_lookup_insert_other by (first [exact w3_ne1 | exact w3_ne2]); exact Hch2|].
           exact (hv_inv_step E E S _ Hdv (agree_refl _ _) ltac:(rewrite add_fact_next, Hn1; lia)). }
      rewrite with_fds_fds, fd_lookup_insert_same. rewrite lden_ladd.
      split; [reflexivity|]. split; [exact HFL'|].
      rewrite bv_add_unsigned. fold cnt. unfold bv_wrap.
      pose proof (bv_unsigned_in_range _ (lden E off)) as Y. unfold bv_modulus in Y. change (2 ^ Z.of_N 64) with two64 in Y.
      rewrite Z.mod_small by (change (bv_modulus 64) with two64; unfold two64 in *; unfold remz in Hcb; lia). unfold remz in Hcb. lia. }
    assert (Hd3 : DEN segs LIMIT (with_fds (fd_insert (m_fds model0) (fd32 (Z_to_bv 64 3)) (FdFile path0 (lden E off + lden E c))) model0)
                      mem0 E (track_hdr (add_fact S1 (FRange (lsub rem c) 1 hi)) i o h k) M ms' m'').
    { apply (den_track_hdr _ mem0 E (add_fact S1 (FRange (lsub rem c) 1 hi)) M ms' m'' i
               (RG (rg_base R) (rg_size R) RW (havoc_range (rg_cont R) o (o + chi))) o h k b sz (file_read data0 (lden E off) (Z_to_bv 64 cnt)) Hd2 Hk16
               ltac:(cbn [add_fact s_rgs]; unfold S1, read_post; rewrite HR; cbn [s_rgs]; exact (nth_upd_same _ _ _ _ HR))
               eq_refl Hb0 Hs0 ltac:(lia) ltac:(lia) ltac:(rewrite add_fact_next, Hn1; exact Hh16) ltac:(lia) ltac:(unfold two64; lia)).
      - intros j Hj. rewrite Hcont, Hub. apply wtm_nth; [lia | rewrite Hlfr; unfold two64; lia | apply Nat2Z.inj_lt; rewrite Hlfr; lia].
      - assert (Hoffz : bv_unsigned (lden E off) = 0) by (rewrite Hoff0; reflexivity).
        exact (hdr_link E h k off cnt Hoff0 Hk16 Hdv' ltac:(unfold remz in *; lia) ltac:(unfold two64; lia)). }
    apply (IHb _ _ _ _ _ f2 H2 _ mem0 E ms' m'' Hd3 (INV_same _ _ _ _ _ _ _ Hi' (put_rg_next _ i o (hdr_bvs h k))) (HAX_same E S _ M a mem0 HX ltac:(unfold track_hdr; rewrite put_rg_next, add_fact_next, Hn1; reflexivity))
             ltac:(unfold track_hdr; rewrite put_rg_next, add_fact_next, Hn1; exact Hw)).
    intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd''' Hi'' Hx'' Hw'' Ha''.
    unfold track_hdr in Ha''. rewrite put_rg_next, add_fact_next, Hn1 in Ha''.
    exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (in_or_app _ _ _ (or_intror Hin'')) Hd''' Hi'' Hx'' Hw'' Ha'').
Qed.


(* [comment removed for export] *)
#[using="Himg path0 data0 Hp4"] Lemma bytes_ok_rd1 : forall E m fs rgs B0 bs j, Forall (rg_ok segs E m) rgs -> Forall (fact_ok E) fs ->
  bytes_ok img fs rgs B0 bs j = true ->
  forall i, (i < length bs)%nat -> rd1 segs m (Z_to_bv 64 (B0 + j + Z.of_nat i)) = Some (Z_to_bv 8 (nth i bs 0)).
Proof. LiaFast.lf_pins (fun (Himg path0 data0 Hp4 : LiaFast.U) => LiaFast.u0).
  intros E m fs rgs B0 bs. induction bs as [|x r IH]; intros j HG HF Hok i Hi; cbn [length] in Hi; [lia|].
  cbn [bytes_ok] in Hok.
  destruct (load_at img fs rgs (lconst (B0 + j)) SZ1 false) as [[l|]|] eqn:Hl; try discriminate.
  apply andb_prop in Hok as [Hx Hr]. apply lin_eqb_eq in Hx. subst l.
  destruct i as [|i].
  - destruct (load_at_sound segs E img fs rgs _ SZ1 false _ m Himg HG HF Hl) as (bs1 & Hrd & Hv).
    specialize (Hv (lconst x) eq_refl). rewrite ov_rdn in Hrd. cbn [nbytes rdn] in Hrd.
    destruct (match m (lden E (lconst (B0 + j))) with Some b => Some b | None => seg_rom segs (lden E (lconst (B0 + j))) end) as [b1|] eqn:Hb1;
      [|discriminate].
    injection Hrd as <-. rewrite ld1_byte, lden_lconst in Hv. rewrite lden_lconst in Hb1.
    rewrite Z.add_0_r. unfold rd1. rewrite Hb1. f_equal. cbn [nth].
    apply bv_eq. apply (f_equal bv_unsigned) in Hv. rewrite !Z_to_bv_unsigned in Hv. rewrite Z_to_bv_unsigned.
    pose proof (bv_unsigned_in_range _ b1) as Hb. change (bv_modulus 8) with 256 in Hb.
    unfold bv_wrap in *. change (bv_modulus 64) with (2 ^ 64) in Hv. change (bv_modulus 8) with 256.
    rewrite (Z.mod_small (bv_unsigned b1)) in Hv by lia.
    rewrite (Zmod_div_mod 256 (2 ^ 64) x) by (first [lia | exists 72057594037927936; reflexivity]). rewrite Hv. symmetry. apply Z.mod_small. lia.
  - cbn [nth]. replace (B0 + j + Z.of_nat (Datatypes.S i)) with (B0 + (j + 1) + Z.of_nat i) by lia. exact (IH (j + 1) HG HF Hr i ltac:(lia)).
Qed.

#[using="path0 data0 Hp4"] Lemma rd1_full_rdn : forall m X n (f : nat -> byte), 0 <= X -> X + Z.of_nat n <= two64 ->
  (forall i, (i < n)%nat -> rd1 segs m (Z_to_bv 64 (X + Z.of_nat i)) = Some (f i)) ->
  rdn segs m (Z_to_bv 64 X) n = Some (List.map f (seq 0 n)).
Proof. LiaFast.lf_pins (fun (path0 data0 Hp4 : LiaFast.U) => LiaFast.u0).
  intros m X n f HX Hn Hall.
  destruct (rdn_from segs m n X HX Hn) as (bs & Hbs & Hlen & Hnth).
  { intros i Hi. rewrite <- (Z2Nat.id i) by lia. rewrite (Hall (Z.to_nat i) ltac:(lia)). discriminate. }
  rewrite Hbs. f_equal. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i n) as [Hi|Hi].
  - rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec i n) as [_|Hc]; [|lia]. cbn [option_map]. rewrite Nat.add_0_l.
    destruct (nth_error bs i) as [b|] eqn:Hb.
    + pose proof (Hnth i b Hb) as X1. rewrite (Hall i Hi) in X1. congruence.
    + apply nth_error_None in Hb. lia.
  - rewrite (proj2 (nth_error_None bs i)) by lia. symmetry. apply nth_error_None. rewrite length_map, length_seq. lia.
Qed.

#[using="path0 data0 Hp4"] Lemma map_seq_skipn : forall (bs : list Z) k, (k <= length bs)%nat ->
  List.map (fun i => Z_to_bv 8 (nth (k + i) bs 0)) (seq 0 (length bs - k)) = skipn k (List.map (Z_to_bv 8) bs).
Proof. LiaFast.lf_pins (fun (path0 data0 Hp4 : LiaFast.U) => LiaFast.u0).
  intros bs k Hk. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs - k)) as [Hi|Hi].
  - rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec i (length bs - k)) as [_|Hc]; [|lia]. cbn [option_map]. rewrite Nat.add_0_l. rewrite nth_error_skipn.
    rewrite nth_error_map. rewrite (nth_error_nth' bs 0) by lia. reflexivity.
  - rewrite (proj2 (nth_error_None _ i)) by (rewrite length_map, length_seq; lia). symmetry. apply nth_error_None.
    rewrite length_skipn, length_map. lia.
Qed.

#[using="Hwx Himg Hect Hp4 awf_mono HA_agree"] Lemma Pm_writev : forall B0 k, Pm k -> Pm (MWritev B0 k).
Proof. LiaFast.lf_pins (fun (Hwx Himg Hect Hp4 awf_mono HA_agree : LiaFast.U) => LiaFast.u0).
  intros B0 k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct sh as [po kc|sa sb|lq loq hiq sa sb|lq jq sa sb]; try discriminate. destruct po as [|p rest]; try discriminate.
  destruct (is_ecall t (s_pc S)) eqn:Hx; [|discriminate]. apply is_ecall_ok in Hx.
  destruct (writev_ok img S B0 p) as [len|] eqn:Hok; [|discriminate].
  destruct p as [ch [bs|pre j lj suf] off]; [|unfold writev_ok in Hok; discriminate Hok]. unfold writev_ok in Hok. cbn [pd_src src_len] in Hck.
  set (iov := argl S 1) in *.
  destruct (a7c S) as [c7|] eqn:H7; [|discriminate]. destruct (arg S 0) as [c0|] eqn:H0; [|discriminate].
  destruct (arg S 2) as [c2|] eqn:H2; [|discriminate].
  destruct (load_at img (s_facts S) (s_rgs S) iov SZ8 false) as [[b|]|] eqn:Hlb; try discriminate.
  destruct (load_at img (s_facts S) (s_rgs S) (laddc iov 8) SZ8 false) as [[len'|]|] eqn:Hll; try discriminate.
  set (n := Z.of_nat (length bs)) in *.
  destruct (Z.eqb c7 66 && Z.eqb c0 ch && (Z.eqb ch 1 || Z.eqb ch 2) && Z.eqb c2 1 &&
            lin_eqb b (laddc off B0) && lin_eqb len' (laddc (lneg off) n) && bytes_ok img (s_facts S) (s_rgs S) B0 bs 0 &&
            Z.leb 0 (fst (irange (s_facts S) off)) && Z.ltb (snd (irange (s_facts S) off)) n && Z.leb 1 n && Z.leb n 1073741824 &&
            Z.leb 0 B0 && Z.leb (B0 + n) TASK_SIZE && Z.leb (snd (irange (s_facts S) iov) + 16) TASK_SIZE &&
            lwf (s_next S) off && lwf (s_next S) iov)%bool eqn:Hb; [|discriminate].
  injection Hok as <-.
  repeat match type of Hb with ((_ && _)%bool = true) => apply andb_prop in Hb as [Hb ?Hq] end.
  rename Hb into H66. apply Z.eqb_eq in H66. subst c7.
  repeat match goal with
         | Hx' : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in Hx'
         | Hx' : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx'
         | Hx' : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hx'
         | Hx' : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in Hx'
         end.
  subst c0 c2 b len'.
  assert (Hch : ch = 1 \/ ch = 2).
  { match goal with Hq' : (Z.eqb ch 1 || Z.eqb ch 2)%bool = true |- _ => apply orb_prop in Hq' as [Hq'|Hq']; apply Z.eqb_eq in Hq'; auto end. }
  assert (Hbo : bytes_ok img (s_facts S) (s_rgs S) B0 bs 0 = true) by assumption.
  assert (Hwoff : lwf (s_next S) off = true) by assumption.
  assert (Hwiov : lwf (s_next S) iov = true) by assumption.
  cbn [shp_wf forallb pend_wf pd_src pd_off] in Hw. apply andb_prop in Hw as [_ Hwr].
  pose proof Hi as Hi0. destruct Hi0 as (Hpv & Hfsw & Hfr & Hm0 & Hlen & Hlk & Hfs0 & Hfds & Hch1 & Hch2 & Hdv).
  apply (den_ecall segs cfg LIMIT model0 mem0 Hwx t E S M ms model _ Hect Hx Hd). intros model1 Hd1.
  set (H1 := Hof E M model1).
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd1)) as (_ & _ & _ & _ & HG0 & _ & HF0 & _).
  pose proof (dn_hoff _ _ _ _ _ _ _ _ _ Hd1) as Hhoff. fold H1 in HG0, Hhoff. cbn [restrict ms_mem] in HG0.
  (* [comment removed for export] *)
  pose proof (irange_sound E _ off HF0) as Ro.
  set (uo := bv_unsigned (lden E off)) in *.
  assert (Huo : 0 <= uo < n) by (unfold uo; lia).
  pose proof (irange_sound E _ iov HF0) as Ri.
  (* [comment removed for export] *)
  destruct (load_at_sound segs E img _ _ iov SZ8 false _ _ Himg HG0 HF0 Hlb) as (bs8a & Hra & Hva). specialize (Hva _ eq_refl).
  destruct (load_at_sound segs E img _ _ (laddc iov 8) SZ8 false _ _ Himg HG0 HF0 Hll) as (bs8b & Hrb & Hvb). specialize (Hvb _ eq_refl).
  rewrite ov_rdn in Hra, Hrb. cbn [nbytes] in Hra, Hrb.
  destruct (rdn_restrict_vis segs mem0 H1 (ms_mem ms) 8 _ bs8a Hhoff Hra) as [Hra' Hava].
  destruct (rdn_restrict_vis segs mem0 H1 (ms_mem ms) 8 _ bs8b Hhoff Hrb) as [Hrb' Havb].
  assert (Hl8a : length bs8a = 8%nat) by exact (rdn_length _ _ _ _ _ Hra').
  assert (Hl8b : length bs8b = 8%nat) by exact (rdn_length _ _ _ _ _ Hrb').
  assert (Hiov8 : lden E (laddc iov 8) = Z_to_bv 64 (bv_unsigned (lden E iov) + 16 - 8)) by (rewrite lden_laddc; f_equal; lia).
  (* [comment removed for export] *)
  assert (Hrd : forall i, (i < length bs - Z.to_nat uo)%nat ->
            rd1 segs (mrestrict H1 (ms_mem ms)) (Z_to_bv 64 ((B0 + uo) + Z.of_nat i)) = Some (Z_to_bv 8 (nth (Z.to_nat uo + i) bs 0))).
  { intros i Hi'. rewrite <- (bytes_ok_rd1 E _ _ _ B0 bs 0 HG0 HF0 Hbo (Z.to_nat uo + i) ltac:(lia)). f_equal. f_equal. lia. }
  pose proof (rd1_full_rdn (mrestrict H1 (ms_mem ms)) (B0 + uo) (length bs - Z.to_nat uo) (fun i => Z_to_bv 8 (nth (Z.to_nat uo + i) bs 0))
                ltac:(lia) ltac:(unfold TASK_SIZE, two64 in *; lia) Hrd) as Hrm.
  rewrite map_seq_skipn in Hrm by lia.
  destruct (rdn_restrict_vis segs mem0 H1 (ms_mem ms) _ _ _ Hhoff Hrm) as [Hrm' Havm].
  set (bsr := skipn (Z.to_nat uo) (List.map (Z_to_bv 8) bs)) in *.
  assert (Hlr : length bsr = (length bs - Z.to_nat uo)%nat) by (unfold bsr; rewrite length_skipn, length_map; reflexivity).
  assert (HbE : lden E (laddc off B0) = Z_to_bv 64 (B0 + uo)) by (rewrite lden_laddc; fold uo; f_equal; lia).
  assert (HlenE : bv_unsigned (lden E (laddc (lneg off) n)) = Z.of_nat (length bsr)).
  { rewrite lden_laddc, Z_to_bv_unsigned. rewrite lneg_eq. rewrite lden_lscale. rewrite Z_to_bv_unsigned. fold uo.
    unfold bv_wrap. change (bv_modulus 64) with two64. rewrite Z.add_mod_idemp_l by (unfold two64; lia).
    unfold M64. replace (18446744073709551615 * uo + n) with ((n - uo) + uo * two64) by (unfold two64; lia).
    rewrite Z.mod_add by (unfold two64; lia). rewrite Z.mod_small by (unfold two64; lia).
    rewrite Hlr, Nat2Z.inj_sub by lia. rewrite Z2Nat.id by lia. reflexivity. }
  (* [comment removed for export] *)
  set (REST := concat (List.map (pend_evs E) rest)).
  set (K := t_emit REST (t_exit (Z_to_bv 64 kc) fs0)).
  assert (HK0 : K []) by apply t_emit_has_nil.
  assert (Hpe : pend_evs E (PD ch (SLit bs) off) = List.map (WriteEv (Z_to_bv 64 ch)) bsr) by reflexivity.
  eapply rzc_conseq; [|cbn [shp_den List.map concat]; rewrite Hpe; apply t_eq_sym; apply t_emit_app].
  fold REST.
  assert (Hfch : fd_lookup (m_fds model0) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch))) by (destruct Hch as [->| ->]; assumption).
  apply (den_writev segs cfg LIMIT mem0 model0 E S M ms model1 K ch (laddc off B0) (laddc (lneg off) n) bsr n Hd1 H7 H0 H2 Hch Hfch
           ltac:(fold iov; rewrite Hra'; f_equal; rewrite Hva; symmetry; exact (ld8_bytes _ Hl8a))
           ltac:(fold iov; rewrite <- Hiov8; rewrite Hrb'; f_equal; rewrite Hvb; symmetry; exact (ld8_bytes _ Hl8b))
           ltac:(rewrite HbE; rewrite Hlr; exact Hrm')
           HlenE ltac:(rewrite Hlr; lia) ltac:(rewrite Hlr; lia) ltac:(lia) ltac:(fold iov; first [solve [clear - Ri Hq3; lia] | solve [clear - Ri Hq4; lia] | (unfold uE in *; lia)])
           ltac:(rewrite HbE, u_small64 by (unfold TASK_SIZE, two64 in *; lia); rewrite Hlr; lia)).
  - intros kk Hkk. fold iov H1. destruct (Nat.lt_ge_cases kk 8) as [Hk8|Hk8]; [exact (Hava kk Hk8)|].
    replace (woff (lden E iov) kk) with (woff (lden E (laddc iov 8)) (kk - 8)); [apply Havb; first [solve [clear - Hk8 Hk16; lia] | solve [clear - Hk8 Hkk; lia] | lia]|].
    unfold woff. rewrite lden_laddc. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. first [solve [clear - Hk8; lia] | solve [clear - Hk16; lia] | solve [clear - Hk24; lia] | lia].
  - fold H1. rewrite HbE. rewrite Hlr. exact Havm.
  - apply lwf_laddc. rewrite lneg_eq. apply lwf_lscale. exact Hwoff.
  - exact HK0.
  - intros E' ms' m'' Hd' Ha' Hkr.
    set (kv := s_next S) in *.
    set (kz := bv_unsigned (E' kv)) in *.
    assert (Hn' : s_next (wv_post S (laddc (lneg off) n) n) = Pos.succ (s_next S)) by reflexivity.
    assert (Hoff' : lden E' off = lden E off) by exact (lden_agree_wf _ E E' off Hwoff Ha').
    assert (Hi' : INV mem0 E' (wv_post S (laddc (lneg off) n) n) M FS model0).
    { apply (INV_agree mem0 E E' S _ M M FS model0 Hi Ha' ltac:(rewrite Hn'; lia) eq_refl (dn_wf _ _ _ _ _ _ _ _ _ Hd)). }
    assert (Hw' : shp_wf (s_next (wv_post S (laddc (lneg off) n) n)) (wv_shp (ShEmit (PD ch (SLit bs) off :: rest) kc) S) = true).
    { rewrite Hn'. cbn [wv_shp shp_wf forallb pend_wf pd_src pd_off]. apply andb_true_intro. split.
      - apply lwf_ladd; [exact (lwf_mono (s_next S) (Pos.succ (s_next S)) off ltac:(lia) Hwoff)|]. unfold lwf, lvar. cbn. rewrite andb_true_r. apply Pos.ltb_lt. lia.
      - exact (shp_wf_mono (s_next S) (Pos.succ (s_next S)) (ShEmit rest kc) ltac:(lia) Hwr). }
    eapply rzc_conseq.
    + apply (IH _ _ _ _ _ finals Hck model0 mem0 E' ms' m'' Hd' Hi'
               (HAX_step E E' S (wv_post S (laddc (lneg off) n) n) M a mem0 HX (dn_wf _ _ _ _ _ _ _ _ _ Hd) Ha' ltac:(rewrite Hn'; lia)) Hw').
      intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' Hx'' Hw'' Ha''.
      exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' Hx'' Hw''
               (agree_trans _ E E' E'' Ha' (agree_mono (s_next S) (s_next (wv_post S (laddc (lneg off) n) n)) E' E'' ltac:(rewrite Hn'; lia) Ha''))).
    + cbn [wv_shp shp_den List.map concat]. eapply t_eq_trans; [apply t_emit_app|].
      assert (HR : concat (List.map (pend_evs E') rest) = REST).
      { unfold REST. f_equal. apply map_ext_in. intros q Hqin.
        rewrite forallb_forall in Hwr. exact (pend_evs_agree _ E E' q (Hwr q Hqin) Ha'). }
      rewrite HR. fold K.
      assert (Hpk : pend_evs E' (PD ch (SLit bs) (ladd off (lvar kv))) = List.map (WriteEv (Z_to_bv 64 ch)) (skipn (Z.to_nat kz) bsr)).
      { unfold pend_evs, bsr. cbn [pd_ch pd_src pd_off src_bytes]. f_equal. rewrite skipn_skipn. f_equal.
        unfold uE. rewrite lden_ladd, lden_lvar, Hoff'. rewrite bv_add_unsigned. fold uo kz. unfold bv_wrap.
        rewrite Z.mod_small by (change (bv_modulus 64) with two64; unfold two64; rewrite Hlr in Hkr; lia). lia. }
      fold kv. rewrite Hpk. apply t_eq_refl.
Qed.

#[using="data0 Hp4"] Lemma pend_done_nil : forall E fs p, Forall (fact_ok E) fs -> pend_done fs p = true -> pend_evs E p = [].
Proof. LiaFast.lf_pins (fun (data0 Hp4 : LiaFast.U) => LiaFast.u0).
  intros E fs [ch [bs|pre j lj suf] off] HF H; unfold pend_done in H; cbn [pd_src pd_off] in H.
  - apply Z.leb_le in H.
    pose proof (irange_sound E fs off HF) as R. unfold pend_evs. cbn [pd_src pd_off src_bytes].
    rewrite skipn_all2; [reflexivity|]. rewrite length_map. unfold uE. lia.
  - destruct (irange fs (lsub off lj)) as [dlo dhi] eqn:Hdr.
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2, H3.
    pose proof (irange_sound E fs (lsub off lj) HF) as R. rewrite Hdr in R. cbn [fst snd] in R.
    pose proof (irange_sound E fs lj HF) as Rl.
    unfold pend_evs. cbn [pd_src pd_off src_bytes]. rewrite skipn_all2; [reflexivity|].
    rewrite !length_app, !length_map. pose proof (firstn_le_length (Z.to_nat (uE E lj)) (sarg j)) as Hf.
    rewrite lden_lsub in R. rewrite bv_sub_unsigned in R. unfold bv_wrap in R. change (bv_modulus 64) with two64 in R.
    pose proof (u_range E off) as Ro. pose proof (u_range E lj) as Rj. unfold uE in *.
    set (uo := bv_unsigned (lden E off)) in *. set (ul := bv_unsigned (lden E lj)) in *.
    assert (Hge : ul <= uo).
    { destruct (Z_lt_le_dec uo ul) as [Hlt|Hle]; [|exact Hle]. exfalso.
      rewrite <- (Z.mod_add (uo - ul) 1 two64) in R by (unfold two64; lia).
      rewrite Z.mod_small in R by (unfold two64 in *; lia). unfold two64 in *. lia. }
    rewrite Z.mod_small in R by (unfold two64 in *; lia). lia.
Qed.

#[using="data0 Hp4"] Lemma pends_done_nil : forall E fs po, Forall (fact_ok E) fs -> forallb (pend_done fs) po = true -> concat (List.map (pend_evs E) po) = [].
Proof. LiaFast.lf_pins (fun (data0 Hp4 : LiaFast.U) => LiaFast.u0).
  intros E fs po HF. induction po as [|p po IH]; intros Hpo; [reflexivity|]. cbn [forallb] in Hpo. apply andb_prop in Hpo as [Hpa Hpb].
  cbn [List.map concat]. rewrite (pend_done_nil E _ p HF Hpa). apply IH. exact Hpb.
Qed.

#[using="Hwx Hect Hp4"] Lemma Pm_exit : Pm MExit.
Proof. LiaFast.lf_pins (fun (Hwx Hect Hp4 : LiaFast.U) => LiaFast.u0).
  intros S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct sh as [po kc|sa sb|lq loq hiq sa sb|lq jq sa sb]; try discriminate.
  destruct (is_ecall t (s_pc S) && exit_args_ok S kc && forallb (pend_done (s_facts S)) po)%bool eqn:Hb; [|discriminate].
  apply andb_prop in Hb as [Hb Hpo]. apply andb_prop in Hb as [Hx Hea]. apply is_ecall_ok in Hx.
  unfold exit_args_ok in Hea. destruct (a7c S) as [c7|] eqn:H7; [|discriminate]. destruct (arg S 0) as [c0|] eqn:H0; [|discriminate].
  apply andb_prop in Hea as [Hea Hk2]. apply andb_prop in Hea as [Hea Hk1]. apply andb_prop in Hea as [H9 Hc0].
  apply Z.leb_le in Hk1, Hk2. apply Z.eqb_eq in Hc0. subst c0.
  pose proof Hi as Hi0. destruct Hi0 as (_ & _ & _ & _ & _ & _ & Hfs0 & _).
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF0 & _).
  apply (den_ecall segs cfg LIMIT model0 mem0 Hwx t E S M ms model _ Hect Hx Hd). intros model1 Hd1.
  pose proof Hd1 as Hd10.
  destruct Hd10 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  assert (Hx8 : ms_reg ms 17 = Z_to_bv 64 c7) by exact (a7_const segs E S (restrict (Hof E M model1) ms) ms c7 Hsd eq_refl H7).
  assert (Hg0 : ms_gpr (svc_set ms) 0 = Z_to_bv 64 kc) by exact (gpr_const segs E S (restrict (Hof E M model1) ms) ms 0 kc Hsd eq_refl ltac:(lia) H0).
  eapply rzc_conseq.
  - apply (rzc_exit segs cfg (svc_set ms) model1 (ms_reg ms 17) Hh eq_refl).
    unfold exit_sysno. rewrite Hx8, u_small64 by (apply orb_prop in H9 as [H9|H9]; apply Z.eqb_eq in H9; subst c7; unfold two64; lia).
    apply orb_prop in H9 as [H9|H9]; apply Z.eqb_eq in H9; [right | left]; exact H9.
  - cbn [shp_den]. rewrite Hg0.
    assert (Hnil : concat (List.map (pend_evs E) po) = []) by exact (pends_done_nil E _ po HF0 Hpo).
    rewrite Hnil.
    assert (Hand : bv_and (Z_to_bv 64 kc) (Z_to_bv 64 255) = Z_to_bv 64 kc).
    { apply bv_eq. rewrite bv_and_unsigned, !u_small64 by (unfold two64; lia). change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
      apply Z.mod_small. change (2 ^ 8) with 256. lia. }
    rewrite Hand.
    assert (Hfsm : m_fs model1 = fs0).
    { rewrite <- Hfs0. destruct Hvmo as (_ & _ & H3' & _). unfold m_fs. rewrite H3'. reflexivity. }
    rewrite Hfsm. apply t_eq_sym. apply t_emit_nil_eq. apply t_emit_has_nil.
Qed.

(* [comment removed for export] *)
#[using="Hp4"] Lemma INV_ent : forall mem0 E S P M FS FP model0 n0,
  INV mem0 E S M FS model0 -> (s_next S <= n0)%positive -> params_fixed (match_st S P) (pos_below n0) = true ->
  pv_okb pv hv n0 = true -> sm_wf n0 M = true -> fs_ent FS FP (match_st S P) = true -> fs_wf (s_next P) FP = true -> (n0 <= s_next P)%positive ->
  INV mem0 (ecomp E (match_st S P)) P M FP model0.
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros mem0 E S P M FS FP model0 n0 Hi Hn Hpf Hpvk Hwf0 Hfe Hfw Hn1. unfold pv_okb in Hpvk. apply andb_prop in Hpvk as [Hpv0 Hhv0].
  set (σ := match_st S P) in *. set (E0 := ecomp E σ).
  assert (Ha : agree n0 E E0) by exact (agree_params n0 E σ Hpf).
  destruct Hi as (Hpv & Hfsw & Hfr & Hm0 & Hlen & Hlk & Hfs0 & Hfds & Hc1 & Hc2 & Hdv).
  assert (Hpv' : lden E0 pv = lden E pv) by exact (lden_agree_wf _ E E0 pv Hpv0 Ha).
  pose proof (sm_wf_frz _ M Hwf0) as Hwz.
  split; [exact (lwf_mono _ _ _ Hn1 Hpv0)|]. split; [exact Hfw|].
  split.
  { intros Hdr k Hk. destruct (Hfr Hdr k Hk) as (p & Hp & Hr). exists p. split; [exact Hp|].
    rewrite Forall_forall in Hwz. destruct (Hwz p Hp) as [W1 W2]. unfold uE in *.
    rewrite (lden_agree_wf _ E E0 _ W1 Ha), (lden_agree_wf _ E E0 _ W2 Ha), Hpv'. exact Hr. }
  split.
  { split; [intros Hdr k Hk; rewrite Hpv'; exact (proj1 Hm0 Hdr k Hk)|].
    intros Hdr w Hw. rewrite Hpv' in Hw. destruct (proj2 Hm0 Hdr w Hw) as [(p & Hp & Hr) Hne]. split; [|exact Hne].
    exists p. split; [exact Hp|].
    rewrite Forall_forall in Hwz. destruct (Hwz p Hp) as [W1 W2]. unfold uE in *.
    rewrite (lden_agree_wf _ E E0 _ W1 Ha), (lden_agree_wf _ E E0 _ W2 Ha). exact Hr. }
  split; [rewrite Hpv'; exact Hlen|]. split; [exact Hlk|]. split; [exact Hfs0|].
  split; [|split; [exact Hc1 | split; [exact Hc2 | exact (hv_inv_agree n0 E E0 S P Hdv Ha Hhv0 Hn1)]]].
  destruct FS as [|off FL| | |off FL]; destruct FP as [|off' FL'| | |off' FL']; cbn [fs_ent] in Hfe; try discriminate; [exact Hfds| |exact I|exact Hfds| ];
  (apply andb_prop in Hfe as [Ho Hf]; apply lin_eqb_eq in Ho, Hf;
   unfold E0; rewrite <- !lden_lsubst; rewrite <- Ho, <- Hf; exact Hfds).
Qed.

#[using="Type"] Lemma went_parts : forall n0 S M FS sh P FP shP, went n0 S M FS sh P FP shP = true ->
  ent_ok n0 S P M = true /\ (s_next S <= n0)%positive /\ fs_ent FS FP (match_st S P) = true /\ shp_ent sh shP (match_st S P) = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n0 S M FS sh P FP shP H. unfold went in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Pos.leb_le in H2. auto.
Qed.
#[using="Type"] Lemma ent_ok_parts : forall n0 S P M, ent_ok n0 S P M = true ->
  params_fixed (match_st S P) (pos_below n0) = true /\ sm_wf n0 M = true /\ (n0 <= s_next P)%positive.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n0 S P M H. unfold ent_ok in H.
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply Pos.leb_le in H5. rewrite fixed_below_eq in H3. auto.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma ent_okN_ok : forall n0 S P M, state_wf P = true -> ent_okN (match_st S P) n0 S P M = true -> ent_ok n0 S P M = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n0 S P M Hw H. unfold ent_okN in H. unfold ent_ok. cbv zeta.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. rewrite H1, Hw, H2, H3, H4. reflexivity.
Qed.
#[using="Type"] Lemma wentN_ok : forall n0 S M FS sh P FP shP, state_wf P = true -> wentN n0 S M FS sh P FP shP = true -> went n0 S M FS sh P FP shP = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n0 S M FS sh P FP shP Hw H. unfold wentN in H. unfold went. cbv zeta in H |- *.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. rewrite (ent_okN_ok _ _ _ _ Hw H1), H2, H3, H4. reflexivity.
Qed.
#[using="Type"] Lemma ent_ok_wf : forall n0 S P M, ent_ok n0 S P M = true -> state_wf P = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n0 S P M H. unfold ent_ok in H. cbv zeta in H.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H]. exact H.
Qed.
#[using="Type"] Lemma forallb_wentN : forall (P : sst) (n0 : positive) (FS0 : fstate) (sh0 : shp) (M0 : smodel) (a0 : A) (J : list (sst * smodel * fstate * shp * A)),
  state_wf P = true ->
  forallb (fun '(F, MF, FSF, shF, aF) => wentN n0 F MF FSF shF P FS0 sh0 && sm_eqb MF M0 && aeqb aF a0) J = true ->
  forallb (fun '(F, MF, FSF, shF, aF) => went n0 F MF FSF shF P FS0 sh0 && sm_eqb MF M0 && aeqb aF a0) J = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros P n0 FS0 sh0 M0 a0 J Hw. induction J as [|[[[[F MF] FSF] shF] aF] J IH]; intros H; [reflexivity|].
  cbn [forallb] in H |- *. apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [H1 Ha]. apply andb_prop in H1 as [H1 Hs].
  rewrite (wentN_ok _ _ _ _ _ _ _ _ Hw H1), Hs, Ha, (IH H2). reflexivity.
Qed.

#[using="Hp4 awf_mono HA_agree"] Lemma Pm_weaken : forall P n0 FP shP k, Pm k -> Pm (MWeaken P n0 FP shP k).
Proof. LiaFast.lf_pins (fun (Hp4 awf_mono HA_agree : LiaFast.U) => LiaFast.u0).
  intros P n0 FP shP k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (went n0 S M FS sh P FP shP && fs_wf (s_next P) FP && shp_wf (s_next P) shP && pv_okb pv hv n0 && awf n0 a)%bool eqn:Hb; [|discriminate].
  apply andb_prop in Hb as [Hb Hwa0]. apply andb_prop in Hb as [Hb Hpv0]. apply andb_prop in Hb as [Hb HwP]. apply andb_prop in Hb as [Hwe Hfw].
  destruct (went_parts _ _ _ _ _ _ _ _ Hwe) as (Hok & Hn & Hfe & Hse).
  destruct (ent_ok_parts _ _ _ _ Hok) as (Hpf & Hwf0 & Hn1).
  destruct (den_weaken segs LIMIT model0 mem0 E S P M ms model n0 Hd Hok) as [Hd0 Ha0].
  pose proof (INV_ent mem0 E S P M FS FP model0 n0 Hi Hn Hpf Hpv0 Hwf0 Hfe Hfw Hn1) as Hi0.
  assert (HX0 : HAX (ecomp E (match_st S P)) P M a mem0) by exact (conj (awf_mono _ _ a Hn1 Hwa0) (HA_agree n0 E _ M a mem0 Hwf0 Hwa0 Ha0 (proj2 HX))).
  rewrite <- (shp_den_ent E sh shP _ Hse).
  apply (IH P M FP shP a finals Hck model0 mem0 _ ms model Hd0 Hi0 HX0 HwP).
  intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' Hx'' Hw'' Ha''.
  apply (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' Hx'' Hw'').
  apply (agree_trans _ E (ecomp E (match_st S P)) E'').
  - exact (agree_mono _ _ E _ Hn Ha0).
  - exact (agree_mono (s_next S) (s_next P) _ E'' ltac:(lia) Ha'').
Qed.

#[using="Type"] Lemma maps_eqb_eq : forall a b, maps_eqb a b = true -> a = b.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction a as [|[[x n] k] a IH]; intros [|[[y m] k'] b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply lin_eqb_eq in H1. apply lin_eqb_eq in H2. destruct k, k'; try discriminate; subst; f_equal; exact (IH b H4).
Qed.
#[using="Type"] Lemma allow_eqb_eq : forall a b, allow_eqb a b = true -> a = b.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction a as [|[x n] a IH]; intros [|[y m] b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply lin_eqb_eq in H1. apply Z.eqb_eq in H2. subst. f_equal. exact (IH b H3).
Qed.
#[using="Type"] Lemma zr_eqb_eq : forall a b, zr_eqb a b = true -> a = b.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction a as [|[x n] a IH]; intros [|[y m] b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1, H2. subst. f_equal. exact (IH b H3).
Qed.
#[using="Type"] Lemma sm_eqb_eq : forall a b, sm_eqb a b = true -> a = b.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros [ma aa za ta ba sa pa fa oa] [mb ab zb tb bb sb pb fb ob] H. unfold sm_eqb in H. cbn [sm_maps sm_allow sm_zr sm_tid sm_brk sm_sbrk sm_sp sm_frz sm_own] in H.
  repeat match type of H with ((_ && _)%bool = true) => apply andb_prop in H as [H ?Hx] end.
  apply maps_eqb_eq in H. subst mb.
  repeat match goal with
         | Hx' : allow_eqb _ _ = true |- _ => apply allow_eqb_eq in Hx'
         | Hx' : zr_eqb _ _ = true |- _ => apply zr_eqb_eq in Hx'
         | Hx' : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in Hx'
         | Hx' : frz_eqb _ _ = true |- _ => apply frz_eqb_eq in Hx'
         end.
  subst. destruct ta as [x|], tb as [y|]; cbn in *; try discriminate; [|reflexivity].
  match goal with Hx' : lin_eqb x y = true |- _ => apply lin_eqb_eq in Hx'; subst; reflexivity end.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma sm_eqbm_eq : forall σ MP MF, sm_eqbm σ MP MF = true -> msubst σ MP = MF /\ marks_ok σ (sm_maps MP) = true.
Proof. LiaFast.lf_pins LiaFast.u0. intros σ MP MF H. unfold sm_eqbm in H. apply andb_prop in H as [H1 H2]. split; [exact (sm_eqb_eq _ _ H1) | exact H2]. Qed.


(* [comment removed for export] *)
#[using="path0 data0 Hp4"] Lemma lmeas_dec_sound : forall E F σ m, Forall (fact_ok E) (s_facts F) -> lmeas_dec F σ m = true ->
  bv_unsigned (lden E m) <= 4611686018427387904 -> bv_unsigned (lden (ecomp E σ) m) <= 4611686018427387904 ->
  bv_unsigned (lden (ecomp E σ) m) < bv_unsigned (lden E m).
Proof. LiaFast.lf_pins (fun (path0 data0 Hp4 : LiaFast.U) => LiaFast.u0).
  intros E F σ m HF H H1 H2. unfold lmeas_dec in H. destruct (irange (s_facts F) (lsub m (lsubst σ m))) as [lo hi] eqn:Hr.
  apply andb_prop in H as [Hlo Hhi]. apply Z.leb_le in Hlo, Hhi.
  pose proof (irange_sound E _ (lsub m (lsubst σ m)) HF) as R. rewrite Hr in R. cbn [fst snd] in R.
  rewrite lden_lsub, lden_lsubst, bv_sub_unsigned in R. unfold bv_wrap in R. change (bv_modulus 64) with two64 in R.
  pose proof (bv_unsigned_in_range _ (lden E m)). pose proof (bv_unsigned_in_range _ (lden (ecomp E σ) m)).
  destruct (Z_lt_le_dec (bv_unsigned (lden (ecomp E σ) m)) (bv_unsigned (lden E m))) as [Hlt|Hge]; [exact Hlt|].
  exfalso. set (a := bv_unsigned (lden E m)) in *. set (b := bv_unsigned (lden (ecomp E σ) m)) in *.
  destruct (Z.eq_dec a b) as [Heq|Hne].
  - rewrite Heq, Z.sub_diag, Z.mod_0_l in R by (unfold two64; lia). lia.
  - replace (a - b) with ((a - b + two64) + (-1) * two64) in R by lia. rewrite Z.mod_add in R by (unfold two64; lia).
    rewrite Z.mod_small in R by (unfold two64 in *; lia). unfold two64 in *. lia.
Qed.

#[using="Hp4"] Lemma INV_ent2 : forall mem0 E S P M FS FP model0 n0,
  INV mem0 E S M FS model0 -> params_fixed (match_st S P) (pos_below n0) = true ->
  pv_okb pv hv n0 = true -> sm_wf n0 M = true -> fs_ent FS FP (match_st S P) = true -> fs_wf (s_next P) FP = true -> (n0 <= s_next P)%positive ->
  INV mem0 (ecomp E (match_st S P)) P M FP model0.
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros mem0 E S P M FS FP model0 n0 Hi Hpf Hpvk Hwf0 Hfe Hfw Hn1. unfold pv_okb in Hpvk. apply andb_prop in Hpvk as [Hpv0 Hhv0].
  set (σ := match_st S P) in *. set (E0 := ecomp E σ).
  assert (Ha : agree n0 E E0) by exact (agree_params n0 E σ Hpf).
  destruct Hi as (Hpv & Hfsw & Hfr & Hm0 & Hlen & Hlk & Hfs0 & Hfds & Hc1 & Hc2 & Hdv).
  assert (Hpv' : lden E0 pv = lden E pv) by exact (lden_agree_wf _ E E0 pv Hpv0 Ha).
  pose proof (sm_wf_frz _ M Hwf0) as Hwz.
  split; [exact (lwf_mono _ _ _ Hn1 Hpv0)|]. split; [exact Hfw|].
  split.
  { intros Hdr k Hk. destruct (Hfr Hdr k Hk) as (p & Hp & Hr). exists p. split; [exact Hp|].
    rewrite Forall_forall in Hwz. destruct (Hwz p Hp) as [W1 W2]. unfold uE in *.
    rewrite (lden_agree_wf _ E E0 _ W1 Ha), (lden_agree_wf _ E E0 _ W2 Ha), Hpv'. exact Hr. }
  split.
  { split; [intros Hdr k Hk; rewrite Hpv'; exact (proj1 Hm0 Hdr k Hk)|].
    intros Hdr w Hw. rewrite Hpv' in Hw. destruct (proj2 Hm0 Hdr w Hw) as [(p & Hp & Hr) Hne]. split; [|exact Hne].
    exists p. split; [exact Hp|].
    rewrite Forall_forall in Hwz. destruct (Hwz p Hp) as [W1 W2]. unfold uE in *.
    rewrite (lden_agree_wf _ E E0 _ W1 Ha), (lden_agree_wf _ E E0 _ W2 Ha). exact Hr. }
  split; [rewrite Hpv'; exact Hlen|]. split; [exact Hlk|]. split; [exact Hfs0|].
  split; [|split; [exact Hc1 | split; [exact Hc2 | exact (hv_inv_agree n0 E E0 S P Hdv Ha Hhv0 Hn1)]]].
  destruct FS as [|off FL| | |off FL]; destruct FP as [|off' FL'| | |off' FL']; cbn [fs_ent] in Hfe; try discriminate; [exact Hfds| |exact I|exact Hfds| ];
  (apply andb_prop in Hfe as [Ho Hf]; apply lin_eqb_eq in Ho, Hf;
   unfold E0; rewrite <- !lden_lsubst; rewrite <- Ho, <- Hf; exact Hfds).
Qed.

#[using="Type"] Lemma fact_in_ok : forall E fs f, Forall (fact_ok E) fs -> existsb (fact_eqb f) fs = true -> fact_ok E f.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs f HF H. apply existsb_exists in H as (g & Hg & Heq). apply fact_eqb_eq in Heq. subst g.
  rewrite Forall_forall in HF. exact (HF f Hg).
Qed.

#[using="path0 data0 Hp4"] Lemma meas_ok_sound : forall E fs m, Forall (fact_ok E) fs -> meas_ok fs m = true -> 0 <= bv_unsigned (lden E m) <= 4611686018427387904.
Proof. LiaFast.lf_pins (fun (path0 data0 Hp4 : LiaFast.U) => LiaFast.u0).
  intros E fs m HF H. unfold meas_ok in H. pose proof (irange_sound E fs m HF) as R. destruct (irange fs m) as [lo hi].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. cbn [fst snd] in R. lia.
Qed.

#[using="Hp4 awf_mono aeqb_eq HA_agree"] Lemma Pm_loop : forall P n0 FP shP meas body ks, Pm body -> Qm ks -> Pm (MLoop P n0 FP shP meas body ks).
Proof. LiaFast.lf_pins (fun (Hp4 awf_mono aeqb_eq HA_agree : LiaFast.U) => LiaFast.u0).
  intros P n0 FP shP meas body ks IHb IHk S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (went n0 S M FS sh P FP shP && fs_wf (s_next P) FP && shp_wf (s_next P) shP && pv_okb pv hv n0 && lwf (s_next P) meas &&
            meas_ok (s_facts P) meas && awf n0 a)%bool eqn:Hb; [|discriminate].
  apply andb_prop in Hb as [Hb Hwa0]. apply andb_prop in Hb as [Hb Hmf]. apply andb_prop in Hb as [Hb Hwm]. apply andb_prop in Hb as [Hb Hpv0].
  apply andb_prop in Hb as [Hb HwP]. apply andb_prop in Hb as [Hwe Hfw].
  destruct (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts body P M FP shP a) as [fb|] eqn:Hbody; [|discriminate].
  destruct (went_parts _ _ _ _ _ _ _ _ Hwe) as (Hok & Hn & Hfe & Hse).
  destruct (ent_ok_parts _ _ _ _ Hok) as (Hpf & Hwf0 & Hn1).
  pose proof (ent_ok_wf _ _ _ _ Hok) as HwfP.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (HQ : forall (v : nat) EP msP modelP model0P mem0P, agree n0 E EP -> DEN segs LIMIT model0P mem0P EP P M msP modelP ->
             INV mem0P EP P M FP model0P -> HAX EP P M a mem0P -> (Z.to_nat (bv_unsigned (lden EP meas)) <= v)%nat ->
             realizes_cfg segs cfg (mkCfg msP modelP) (shp_den EP shP)).
  { intros v. induction v as [|v IHv]; intros EP msP modelP model0P mem0P HaP HdP HiP HxP Hv.
    all: apply (IHb P M FP shP a fb Hbody model0P mem0P EP msP modelP HdP HiP HxP HwP).
    all: intros F MF FSF shF aF model0F mem0F EF msF modelF HinF HdF HiF HxF HwF HaF.
    all: destruct (all_some_spec _ _ _ Hck (F, MF, FSF, shF, aF) HinF) as (o & Ho & Hsub); cbv beta in Ho.
    all: destruct (Z.eqb (s_pc F) (s_pc P)) eqn:Hpc.
    all: try (destruct (Pos.leb n0 (s_next F)) eqn:Hnf; [|discriminate]; apply Pos.leb_le in Hnf;
              apply (IHk F MF FSF shF aF o Ho model0F mem0F EF msF modelF HdF HiF HxF HwF);
              intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' Hx'' Hw'' Ha'';
              apply (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (Hsub _ Hin'') Hd'' Hi'' Hx'' Hw'');
              apply (agree_trans _ E EP E''); [exact (agree_mono _ _ E EP Hn HaP)|];
              apply (agree_trans _ EP EF E''); [exact (agree_mono (s_next S) (s_next P) EP EF ltac:(lia) HaF)|];
              exact (agree_mono (s_next S) (s_next F) EF E'' ltac:(lia) Ha'')).
    all: destruct (ent_okN (match_st F P) n0 F P MF && fs_ent FSF FP (match_st F P) && shp_ent shF shP (match_st F P) && sm_eqb MF M && aeqb aF a &&
                   lmeas_dec F (match_st F P) meas)%bool eqn:Hbe; [|discriminate].
    all: apply andb_prop in Hbe as [Hbe Hmd]; apply andb_prop in Hbe as [Hbe Hae]; apply andb_prop in Hbe as [Hbe Hsm]; apply andb_prop in Hbe as [Hbe Hse'];
         apply andb_prop in Hbe as [HokN Hfe']; apply sm_eqb_eq in Hsm; subst MF; apply aeqb_eq in Hae; subst aF.
    all: pose proof (ent_okN_ok _ _ _ _ HwfP HokN) as Hok'.
    all: destruct (ent_ok_parts _ _ _ _ Hok') as (Hpf' & _ & Hn1').
    all: destruct (den_weaken segs LIMIT model0F mem0F EF F P M msF modelF n0 HdF Hok') as [HdP' HaP'].
    all: pose proof (INV_ent2 mem0F EF F P M FSF FP model0F n0 HiF Hpf' Hpv0 Hwf0 Hfe' Hfw Hn1') as HiP'.
    all: assert (HxP' : HAX (ecomp EF (match_st F P)) P M a mem0F)
           by exact (conj (awf_mono _ _ a Hn1' Hwa0) (HA_agree n0 EF _ M a mem0F Hwf0 Hwa0 HaP' (proj2 HxF))).
    all: rewrite <- (shp_den_ent EF shF shP (match_st F P) Hse').
    (* [comment removed for export] *)
    all: destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ HdF)) as (_ & _ & _ & _ & _ & _ & HFF & _).
    all: destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ HdP)) as (_ & _ & _ & _ & _ & _ & HFP & _).
    all: destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ HdP')) as (_ & _ & _ & _ & _ & _ & HFP' & _).
    all: pose proof (meas_ok_sound _ _ _ HFP Hmf) as Mv; pose proof (meas_ok_sound _ _ _ HFP' Hmf) as Mv'.
    all: assert (HmE : lden EF meas = lden EP meas) by exact (lden_agree_wf _ EP EF meas Hwm HaF).
    all: pose proof (lmeas_dec_sound EF F (match_st F P) meas HFF Hmd ltac:(rewrite HmE; lia) ltac:(lia)) as Hlt; rewrite HmE in Hlt.
    - exfalso. lia.
    - apply (IHv (ecomp EF (match_st F P)) msF modelF model0F mem0F); [| exact HdP' | exact HiP' | exact HxP' | lia].
      apply (agree_trans _ E EP _ HaP). apply (agree_trans _ EP EF _).
      + exact (agree_mono n0 (s_next P) EP EF Hn1 HaF).
      + exact HaP'. }
  (* [comment removed for export] *)
  destruct (den_weaken segs LIMIT model0 mem0 E S P M ms model n0 Hd Hok) as [Hd0 Ha0].
  pose proof (INV_ent2 mem0 E S P M FS FP model0 n0 Hi Hpf Hpv0 Hwf0 Hfe Hfw Hn1) as Hi0.
  assert (HX0 : HAX (ecomp E (match_st S P)) P M a mem0) by exact (conj (awf_mono _ _ a Hn1 Hwa0) (HA_agree n0 E _ M a mem0 Hwf0 Hwa0 Ha0 (proj2 HX))).
  rewrite <- (shp_den_ent E sh shP _ Hse).
  exact (HQ _ _ ms model model0 mem0 Ha0 Hd0 Hi0 HX0 (Nat.le_refl _)).
Qed.

(* [comment removed for export] *)
#[using="Hp4 awf_mono aeqb_eq HA_agree"] Lemma Pm_loopW : forall zk body ks, Pm body -> Qm ks -> Pm (MLoopW zk body ks).
Proof. LiaFast.lf_pins (fun (Hp4 awf_mono aeqb_eq HA_agree : LiaFast.U) => LiaFast.u0).
  intros zk body ks IHb IHk S M FS sh a finals Hck. cbn [mcheck] in Hck.
  destruct (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts body S M FS sh a) as [fb1|]; [|discriminate].
  destruct (List.find (fun '(F, _, _, _, _) => Z.eqb (s_pc F) (s_pc S)) fb1) as [[[[[F1 M1] FS1] sh1] a1]|]; [|discriminate].
  destruct (wgen false S F1 FS FS1 sh sh1 zk) as [[[[[P0 n0] FP] shP] meas]|]; [|discriminate].
  match type of Hck with
  | context [went n0 S M FS sh ?P FP shP] => exact (Pm_loop P n0 FP shP meas body ks IHb IHk S M FS sh a finals Hck)
  end.
Qed.

(* [comment removed for export] *)
#[using="Hp4"] Lemma INV_node : forall mem0 mem0' E E' S S' M M' FS model0,
  INV mem0 E S M FS model0 -> agree (s_next S) E E' -> (s_next S <= s_next S')%positive -> sm_frz M' = sm_frz M ->
  sm_wf (s_next S) M = true -> frz_same E M mem0 mem0' -> INV mem0' E' S' M' FS model0.
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros mem0 mem0' E E' S S' M M' FS model0 Hi Ha Hle Hfz Hwf Hfsm.
  pose proof (INV_agree mem0 E E' S S' M M' FS model0 Hi Ha Hle Hfz Hwf) as Hi'.
  destruct Hi as (Hpv & _ & Hfr & Hm0 & _).
  destruct Hi' as (H1 & H2 & H3 & H4 & H5).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
  split.
  - intros Hdr k Hk. rewrite (lden_agree_wf _ E E' pv Hpv Ha). destruct (Hfr Hdr k Hk) as (p & Hp & Hr).
    rewrite (Hfsm p Hp _ Hr). exact (proj1 Hm0 Hdr k Hk).
  - intros Hdr w Hw. destruct (proj2 H4 Hdr w Hw) as [Hex _]. split; [exact Hex|].
    rewrite (lden_agree_wf _ E E' pv Hpv Ha) in Hw. destruct (proj2 Hm0 Hdr w Hw) as [(p & Hp & Hr) Hne].
    rewrite (Hfsm p Hp _ Hr). exact Hne.
Qed.

(* [comment removed for export] *)
#[using="path0 data0 Hp4"] Lemma fx_contra_false : forall E fs, Forall (fact_ok E) fs -> fx_contra fs = true -> False.
Proof. LiaFast.lf_pins (fun (path0 data0 Hp4 : LiaFast.U) => LiaFast.u0).
  intros E fs HF H. rewrite fx_contra_eq in H. unfold empty_rng in H. apply existsb_exists in H as (f & _ & Hf).
  destruct f as [c a0 b0 tk|l lo hi|l k r|l m v|x v j|xb bsb]; try discriminate.
  pose proof (irange_sound E fs l HF) as R. destruct (irange fs l) as [lo' hi']. apply Z.ltb_lt in Hf. cbn [fst snd] in R. lia.
Qed.
#[using="Hp4"] Lemma Pm_void : Pm MVoid.
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (fx_contra (s_facts S)) eqn:Hc; [|discriminate].
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF0 & _).
  exfalso. exact (fx_contra_false E _ HF0 Hc).
Qed.

(* [comment removed for export] *)
#[using="Hp4"] Lemma Pm_pop : forall k, Pm k -> Pm (MPop k).
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct sh as [po kc|sa sb|lq loq hiq sa sb|lq jq sa sb]; try discriminate. destruct po as [|p rest]; try discriminate.
  destruct (pend_done (s_facts S) p) eqn:Hpd; [|discriminate].
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF0 & _).
  assert (Heq : shp_den E (ShEmit (p :: rest) kc) = shp_den E (ShEmit rest kc)).
  { cbn [shp_den List.map concat]. rewrite (pend_done_nil E _ p HF0 Hpd). reflexivity. }
  rewrite Heq.
  assert (Hw' : shp_wf (s_next S) (ShEmit rest kc) = true) by (cbn [shp_wf forallb] in Hw |- *; apply andb_prop in Hw as [_ Hw]; exact Hw).
  exact (IH S M FS (ShEmit rest kc) a finals Hck model0 mem0 E ms model Hd Hi HX Hw' Hk).
Qed.
#[using="Hp4"] Lemma Pm_alt : forall k1 k2, Pm k1 -> Pm k2 -> Pm (MAlt k1 k2).
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros k1 k2 IH1 IH2 S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (is_mvoid k1) eqn:Hv.
  - destruct (fx_contra1 (s_facts S)) eqn:Hc.
    + destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF0 & _).
      exfalso. exact (fx_contra_false E _ HF0 (fx_contra1_contra _ Hc)).
    + exact (IH2 S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk).
  - destruct (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts k1 S M FS sh a) as [f1|] eqn:H1.
    + injection Hck as <-. exact (IH1 S M FS sh a f1 H1 model0 mem0 E ms model Hd Hi HX Hw Hk).
    + exact (IH2 S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk).
Qed.

(* [comment removed for export] *)
#[using="Hp4 awf_mono aeqb_eq HA_agree"] Lemma Pm_join : forall body jpc k, Pm body -> Pm k -> Pm (MJoin body jpc k).
Proof. LiaFast.lf_pins (fun (Hp4 awf_mono aeqb_eq HA_agree : LiaFast.U) => LiaFast.u0).
  intros body jpc k IHb IHk S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts body S M FS sh a) as [fb|] eqn:Hb; [|discriminate].
  set (J := List.filter (fun '(F, _, _, _, _) => Z.eqb (s_pc F) jpc) fb) in *.
  set (O := List.filter (fun '(F, _, _, _, _) => negb (Z.eqb (s_pc F) jpc)) fb) in *.
  assert (HinO : forall F MF FSF shF aF, In (F, MF, FSF, shF, aF) fb -> Z.eqb (s_pc F) jpc = false -> In (F, MF, FSF, shF, aF) O).
  { intros F MF FSF shF aF Hin Hpc. unfold O. apply filter_In. split; [exact Hin|]. rewrite Hpc. reflexivity. }
  assert (HinJ : forall F MF FSF shF aF, In (F, MF, FSF, shF, aF) fb -> Z.eqb (s_pc F) jpc = true -> In (F, MF, FSF, shF, aF) J).
  { intros F MF FSF shF aF Hin Hpc. unfold J. apply filter_In. split; [exact Hin|]. exact Hpc. }
  destruct J as [|[[[[F0 M0] FS0] sh0] a0] Jr] eqn:HJ.
  - injection Hck as <-.
    apply (IHb S M FS sh a fb Hb model0 mem0 E ms model Hd Hi HX Hw).
    intros F MF FSF shF aF model0F mem0F EF msF modelF Hin HdF HiF HXF HwF HaF.
    destruct (Z.eqb (s_pc F) jpc) eqn:Hpc; [destruct (HinJ F MF FSF shF aF Hin Hpc)|].
    exact (Hk F MF FSF shF aF model0F mem0F EF msF modelF (HinO F MF FSF shF aF Hin Hpc) HdF HiF HXF HwF HaF).
  - set (n0 := max_next (List.map (fun '(F, _, _, _, _) => F) Jr) (s_next F0)) in *.
    set (P := join_fs_hull (fst (gen2 F0 (List.map (fun '(F, _, _, _, _) => F) Jr))) FS0 ((F0, M0, FS0, sh0, a0) :: Jr)) in *.
    destruct (forallb (fun '(F, MF, FSF, shF, aF) => wentN n0 F MF FSF shF P FS0 sh0 && sm_eqb MF M0 && aeqb aF a0) ((F0, M0, FS0, sh0, a0) :: Jr) && state_wf P &&
              Pos.leb (s_next S) n0 && fs_wf (s_next P) FS0 && shp_wf (s_next P) sh0 && pv_okb pv hv n0 && awf n0 a0)%bool eqn:Hc; [|discriminate].
    destruct (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts k P M0 FS0 sh0 a0) as [fk|] eqn:Hk0; [|discriminate].
    injection Hck as <-.
    apply andb_prop in Hc as [Hc Hwa0]. apply andb_prop in Hc as [Hc Hpv0]. apply andb_prop in Hc as [Hc HwP].
    apply andb_prop in Hc as [Hc Hfw]. apply andb_prop in Hc as [Hc Hsn]. apply andb_prop in Hc as [HallN HwfP]. apply Pos.leb_le in Hsn.
    pose proof (forallb_wentN P n0 FS0 sh0 M0 a0 _ HwfP HallN) as Hall.
    rewrite forallb_forall in Hall.
    apply (IHb S M FS sh a fb Hb model0 mem0 E ms model Hd Hi HX Hw).
    intros F MF FSF shF aF model0F mem0F EF msF modelF Hin HdF HiF HXF HwF HaF.
    destruct (Z.eqb (s_pc F) jpc) eqn:Hpc.
    + pose proof (Hall _ (HinJ F MF FSF shF aF Hin Hpc)) as Hq. cbv beta in Hq.
      apply andb_prop in Hq as [Hq Hae]. apply andb_prop in Hq as [Hwe Hsm]. apply sm_eqb_eq in Hsm. apply aeqb_eq in Hae. subst MF aF.
      destruct (went_parts _ _ _ _ _ _ _ _ Hwe) as (Hok & HnF & Hfe & Hse).
      destruct (ent_ok_parts _ _ _ _ Hok) as (Hpf & Hwf0 & Hn1).
      destruct (den_weaken segs LIMIT model0F mem0F EF F P M0 msF modelF n0 HdF Hok) as [HdP HaP].
      pose proof (INV_ent2 mem0F EF F P M0 FSF FS0 model0F n0 HiF Hpf Hpv0 Hwf0 Hfe Hfw Hn1) as HiP.
      assert (HXP : HAX (ecomp EF (match_st F P)) P M0 a0 mem0F)
        by exact (conj (awf_mono _ _ a0 Hn1 Hwa0) (HA_agree n0 EF _ M0 a0 mem0F Hwf0 Hwa0 HaP (proj2 HXF))).
      rewrite <- (shp_den_ent EF shF sh0 (match_st F P) Hse).
      apply (IHk P M0 FS0 sh0 a0 fk Hk0 model0F mem0F _ msF modelF HdP HiP HXP HwP).
      intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' HX'' Hw'' Ha''.
      apply (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (in_or_app _ _ _ (or_introl Hin'')) Hd'' Hi'' HX'' Hw'').
      apply (agree_trans _ E EF E'' HaF). apply (agree_trans _ EF (ecomp EF (match_st F P)) E'').
      * exact (agree_mono (s_next S) n0 EF _ Hsn HaP).
      * exact (agree_mono (s_next S) (s_next P) _ E'' ltac:(lia) Ha'').
    + exact (Hk F MF FSF shF aF model0F mem0F EF msF modelF (in_or_app _ _ _ (or_intror (HinO F MF FSF shF aF Hin Hpc))) HdF HiF HXF HwF HaF).
Qed.

(* [comment removed for export] *)
#[using="Hp4 Hanode"] Lemma Pm_call : forall nk k, Pm k -> Pm (MCall nk k).
Proof. LiaFast.lf_pins (fun (Hp4 Hanode : LiaFast.U) => LiaFast.u0).
  intros nk k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (apost nk S M a) as [[[S' M'] a']|] eqn:Hap; [|discriminate].
  destruct (Pos.leb (s_next S) (s_next S') && fs_wf (s_next S') FS && frz_eqb (sm_frz M') (sm_frz M) && awf (s_next S') a')%bool eqn:Hb;
    [|discriminate].
  apply andb_prop in Hb as [Hb Hwa']. apply andb_prop in Hb as [Hb Hfz]. apply andb_prop in Hb as [Hle Hfsw].
  apply Pos.leb_le in Hle. apply frz_eqb_eq in Hfz.
  assert (Hwf : sm_wf (s_next S) M = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ Hd).
  apply (Hanode nk S M a S' M' a' Hap model0 mem0 E ms model _ Hd (proj1 HX) (proj2 HX)).
  intros E' mem0' ms' model' Ha' Hfsm Hd' Hha'.
  rewrite <- (shp_den_agree (s_next S) E E' sh Hw Ha').
  apply (IH S' M' FS sh a' finals Hck model0 mem0' E' ms' model' Hd' (INV_node mem0 mem0' E E' S S' M M' FS model0 Hi Ha' Hle Hfz Hwf Hfsm)
           (conj Hwa' Hha') (shp_wf_mono _ _ sh Hle Hw)).
  intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' Hx'' Hw'' Ha''.
  exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' Hx'' Hw'' (agree_trans _ E E' E'' Ha' (agree_mono _ _ E' E'' Hle Ha''))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Himg path0 data0 Hp4"] Lemma lbytes_ok_rd1 : forall E m fs rgs (b : lin) bs j, Forall (rg_ok segs E m) rgs -> Forall (fact_ok E) fs ->
  lbytes_ok img fs rgs b bs j = true ->
  forall i, (i < length bs)%nat -> rd1 segs m (lden E (laddc b (j + Z.of_nat i))) = Some (Z_to_bv 8 (nth i bs 0)).
Proof. LiaFast.lf_pins (fun (Himg path0 data0 Hp4 : LiaFast.U) => LiaFast.u0).
  intros E m fs rgs b bs. induction bs as [|x r IH]; intros j HG HF Hok i Hi; cbn [length] in Hi; [lia|].
  cbn [lbytes_ok] in Hok.
  destruct (load_at img fs rgs (laddc b j) SZ1 false) as [[l|]|] eqn:Hl; try discriminate.
  apply andb_prop in Hok as [Hx Hr]. apply lin_eqb_eq in Hx. subst l.
  destruct i as [|i].
  - destruct (load_at_sound segs E img fs rgs _ SZ1 false _ m Himg HG HF Hl) as (bs1 & Hrd & Hv).
    specialize (Hv (lconst x) eq_refl). rewrite ov_rdn in Hrd. cbn [nbytes rdn] in Hrd.
    destruct (match m (lden E (laddc b j)) with Some b0 => Some b0 | None => seg_rom segs (lden E (laddc b j)) end) as [b1|] eqn:Hb1;
      [|discriminate].
    injection Hrd as <-. rewrite ld1_byte, lden_lconst in Hv.
    replace (j + Z.of_nat 0) with j by lia. unfold rd1. rewrite Hb1. f_equal. cbn [nth].
    apply bv_eq. apply (f_equal bv_unsigned) in Hv. rewrite !Z_to_bv_unsigned in Hv. rewrite Z_to_bv_unsigned.
    pose proof (bv_unsigned_in_range _ b1) as Hb. change (bv_modulus 8) with 256 in Hb.
    unfold bv_wrap in *. change (bv_modulus 64) with (2 ^ 64) in Hv. change (bv_modulus 8) with 256.
    rewrite (Z.mod_small (bv_unsigned b1)) in Hv by lia.
    rewrite (Zmod_div_mod 256 (2 ^ 64) x) by (first [lia | exists 72057594037927936; reflexivity]). rewrite Hv. symmetry. apply Z.mod_small. lia.
  - cbn [nth]. replace (j + Z.of_nat (Datatypes.S i)) with ((j + 1) + Z.of_nat i) by lia. exact (IH (j + 1) HG HF Hr i ltac:(lia)).
Qed.

(* [comment removed for export] *)
#[using="Himg path0 data0 Hp4"] Lemma dir_path_ok : forall mem0 model0 E S M ms model1,
  DEN segs LIMIT model0 mem0 E S M ms model1 -> lbytes_ok img (s_facts S) (s_rgs S) pv dot_z 0 = true ->
  read_cstr (in_mem (sys_input segs (svc_set ms) (ms_reg ms 17))) (lden E pv) = CstrOk [Z_to_bv 8 46] /\
  ranges_avoid (Hof E M model1) [(lden E pv, cstr_access_len_aux (in_mem (sys_input segs (svc_set ms) (ms_reg ms 17))) (lden E pv) path_max)].
Proof. LiaFast.lf_pins (fun (Himg path0 data0 Hp4 : LiaFast.U) => LiaFast.u0).
  intros mem0 model0 E S M ms model1 Hd Hlb.
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & HG0 & _ & HF0 & _).
  pose proof (dn_hoff _ _ _ _ _ _ _ _ _ Hd) as Hhoff. pose proof (dn_rom _ _ _ _ _ _ _ _ _ Hd) as Hrom.
  cbn [restrict ms_mem] in HG0.
  assert (Hmp : forall j, (j <= length [Z_to_bv 8 46])%nat ->
            in_mem (sys_input segs (svc_set ms) (ms_reg ms 17)) (woff (lden E pv) j) = Some (nth j ([Z_to_bv 8 46] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))
            /\ Hof E M model1 (woff (lden E pv) j) = false).
  { intros j Hj. cbn [length] in Hj.
    pose proof (lbytes_ok_rd1 E _ _ _ pv dot_z 0 HG0 HF0 Hlb j ltac:(cbn [length dot_z]; lia)) as Hr.
    destruct (rd1_restrict_vis segs _ (ms_mem ms) _ _ Hhoff Hr) as [Hf Hh].
    assert (Hw : lden E (laddc pv (0 + Z.of_nat j)) = woff (lden E pv) j) by (unfold woff; rewrite lden_laddc; f_equal; lia).
    rewrite Hw in Hf, Hh. split; [|exact Hh].
    cbn [in_mem sys_input]. unfold ms_read_byte. cbn [svc_set ms_mem ms_rom]. unfold rd1 in Hf. rewrite Hrom.
    destruct (ms_mem ms (woff (lden E pv) j)) as [bb|] eqn:Hm; rewrite Hf; destruct j as [|[|j]]; try reflexivity; lia. }
  assert (Hnz : Forall (fun b => b <> Z_to_bv 8 0) [Z_to_bv 8 46]).
  { constructor; [|constructor]. intros Hc. apply (f_equal bv_unsigned) in Hc. discriminate. }
  assert (Hk : (length [Z_to_bv 8 46] < path_max)%nat) by (cbn [length]; unfold path_max; lia).
  split.
  - unfold read_cstr. exact (read_cstr_aux_ok _ [Z_to_bv 8 46] (lden E pv) path_max Hk Hnz (fun j Hj => proj1 (Hmp j Hj))).
  - rewrite (cstr_access_len_ok _ [Z_to_bv 8 46] (lden E pv) path_max Hk Hnz (fun j Hj => proj1 (Hmp j Hj))).
    apply ranges_avoid_cons; [|apply ranges_avoid_nil]. intros kk Hkk. exact (proj2 (Hmp kk ltac:(cbn [length] in *; lia))).
Qed.

#[using="Hwx Hfs Himg Hect Hp4 awf_mono HA_agree"] Lemma Pm_opendir : forall kerr kok, Pm kerr -> Pm kok -> Pm (MOpenDir kerr kok).
Proof. LiaFast.lf_pins (fun (Hwx Hfs Himg Hect Hp4 awf_mono HA_agree : LiaFast.U) => LiaFast.u0).
  intros kerr kok IHe IHo S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct FS as [|off FL| | |off FL]; try discriminate. destruct sh as [po kc|sa sb|lq loq hiq sa sb|lq jq sa sb]; try discriminate.
  destruct (dr && is_ecall t (s_pc S) && open_args_ok S pv && lbytes_ok img (s_facts S) (s_rgs S) pv dot_z 0)%bool eqn:Hb; [|discriminate].
  apply andb_prop in Hb as [Hb Hlb]. apply andb_prop in Hb as [Hb Hoa]. apply andb_prop in Hb as [_ Hx]. apply is_ecall_ok in Hx.
  destruct (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts kerr (ret_gen S ERRLO ERRHI) M FSClosed sa a) as [f1|] eqn:H1;
    [|discriminate].
  destruct (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts kok (ret_post S (lconst 3)) M FSDir sb a) as [f2|] eqn:H2; [|discriminate].
  injection Hck as <-. cbn [shp_wf] in Hw. apply andb_prop in Hw as [Hwa Hwb]. cbn [shp_den].
  unfold open_args_ok in Hoa.
  destruct (a7c S) as [c7|] eqn:H7; [|discriminate]. destruct (arg S 0) as [c0|] eqn:H0; [|discriminate].
  destruct (arg S 2) as [fl|] eqn:H2a; [|discriminate].
  apply andb_prop in Hoa as [Hoa Hpvl]. apply andb_prop in Hoa as [Hoa Hldiff]. apply andb_prop in Hoa as [H56 Hdfd].
  apply Z.eqb_eq in H56, Hldiff. apply bv_eqb_eq in Hdfd. apply lin_eqb_eq in Hpvl. subst c7.
  pose proof Hi as Hi0.
  destruct Hi0 as (Hpv & Hfsw & Hfr & Hm0 & Hlen & Hlk & Hfs0 & (Hal & Hfree) & Hc1 & Hc2 & Hdv).
  apply (den_ecall segs cfg LIMIT model0 mem0 Hwx t E S M ms model _ Hect Hx Hd). intros model1 Hd1.
  destruct (dir_path_ok mem0 model0 E S M ms model1 Hd1 Hlb) as [Hcstr Hav].
  rewrite <- Hpvl in Hcstr, Hav.
  apply (den_openat_dirref segs cfg LIMIT mem0 Hfs model0 E S M ms model1 _ _ c0 fl [Z_to_bv 8 46] (Z_to_bv 64 3) Hd1 H7 H0 Hdfd H2a Hldiff
           Hcstr eq_refl eq_refl eq_refl Hal Hfree ltac:(rewrite u_small64 by (unfold two64; lia); lia) Hav).
  - intros e He ms' m'' Hd''.
    pose proof (errno_in_range e He) as Hcr.
    assert (Hc64 : 0 <= bv_unsigned (errno_ret e) < two64) by (unfold ERRLO, ERRHI, two64 in *; lia).
    pose proof (den_gen_ret segs LIMIT model0 mem0 E S M ms' m'' (bv_unsigned (errno_ret e)) ERRLO ERRHI Hd'' Hc64 Hcr) as Hd3.
    set (E1 := upd E (s_next S) (Z_to_bv 64 (bv_unsigned (errno_ret e)))) in *.
    assert (Ha : agree (s_next S) E E1) by exact (agree_upd (s_next S) E _).
    assert (Hle : (s_next S <= s_next (ret_gen S ERRLO ERRHI))%positive) by (cbn [ret_gen add_fact bump ret_post s_next]; lia).
    pose proof (dn_wf _ _ _ _ _ _ _ _ _ Hd) as Hwf0.
    rewrite <- (shp_den_agree (s_next S) E E1 sa Hwa Ha).
    apply (IHe _ _ _ _ _ f1 H1 model0 mem0 E1 ms' m'' Hd3
             (INV_agree mem0 E E1 S (ret_gen S ERRLO ERRHI) M M FSClosed model0 Hi Ha Hle eq_refl Hwf0)
             (HAX_step E E1 S (ret_gen S ERRLO ERRHI) M a mem0 HX Hwf0 Ha Hle) (shp_wf_mono _ _ sa Hle Hwa)).
    intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd''' Hi'' Hx'' Hw'' Ha''.
    exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (in_or_app _ _ _ (or_introl Hin'')) Hd''' Hi'' Hx'' Hw''
             (agree_trans _ E E1 E'' Ha (agree_mono _ _ E1 E'' Hle Ha''))).
  - intros ms' m'' Hd''.
    set (model0' := with_fds (fd_insert (m_fds model0) (Z_to_bv 64 3) FdDir) model0) in *.
    change (lconst (bv_unsigned (Z_to_bv 64 3))) with (lconst 3) in Hd''.
    assert (Hi' : INV mem0 E (ret_post S (lconst 3)) M FSDir model0').
    { unfold INV. cbn [ret_post s_next].
      split; [exact Hpv|]. split; [reflexivity|]. split; [exact Hfr|]. split; [exact Hm0|]. split; [exact Hlen|].
      split; [intros Hdr'; unfold model0'; rewrite with_fds_fs; exact (Hlk Hdr')|]. split; [unfold model0'; rewrite with_fds_fs; exact Hfs0|].
      split; [unfold model0'; rewrite with_fds_fds, fd_lookup_insert_same; reflexivity|].
      split; [unfold model0'; rewrite with_fds_fds, fd_lookup_insert_other by (first [exact w3_ne1 | exact w3_ne2]); assumption|].
      split; [unfold model0'; rewrite with_fds_fds, fd_lookup_insert_other by (first [exact w3_ne1 | exact w3_ne2]); assumption|].
      exact (hv_inv_step E E S (ret_post S (lconst 3)) Hdv (agree_refl _ _) ltac:(cbn [ret_post s_next]; lia)). }
    apply (IHo _ _ _ _ _ f2 H2 model0' mem0 E ms' m'' Hd'' Hi' (HAX_same E S _ M a mem0 HX eq_refl) Hwb).
    intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd''' Hi'' Hx'' Hw'' Ha''.
    exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (in_or_app _ _ _ (or_intror Hin'')) Hd''' Hi'' Hx'' Hw'' Ha'').
Qed.

#[using="Hwx Hect Hp4"] Lemma Pm_readdir : forall k, Pm k -> Pm (MReadDir k).
Proof. LiaFast.lf_pins (fun (Hwx Hect Hp4 : LiaFast.U) => LiaFast.u0).
  intros k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct FS as [|off FL| | |off FL]; try discriminate.
  destruct (is_ecall t (s_pc S) && readdir_args_ok S)%bool eqn:Hb; [|discriminate].
  apply andb_prop in Hb as [Hx Hra]. apply is_ecall_ok in Hx.
  unfold readdir_args_ok in Hra. destruct (a7c S) as [c7|] eqn:H7; [|discriminate]. destruct (arg S 0) as [c0|] eqn:H0; [|discriminate].
  cbv zeta in Hra.
  apply andb_prop in Hra as [Hra Hb12]. apply andb_prop in Hra as [Hra Hb2]. apply andb_prop in Hra as [H63 H3].
  apply Z.eqb_eq in H63, H3. apply Z.leb_le in Hb12, Hb2. subst c7 c0.
  pose proof Hi as Hi0. destruct Hi0 as (_ & _ & _ & _ & _ & _ & _ & Hfd3 & _ & _).
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF0 & _).
  pose proof (irange_sound E _ (argl S 1) HF0) as R1. pose proof (irange_sound E _ (argl S 2) HF0) as R2.
  assert (Hok : access_okb (lden E (argl S 1)) (bv_unsigned (lden E (argl S 2))) = true).
  { unfold access_okb. apply andb_true_intro. split; apply Z.leb_le; lia. }
  apply (den_ecall segs cfg LIMIT model0 mem0 Hwx t E S M ms model _ Hect Hx Hd). intros model1 Hd1.
  apply (den_read_dir segs cfg LIMIT mem0 model0 E S M ms model1 _ 3 Hd1 H7 H0 ltac:(rewrite fd32_3; exact Hfd3) Hok).
  intros ms' m'' Hd''.
  apply (IH _ _ _ _ _ finals Hck model0 mem0 E ms' m'' Hd'' (INV_same mem0 E S _ M FSDir model0 Hi eq_refl) (HAX_same E S _ M a mem0 HX eq_refl) Hw). exact Hk.
Qed.

(* [comment removed for export] *)
#[using="Hwx Himg Hect Hp4 awf_mono HA_agree"] Lemma Pm_writev2 : forall B0 k, Pm k -> Pm (MWritev2 B0 k).
Proof. LiaFast.lf_pins (fun (Hwx Himg Hect Hp4 awf_mono HA_agree : LiaFast.U) => LiaFast.u0).
  intros B0 k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct sh as [po kc|sa sb|lq loq hiq sa sb|lq jq sa sb]; try discriminate. destruct po as [|p rest]; try discriminate.
  destruct (is_ecall t (s_pc S)) eqn:Hx; [|discriminate]. apply is_ecall_ok in Hx.
  destruct (writev2_ok img S B0 p) as [len|] eqn:Hok; [|discriminate].
  destruct p as [ch [bs|pre j lj suf] off]; [|unfold writev2_ok in Hok; discriminate Hok]. unfold writev2_ok in Hok. cbn [pd_src src_len] in Hck.
  set (iov := argl S 1) in *.
  destruct (a7c S) as [c7|] eqn:H7; [|discriminate]. destruct (arg S 0) as [c0|] eqn:H0; [|discriminate].
  destruct (arg S 2) as [c2|] eqn:H2; [|discriminate].
  destruct (load_at img (s_facts S) (s_rgs S) iov SZ8 false) as [[b|]|] eqn:Hlb; try discriminate.
  destruct (load_at img (s_facts S) (s_rgs S) (laddc iov 8) SZ8 false) as [[len'|]|] eqn:Hll; try discriminate.
  destruct (load_at img (s_facts S) (s_rgs S) (laddc iov 16) SZ8 false) as [[z1|]|] eqn:Hlz1; try discriminate.
  destruct (load_at img (s_facts S) (s_rgs S) (laddc iov 24) SZ8 false) as [[z2|]|] eqn:Hlz2; try discriminate.
  set (n := Z.of_nat (length bs)) in *.
  destruct (Z.eqb c7 66 && Z.eqb c0 ch && (Z.eqb ch 1 || Z.eqb ch 2) && Z.eqb c2 2 &&
            lin_eqb b (ladd off B0) && lin_eqb len' (laddc (lneg off) n) && lin_eqb z1 (lconst 0) && lin_eqb z2 (lconst 0) &&
            lbytes_ok img (s_facts S) (s_rgs S) B0 bs 0 &&
            Z.leb 0 (fst (irange (s_facts S) off)) && Z.ltb (snd (irange (s_facts S) off)) n && Z.leb 1 n && Z.leb n 1073741824 &&
            Z.leb (snd (irange (s_facts S) B0) + n) TASK_SIZE && Z.leb (snd (irange (s_facts S) iov) + 32) TASK_SIZE &&
            lwf (s_next S) off && lwf (s_next S) iov && lwf (s_next S) B0)%bool eqn:Hb; [|discriminate].
  injection Hok as <-.
  repeat match type of Hb with ((_ && _)%bool = true) => apply andb_prop in Hb as [Hb ?Hq] end.
  rename Hb into H66. apply Z.eqb_eq in H66. subst c7.
  repeat match goal with
         | Hx' : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in Hx'
         | Hx' : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx'
         | Hx' : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hx'
         | Hx' : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in Hx'
         end.
  subst c0 c2 b len' z1 z2.
  assert (Hch : ch = 1 \/ ch = 2).
  { match goal with Hq' : (Z.eqb ch 1 || Z.eqb ch 2)%bool = true |- _ => apply orb_prop in Hq' as [Hq'|Hq']; apply Z.eqb_eq in Hq'; auto end. }
  assert (Hbo : lbytes_ok img (s_facts S) (s_rgs S) B0 bs 0 = true) by assumption.
  assert (Hwoff : lwf (s_next S) off = true) by assumption.
  assert (Hwiov : lwf (s_next S) iov = true) by assumption.
  cbn [shp_wf forallb pend_wf pd_src pd_off] in Hw. apply andb_prop in Hw as [_ Hwr].
  pose proof Hi as Hi0. destruct Hi0 as (Hpv & Hfsw & Hfr & Hm0 & Hlen & Hlk & Hfs0 & Hfds & Hch1 & Hch2 & Hdv).
  apply (den_ecall segs cfg LIMIT model0 mem0 Hwx t E S M ms model _ Hect Hx Hd). intros model1 Hd1.
  set (H1 := Hof E M model1).
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd1)) as (_ & _ & _ & _ & HG0 & _ & HF0 & _).
  pose proof (dn_hoff _ _ _ _ _ _ _ _ _ Hd1) as Hhoff. fold H1 in HG0, Hhoff. cbn [restrict ms_mem] in HG0.
  (* [comment removed for export] *)
  pose proof (irange_sound E _ off HF0) as Ro.
  set (uo := bv_unsigned (lden E off)) in *.
  assert (Huo : 0 <= uo < n) by (unfold uo; lia).
  pose proof (irange_sound E _ iov HF0) as Ri.
  pose proof (irange_sound E _ B0 HF0) as RB. pose proof (bv_unsigned_in_range _ (lden E B0)) as RB0.
  unfold bv_modulus in RB0. change (2 ^ Z.of_N 64) with two64 in RB0.
  set (uB := bv_unsigned (lden E B0)) in *.
  (* [comment removed for export] *)
  destruct (load_at_sound segs E img _ _ iov SZ8 false _ _ Himg HG0 HF0 Hlb) as (bs8a & Hra & Hva). specialize (Hva _ eq_refl).
  destruct (load_at_sound segs E img _ _ (laddc iov 8) SZ8 false _ _ Himg HG0 HF0 Hll) as (bs8b & Hrb & Hvb). specialize (Hvb _ eq_refl).
  destruct (load_at_sound segs E img _ _ (laddc iov 16) SZ8 false _ _ Himg HG0 HF0 Hlz1) as (bs8c & Hrc & Hvc). specialize (Hvc _ eq_refl).
  destruct (load_at_sound segs E img _ _ (laddc iov 24) SZ8 false _ _ Himg HG0 HF0 Hlz2) as (bs8d & Hrd' & Hvd). specialize (Hvd _ eq_refl).
  rewrite ov_rdn in Hra, Hrb, Hrc, Hrd'. cbn [nbytes] in Hra, Hrb, Hrc, Hrd'.
  destruct (rdn_restrict_vis segs mem0 H1 (ms_mem ms) 8 _ bs8a Hhoff Hra) as [Hra' Hava].
  destruct (rdn_restrict_vis segs mem0 H1 (ms_mem ms) 8 _ bs8b Hhoff Hrb) as [Hrb' Havb].
  destruct (rdn_restrict_vis segs mem0 H1 (ms_mem ms) 8 _ bs8c Hhoff Hrc) as [Hrc' Havc].
  destruct (rdn_restrict_vis segs mem0 H1 (ms_mem ms) 8 _ bs8d Hhoff Hrd') as [Hrd'' Havd].
  assert (Hl8a : length bs8a = 8%nat) by exact (rdn_length _ _ _ _ _ Hra').
  assert (Hl8b : length bs8b = 8%nat) by exact (rdn_length _ _ _ _ _ Hrb').
  assert (Hl8c : length bs8c = 8%nat) by exact (rdn_length _ _ _ _ _ Hrc').
  assert (Hl8d : length bs8d = 8%nat) by exact (rdn_length _ _ _ _ _ Hrd'').
  assert (Hiov8 : lden E (laddc iov 8) = Z_to_bv 64 (bv_unsigned (lden E iov) + 8)) by (rewrite lden_laddc; f_equal; lia).
  assert (Hiov16 : lden E (laddc iov 16) = Z_to_bv 64 (bv_unsigned (lden E iov) + 16)) by (rewrite lden_laddc; f_equal; lia).
  assert (Hiov24 : lden E (laddc iov 24) = Z_to_bv 64 (bv_unsigned (lden E iov) + 24)) by (rewrite lden_laddc; f_equal; lia).
  (* [comment removed for export] *)
  assert (Hrd : forall i, (i < length bs - Z.to_nat uo)%nat ->
            rd1 segs (mrestrict H1 (ms_mem ms)) (Z_to_bv 64 ((uB + uo) + Z.of_nat i)) = Some (Z_to_bv 8 (nth (Z.to_nat uo + i) bs 0))).
  { intros i Hi'. rewrite <- (lbytes_ok_rd1 E _ _ _ B0 bs 0 HG0 HF0 Hbo (Z.to_nat uo + i) ltac:(lia)). f_equal. rewrite lden_laddc. fold uB. f_equal. lia. }
  pose proof (rd1_full_rdn (mrestrict H1 (ms_mem ms)) (uB + uo) (length bs - Z.to_nat uo) (fun i => Z_to_bv 8 (nth (Z.to_nat uo + i) bs 0))
                ltac:(lia) ltac:(unfold TASK_SIZE, two64 in *; lia) Hrd) as Hrm.
  rewrite map_seq_skipn in Hrm by lia.
  destruct (rdn_restrict_vis segs mem0 H1 (ms_mem ms) _ _ _ Hhoff Hrm) as [Hrm' Havm].
  set (bsr := skipn (Z.to_nat uo) (List.map (Z_to_bv 8) bs)) in *.
  assert (Hlr : length bsr = (length bs - Z.to_nat uo)%nat) by (unfold bsr; rewrite length_skipn, length_map; reflexivity).
  assert (HbE : lden E (ladd off B0) = Z_to_bv 64 (uB + uo)).
  { rewrite lden_ladd. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. fold uo uB. f_equal. lia. }
  assert (HlenE : bv_unsigned (lden E (laddc (lneg off) n)) = Z.of_nat (length bsr)).
  { rewrite lden_laddc, Z_to_bv_unsigned. rewrite lneg_eq. rewrite lden_lscale. rewrite Z_to_bv_unsigned. fold uo.
    unfold bv_wrap. change (bv_modulus 64) with two64. rewrite Z.add_mod_idemp_l by (unfold two64; lia).
    unfold M64. replace (18446744073709551615 * uo + n) with ((n - uo) + uo * two64) by (unfold two64; lia).
    rewrite Z.mod_add by (unfold two64; lia). rewrite Z.mod_small by (unfold two64; lia).
    rewrite Hlr, Nat2Z.inj_sub by lia. rewrite Z2Nat.id by lia. reflexivity. }
  (* [comment removed for export] *)
  set (REST := concat (List.map (pend_evs E) rest)).
  set (K := t_emit REST (t_exit (Z_to_bv 64 kc) fs0)).
  assert (HK0 : K []) by apply t_emit_has_nil.
  assert (Hpe : pend_evs E (PD ch (SLit bs) off) = List.map (WriteEv (Z_to_bv 64 ch)) bsr) by reflexivity.
  eapply rzc_conseq; [|cbn [shp_den List.map concat]; rewrite Hpe; apply t_eq_sym; apply t_emit_app].
  fold REST.
  assert (Hfch : fd_lookup (m_fds model0) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch))) by (destruct Hch as [->| ->]; assumption).
  apply (den_writev2 segs cfg LIMIT mem0 model0 E S M ms model1 K ch (ladd off B0) (laddc (lneg off) n) bsr n Hd1 H7 H0 H2 Hch Hfch
           ltac:(fold iov; rewrite Hra'; f_equal; rewrite Hva; symmetry; exact (ld8_bytes _ Hl8a))
           ltac:(fold iov; rewrite <- Hiov8; rewrite Hrb'; f_equal; rewrite Hvb; symmetry; exact (ld8_bytes _ Hl8b))
           ltac:(fold iov; rewrite <- Hiov16; rewrite Hrc'; f_equal; rewrite <- (lden_lconst E 0), Hvc; symmetry; exact (ld8_bytes _ Hl8c))
           ltac:(fold iov; rewrite <- Hiov24; rewrite Hrd''; f_equal; rewrite <- (lden_lconst E 0), Hvd; symmetry; exact (ld8_bytes _ Hl8d))
           ltac:(rewrite HbE; rewrite Hlr; exact Hrm')
           HlenE ltac:(rewrite Hlr; lia) ltac:(rewrite Hlr; lia) ltac:(lia) ltac:(fold iov; first [solve [clear - Ri Hq3; lia] | solve [clear - Ri Hq4; lia] | (unfold uE in *; lia)])
           ltac:(rewrite HbE, u_small64 by (unfold TASK_SIZE, two64 in *; lia); rewrite Hlr; lia)).
  - intros kk Hkk. fold iov H1. destruct (Nat.lt_ge_cases kk 8) as [Hk8|Hk8]; [exact (Hava kk Hk8)|].
    destruct (Nat.lt_ge_cases kk 16) as [Hk16|Hk16].
    { replace (woff (lden E iov) kk) with (woff (lden E (laddc iov 8)) (kk - 8)); [apply Havb; first [solve [clear - Hk8 Hk16; lia] | solve [clear - Hk8 Hkk; lia] | lia]|].
      unfold woff. rewrite lden_laddc. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. first [solve [clear - Hk8; lia] | solve [clear - Hk16; lia] | solve [clear - Hk24; lia] | lia]. }
    destruct (Nat.lt_ge_cases kk 24) as [Hk24|Hk24].
    { replace (woff (lden E iov) kk) with (woff (lden E (laddc iov 16)) (kk - 16)); [apply Havc; first [solve [clear - Hk16 Hk24; lia] | lia]|].
      unfold woff. rewrite lden_laddc. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. first [solve [clear - Hk8; lia] | solve [clear - Hk16; lia] | solve [clear - Hk24; lia] | lia]. }
    { replace (woff (lden E iov) kk) with (woff (lden E (laddc iov 24)) (kk - 24)); [apply Havd; first [solve [clear - Hk24 Hkk; lia] | lia]|].
      unfold woff. rewrite lden_laddc. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. first [solve [clear - Hk8; lia] | solve [clear - Hk16; lia] | solve [clear - Hk24; lia] | lia]. }
  - fold H1. rewrite HbE. rewrite Hlr. exact Havm.
  - apply lwf_laddc. rewrite lneg_eq. apply lwf_lscale. exact Hwoff.
  - exact HK0.
  - intros E' ms' m'' Hd' Ha' Hkr.
    set (kv := s_next S) in *.
    set (kz := bv_unsigned (E' kv)) in *.
    assert (Hn' : s_next (wv_post S (laddc (lneg off) n) n) = Pos.succ (s_next S)) by reflexivity.
    assert (Hoff' : lden E' off = lden E off) by exact (lden_agree_wf _ E E' off Hwoff Ha').
    assert (Hi' : INV mem0 E' (wv_post S (laddc (lneg off) n) n) M FS model0).
    { apply (INV_agree mem0 E E' S _ M M FS model0 Hi Ha' ltac:(rewrite Hn'; lia) eq_refl (dn_wf _ _ _ _ _ _ _ _ _ Hd)). }
    assert (Hw' : shp_wf (s_next (wv_post S (laddc (lneg off) n) n)) (wv_shp (ShEmit (PD ch (SLit bs) off :: rest) kc) S) = true).
    { rewrite Hn'. cbn [wv_shp shp_wf forallb pend_wf pd_src pd_off]. apply andb_true_intro. split.
      - apply lwf_ladd; [exact (lwf_mono (s_next S) (Pos.succ (s_next S)) off ltac:(lia) Hwoff)|]. unfold lwf, lvar. cbn. rewrite andb_true_r. apply Pos.ltb_lt. lia.
      - exact (shp_wf_mono (s_next S) (Pos.succ (s_next S)) (ShEmit rest kc) ltac:(lia) Hwr). }
    eapply rzc_conseq.
    + apply (IH _ _ _ _ _ finals Hck model0 mem0 E' ms' m'' Hd' Hi'
               (HAX_step E E' S (wv_post S (laddc (lneg off) n) n) M a mem0 HX (dn_wf _ _ _ _ _ _ _ _ _ Hd) Ha' ltac:(rewrite Hn'; lia)) Hw').
      intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' Hx'' Hw'' Ha''.
      exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' Hx'' Hw''
               (agree_trans _ E E' E'' Ha' (agree_mono (s_next S) (s_next (wv_post S (laddc (lneg off) n) n)) E' E'' ltac:(rewrite Hn'; lia) Ha''))).
    + cbn [wv_shp shp_den List.map concat]. eapply t_eq_trans; [apply t_emit_app|].
      assert (HR : concat (List.map (pend_evs E') rest) = REST).
      { unfold REST. f_equal. apply map_ext_in. intros q Hqin.
        rewrite forallb_forall in Hwr. exact (pend_evs_agree _ E E' q (Hwr q Hqin) Ha'). }
      rewrite HR. fold K.
      assert (Hpk : pend_evs E' (PD ch (SLit bs) (ladd off (lvar kv))) = List.map (WriteEv (Z_to_bv 64 ch)) (skipn (Z.to_nat kz) bsr)).
      { unfold pend_evs, bsr. cbn [pd_ch pd_src pd_off src_bytes]. f_equal. rewrite skipn_skipn. f_equal.
        unfold uE. rewrite lden_ladd, lden_lvar, Hoff'. rewrite bv_add_unsigned. fold uo kz. unfold bv_wrap.
        rewrite Z.mod_small by (change (bv_modulus 64) with two64; unfold two64; rewrite Hlr in Hkr; lia). lia. }
      fold kv. rewrite Hpk. apply t_eq_refl.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sep_post_den : forall op model0 mem0 E S M ms model S', DEN segs LIMIT model0 mem0 E S M ms model -> sep_post segs op S M = Some S' ->
  DEN segs LIMIT model0 mem0 E S' M ms model /\ s_next S' = s_next S.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros op model0 mem0 E S M ms model S' Hd Hs. destruct op as [bases| |n|x|i j|i j|j lo hi|j]; cbn [sep_post] in Hs; try discriminate.
  - split; [exact (den_sepg segs LIMIT model0 mem0 E S M ms model i j S' Hd Hs)|].
    unfold sepg_post in Hs. destruct (nth_error (sm_maps M) i), (nth_error (sm_maps M) j); try discriminate.
    destruct (is_mark _ || is_mark _)%bool; [discriminate|].
    destruct (is_const _); [|discriminate]. destruct (_ && _)%bool; [|discriminate]. injection Hs as <-. reflexivity.
  - split; [exact (den_sepw segs LIMIT model0 mem0 E S M ms model i j S' Hd Hs)|].
    unfold sepw_post in Hs. destruct (nth_error (sm_maps M) i), (nth_error (sm_maps M) j); try discriminate.
    destruct (is_mark _ || is_mark _)%bool; [discriminate|].
    destruct (_ && _)%bool; [|discriminate]. injection Hs as <-. reflexivity.
  - split; [exact (den_sepr segs LIMIT model0 mem0 E S M ms model j lo hi S' Hd Hs)|].
    unfold sepr_post in Hs. destruct (nth_error (sm_maps M) j); try discriminate.
    destruct (is_mark _); [discriminate|].
    destruct (_ && _)%bool; [|discriminate]. injection Hs as <-. reflexivity.
  - split; [exact (den_seps segs LIMIT model0 mem0 E S M ms model j S' Hd Hs)|].
    unfold seps_post in Hs. destruct (nth_error (sm_maps M) j); try discriminate.
    destruct (lwf _ _); [|discriminate]. injection Hs as <-. reflexivity.
Qed.
#[using="Type"] Lemma Pm_sep : forall op k, Pm k -> Pm (MSep op k).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros op k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (sep_post segs op S M) as [S'|] eqn:Hs; [|discriminate].
  destruct (sep_post_den op model0 mem0 E S M ms model S' Hd Hs) as [Hd' Hn].
  apply (IH S' M FS sh a finals Hck model0 mem0 E ms model Hd' (INV_same mem0 E S S' M FS model0 Hi Hn) (HAX_same E S S' M a mem0 HX Hn)
           ltac:(rewrite Hn; exact Hw)).
  intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin Hd'' Hi'' Hx'' Hw'' Ha''.
  rewrite Hn in Ha''. exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin Hd'' Hi'' Hx'' Hw'' Ha'').
Qed.

(* [comment removed for export] *)
#[using="Hp4"] Lemma Pm_split : forall l c ka kb, Pm ka -> Pm kb -> Pm (MSplit l c ka kb).
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros l c ka kb IHa IHb S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (lwf (s_next S) l) eqn:Hwl; [|discriminate].
  set (r := irange (s_facts S) l) in *.
  destruct (if Z.leb (fst r) c then mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts ka (add_fact S (FRange l (fst r) (Z.min c (snd r)))) M FS sh a else Some []) as [f1|] eqn:H1; [|discriminate].
  destruct (if Z.ltb c (snd r) then mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts kb (add_fact S (FRange l (Z.max (c + 1) (fst r)) (snd r))) M FS sh a else Some []) as [f2|] eqn:H2; [|discriminate].
  injection Hck as <-.
  assert (Hn : forall f, s_next (add_fact S f) = s_next S) by reflexivity.
  pose proof (u_range E l) as Rl.
  assert (HFs : Forall (fact_ok E) (s_facts S)) by (destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & X & _); exact X).
  pose proof (irange_sound E (s_facts S) l HFs) as Ir. fold r in Ir.
  destruct (Z_le_gt_dec (bv_unsigned (lden E l)) c) as [Hle|Hgt].
  - assert (Hc1 : Z.leb (fst r) c = true) by (apply Z.leb_le; lia). rewrite Hc1 in H1.
    apply (IHa (add_fact S (FRange l (fst r) (Z.min c (snd r)))) M FS sh a f1 H1 model0 mem0 E ms model).
    + apply den_addfact; [exact Hd|]. intros E' Ha'. cbn [fact_ok]. rewrite <- (lden_agree (s_next S) E E' l Hwl Ha'). lia.
    + exact (INV_same mem0 E S _ M FS model0 Hi (Hn _)).
    + exact (HAX_same E S _ M a mem0 HX (Hn _)).
    + rewrite Hn. exact Hw.
    + intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin Hd'' Hi'' Hx'' Hw'' Ha''. rewrite Hn in Ha''.
      exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (in_or_app _ _ _ (or_introl Hin)) Hd'' Hi'' Hx'' Hw'' Ha'').
  - assert (Hc2 : Z.ltb c (snd r) = true) by (apply Z.ltb_lt; lia). rewrite Hc2 in H2.
    apply (IHb (add_fact S (FRange l (Z.max (c + 1) (fst r)) (snd r))) M FS sh a f2 H2 model0 mem0 E ms model).
    + apply den_addfact; [exact Hd|]. intros E' Ha'. cbn [fact_ok]. rewrite <- (lden_agree (s_next S) E E' l Hwl Ha'). unfold M64, two64 in *. lia.
    + exact (INV_same mem0 E S _ M FS model0 Hi (Hn _)).
    + exact (HAX_same E S _ M a mem0 HX (Hn _)).
    + rewrite Hn. exact Hw.
    + intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin Hd'' Hi'' Hx'' Hw'' Ha''. rewrite Hn in Ha''.
      exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (in_or_app _ _ _ (or_intror Hin)) Hd'' Hi'' Hx'' Hw'' Ha'').
Qed.
#[using="Hp4"] Lemma Pm_splitG : forall j c ka kb, Pm ka -> Pm kb -> Pm (MSplitG j c ka kb).
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros j c ka kb IHa IHb S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (nth_error (sm_maps M) j) as [g|]; [|discriminate]. set (l := fst (fst g)) in *.
  destruct (lwf (s_next S) l) eqn:Hwl; [|discriminate].
  set (r := irange (s_facts S) l) in *.
  destruct (if Z.leb (fst r) c then mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts ka (add_fact S (FRange l (fst r) (Z.min c (snd r)))) M FS sh a else Some []) as [f1|] eqn:H1; [|discriminate].
  destruct (if Z.ltb c (snd r) then mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts kb (add_fact S (FRange l (Z.max (c + 1) (fst r)) (snd r))) M FS sh a else Some []) as [f2|] eqn:H2; [|discriminate].
  injection Hck as <-.
  assert (Hn : forall f, s_next (add_fact S f) = s_next S) by reflexivity.
  pose proof (u_range E l) as Rl.
  assert (HFs : Forall (fact_ok E) (s_facts S)) by (destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & X & _); exact X).
  pose proof (irange_sound E (s_facts S) l HFs) as Ir. fold r in Ir.
  destruct (Z_le_gt_dec (bv_unsigned (lden E l)) c) as [Hle|Hgt].
  - assert (Hc1 : Z.leb (fst r) c = true) by (apply Z.leb_le; lia). rewrite Hc1 in H1.
    apply (IHa (add_fact S (FRange l (fst r) (Z.min c (snd r)))) M FS sh a f1 H1 model0 mem0 E ms model).
    + apply den_addfact; [exact Hd|]. intros E' Ha'. cbn [fact_ok]. rewrite <- (lden_agree (s_next S) E E' l Hwl Ha'). lia.
    + exact (INV_same mem0 E S _ M FS model0 Hi (Hn _)).
    + exact (HAX_same E S _ M a mem0 HX (Hn _)).
    + rewrite Hn. exact Hw.
    + intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin Hd'' Hi'' Hx'' Hw'' Ha''. rewrite Hn in Ha''.
      exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (in_or_app _ _ _ (or_introl Hin)) Hd'' Hi'' Hx'' Hw'' Ha'').
  - assert (Hc2 : Z.ltb c (snd r) = true) by (apply Z.ltb_lt; lia). rewrite Hc2 in H2.
    apply (IHb (add_fact S (FRange l (Z.max (c + 1) (fst r)) (snd r))) M FS sh a f2 H2 model0 mem0 E ms model).
    + apply den_addfact; [exact Hd|]. intros E' Ha'. cbn [fact_ok]. rewrite <- (lden_agree (s_next S) E E' l Hwl Ha'). unfold M64, two64 in *. lia.
    + exact (INV_same mem0 E S _ M FS model0 Hi (Hn _)).
    + exact (HAX_same E S _ M a mem0 HX (Hn _)).
    + rewrite Hn. exact Hw.
    + intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin Hd'' Hi'' Hx'' Hw'' Ha''. rewrite Hn in Ha''.
      exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (in_or_app _ _ _ (or_intror Hin)) Hd'' Hi'' Hx'' Hw'' Ha'').
Qed.

(* [comment removed for export] *)
#[using="path0 data0 Hp4"] Lemma concr_lin_den : forall E fs l, Forall (fact_ok E) fs -> lden E (concr_lin fs l) = lden E l.
Proof. LiaFast.lf_pins (fun (path0 data0 Hp4 : LiaFast.U) => LiaFast.u0).
  intros E fs l HF. unfold concr_lin. pose proof (irange_sound E fs l HF) as Ir.
  destruct (irange fs l) as [lo hi] eqn:Hir. cbn [fst snd] in Ir. destruct (Z.eqb lo hi) eqn:Heq; [|reflexivity].
  apply Z.eqb_eq in Heq. subst hi. rewrite lden_lconst. apply bv_eq. pose proof (u_range E l) as Rg.
  rewrite u_small64 by lia. lia.
Qed.
#[using="path0 data0 Hp4"] Lemma regs_concr : forall E fs R regs, Forall (fact_ok E) fs -> regs_ok E R regs -> regs_ok E (tmap (concr_lin fs) R) regs.
Proof. LiaFast.lf_pins (fun (path0 data0 Hp4 : LiaFast.U) => LiaFast.u0).
  intros E fs R regs HF HR r. rewrite (HR r). unfold rget. destruct (rkey r) as [p|p|] eqn:Hk; try reflexivity;
    rewrite tget_tmap; destruct (tget _ R) as [l|]; cbn [option_map]; try reflexivity; symmetry; apply concr_lin_den; exact HF.
Qed.
#[using="path0 data0 Hp4"] Lemma den_concr : forall model0 mem0 E S M ms model, DEN segs LIMIT model0 mem0 E S M ms model -> DEN segs LIMIT model0 mem0 E (concr S) M ms model.
Proof. LiaFast.lf_pins (fun (path0 data0 Hp4 : LiaFast.U) => LiaFast.u0).
  intros model0 mem0 E S M ms model Hd. destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  constructor; try assumption.
  intros E' Ha'. destruct (Hsd E' Ha') as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  unfold sden0; cbn [s_pc s_regs s_rgs s_facts s_resv concr]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [exact (regs_concr E' _ _ _ H7 H4)|]. split; [exact H5|]. split; [exact H6|]. split; [exact H7 | exact H8].
Qed.
#[using="Hp4"] Lemma Pm_concr : forall k, Pm k -> Pm (MConcR k).
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  assert (Hn : s_next (concr S) = s_next S) by reflexivity.
  apply (IH (concr S) M FS sh a finals Hck model0 mem0 E ms model).
  - exact (den_concr model0 mem0 E S M ms model Hd).
  - exact (INV_same mem0 E S _ M FS model0 Hi Hn).
  - exact (HAX_same E S _ M a mem0 HX Hn).
  - rewrite Hn. exact Hw.
  - intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin Hd'' Hi'' Hx'' Hw'' Ha''. rewrite Hn in Ha''.
    exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin Hd'' Hi'' Hx'' Hw'' Ha'').
Qed.
#[using="Hp4"] Lemma INV_concf : forall mem0 E S M FS model0, Forall (fact_ok E) (s_facts S) -> INV mem0 E S M FS model0 ->
  INV mem0 E S M (concr_fs (s_facts S) FS) model0.
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros mem0 E S M FS model0 HF Hi. destruct FS as [|off FL| | |off FL]; try exact Hi; cbn [concr_fs].
  all: destruct Hi as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  all: assert (Hc : lden E (concr_lin (s_facts S) off) = lden E off) by exact (concr_lin_den E _ off HF).
  all: split; [exact H1|]; split;
    [cbn [fs_wf] in H2 |- *; apply andb_prop in H2 as [H2a H2b]; rewrite H2b, andb_true_r;
     unfold concr_lin; destruct (irange (s_facts S) off) as [lo hi]; destruct (Z.eqb lo hi); [apply lwf_lconst | exact H2a]
    | split; [exact H3|]; split; [exact H4|]; split; [exact H5|]; split; [exact H6|]; split; [exact H7|];
      split; [|split; [exact H9 | split; [exact H10 | exact H11]]]; rewrite Hc; exact H8].
Qed.
(* [comment removed for export] *)
#[using="Hp4 awf_mono aeqb_eq HA_agree"] Lemma Pm_joinS : forall body jpc shj k, Pm body -> Pm k -> Pm (MJoinS body jpc shj k).
Proof. LiaFast.lf_pins (fun (Hp4 awf_mono aeqb_eq HA_agree : LiaFast.U) => LiaFast.u0).
  intros body jpc shj k IHb IHk S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts body S M FS sh a) as [fb|] eqn:Hb; [|discriminate].
  set (J := List.filter (fun '(F, _, _, shF, _) => (Z.eqb (s_pc F) jpc && shp_ent shF shj TEmpty)%bool) fb) in *.
  set (O := List.filter (fun '(F, _, _, shF, _) => negb (Z.eqb (s_pc F) jpc && shp_ent shF shj TEmpty)%bool) fb) in *.
  assert (HinO : forall F MF FSF shF aF, In (F, MF, FSF, shF, aF) fb -> (Z.eqb (s_pc F) jpc && shp_ent shF shj TEmpty)%bool = false ->
            In (F, MF, FSF, shF, aF) O).
  { intros F MF FSF shF aF Hin Hpc. unfold O. apply filter_In. split; [exact Hin|]. cbv beta iota. rewrite Hpc. reflexivity. }
  assert (HinJ : forall F MF FSF shF aF, In (F, MF, FSF, shF, aF) fb -> (Z.eqb (s_pc F) jpc && shp_ent shF shj TEmpty)%bool = true ->
            In (F, MF, FSF, shF, aF) J).
  { intros F MF FSF shF aF Hin Hpc. unfold J. apply filter_In. split; [exact Hin|]. cbv beta iota. exact Hpc. }
  destruct J as [|[[[[F0 M0] FS0] sh0] a0] Jr] eqn:HJ.
  - injection Hck as <-.
    apply (IHb S M FS sh a fb Hb model0 mem0 E ms model Hd Hi HX Hw).
    intros F MF FSF shF aF model0F mem0F EF msF modelF Hin HdF HiF HXF HwF HaF.
    destruct (Z.eqb (s_pc F) jpc && shp_ent shF shj TEmpty)%bool eqn:Hpc; [destruct (HinJ F MF FSF shF aF Hin Hpc)|].
    exact (Hk F MF FSF shF aF model0F mem0F EF msF modelF (HinO F MF FSF shF aF Hin Hpc) HdF HiF HXF HwF HaF).
  - set (n0 := max_next (List.map (fun '(F, _, _, _, _) => F) Jr) (s_next F0)) in *.
    set (P := join_fs_hull (fst (gen2 F0 (List.map (fun '(F, _, _, _, _) => F) Jr))) FS0 ((F0, M0, FS0, sh0, a0) :: Jr)) in *.
    destruct (forallb (fun '(F, MF, FSF, shF, aF) => wentN n0 F MF FSF shF P FS0 sh0 && sm_eqb MF M0 && aeqb aF a0) ((F0, M0, FS0, sh0, a0) :: Jr) && state_wf P &&
              Pos.leb (s_next S) n0 && fs_wf (s_next P) FS0 && shp_wf (s_next P) sh0 && pv_okb pv hv n0 && awf n0 a0)%bool eqn:Hc; [|discriminate].
    destruct (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts k P M0 FS0 sh0 a0) as [fk|] eqn:Hk0; [|discriminate].
    injection Hck as <-.
    apply andb_prop in Hc as [Hc Hwa0]. apply andb_prop in Hc as [Hc Hpv0]. apply andb_prop in Hc as [Hc HwP].
    apply andb_prop in Hc as [Hc Hfw]. apply andb_prop in Hc as [Hc Hsn]. apply andb_prop in Hc as [HallN HwfP]. apply Pos.leb_le in Hsn.
    pose proof (forallb_wentN P n0 FS0 sh0 M0 a0 _ HwfP HallN) as Hall.
    rewrite forallb_forall in Hall.
    apply (IHb S M FS sh a fb Hb model0 mem0 E ms model Hd Hi HX Hw).
    intros F MF FSF shF aF model0F mem0F EF msF modelF Hin HdF HiF HXF HwF HaF.
    destruct (Z.eqb (s_pc F) jpc && shp_ent shF shj TEmpty)%bool eqn:Hpc.
    + pose proof (Hall _ (HinJ F MF FSF shF aF Hin Hpc)) as Hq. cbv beta in Hq.
      apply andb_prop in Hq as [Hq Hae]. apply andb_prop in Hq as [Hwe Hsm]. apply sm_eqb_eq in Hsm. apply aeqb_eq in Hae. subst MF aF.
      destruct (went_parts _ _ _ _ _ _ _ _ Hwe) as (Hok & HnF & Hfe & Hse).
      destruct (ent_ok_parts _ _ _ _ Hok) as (Hpf & Hwf0 & Hn1).
      destruct (den_weaken segs LIMIT model0F mem0F EF F P M0 msF modelF n0 HdF Hok) as [HdP HaP].
      pose proof (INV_ent2 mem0F EF F P M0 FSF FS0 model0F n0 HiF Hpf Hpv0 Hwf0 Hfe Hfw Hn1) as HiP.
      assert (HXP : HAX (ecomp EF (match_st F P)) P M0 a0 mem0F)
        by exact (conj (awf_mono _ _ a0 Hn1 Hwa0) (HA_agree n0 EF _ M0 a0 mem0F Hwf0 Hwa0 HaP (proj2 HXF))).
      rewrite <- (shp_den_ent EF shF sh0 (match_st F P) Hse).
      apply (IHk P M0 FS0 sh0 a0 fk Hk0 model0F mem0F _ msF modelF HdP HiP HXP HwP).
      intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' HX'' Hw'' Ha''.
      apply (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (in_or_app _ _ _ (or_introl Hin'')) Hd'' Hi'' HX'' Hw'').
      apply (agree_trans _ E EF E'' HaF). apply (agree_trans _ EF (ecomp EF (match_st F P)) E'').
      * exact (agree_mono (s_next S) n0 EF _ Hsn HaP).
      * exact (agree_mono (s_next S) (s_next P) _ E'' ltac:(lia) Ha'').
    + exact (Hk F MF FSF shF aF model0F mem0F EF msF modelF (in_or_app _ _ _ (or_intror (HinO F MF FSF shF aF Hin Hpc))) HdF HiF HXF HwF HaF).
Qed.
#[using="Hp4"] Lemma Pm_concf : forall k, Pm k -> Pm (MConcF k).
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  assert (HF : Forall (fact_ok E) (s_facts S)) by (destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & X & _); exact X).
  exact (IH S M (concr_fs (s_facts S) FS) sh a finals Hck model0 mem0 E ms model Hd (INV_concf mem0 E S M FS model0 HF Hi) HX Hw Hk).
Qed.

(* [comment removed for export] *)
#[using="Hwx Hfs Hect Hp1 Hp2 Hp3 Hp4 Hp5 HFL awf_mono HA_agree"] Lemma Pm_openLB : forall kerr kok, Pm kerr -> Pm kok -> Pm (MOpenLB kerr kok).
Proof. LiaFast.lf_pins (fun (Hwx Hfs Hect Hp1 Hp2 Hp3 Hp4 Hp5 HFL awf_mono HA_agree : LiaFast.U) => LiaFast.u0).
  intros kerr kok IHe IHo S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct FS as [|off FL| | |off FL]; try discriminate. destruct sh as [po kc|sa sb|lq loq hiq sa sb|lq jq sa sb]; try discriminate.
  destruct (negb dr && is_ecall t (s_pc S) && open_args_ok S pv && Z.leb 0 FLlo && Z.ltb FLlo 4611686018427387904)%bool eqn:Hb; [|discriminate].
  apply andb_prop in Hb as [Hb Hlo62]. apply Z.ltb_lt in Hlo62. apply andb_prop in Hb as [Hb Hlo0]. apply Z.leb_le in Hlo0.
  apply andb_prop in Hb as [Hb Hoa]. apply andb_prop in Hb as [Hdr Hx]. apply negb_true_iff in Hdr. apply is_ecall_ok in Hx.
  destruct (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts kerr (ret_gen S ERRLO ERRHI) M FSClosed sa a) as [f1|] eqn:H1;
    [|discriminate].
  destruct (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts kok (ret_post S (lconst 3)) M (FSOpenLB (lconst 0) (lconst FLlo)) sb a) as [f2|] eqn:H2; [|discriminate].
  injection Hck as <-. cbn [shp_wf] in Hw. apply andb_prop in Hw as [Hwa Hwb]. cbn [shp_den].
  unfold open_args_ok in Hoa.
  destruct (a7c S) as [c7|] eqn:H7; [|discriminate]. destruct (arg S 0) as [c0|] eqn:H0; [|discriminate].
  destruct (arg S 2) as [fl|] eqn:H2a; [|discriminate].
  apply andb_prop in Hoa as [Hoa Hpvl]. apply andb_prop in Hoa as [Hoa Hldiff]. apply andb_prop in Hoa as [H56 Hdfd].
  apply Z.eqb_eq in H56, Hldiff. apply bv_eqb_eq in Hdfd. apply lin_eqb_eq in Hpvl. subst c7.
  pose proof Hi as Hi0.
  destruct Hi0 as (Hpv & Hfsw & Hfr & Hm0 & Hlen & Hlk & Hfs0 & (Hal & Hfree) & Hc1 & Hc2 & Hdv).
  apply (den_ecall segs cfg LIMIT model0 mem0 Hwx t E S M ms model _ Hect Hx Hd). intros model1 Hd1.
  destruct (open_path_ok mem0 model0 E S M ms model model1 FSClosed Hdr Hd Hd1 Hi) as [Hcstr Hav].
  rewrite <- Hpvl in Hcstr, Hav.
  apply (den_openat_file segs cfg LIMIT mem0 Hfs model0 E S M ms model1 _ _ c0 fl path0 data0 (Z_to_bv 64 3) Hd1 H7 H0 Hdfd H2a Hldiff
           Hcstr Hp1 Hp2 (Hp3 Hdr) (Hlk Hdr) Hal Hfree ltac:(rewrite u_small64 by (unfold two64; lia); lia) Hav).
  - intros e He ms' m'' Hd''.
    pose proof (errno_in_range e He) as Hcr.
    assert (Hc64 : 0 <= bv_unsigned (errno_ret e) < two64) by (unfold ERRLO, ERRHI, two64 in *; lia).
    pose proof (den_gen_ret segs LIMIT model0 mem0 E S M ms' m'' (bv_unsigned (errno_ret e)) ERRLO ERRHI Hd'' Hc64 Hcr) as Hd3.
    set (E1 := upd E (s_next S) (Z_to_bv 64 (bv_unsigned (errno_ret e)))) in *.
    assert (Ha : agree (s_next S) E E1) by exact (agree_upd (s_next S) E _).
    assert (Hle : (s_next S <= s_next (ret_gen S ERRLO ERRHI))%positive) by (cbn [ret_gen add_fact bump ret_post s_next]; lia).
    pose proof (dn_wf _ _ _ _ _ _ _ _ _ Hd) as Hwf0.
    rewrite <- (shp_den_agree (s_next S) E E1 sa Hwa Ha).
    apply (IHe _ _ _ _ _ f1 H1 model0 mem0 E1 ms' m'' Hd3
             (INV_agree mem0 E E1 S (ret_gen S ERRLO ERRHI) M M FSClosed model0 Hi Ha Hle eq_refl Hwf0)
             (HAX_step E E1 S (ret_gen S ERRLO ERRHI) M a mem0 HX Hwf0 Ha Hle) (shp_wf_mono _ _ sa Hle Hwa)).
    intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd''' Hi'' Hx'' Hw'' Ha''.
    exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (in_or_app _ _ _ (or_introl Hin'')) Hd''' Hi'' Hx'' Hw''
             (agree_trans _ E E1 E'' Ha (agree_mono _ _ E1 E'' Hle Ha''))).
  - intros ms' m'' Hd''.
    set (model0' := with_fds (fd_insert (m_fds model0) (Z_to_bv 64 3) (FdFile path0 (Z_to_bv 64 0))) model0) in *.
    change (lconst (bv_unsigned (Z_to_bv 64 3))) with (lconst 3) in Hd''.
    assert (Hi' : INV mem0 E (ret_post S (lconst 3)) M (FSOpenLB (lconst 0) (lconst FLlo)) model0').
    { unfold INV. cbn [ret_post s_next].
      split; [exact Hpv|]. split; [cbn [fs_wf]; rewrite !lwf_lconst; reflexivity|].
      split; [exact Hfr|]. split; [exact Hm0|]. split; [exact Hlen|].
      split; [intros Hdr'; unfold model0'; rewrite with_fds_fs; exact (Hlk Hdr')|]. split; [unfold model0'; rewrite with_fds_fs; exact Hfs0|].
      split; [|split; [unfold model0'; rewrite with_fds_fds, fd_lookup_insert_other by (first [exact w3_ne1 | exact w3_ne2]); assumption|]].
      2: { split; [unfold model0'; rewrite with_fds_fds, fd_lookup_insert_other by (first [exact w3_ne1 | exact w3_ne2]); assumption|].
           exact (hv_inv_step E E S (ret_post S (lconst 3)) Hdv (agree_refl _ _) ltac:(cbn [ret_post s_next]; lia)). }
      unfold model0'. rewrite with_fds_fds, fd_lookup_insert_same. rewrite !lden_lconst. split; [reflexivity|].
      rewrite !u_small64 by (unfold two64; lia). split; [lia | exact (proj1 HFL)]. }
    apply (IHo _ _ _ _ _ f2 H2 model0' mem0 E ms' m'' Hd'' Hi' (HAX_same E S _ M a mem0 HX eq_refl) Hwb).
    intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd''' Hi'' Hx'' Hw'' Ha''.
    exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (in_or_app _ _ _ (or_intror Hin'')) Hd''' Hi'' Hx'' Hw'' Ha'').
Qed.

(* [comment removed for export] *)
#[using="Hwx Hect Hp3 Hp4 HFLhi Hseg"] Lemma Pm_readLB : forall b o k, Pm k -> Pm (MReadLB b o k).
Proof. LiaFast.lf_pins (fun (Hwx Hect Hp3 Hp4 HFLhi Hseg : LiaFast.U) => LiaFast.u0).
  intros b0 o k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct FS as [|off FL| | |off B]; try discriminate.
  destruct (negb dr && is_ecall t (s_pc S))%bool eqn:Hx; [|discriminate]. apply andb_prop in Hx as [Hdr Hx]. apply negb_true_iff in Hdr. apply is_ecall_ok in Hx.
  set (i := rg_index (s_rgs S) b0 O) in *.
  destruct (read_args_ok S i o) as [chi|] eqn:Hra; [|discriminate].
  set (c := argl S 2) in *.
  destruct (Z.leb chi (fst (irange (s_facts S) (lsub B off)))) eqn:Hlb; [|discriminate]. apply Z.leb_le in Hlb.
  destruct (irange (s_facts S) c) as [clo chi0] eqn:Hic.
  unfold read_args_ok in Hra. fold c in Hra. rewrite Hic in Hra.
  destruct (a7c S) as [c7|] eqn:H7; [|discriminate]. destruct (arg S 0) as [c0|] eqn:H0; [|discriminate].
  destruct (nth_error (s_rgs S) i) as [R|] eqn:HR; [|discriminate].
  destruct (is_const (rg_base R)) as [b|] eqn:Hb0; [|discriminate].
  destruct (is_const (rg_size R)) as [sz|] eqn:Hs0; [|discriminate].
  destruct (Z.eqb c7 63 && Z.eqb c0 3 && Z.ltb 0 clo && Z.leb chi0 65536 && rk_is_rwz (rg_kind R) && Z.leb 0 o &&
            Z.leb (o + chi0) sz && Z.leb 0x10000 b && Z.leb (b + sz) 0x61a000 && lwf (s_next S) c &&
            lin_eqb (argl S 1) (lconst (b + o)))%bool eqn:Hcq; [|discriminate].
  injection Hra as Hchi. subst chi0.
  repeat match type of Hcq with ((_ && _)%bool = true) => apply andb_prop in Hcq as [Hcq ?Hc] end.
  repeat match goal with
         | Hx' : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in Hx'
         | Hx' : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx'
         | Hx' : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hx'
         | Hx' : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in Hx'
         end.
  subst c7 c0.
  assert (Hwc : lwf (s_next S) c = true) by assumption.
  pose proof Hi as Hi0. destruct Hi0 as (Hpv & Hfsw & Hfr & Hm0 & Hlen & Hlk & Hfs0 & (Hfd & HoB & HBd) & Hch1 & Hch2 & Hdv).
  cbn [fs_wf] in Hfsw. apply andb_prop in Hfsw as [Hwoff HwB].
  assert (Hkd : rg_kind R = RW \/ rg_kind R = RZ).
  { match goal with Hk' : rk_is_rwz (rg_kind R) = true |- _ => destruct (rg_kind R); try discriminate; auto end. }
  destruct (is_const_sound E _ b Hb0) as [HbE Hb64].
  set (remz := Z.of_nat (length data0) - bv_unsigned (lden E off)).
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF0 & _).
  pose proof (irange_sound E _ (lsub B off) HF0) as HirB.
  pose proof (irange_sound E _ c HF0) as Hics. rewrite Hic in Hics. cbn [fst snd] in Hics.
  set (cnt := bv_unsigned (lden E c)) in *.
  assert (HBo : bv_unsigned (lden E (lsub B off)) = bv_unsigned (lden E B) - bv_unsigned (lden E off)).
  { rewrite lden_lsub, bv_sub_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
    pose proof (bv_unsigned_in_range _ (lden E B)) as X. unfold bv_modulus in X. change (2 ^ Z.of_N 64) with two64 in X.
    pose proof (bv_unsigned_in_range _ (lden E off)) as Y. unfold bv_modulus in Y. change (2 ^ Z.of_N 64) with two64 in Y.
    apply Z.mod_small. lia. }
  assert (Hcr : cnt <= remz) by (unfold remz; lia).
  assert (Hcw : lden E c = Z_to_bv 64 cnt) by (unfold cnt; symmetry; apply Z_to_bv_bv_unsigned).
  apply (den_ecall segs cfg LIMIT model0 mem0 Hwx t E S M ms model _ Hect Hx Hd). intros model1 Hd1.
  assert (Hbuf : lden E (rget (s_regs S) (rkey a1r)) = Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)).
  { change (rget (s_regs S) (rkey a1r)) with (argl S 1).
    match goal with Hq : argl S 1 = lconst (b + o) |- _ => rewrite Hq end. rewrite lden_lconst, HbE, u_small64 by exact Hb64. reflexivity. }
  assert (Hsz : forall E', agree (s_next S) E E' -> o + chi <= rsz E' R) by (intros E' _; rewrite (rsz_is_const E' R sz Hs0); lia).
  assert (Hub : bv_unsigned (lden E (rg_base R)) = b) by (rewrite HbE; apply u_small64; exact Hb64).
  assert (Hok : access_okb (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) cnt = true).
  { unfold access_okb. rewrite Hub, u_small64 by (unfold two64; lia). apply andb_true_intro. split; apply Z.leb_le; unfold TASK_SIZE; lia. }
  assert (Hav : range_avoids (Hof E M model1) (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) (Z.to_nat cnt)).
  { intros kk Hkk. assert (Hkk' : Z.of_nat kk < cnt) by (apply Nat2Z.inj_lt in Hkk; rewrite Z2Nat.id in Hkk by lia; exact Hkk).
    destruct (Hof E M model1 (woff (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) kk)) eqn:Hh; [|reflexivity].
    exfalso. apply (dn_hoff _ _ _ _ _ _ _ _ _ Hd1) in Hh. unfold woff in Hh. rewrite Hub in Hh.
    rewrite (u_small64 (b + o)) in Hh by (unfold two64; lia). rewrite u_small64 in Hh by (unfold two64; lia).
    apply (Hseg (b + o + Z.of_nat kk)); [lia | exact Hh]. }
  assert (Hfd3 : fd_lookup (m_fds model0) (fd32 (Z_to_bv 64 3)) = Some (FdFile path0 (lden E off))) by (rewrite fd32_3; exact Hfd).
  assert (Hlfr : Z.of_nat (length (file_read data0 (lden E off) (Z_to_bv 64 cnt))) = Z.min cnt remz).
  { rewrite length_file_read by lia. rewrite u_small64 by (unfold two64; lia). reflexivity. }
  assert (Hc2' : lden E (argl S 2) = Z_to_bv 64 cnt) by exact Hcw.
  assert (Hv : lden E c = len_word (file_read data0 (lden E off) (Z_to_bv 64 cnt))).
  { apply bv_eq. unfold len_word. fold cnt. rewrite u_small64 by (rewrite Hlfr; unfold two64; lia). rewrite Hlfr. lia. }
  apply (den_read_file2 segs cfg LIMIT mem0 model0 E S M ms model1 _ 3 cnt path0 (lden E off) data0 i R o c
           Hd1 H7 H0 Hc2' ltac:(lia) chi ltac:(lia) HR Hkd ltac:(lia) Hbuf Hsz Hfd3 (Hlk Hdr) Hwc Hv Hok Hav).
  intros ms' m'' Hd'' _.
  set (S1 := read_post S i o (o + chi) c) in *.
  assert (Hn1 : s_next S1 = s_next S) by apply read_post_next.
  assert (Hi' : INV mem0 E S1 M (FSOpenLB (ladd off c) B)
                  (with_fds (fd_insert (m_fds model0) (fd32 (Z_to_bv 64 3)) (FdFile path0 (lden E off + lden E c))) model0)).
  { unfold INV. rewrite Hn1. split; [exact Hpv|].
    split; [cbn [fs_wf]; rewrite HwB, andb_true_r; exact (lwf_ladd _ _ _ Hwoff Hwc)|].
    split; [exact Hfr|]. split; [exact Hm0|]. split; [exact Hlen|]. split; [intros Hdr'; rewrite with_fds_fs; exact (Hlk Hdr')|]. split; [rewrite with_fds_fs; exact Hfs0|].
    rewrite fd32_3.
    split; [|split; [rewrite with_fds_fds, fd_lookup_insert_other by (first [exact w3_ne1 | exact w3_ne2]); exact Hch1|]].
    2: { split; [rewrite with_fds_fds, fd_lookup_insert_other by (first [exact w3_ne1 | exact w3_ne2]); exact Hch2|].
         exact (hv_inv_step E E S _ Hdv (agree_refl _ _) ltac:(rewrite Hn1; lia)). }
    rewrite with_fds_fds, fd_lookup_insert_same. rewrite lden_ladd.
    split; [reflexivity|]. split; [|exact HBd].
    rewrite bv_add_unsigned. fold cnt. unfold bv_wrap.
    pose proof (bv_unsigned_in_range _ (lden E off)) as Y. unfold bv_modulus in Y. change (2 ^ Z.of_N 64) with two64 in Y.
    pose proof (bv_unsigned_in_range _ (lden E B)) as X. unfold bv_modulus in X. change (2 ^ Z.of_N 64) with two64 in X.
    rewrite Z.mod_small by (change (bv_modulus 64) with two64; unfold two64 in *; lia). lia. }
  apply (IH _ _ _ _ _ finals Hck _ mem0 E ms' m'' Hd'' Hi' (HAX_same E S _ M a mem0 HX Hn1) ltac:(rewrite Hn1; exact Hw)).
  intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd''' Hi'' Hx'' Hw'' Ha''.
  rewrite Hn1 in Ha''. exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd''' Hi'' Hx'' Hw'' Ha'').
Qed.
#[using="Hwx Hect Hp3 Hp4 HFLhi Hseg"] Lemma Pm_readB : forall b o ka kb, Pm ka -> Pm kb -> Pm (MReadB b o ka kb).
Proof. LiaFast.lf_pins (fun (Hwx Hect Hp3 Hp4 HFLhi Hseg : LiaFast.U) => LiaFast.u0).
  intros b o ka kb IHa IHb S M FS sh a finals Hck. change (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts (MRead (rg_index (s_rgs S) b O) o ka kb) S M FS sh a = Some finals) in Hck.
  exact (Pm_read (rg_index (s_rgs S) b O) o ka kb IHa IHb S M FS sh a finals Hck).
Qed.
#[using="Hwx Hect Hp3 Hp4 HFLhi Hseg"] Lemma Pm_readHB : forall b o k ka kb, Pm ka -> Pm kb -> Pm (MReadHB b o k ka kb).
Proof. LiaFast.lf_pins (fun (Hwx Hect Hp3 Hp4 HFLhi Hseg : LiaFast.U) => LiaFast.u0).
  intros b o k ka kb IHa IHb S M FS sh a finals Hck. change (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts (MReadH (rg_index (s_rgs S) b O) o k ka kb) S M FS sh a = Some finals) in Hck.
  exact (Pm_readH (rg_index (s_rgs S) b O) o k ka kb IHa IHb S M FS sh a finals Hck).
Qed.
#[using="Hp4"] Lemma Pm_splitR : forall r c ka kb, Pm ka -> Pm kb -> Pm (MSplitR r c ka kb).
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros r c ka kb IHa IHb S M FS sh a finals Hck. change (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts (MSplit (rget (s_regs S) (Z.to_pos (r + 1))) c ka kb) S M FS sh a = Some finals) in Hck.
  exact (Pm_split (rget (s_regs S) (Z.to_pos (r + 1))) c ka kb IHa IHb S M FS sh a finals Hck).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma uE_rng : forall E l, 0 <= uE E l < two64.
Proof. LiaFast.lf_pins LiaFast.u0. intros E l. unfold uE. pose proof (bv_unsigned_in_range _ (lden E l)) as X. unfold bv_modulus in X. change (2 ^ Z.of_N 64) with two64 in X. exact X. Qed.
#[using="Type"] Lemma firstn_add2 : forall (l : list byte) n m, firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
Proof. LiaFast.lf_pins LiaFast.u0. induction l as [|x l IH]; intros [|n] m; cbn [firstn skipn app Nat.add]; rewrite ?firstn_nil; try reflexivity. f_equal. apply IH. Qed.
#[using="Type"] Lemma skipn_split2 : forall (l : list byte) o n, skipn o l = firstn n (skipn o l) ++ skipn (o + n) l.
Proof. LiaFast.lf_pins LiaFast.u0. intros l o n. rewrite <- (firstn_skipn n (skipn o l)) at 1. f_equal. rewrite skipn_skipn. f_equal. apply Nat.add_comm. Qed.
#[using="Type"] Lemma firstn_skipn_app2 : forall (l : list byte) o a b, firstn a (skipn o l) ++ firstn b (skipn (o + a) l) = firstn (a + b) (skipn o l).
Proof. LiaFast.lf_pins LiaFast.u0. intros l o a b. rewrite firstn_add2, skipn_skipn, Nat.add_comm. reflexivity. Qed.
#[using="Type"] Lemma src_bytes_args : forall E pre j lj suf, uE E lj = Z.of_nat (length (sarg j)) ->
  src_bytes E (SArgs pre j lj suf) = msgb sarg pre suf j.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E pre j lj suf H. cbn [src_bytes]. unfold msgb. rewrite H, Nat2Z.id, firstn_all. reflexivity.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma src_bytes_lit : forall E Pn bs, src_bytes E (SLit bs) = msgb (fun _ : nat => @nil byte) (firstn Pn bs) (skipn Pn bs) O.
Proof. LiaFast.lf_pins LiaFast.u0. intros E Pn bs. cbn [src_bytes]. unfold msgb. cbn [app]. rewrite <- map_app, firstn_skipn. reflexivity. Qed.
#[using="Type"] Lemma len_rec_sound : forall E m0 recs lj j, Forall (sbytes_ok sarg E m0) recs -> len_rec recs lj j = true ->
  uE E lj = Z.of_nat (length (sarg j)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m0 recs lj j HF H. unfold len_rec in H. apply existsb_exists in H as (r & Hr & Hc). apply andb_prop in Hc as [H1 H2].
  apply lin_eqb_eq in H1. apply Nat.eqb_eq in H2. rewrite Forall_forall in HF. destruct r as [[b l] jj]. cbn [fst snd] in H1, H2. subst.
  exact (proj1 (HF _ Hr)).
Qed.

(* [comment removed for export] *)
#[using="Hp4"] Lemma Pm_wvpost : forall k, Pm k -> forall S M FS sh a len (ol0 : option lin) finals,
  match ol0 with
  | Some l0 => match mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts k (wv_lo S len l0) M FS sh a,
                     mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts k (wv_hi S len l0) M FS sh a with
               | Some f1, Some f2 => Some (f1 ++ f2)
               | _, _ => None
               end
  | None => mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts k (wv_post S len 1073741824) M FS sh a
  end = Some finals ->
  forall model0 mem0 E' ms' m'', DEN segs LIMIT model0 mem0 E' (wv_post S len 1073741824) M ms' m'' ->
  INV mem0 E' (wv_post S len 1073741824) M FS model0 -> HAX E' (wv_post S len 1073741824) M a mem0 ->
  shp_wf (s_next (wv_post S len 1073741824)) sh = true ->
  (forall l0, ol0 = Some l0 -> lwf (s_next S) l0 = true /\ bv_unsigned (lden E' l0) <= 1073741824 /\
                               1 <= bv_unsigned (E' (s_next S)) <= 1073741824) ->
  (forall S' M' FS' sh' a' model0' mem0' E'' ms'' model', In (S', M', FS', sh', a') finals -> DEN segs LIMIT model0' mem0' E'' S' M' ms'' model' ->
     INV mem0' E'' S' M' FS' model0' -> HAX E'' S' M' a' mem0' -> shp_wf (s_next S') sh' = true ->
     agree (s_next (wv_post S len 1073741824)) E' E'' -> realizes_cfg segs cfg (mkCfg ms'' model') (shp_den E'' sh')) ->
  realizes_cfg segs cfg (mkCfg ms' m'') (shp_den E' sh).
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros k IH S M FS sh a len ol0 finals Hck model0 mem0 E' ms' m'' Hd Hi HX Hw Hol Hk.
  destruct ol0 as [l0|]; [|exact (IH _ _ _ _ _ finals Hck model0 mem0 E' ms' m'' Hd Hi HX Hw Hk)].
  destruct (Hol l0 eq_refl) as (Hwl0 & Hb0 & Hkz).
  destruct (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts k (wv_lo S len l0) M FS sh a) as [f1|] eqn:H1; [|discriminate].
  destruct (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts k (wv_hi S len l0) M FS sh a) as [f2|] eqn:H2; [|discriminate].
  injection Hck as <-.
  assert (Hn : forall f, s_next (add_fact (wv_post S len 1073741824) f) = s_next (wv_post S len 1073741824)) by reflexivity.
  assert (Hnx : s_next (wv_post S len 1073741824) = Pos.succ (s_next S)) by reflexivity.
  set (kz := bv_unsigned (E' (s_next S))) in *.
  assert (Hag : forall E'', agree (s_next (wv_post S len 1073741824)) E' E'' -> lden E'' l0 = lden E' l0 /\ E'' (s_next S) = E' (s_next S)).
  { intros E'' Ha''. rewrite Hnx in Ha''. split; [|symmetry; apply Ha''; lia].
    exact (lden_agree_wf _ E' E'' l0 (lwf_mono (s_next S) (Pos.succ (s_next S)) l0 ltac:(lia) Hwl0) Ha''). }
  pose proof (u_range E' l0) as Rl0.
  destruct (Z_le_gt_dec kz (bv_unsigned (lden E' l0))) as [Hle|Hgt].
  - apply (IH (wv_lo S len l0) M FS sh a f1 H1 model0 mem0 E' ms' m'').
    + unfold wv_lo. apply den_addfact; [exact Hd|]. intros E'' Ha''. destruct (Hag E'' Ha'') as [A1 A2]. cbn [fact_ok].
      rewrite lden_lsub, lden_lvar, A1, A2, bv_sub_unsigned. fold kz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
      rewrite Z.mod_small by (unfold two64; lia). lia.
    + exact (INV_same mem0 E' _ _ M FS model0 Hi (Hn _)).
    + exact (HAX_same E' _ _ M a mem0 HX (Hn _)).
    + unfold wv_lo. rewrite Hn. exact Hw.
    + intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin Hd'' Hi'' Hx'' Hw'' Ha''. unfold wv_lo in Ha''. rewrite Hn in Ha''.
      exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (in_or_app _ _ _ (or_introl Hin)) Hd'' Hi'' Hx'' Hw'' Ha'').
  - apply (IH (wv_hi S len l0) M FS sh a f2 H2 model0 mem0 E' ms' m'').
    + unfold wv_hi. apply den_addfact; [exact Hd|]. intros E'' Ha''. destruct (Hag E'' Ha'') as [A1 A2]. cbn [fact_ok].
      rewrite lden_lsub, lden_lvar, lden_laddc, A1, A2, bv_sub_unsigned. fold kz. rewrite Z_to_bv_unsigned.
      unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
      rewrite (Z.mod_small (bv_unsigned (lden E' l0) + 1)) by (unfold two64; lia).
      rewrite Z.mod_small by (unfold two64; lia). lia.
    + exact (INV_same mem0 E' _ _ M FS model0 Hi (Hn _)).
    + exact (HAX_same E' _ _ M a mem0 HX (Hn _)).
    + unfold wv_hi. rewrite Hn. exact Hw.
    + intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin Hd'' Hi'' Hx'' Hw'' Ha''. unfold wv_hi in Ha''. rewrite Hn in Ha''.
      exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (in_or_app _ _ _ (or_intror Hin)) Hd'' Hi'' Hx'' Hw'' Ha'').
Qed.

#[using="Hwx Himg Hect Hp4 awf_mono HA_agree HA_copy"] Lemma Pm_writevC : forall F0 F1 k, Pm k -> Pm (MWritevC F0 F1 k).
Proof. LiaFast.lf_pins (fun (Hwx Himg Hect Hp4 awf_mono HA_agree HA_copy : LiaFast.U) => LiaFast.u0).
  intros F0 F1 k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct sh as [po kc|sa sb|lq loq hiq sa sb|lq jq sa sb]; try discriminate. destruct po as [|p rest]; try discriminate.
  destruct (is_ecall t (s_pc S)) eqn:Hx; [|discriminate]. apply is_ecall_ok in Hx.
  destruct (writevC_ok img S M (acopy a) F0 F1 p) as [len|] eqn:Hok; [|discriminate].
  destruct p as [ch [bs|pre j lj suf] off]; [unfold writevC_ok in Hok; discriminate Hok|]. unfold writevC_ok in Hok.
  set (iov := argl S 1) in *. set (recs := acopy a) in *.
  set (P := Z.of_nat (length pre)) in *. set (Sl := Z.of_nat (length suf)) in *.
  destruct (a7c S) as [c7|] eqn:H7; [|discriminate]. destruct (arg S 0) as [c0|] eqn:H0; [|discriminate].
  destruct (arg S 2) as [c2|] eqn:H2; [|discriminate].
  destruct (load_at img (s_facts S) (s_rgs S) iov SZ8 false) as [[b0|]|] eqn:Hlb0; try discriminate.
  destruct (load_at img (s_facts S) (s_rgs S) (laddc iov 8) SZ8 false) as [[l0|]|] eqn:Hll0; try discriminate.
  match type of Hok with ((if ?c then ?x else None) = Some _) =>
    assert (Hc1 : c = true) by (destruct c; [reflexivity | discriminate Hok]); rewrite Hc1 in Hok end.
  repeat match type of Hc1 with ((_ && _)%bool = true) => apply andb_prop in Hc1 as [Hc1 ?Hq] end.
  rename Hc1 into H66. apply Z.eqb_eq in H66. subst c7.
  match goal with Hq' : wsrc_ok img S M recs pre suf j lj F0 = true |- _ => rename Hq' into Hws0 end.
  match goal with Hq' : len_rec recs lj j = true |- _ => rename Hq' into Hlr end.
  match goal with Hq' : iov_src_ok _ recs P Sl lj b0 l0 off F0 = true |- _ => rename Hq' into Hio0 end.
  repeat match goal with
         | Hx' : Z.eqb c0 ch = true |- _ => apply Z.eqb_eq in Hx'
         | Hx' : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hx'
         end.
  subst c0.
  match goal with Hx' : snd (irange (s_facts S) lj) < 2 ^ 62 |- _ => rename Hx' into Hlhi end.
  assert (Hch : ch = 1 \/ ch = 2).
  { match goal with Hq' : (Z.eqb ch 1 || Z.eqb ch 2)%bool = true |- _ => apply orb_prop in Hq' as [Hq'|Hq']; apply Z.eqb_eq in Hq'; auto end. }
  assert (Hwoff : lwf (s_next S) off = true) by assumption.
  assert (Hwiov : lwf (s_next S) iov = true) by assumption.
  assert (Hwlj : lwf (s_next S) lj = true) by assumption.
  cbn [shp_wf forallb pend_wf pd_src pd_off] in Hw. apply andb_prop in Hw as [_ Hwr].
  pose proof Hi as Hi0. destruct Hi0 as (Hpv & Hfsw & Hfr & Hm0 & Hlen & Hlk & Hfs0 & Hfds & Hch1 & Hch2 & Hdv).
  destruct HX as [Haw HHA]. pose proof (HA_copy E M a mem0 HHA) as Hrec. fold recs in Hrec.
  pose proof (len_rec_sound E mem0 recs lj j Hrec Hlr) as HLj.
  assert (HPl : P < 2 ^ 20) by (unfold P in *; lia).
  assert (HSl : Sl < 2 ^ 20) by (unfold Sl in *; lia).
  apply (den_ecall segs cfg LIMIT model0 mem0 Hwx t E S M ms model _ Hect Hx Hd). intros model1 Hd1.
  set (H1 := Hof E M model1).
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd1)) as (_ & _ & _ & _ & HG0 & _ & HF0 & _).
  pose proof (dn_hoff _ _ _ _ _ _ _ _ _ Hd1) as Hhoff. fold H1 in HG0, Hhoff. cbn [restrict ms_mem] in HG0.
  set (msg := msgb sarg pre suf j).
  assert (Hsrc : src_bytes E (SArgs pre j lj suf) = msg) by exact (src_bytes_args E pre j lj suf HLj).
  assert (Hmsgl : Z.of_nat (length msg) < 2 ^ 63).
  { unfold msg. rewrite length_msgb. pose proof (irange_sound E _ lj HF0) as Rlj. fold (uE E lj) in Rlj.
    rewrite !Nat2Z.inj_add, <- HLj. fold P Sl. lia. }
  pose proof (irange_sound E _ iov HF0) as Ri.
  (* [comment removed for export] *)
  destruct (iov_src_sound segs LIMIT model0 mem0 img Himg sarg E S M ms model1 recs pre suf j lj b0 l0 off F0 Hd1 Hrec HLj Hlhi HPl HSl Hws0 Hio0)
    as (B0a & B0b & B0c & Hbuf0).
  fold msg H1 in Hbuf0. fold msg in B0a.
  destruct (load_at_sound segs E img _ _ iov SZ8 false _ _ Himg HG0 HF0 Hlb0) as (bs8a & Hra & Hva). specialize (Hva _ eq_refl).
  destruct (load_at_sound segs E img _ _ (laddc iov 8) SZ8 false _ _ Himg HG0 HF0 Hll0) as (bs8b & Hrb & Hvb). specialize (Hvb _ eq_refl).
  rewrite ov_rdn in Hra, Hrb. cbn [nbytes] in Hra, Hrb.
  destruct (rdn_restrict_vis segs mem0 H1 (ms_mem ms) 8 _ bs8a Hhoff Hra) as [Hra' Hava].
  destruct (rdn_restrict_vis segs mem0 H1 (ms_mem ms) 8 _ bs8b Hhoff Hrb) as [Hrb' Havb].
  assert (Hl8a : length bs8a = 8%nat) by exact (rdn_length _ _ _ _ _ Hra').
  assert (Hl8b : length bs8b = 8%nat) by exact (rdn_length _ _ _ _ _ Hrb').
  assert (Hiov8 : lden E (laddc iov 8) = Z_to_bv 64 (bv_unsigned (lden E iov) + 8)) by (rewrite lden_laddc; f_equal; lia).
  set (bs0 := firstn (Z.to_nat (uE E l0)) (skipn (Z.to_nat (uE E off)) msg)) in *.
  destruct (rdn_restrict_vis segs mem0 H1 (ms_mem ms) _ _ _ Hhoff Hbuf0) as [Hbuf0' Havm0].
  pose proof (uE_rng E off) as Roff. pose proof (uE_rng E l0) as Rl0.
  assert (Hlen0 : length bs0 = Z.to_nat (uE E l0)).
  { unfold bs0. rewrite length_firstn, length_skipn. apply Nat.min_l. apply Nat2Z.inj_le. rewrite Nat2Z.inj_sub by lia. rewrite !Z2Nat.id by lia. lia. }
  (* [comment removed for export] *)
  set (REST := concat (List.map (pend_evs E) rest)).
  assert (Hpe : pend_evs E (PD ch (SArgs pre j lj suf) off) = List.map (WriteEv (Z_to_bv 64 ch)) (skipn (Z.to_nat (uE E off)) msg)).
  { unfold pend_evs. cbn [pd_ch pd_src pd_off]. rewrite Hsrc. reflexivity. }
  destruct (Z.eqb c2 1) eqn:Hc21.
  - (* [comment removed for export] *)
    apply Z.eqb_eq in Hc21. subst c2.
    match type of Hok with ((if ?c then ?x else None) = Some _) =>
      assert (Hc2 : c = true) by (destruct c; [reflexivity | discriminate Hok]); rewrite Hc2 in Hok end.
    injection Hok as <-.
    repeat match type of Hc2 with ((_ && _)%bool = true) => apply andb_prop in Hc2 as [Hc2 ?Hq] end.
    repeat match goal with Hx' : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx' end.
    pose proof (irange_sound E _ l0 HF0) as Rl0'. fold (uE E l0) in Rl0'.
    set (K := t_emit (List.map (WriteEv (Z_to_bv 64 ch)) (skipn (Z.to_nat (uE E off) + length bs0) msg) ++ REST) (t_exit (Z_to_bv 64 kc) fs0)).
    assert (HK0 : K []) by apply t_emit_has_nil.
    eapply rzc_conseq; [|cbn [shp_den List.map concat]; rewrite Hpe; fold REST;
      rewrite (skipn_split2 msg (Z.to_nat (uE E off)) (length bs0)); rewrite Hlen0 at 1; fold bs0;
      rewrite map_app, <- app_assoc; apply t_eq_sym; apply t_emit_app].
    fold K.
    assert (Hfch : fd_lookup (m_fds model0) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch))) by (destruct Hch as [->| ->]; assumption).
    assert (Hwl0 : lwf (s_next S) l0 = true) by assumption.
    assert (Hl1 : (1 <= length bs0)%nat) by (rewrite Hlen0; lia).
    apply (den_writev segs cfg LIMIT mem0 model0 E S M ms model1 K ch b0 l0 bs0 1073741824 Hd1 H7 H0 H2 Hch Hfch
             ltac:(fold iov; rewrite Hra'; f_equal; rewrite Hva; symmetry; exact (ld8_bytes _ Hl8a))
             ltac:(fold iov; replace (bv_unsigned (lden E iov) + 16 - 8) with (bv_unsigned (lden E iov) + 8) by (clear; lia); rewrite <- Hiov8; rewrite Hrb'; f_equal; rewrite Hvb; symmetry; exact (ld8_bytes _ Hl8b))
             ltac:(rewrite Hlen0; exact Hbuf0')
             ltac:(rewrite Hlen0, Z2Nat.id by (first [solve [clear - Rl0; lia] | lia]); reflexivity) Hl1 ltac:(rewrite Hlen0, Z2Nat.id by (first [solve [clear - Rl0; lia] | lia]); first [solve [clear - Rl0' Hq6; lia] | lia]) ltac:(clear; lia)
             ltac:(fold iov; first [solve [clear - Ri Hq3; lia] | solve [clear - Ri Hq4; lia] | (unfold uE in *; lia)]) ltac:(rewrite Hlen0, Z2Nat.id by (first [solve [clear - Rl0; lia] | lia]); first [solve [clear - B0c; unfold uE in *; lia] | (unfold uE in *; lia)])).
    + intros kk Hkk. fold iov H1. destruct (Nat.lt_ge_cases kk 8) as [Hk8|Hk8]; [exact (Hava kk Hk8)|].
      replace (woff (lden E iov) kk) with (woff (lden E (laddc iov 8)) (kk - 8)); [apply Havb; first [solve [clear - Hk8 Hk16; lia] | solve [clear - Hk8 Hkk; lia] | lia]|].
      unfold woff. rewrite lden_laddc. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. first [solve [clear - Hk8; lia] | solve [clear - Hk16; lia] | solve [clear - Hk24; lia] | lia].
    + fold H1. rewrite Hlen0. exact Havm0.
    + exact Hwl0.
    + exact HK0.
    + intros E' ms' m'' Hd' Ha' Hkr.
      set (kv := s_next S) in *.
      set (kz := bv_unsigned (E' kv)) in *.
      assert (Hn' : s_next (wv_post S l0 1073741824) = Pos.succ (s_next S)) by reflexivity.
      assert (Hoff' : lden E' off = lden E off) by exact (lden_agree_wf _ E E' off Hwoff Ha').
      assert (Hlj' : lden E' lj = lden E lj) by exact (lden_agree_wf _ E E' lj Hwlj Ha').
      assert (Hi' : INV mem0 E' (wv_post S l0 1073741824) M FS model0).
      { apply (INV_agree mem0 E E' S _ M M FS model0 Hi Ha' ltac:(rewrite Hn'; lia) eq_refl (dn_wf _ _ _ _ _ _ _ _ _ Hd)). }
      assert (Hw' : shp_wf (s_next (wv_post S l0 1073741824)) (wv_shp (ShEmit (PD ch (SArgs pre j lj suf) off :: rest) kc) S) = true).
      { rewrite Hn'. cbn [wv_shp shp_wf forallb pend_wf pd_src pd_off]. apply andb_true_intro. split; [apply andb_true_intro; split|].
        - apply lwf_ladd; [exact (lwf_mono (s_next S) (Pos.succ (s_next S)) off ltac:(lia) Hwoff)|]. unfold lwf, lvar. cbn. rewrite andb_true_r. apply Pos.ltb_lt. lia.
        - exact (lwf_mono (s_next S) (Pos.succ (s_next S)) lj ltac:(lia) Hwlj).
        - exact (shp_wf_mono (s_next S) (Pos.succ (s_next S)) (ShEmit rest kc) ltac:(lia) Hwr). }
      assert (HOL : forall l0', wv_l0 img S F1 = Some l0' -> lwf (s_next S) l0' = true /\ bv_unsigned (lden E' l0') <= 1073741824 /\
                                                          1 <= bv_unsigned (E' (s_next S)) <= 1073741824).
      { intros l0' Hs. unfold wv_l0 in Hs. destruct F1; try discriminate Hs; rewrite H2 in Hs; discriminate Hs. }
      eapply rzc_conseq.
      * apply (Pm_wvpost k IH S M FS _ a l0 (wv_l0 img S F1) finals Hck model0 mem0 E' ms' m'' Hd' Hi'
                 (HAX_step E E' S (wv_post S l0 1073741824) M a mem0 (conj Haw HHA) (dn_wf _ _ _ _ _ _ _ _ _ Hd) Ha' ltac:(rewrite Hn'; lia)) Hw' HOL).
        intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' Hx'' Hw'' Ha''.
        exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' Hx'' Hw''
                 (agree_trans _ E E' E'' Ha' (agree_mono (s_next S) (s_next (wv_post S l0 1073741824)) E' E'' ltac:(rewrite Hn'; lia) Ha''))).
      * cbn [wv_shp shp_den List.map concat].
        assert (HR : concat (List.map (pend_evs E') rest) = REST).
        { unfold REST. f_equal. apply map_ext_in. intros q Hqin.
          rewrite forallb_forall in Hwr. exact (pend_evs_agree _ E E' q (Hwr q Hqin) Ha'). }
        rewrite HR. unfold K.
        assert (Hpk : pend_evs E' (PD ch (SArgs pre j lj suf) (ladd off (lvar kv))) =
                      List.map (WriteEv (Z_to_bv 64 ch)) (skipn (Z.to_nat kz) bs0) ++ List.map (WriteEv (Z_to_bv 64 ch)) (skipn (Z.to_nat (uE E off) + length bs0) msg)).
        { unfold pend_evs. cbn [pd_ch pd_src pd_off]. rewrite <- map_app. f_equal.
          assert (HsE : src_bytes E' (SArgs pre j lj suf) = msg).
          { rewrite src_bytes_args; [reflexivity|]. unfold uE. rewrite Hlj'. exact HLj. }
          rewrite HsE. unfold uE at 1. rewrite lden_ladd, lden_lvar, Hoff'. rewrite bv_add_unsigned. fold (uE E off) kz. unfold bv_wrap.
          rewrite Z.mod_small by (change (bv_modulus 64) with two64; rewrite Hlen0 in Hkr; rewrite Z2Nat.id in Hkr by lia; pose proof (bv_unsigned_in_range _ (E' kv)) as Rkz; unfold two64 in *; lia).
          rewrite Hlen0 in Hkr |- *. rewrite Z2Nat.id in Hkr by lia. unfold bs0. rewrite skipn_firstn_comm, skipn_skipn.
          rewrite (skipn_split2 msg (Z.to_nat (uE E off + kz)) (Z.to_nat (uE E l0) - Z.to_nat kz)).
          f_equal; [f_equal; f_equal; first [solve [clear - Roff Hkr; lia] | lia] | f_equal; first [solve [clear - Roff Rl0 Hkr; lia] | solve [clear - Roff Rl0 Rl1 Hkr; lia] | lia]].   (* [comment removed for export] *) }
        fold kv. rewrite Hpk, <- app_assoc. apply t_emit_app.
  - (* [comment removed for export] *)
    destruct (Z.eqb c2 2) eqn:Hc22; [|discriminate]. apply Z.eqb_eq in Hc22. subst c2.
    destruct (load_at img (s_facts S) (s_rgs S) (laddc iov 16) SZ8 false) as [[b1|]|] eqn:Hlb1; try discriminate.
    destruct (load_at img (s_facts S) (s_rgs S) (laddc iov 24) SZ8 false) as [[l1|]|] eqn:Hll1; try discriminate.
    match type of Hok with ((if ?c then ?x else None) = Some _) =>
      assert (Hc2 : c = true) by (destruct c; [reflexivity | discriminate Hok]); rewrite Hc2 in Hok end.
    injection Hok as <-.
    repeat match type of Hc2 with ((_ && _)%bool = true) => apply andb_prop in Hc2 as [Hc2 ?Hq] end.
    rename Hc2 into Hws1.
    match goal with Hq' : iov_src_ok _ recs P Sl lj b1 l1 (ladd off l0) F1 = true |- _ => rename Hq' into Hio1 end.
    repeat match goal with Hx' : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx' end.
    assert (Hwl0 : lwf (s_next S) l0 = true) by assumption.
    assert (Hwl1 : lwf (s_next S) l1 = true) by assumption.
    pose proof (irange_sound E _ (ladd l0 l1) HF0) as Rl01. fold (uE E (ladd l0 l1)) in Rl01.
    destruct (iov_src_sound segs LIMIT model0 mem0 img Himg sarg E S M ms model1 recs pre suf j lj b1 l1 (ladd off l0) F1 Hd1 Hrec HLj Hlhi HPl HSl Hws1 Hio1)
      as (B1a & B1b & B1c & Hbuf1).
    fold msg H1 in Hbuf1. fold msg in B1a.
    pose proof (uE_rng E l1) as Rl1.
    assert (Hol : uE E (ladd off l0) = uE E off + uE E l0).
    { unfold uE at 1. rewrite lden_ladd, bv_add_unsigned. fold (uE E off) (uE E l0). unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. unfold two64 in *. lia. }
    rewrite Hol in B1a, Hbuf1.
    assert (Hl01 : uE E (ladd l0 l1) = uE E l0 + uE E l1).
    { unfold uE at 1. rewrite lden_ladd, bv_add_unsigned. fold (uE E l0) (uE E l1). unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. unfold two64 in *. lia. }
    destruct (load_at_sound segs E img _ _ (laddc iov 16) SZ8 false _ _ Himg HG0 HF0 Hlb1) as (bs8c & Hrc & Hvc). specialize (Hvc _ eq_refl).
    destruct (load_at_sound segs E img _ _ (laddc iov 24) SZ8 false _ _ Himg HG0 HF0 Hll1) as (bs8d & Hrd & Hvd). specialize (Hvd _ eq_refl).
    rewrite ov_rdn in Hrc, Hrd. cbn [nbytes] in Hrc, Hrd.
    destruct (rdn_restrict_vis segs mem0 H1 (ms_mem ms) 8 _ bs8c Hhoff Hrc) as [Hrc' Havc].
    destruct (rdn_restrict_vis segs mem0 H1 (ms_mem ms) 8 _ bs8d Hhoff Hrd) as [Hrd' Havd].
    assert (Hl8c : length bs8c = 8%nat) by exact (rdn_length _ _ _ _ _ Hrc').
    assert (Hl8d : length bs8d = 8%nat) by exact (rdn_length _ _ _ _ _ Hrd').
    assert (Hiov16 : lden E (laddc iov 16) = Z_to_bv 64 (bv_unsigned (lden E iov) + 16)) by (rewrite lden_laddc; f_equal; lia).
    assert (Hiov24 : lden E (laddc iov 24) = Z_to_bv 64 (bv_unsigned (lden E iov) + 24)) by (rewrite lden_laddc; f_equal; lia).
    set (bs1 := firstn (Z.to_nat (uE E l1)) (skipn (Z.to_nat (uE E off + uE E l0)) msg)) in *.
    destruct (rdn_restrict_vis segs mem0 H1 (ms_mem ms) _ _ _ Hhoff Hbuf1) as [Hbuf1' Havm1].
    assert (Hlen1 : length bs1 = Z.to_nat (uE E l1)).
    { unfold bs1. rewrite length_firstn, length_skipn. apply Nat.min_l. apply Nat2Z.inj_le. rewrite Nat2Z.inj_sub by lia. rewrite !Z2Nat.id by lia. lia. }
    set (bsT := bs0 ++ bs1).
    assert (HbsT : bsT = firstn (length bs0 + length bs1) (skipn (Z.to_nat (uE E off)) msg)).
    { rewrite Hlen0, Hlen1. unfold bsT, bs0, bs1. rewrite <- firstn_skipn_app2. f_equal. f_equal. f_equal. lia. }
    assert (HlT : length bsT = (length bs0 + length bs1)%nat) by (unfold bsT; apply length_app).
    set (K := t_emit (List.map (WriteEv (Z_to_bv 64 ch)) (skipn (Z.to_nat (uE E off) + length bsT) msg) ++ REST) (t_exit (Z_to_bv 64 kc) fs0)).
    assert (HK0 : K []) by apply t_emit_has_nil.
    eapply rzc_conseq; [|cbn [shp_den List.map concat]; rewrite Hpe; fold REST;
      rewrite (skipn_split2 msg (Z.to_nat (uE E off)) (length bsT)); rewrite HlT at 1; rewrite <- HbsT;
      rewrite map_app, <- app_assoc; apply t_eq_sym; apply t_emit_app].
    fold K.
    assert (Hfch : fd_lookup (m_fds model0) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch))) by (destruct Hch as [->| ->]; assumption).
    apply (den_writevG2 segs cfg LIMIT mem0 model0 E S M ms model1 K ch b0 l0 b1 l1 (ladd l0 l1) bs0 bs1 1073741824 Hd1 H7 H0 H2 Hch Hfch
             ltac:(fold iov; rewrite Hra'; f_equal; rewrite Hva; symmetry; exact (ld8_bytes _ Hl8a))
             ltac:(fold iov; rewrite <- Hiov8; rewrite Hrb'; f_equal; rewrite Hvb; symmetry; exact (ld8_bytes _ Hl8b))
             ltac:(fold iov; rewrite <- Hiov16; rewrite Hrc'; f_equal; rewrite Hvc; symmetry; exact (ld8_bytes _ Hl8c))
             ltac:(fold iov; rewrite <- Hiov24; rewrite Hrd'; f_equal; rewrite Hvd; symmetry; exact (ld8_bytes _ Hl8d))
             ltac:(rewrite Hlen0; exact Hbuf0') ltac:(rewrite Hlen1; exact Hbuf1')
             ltac:(rewrite Hlen0, Z2Nat.id by (first [solve [clear - Rl0; lia] | lia]); reflexivity) ltac:(rewrite Hlen1, Z2Nat.id by (first [solve [clear - Rl1; lia] | lia]); reflexivity)
             ltac:(rewrite Nat2Z.inj_add, Hlen0, Hlen1, !Z2Nat.id by (first [solve [clear - Rl0; lia] | solve [clear - Rl1; lia] | lia]); unfold uE in Hl01; exact Hl01)
             ltac:(rewrite Hlen0, Hlen1; first [solve [clear - Rl0 Rl1 Rl01 Hl01 Hc2; lia] | lia]) ltac:(rewrite Nat2Z.inj_add, Hlen0, Hlen1, !Z2Nat.id by (first [solve [clear - Rl0; lia] | solve [clear - Rl1; lia] | lia]); first [solve [clear - Rl01 Hl01 Hq6; lia] | solve [clear - Rl01 Hl01 Hq7; lia] | lia]) ltac:(clear; lia)
             ltac:(fold iov; first [solve [clear - Ri Hq3; lia] | solve [clear - Ri Hq4; lia] | (unfold uE in *; lia)])
             ltac:(rewrite Hlen0, Z2Nat.id by (first [solve [clear - Rl0; lia] | lia]); first [solve [clear - B0c; unfold uE in *; lia] | (unfold uE in *; lia)]) ltac:(rewrite Hlen1, Z2Nat.id by (first [solve [clear - Rl1; lia] | lia]); first [solve [clear - B1c; unfold uE in *; lia] | (unfold uE in *; lia)])).
    + intros kk Hkk. fold iov H1. destruct (Nat.lt_ge_cases kk 8) as [Hk8|Hk8]; [exact (Hava kk Hk8)|].
      destruct (Nat.lt_ge_cases kk 16) as [Hk16|Hk16].
      { replace (woff (lden E iov) kk) with (woff (lden E (laddc iov 8)) (kk - 8)); [apply Havb; first [solve [clear - Hk8 Hk16; lia] | solve [clear - Hk8 Hkk; lia] | lia]|].
        unfold woff. rewrite lden_laddc. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. first [solve [clear - Hk8; lia] | solve [clear - Hk16; lia] | solve [clear - Hk24; lia] | lia]. }
      destruct (Nat.lt_ge_cases kk 24) as [Hk24|Hk24].
      { replace (woff (lden E iov) kk) with (woff (lden E (laddc iov 16)) (kk - 16)); [apply Havc; first [solve [clear - Hk16 Hk24; lia] | lia]|].
        unfold woff. rewrite lden_laddc. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. first [solve [clear - Hk8; lia] | solve [clear - Hk16; lia] | solve [clear - Hk24; lia] | lia]. }
      { replace (woff (lden E iov) kk) with (woff (lden E (laddc iov 24)) (kk - 24)); [apply Havd; first [solve [clear - Hk24 Hkk; lia] | lia]|].
        unfold woff. rewrite lden_laddc. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. first [solve [clear - Hk8; lia] | solve [clear - Hk16; lia] | solve [clear - Hk24; lia] | lia]. }
    + fold H1. rewrite Hlen0. exact Havm0.
    + fold H1. rewrite Hlen1. exact Havm1.
    + apply lwf_ladd; assumption.
    + exact HK0.
    + intros E' ms' m'' Hd' Ha' Hkr. fold bsT in Hkr |- *.
      set (kv := s_next S) in *.
      set (kz := bv_unsigned (E' kv)) in *.
      assert (Hn' : s_next (wv_post S (ladd l0 l1) 1073741824) = Pos.succ (s_next S)) by reflexivity.
      assert (Hoff' : lden E' off = lden E off) by exact (lden_agree_wf _ E E' off Hwoff Ha').
      assert (Hlj' : lden E' lj = lden E lj) by exact (lden_agree_wf _ E E' lj Hwlj Ha').
      assert (Hi' : INV mem0 E' (wv_post S (ladd l0 l1) 1073741824) M FS model0).
      { apply (INV_agree mem0 E E' S _ M M FS model0 Hi Ha' ltac:(rewrite Hn'; lia) eq_refl (dn_wf _ _ _ _ _ _ _ _ _ Hd)). }
      assert (Hw' : shp_wf (s_next (wv_post S (ladd l0 l1) 1073741824)) (wv_shp (ShEmit (PD ch (SArgs pre j lj suf) off :: rest) kc) S) = true).
      { rewrite Hn'. cbn [wv_shp shp_wf forallb pend_wf pd_src pd_off]. apply andb_true_intro. split; [apply andb_true_intro; split|].
        - apply lwf_ladd; [exact (lwf_mono (s_next S) (Pos.succ (s_next S)) off ltac:(lia) Hwoff)|]. unfold lwf, lvar. cbn. rewrite andb_true_r. apply Pos.ltb_lt. lia.
        - exact (lwf_mono (s_next S) (Pos.succ (s_next S)) lj ltac:(lia) Hwlj).
        - exact (shp_wf_mono (s_next S) (Pos.succ (s_next S)) (ShEmit rest kc) ltac:(lia) Hwr). }
      assert (HOL : forall l0', wv_l0 img S F1 = Some l0' -> lwf (s_next S) l0' = true /\ bv_unsigned (lden E' l0') <= 1073741824 /\
                                                          1 <= bv_unsigned (E' (s_next S)) <= 1073741824).
      { intros l0' Hs. unfold wv_l0 in Hs. fold iov in Hs.
        assert (Hs' : Some l0 = Some l0') by (destruct F1; try discriminate Hs; rewrite H2 in Hs; cbn [Z.eqb Pos.eqb] in Hs; rewrite Hll0 in Hs; exact Hs).
        injection Hs' as <-. split; [exact Hwl0|]. rewrite (lden_agree_wf _ E E' l0 Hwl0 Ha'). fold (uE E l0). change (bv_unsigned (E' (s_next S))) with kz.
        rewrite Hlen0, Hlen1 in Hkr. rewrite Nat2Z.inj_add, !Z2Nat.id in Hkr by (first [solve [clear - Rl0; lia] | solve [clear - Rl1; lia] | lia]). unfold uE in *. lia. }
      eapply rzc_conseq.
      * apply (Pm_wvpost k IH S M FS _ a (ladd l0 l1) (wv_l0 img S F1) finals Hck model0 mem0 E' ms' m'' Hd' Hi'
                 (HAX_step E E' S (wv_post S (ladd l0 l1) 1073741824) M a mem0 (conj Haw HHA) (dn_wf _ _ _ _ _ _ _ _ _ Hd) Ha' ltac:(rewrite Hn'; lia)) Hw' HOL).
        intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' Hx'' Hw'' Ha''.
        exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' Hx'' Hw''
                 (agree_trans _ E E' E'' Ha' (agree_mono (s_next S) (s_next (wv_post S (ladd l0 l1) 1073741824)) E' E'' ltac:(rewrite Hn'; lia) Ha''))).
      * cbn [wv_shp shp_den List.map concat].
        assert (HR : concat (List.map (pend_evs E') rest) = REST).
        { unfold REST. f_equal. apply map_ext_in. intros q Hqin.
          rewrite forallb_forall in Hwr. exact (pend_evs_agree _ E E' q (Hwr q Hqin) Ha'). }
        rewrite HR. unfold K.
        assert (Hpk : pend_evs E' (PD ch (SArgs pre j lj suf) (ladd off (lvar kv))) =
                      List.map (WriteEv (Z_to_bv 64 ch)) (skipn (Z.to_nat kz) bsT) ++ List.map (WriteEv (Z_to_bv 64 ch)) (skipn (Z.to_nat (uE E off) + length bsT) msg)).
        { unfold pend_evs. cbn [pd_ch pd_src pd_off]. rewrite <- map_app. f_equal.
          assert (HsE : src_bytes E' (SArgs pre j lj suf) = msg).
          { rewrite src_bytes_args; [reflexivity|]. unfold uE. rewrite Hlj'. exact HLj. }
          rewrite HsE. unfold uE at 1. rewrite lden_ladd, lden_lvar, Hoff'. rewrite bv_add_unsigned. fold (uE E off) kz. unfold bv_wrap.
          rewrite Hlen0, Hlen1 in Hkr. rewrite Nat2Z.inj_add, !Z2Nat.id in Hkr by (first [solve [clear - Rl0; lia] | solve [clear - Rl1; lia] | lia]).
          rewrite Z.mod_small by (change (bv_modulus 64) with two64; pose proof (bv_unsigned_in_range _ (E' kv)) as Rkz; unfold two64 in *; lia).
          rewrite HlT, HbsT, skipn_firstn_comm, skipn_skipn.
          rewrite (skipn_split2 msg (Z.to_nat (uE E off + kz)) (length bs0 + length bs1 - Z.to_nat kz)).
          rewrite Hlen0, Hlen1. f_equal; [f_equal; f_equal; first [solve [clear - Roff Hkr; lia] | lia] | f_equal; first [solve [clear - Roff Rl0 Hkr; lia] | solve [clear - Roff Rl0 Rl1 Hkr; lia] | lia]].   (* [comment removed for export] *) }
        fold kv. rewrite Hpk, <- app_assoc. apply t_emit_app.
Qed.

#[using="Hwx Himg Hect Hp4 awf_mono HA_agree"] Lemma Pm_writevL : forall Pn F0 F1 k, Pm k -> Pm (MWritevL Pn F0 F1 k).
Proof. LiaFast.lf_pins (fun (Hwx Himg Hect Hp4 awf_mono HA_agree : LiaFast.U) => LiaFast.u0).
  intros Pn F0 F1 k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct sh as [po kc|sa sb|lq loq hiq sa sb|lq jq sa sb]; try discriminate. destruct po as [|p rest]; try discriminate.
  destruct (is_ecall t (s_pc S)) eqn:Hx; [|discriminate]. apply is_ecall_ok in Hx.
  destruct (writevL_ok img S M Pn F0 F1 p) as [len|] eqn:Hok; [|discriminate].
  destruct p as [ch [bs|pre0 j0 lj0 suf0] off]; [|unfold writevL_ok in Hok; discriminate Hok]. unfold writevL_ok, writevL_core in Hok.
  set (sarg0 := fun _ : nat => @nil byte).
  remember (firstn Pn bs) as pre eqn:Hpre. remember (skipn Pn bs) as suf eqn:Hsuf. remember O as j eqn:Hj. remember (lconst 0) as lj eqn:Hlj.
  set (iov := argl S 1) in *. remember (@nil srec) as recs eqn:Hrecs.
  set (P := Z.of_nat (length pre)) in *. set (Sl := Z.of_nat (length suf)) in *.
  destruct (a7c S) as [c7|] eqn:H7; [|discriminate]. destruct (arg S 0) as [c0|] eqn:H0; [|discriminate].
  destruct (arg S 2) as [c2|] eqn:H2; [|discriminate].
  destruct (load_at img (s_facts S) (s_rgs S) iov SZ8 false) as [[b0|]|] eqn:Hlb0; try discriminate.
  destruct (load_at img (s_facts S) (s_rgs S) (laddc iov 8) SZ8 false) as [[l0|]|] eqn:Hll0; try discriminate.
  match type of Hok with ((if ?c then ?x else None) = Some _) =>
    assert (Hc1 : c = true) by (destruct c; [reflexivity | discriminate Hok]); rewrite Hc1 in Hok end.
  repeat match type of Hc1 with ((_ && _)%bool = true) => apply andb_prop in Hc1 as [Hc1 ?Hq] end.
  rename Hc1 into H66. apply Z.eqb_eq in H66. subst c7.
  match goal with Hq' : wsrc_ok img S M recs pre suf j lj F0 = true |- _ => rename Hq' into Hws0 end.
  match goal with Hq' : iov_src_ok _ recs P Sl lj b0 l0 off F0 = true |- _ => rename Hq' into Hio0 end.
  repeat match goal with
         | Hx' : Z.eqb c0 ch = true |- _ => apply Z.eqb_eq in Hx'
         | Hx' : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hx'
         end.
  subst c0.
  match goal with Hx' : snd (irange (s_facts S) lj) < 2 ^ 62 |- _ => rename Hx' into Hlhi end.
  assert (Hch : ch = 1 \/ ch = 2).
  { match goal with Hq' : (Z.eqb ch 1 || Z.eqb ch 2)%bool = true |- _ => apply orb_prop in Hq' as [Hq'|Hq']; apply Z.eqb_eq in Hq'; auto end. }
  assert (Hwoff : lwf (s_next S) off = true) by assumption.
  assert (Hwiov : lwf (s_next S) iov = true) by assumption.
  assert (Hwlj : lwf (s_next S) lj = true) by assumption.
  cbn [shp_wf forallb pend_wf pd_src pd_off] in Hw. apply andb_prop in Hw as [_ Hwr].
  pose proof Hi as Hi0. destruct Hi0 as (Hpv & Hfsw & Hfr & Hm0 & Hlen & Hlk & Hfs0 & Hfds & Hch1 & Hch2 & Hdv).
  destruct HX as [Haw HHA]. assert (Hrec : Forall (sbytes_ok sarg0 E mem0) recs) by (rewrite Hrecs; constructor).
  assert (HLj : uE E lj = Z.of_nat (length (sarg0 j))) by (rewrite Hlj; unfold uE; rewrite lden_lconst; reflexivity).
  assert (HPl : P < 2 ^ 20) by (unfold P in *; lia).
  assert (HSl : Sl < 2 ^ 20) by (unfold Sl in *; lia).
  apply (den_ecall segs cfg LIMIT model0 mem0 Hwx t E S M ms model _ Hect Hx Hd). intros model1 Hd1.
  set (H1 := Hof E M model1).
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd1)) as (_ & _ & _ & _ & HG0 & _ & HF0 & _).
  pose proof (dn_hoff _ _ _ _ _ _ _ _ _ Hd1) as Hhoff. fold H1 in HG0, Hhoff. cbn [restrict ms_mem] in HG0.
  set (msg := msgb sarg0 pre suf j).
  assert (Hsrc : forall E0, src_bytes E0 (SLit bs) = msg) by (intros E0; unfold msg; rewrite Hpre, Hsuf, Hj; exact (src_bytes_lit E0 Pn bs)).
  assert (Hmsgl : Z.of_nat (length msg) < 2 ^ 63).
  { unfold msg. rewrite length_msgb. pose proof (irange_sound E _ lj HF0) as Rlj. fold (uE E lj) in Rlj.
    rewrite !Nat2Z.inj_add, <- HLj. fold P Sl. lia. }
  pose proof (irange_sound E _ iov HF0) as Ri.
  (* [comment removed for export] *)
  destruct (iov_src_sound segs LIMIT model0 mem0 img Himg sarg0 E S M ms model1 recs pre suf j lj b0 l0 off F0 Hd1 Hrec HLj Hlhi HPl HSl Hws0 Hio0)
    as (B0a & B0b & B0c & Hbuf0).
  fold msg H1 in Hbuf0. fold msg in B0a.
  destruct (load_at_sound segs E img _ _ iov SZ8 false _ _ Himg HG0 HF0 Hlb0) as (bs8a & Hra & Hva). specialize (Hva _ eq_refl).
  destruct (load_at_sound segs E img _ _ (laddc iov 8) SZ8 false _ _ Himg HG0 HF0 Hll0) as (bs8b & Hrb & Hvb). specialize (Hvb _ eq_refl).
  rewrite ov_rdn in Hra, Hrb. cbn [nbytes] in Hra, Hrb.
  destruct (rdn_restrict_vis segs mem0 H1 (ms_mem ms) 8 _ bs8a Hhoff Hra) as [Hra' Hava].
  destruct (rdn_restrict_vis segs mem0 H1 (ms_mem ms) 8 _ bs8b Hhoff Hrb) as [Hrb' Havb].
  assert (Hl8a : length bs8a = 8%nat) by exact (rdn_length _ _ _ _ _ Hra').
  assert (Hl8b : length bs8b = 8%nat) by exact (rdn_length _ _ _ _ _ Hrb').
  assert (Hiov8 : lden E (laddc iov 8) = Z_to_bv 64 (bv_unsigned (lden E iov) + 8)) by (rewrite lden_laddc; f_equal; lia).
  set (bs0 := firstn (Z.to_nat (uE E l0)) (skipn (Z.to_nat (uE E off)) msg)) in *.
  destruct (rdn_restrict_vis segs mem0 H1 (ms_mem ms) _ _ _ Hhoff Hbuf0) as [Hbuf0' Havm0].
  pose proof (uE_rng E off) as Roff. pose proof (uE_rng E l0) as Rl0.
  assert (Hlen0 : length bs0 = Z.to_nat (uE E l0)).
  { unfold bs0. rewrite length_firstn, length_skipn. apply Nat.min_l. apply Nat2Z.inj_le. rewrite Nat2Z.inj_sub by lia. rewrite !Z2Nat.id by lia. lia. }
  (* [comment removed for export] *)
  set (REST := concat (List.map (pend_evs E) rest)).
  assert (Hpe : pend_evs E (PD ch (SLit bs) off) = List.map (WriteEv (Z_to_bv 64 ch)) (skipn (Z.to_nat (uE E off)) msg)).
  { unfold pend_evs. cbn [pd_ch pd_src pd_off]. rewrite (Hsrc E). reflexivity. }
  destruct (Z.eqb c2 1) eqn:Hc21.
  - (* [comment removed for export] *)
    apply Z.eqb_eq in Hc21. subst c2.
    match type of Hok with ((if ?c then ?x else None) = Some _) =>
      assert (Hc2 : c = true) by (destruct c; [reflexivity | discriminate Hok]); rewrite Hc2 in Hok end.
    injection Hok as <-.
    repeat match type of Hc2 with ((_ && _)%bool = true) => apply andb_prop in Hc2 as [Hc2 ?Hq] end.
    repeat match goal with Hx' : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx' end.
    pose proof (irange_sound E _ l0 HF0) as Rl0'. fold (uE E l0) in Rl0'.
    set (K := t_emit (List.map (WriteEv (Z_to_bv 64 ch)) (skipn (Z.to_nat (uE E off) + length bs0) msg) ++ REST) (t_exit (Z_to_bv 64 kc) fs0)).
    assert (HK0 : K []) by apply t_emit_has_nil.
    eapply rzc_conseq; [|cbn [shp_den List.map concat]; rewrite Hpe; fold REST;
      rewrite (skipn_split2 msg (Z.to_nat (uE E off)) (length bs0)); rewrite Hlen0 at 1; fold bs0;
      rewrite map_app, <- app_assoc; apply t_eq_sym; apply t_emit_app].
    fold K.
    assert (Hfch : fd_lookup (m_fds model0) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch))) by (destruct Hch as [->| ->]; assumption).
    assert (Hwl0 : lwf (s_next S) l0 = true) by assumption.
    assert (Hl1 : (1 <= length bs0)%nat) by (rewrite Hlen0; lia).
    apply (den_writev segs cfg LIMIT mem0 model0 E S M ms model1 K ch b0 l0 bs0 1073741824 Hd1 H7 H0 H2 Hch Hfch
             ltac:(fold iov; rewrite Hra'; f_equal; rewrite Hva; symmetry; exact (ld8_bytes _ Hl8a))
             ltac:(fold iov; replace (bv_unsigned (lden E iov) + 16 - 8) with (bv_unsigned (lden E iov) + 8) by (clear; lia); rewrite <- Hiov8; rewrite Hrb'; f_equal; rewrite Hvb; symmetry; exact (ld8_bytes _ Hl8b))
             ltac:(rewrite Hlen0; exact Hbuf0')
             ltac:(rewrite Hlen0, Z2Nat.id by (first [solve [clear - Rl0; lia] | lia]); reflexivity) Hl1 ltac:(rewrite Hlen0, Z2Nat.id by (first [solve [clear - Rl0; lia] | lia]); first [solve [clear - Rl0' Hq6; lia] | lia]) ltac:(clear; lia)
             ltac:(fold iov; first [solve [clear - Ri Hq3; lia] | solve [clear - Ri Hq4; lia] | (unfold uE in *; lia)]) ltac:(rewrite Hlen0, Z2Nat.id by (first [solve [clear - Rl0; lia] | lia]); first [solve [clear - B0c; unfold uE in *; lia] | (unfold uE in *; lia)])).
    + intros kk Hkk. fold iov H1. destruct (Nat.lt_ge_cases kk 8) as [Hk8|Hk8]; [exact (Hava kk Hk8)|].
      replace (woff (lden E iov) kk) with (woff (lden E (laddc iov 8)) (kk - 8)); [apply Havb; first [solve [clear - Hk8 Hk16; lia] | solve [clear - Hk8 Hkk; lia] | lia]|].
      unfold woff. rewrite lden_laddc. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. first [solve [clear - Hk8; lia] | solve [clear - Hk16; lia] | solve [clear - Hk24; lia] | lia].
    + fold H1. rewrite Hlen0. exact Havm0.
    + exact Hwl0.
    + exact HK0.
    + intros E' ms' m'' Hd' Ha' Hkr.
      set (kv := s_next S) in *.
      set (kz := bv_unsigned (E' kv)) in *.
      assert (Hn' : s_next (wv_post S l0 1073741824) = Pos.succ (s_next S)) by reflexivity.
      assert (Hoff' : lden E' off = lden E off) by exact (lden_agree_wf _ E E' off Hwoff Ha').
      assert (Hlj' : lden E' lj = lden E lj) by exact (lden_agree_wf _ E E' lj Hwlj Ha').
      assert (Hi' : INV mem0 E' (wv_post S l0 1073741824) M FS model0).
      { apply (INV_agree mem0 E E' S _ M M FS model0 Hi Ha' ltac:(rewrite Hn'; lia) eq_refl (dn_wf _ _ _ _ _ _ _ _ _ Hd)). }
      assert (Hw' : shp_wf (s_next (wv_post S l0 1073741824)) (wv_shp (ShEmit (PD ch (SLit bs) off :: rest) kc) S) = true).
      { rewrite Hn'. cbn [wv_shp shp_wf forallb pend_wf pd_src pd_off]. apply andb_true_intro. split.
        - apply lwf_ladd; [exact (lwf_mono (s_next S) (Pos.succ (s_next S)) off ltac:(lia) Hwoff)|]. unfold lwf, lvar. cbn. rewrite andb_true_r. apply Pos.ltb_lt. lia.
        - exact (shp_wf_mono (s_next S) (Pos.succ (s_next S)) (ShEmit rest kc) ltac:(lia) Hwr). }
      assert (HOL : forall l0', wv_l0 img S F1 = Some l0' -> lwf (s_next S) l0' = true /\ bv_unsigned (lden E' l0') <= 1073741824 /\
                                                          1 <= bv_unsigned (E' (s_next S)) <= 1073741824).
      { intros l0' Hs. unfold wv_l0 in Hs. destruct F1; try discriminate Hs; rewrite H2 in Hs; discriminate Hs. }
      eapply rzc_conseq.
      * apply (Pm_wvpost k IH S M FS _ a l0 (wv_l0 img S F1) finals Hck model0 mem0 E' ms' m'' Hd' Hi'
                 (HAX_step E E' S (wv_post S l0 1073741824) M a mem0 (conj Haw HHA) (dn_wf _ _ _ _ _ _ _ _ _ Hd) Ha' ltac:(rewrite Hn'; lia)) Hw' HOL).
        intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' Hx'' Hw'' Ha''.
        exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' Hx'' Hw''
                 (agree_trans _ E E' E'' Ha' (agree_mono (s_next S) (s_next (wv_post S l0 1073741824)) E' E'' ltac:(rewrite Hn'; lia) Ha''))).
      * cbn [wv_shp shp_den List.map concat].
        assert (HR : concat (List.map (pend_evs E') rest) = REST).
        { unfold REST. f_equal. apply map_ext_in. intros q Hqin.
          rewrite forallb_forall in Hwr. exact (pend_evs_agree _ E E' q (Hwr q Hqin) Ha'). }
        rewrite HR. unfold K.
        assert (Hpk : pend_evs E' (PD ch (SLit bs) (ladd off (lvar kv))) =
                      List.map (WriteEv (Z_to_bv 64 ch)) (skipn (Z.to_nat kz) bs0) ++ List.map (WriteEv (Z_to_bv 64 ch)) (skipn (Z.to_nat (uE E off) + length bs0) msg)).
        { unfold pend_evs. cbn [pd_ch pd_src pd_off]. rewrite <- map_app. f_equal.
          assert (HsE : src_bytes E' (SLit bs) = msg) by exact (Hsrc E').
          rewrite HsE. unfold uE at 1. rewrite lden_ladd, lden_lvar, Hoff'. rewrite bv_add_unsigned. fold (uE E off) kz. unfold bv_wrap.
          rewrite Z.mod_small by (change (bv_modulus 64) with two64; rewrite Hlen0 in Hkr; rewrite Z2Nat.id in Hkr by lia; pose proof (bv_unsigned_in_range _ (E' kv)) as Rkz; unfold two64 in *; lia).
          rewrite Hlen0 in Hkr |- *. rewrite Z2Nat.id in Hkr by lia. unfold bs0. rewrite skipn_firstn_comm, skipn_skipn.
          rewrite (skipn_split2 msg (Z.to_nat (uE E off + kz)) (Z.to_nat (uE E l0) - Z.to_nat kz)).
          f_equal; [f_equal; f_equal; first [solve [clear - Roff Hkr; lia] | lia] | f_equal; first [solve [clear - Roff Rl0 Hkr; lia] | solve [clear - Roff Rl0 Rl1 Hkr; lia] | lia]].   (* [comment removed for export] *) }
        fold kv. rewrite Hpk, <- app_assoc. apply t_emit_app.
  - (* [comment removed for export] *)
    destruct (Z.eqb c2 2) eqn:Hc22; [|discriminate]. apply Z.eqb_eq in Hc22. subst c2.
    destruct (load_at img (s_facts S) (s_rgs S) (laddc iov 16) SZ8 false) as [[b1|]|] eqn:Hlb1; try discriminate.
    destruct (load_at img (s_facts S) (s_rgs S) (laddc iov 24) SZ8 false) as [[l1|]|] eqn:Hll1; try discriminate.
    match type of Hok with ((if ?c then ?x else None) = Some _) =>
      assert (Hc2 : c = true) by (destruct c; [reflexivity | discriminate Hok]); rewrite Hc2 in Hok end.
    injection Hok as <-.
    repeat match type of Hc2 with ((_ && _)%bool = true) => apply andb_prop in Hc2 as [Hc2 ?Hq] end.
    rename Hc2 into Hws1.
    match goal with Hq' : iov_src_ok _ recs P Sl lj b1 l1 (ladd off l0) F1 = true |- _ => rename Hq' into Hio1 end.
    repeat match goal with Hx' : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx' end.
    assert (Hwl0 : lwf (s_next S) l0 = true) by assumption.
    assert (Hwl1 : lwf (s_next S) l1 = true) by assumption.
    pose proof (irange_sound E _ (ladd l0 l1) HF0) as Rl01. fold (uE E (ladd l0 l1)) in Rl01.
    destruct (iov_src_sound segs LIMIT model0 mem0 img Himg sarg0 E S M ms model1 recs pre suf j lj b1 l1 (ladd off l0) F1 Hd1 Hrec HLj Hlhi HPl HSl Hws1 Hio1)
      as (B1a & B1b & B1c & Hbuf1).
    fold msg H1 in Hbuf1. fold msg in B1a.
    pose proof (uE_rng E l1) as Rl1.
    assert (Hol : uE E (ladd off l0) = uE E off + uE E l0).
    { unfold uE at 1. rewrite lden_ladd, bv_add_unsigned. fold (uE E off) (uE E l0). unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. unfold two64 in *. lia. }
    rewrite Hol in B1a, Hbuf1.
    assert (Hl01 : uE E (ladd l0 l1) = uE E l0 + uE E l1).
    { unfold uE at 1. rewrite lden_ladd, bv_add_unsigned. fold (uE E l0) (uE E l1). unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. unfold two64 in *. lia. }
    destruct (load_at_sound segs E img _ _ (laddc iov 16) SZ8 false _ _ Himg HG0 HF0 Hlb1) as (bs8c & Hrc & Hvc). specialize (Hvc _ eq_refl).
    destruct (load_at_sound segs E img _ _ (laddc iov 24) SZ8 false _ _ Himg HG0 HF0 Hll1) as (bs8d & Hrd & Hvd). specialize (Hvd _ eq_refl).
    rewrite ov_rdn in Hrc, Hrd. cbn [nbytes] in Hrc, Hrd.
    destruct (rdn_restrict_vis segs mem0 H1 (ms_mem ms) 8 _ bs8c Hhoff Hrc) as [Hrc' Havc].
    destruct (rdn_restrict_vis segs mem0 H1 (ms_mem ms) 8 _ bs8d Hhoff Hrd) as [Hrd' Havd].
    assert (Hl8c : length bs8c = 8%nat) by exact (rdn_length _ _ _ _ _ Hrc').
    assert (Hl8d : length bs8d = 8%nat) by exact (rdn_length _ _ _ _ _ Hrd').
    assert (Hiov16 : lden E (laddc iov 16) = Z_to_bv 64 (bv_unsigned (lden E iov) + 16)) by (rewrite lden_laddc; f_equal; lia).
    assert (Hiov24 : lden E (laddc iov 24) = Z_to_bv 64 (bv_unsigned (lden E iov) + 24)) by (rewrite lden_laddc; f_equal; lia).
    set (bs1 := firstn (Z.to_nat (uE E l1)) (skipn (Z.to_nat (uE E off + uE E l0)) msg)) in *.
    destruct (rdn_restrict_vis segs mem0 H1 (ms_mem ms) _ _ _ Hhoff Hbuf1) as [Hbuf1' Havm1].
    assert (Hlen1 : length bs1 = Z.to_nat (uE E l1)).
    { unfold bs1. rewrite length_firstn, length_skipn. apply Nat.min_l. apply Nat2Z.inj_le. rewrite Nat2Z.inj_sub by lia. rewrite !Z2Nat.id by lia. lia. }
    set (bsT := bs0 ++ bs1).
    assert (HbsT : bsT = firstn (length bs0 + length bs1) (skipn (Z.to_nat (uE E off)) msg)).
    { rewrite Hlen0, Hlen1. unfold bsT, bs0, bs1. rewrite <- firstn_skipn_app2. f_equal. f_equal. f_equal. lia. }
    assert (HlT : length bsT = (length bs0 + length bs1)%nat) by (unfold bsT; apply length_app).
    set (K := t_emit (List.map (WriteEv (Z_to_bv 64 ch)) (skipn (Z.to_nat (uE E off) + length bsT) msg) ++ REST) (t_exit (Z_to_bv 64 kc) fs0)).
    assert (HK0 : K []) by apply t_emit_has_nil.
    eapply rzc_conseq; [|cbn [shp_den List.map concat]; rewrite Hpe; fold REST;
      rewrite (skipn_split2 msg (Z.to_nat (uE E off)) (length bsT)); rewrite HlT at 1; rewrite <- HbsT;
      rewrite map_app, <- app_assoc; apply t_eq_sym; apply t_emit_app].
    fold K.
    assert (Hfch : fd_lookup (m_fds model0) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch))) by (destruct Hch as [->| ->]; assumption).
    apply (den_writevG2 segs cfg LIMIT mem0 model0 E S M ms model1 K ch b0 l0 b1 l1 (ladd l0 l1) bs0 bs1 1073741824 Hd1 H7 H0 H2 Hch Hfch
             ltac:(fold iov; rewrite Hra'; f_equal; rewrite Hva; symmetry; exact (ld8_bytes _ Hl8a))
             ltac:(fold iov; rewrite <- Hiov8; rewrite Hrb'; f_equal; rewrite Hvb; symmetry; exact (ld8_bytes _ Hl8b))
             ltac:(fold iov; rewrite <- Hiov16; rewrite Hrc'; f_equal; rewrite Hvc; symmetry; exact (ld8_bytes _ Hl8c))
             ltac:(fold iov; rewrite <- Hiov24; rewrite Hrd'; f_equal; rewrite Hvd; symmetry; exact (ld8_bytes _ Hl8d))
             ltac:(rewrite Hlen0; exact Hbuf0') ltac:(rewrite Hlen1; exact Hbuf1')
             ltac:(rewrite Hlen0, Z2Nat.id by (first [solve [clear - Rl0; lia] | lia]); reflexivity) ltac:(rewrite Hlen1, Z2Nat.id by (first [solve [clear - Rl1; lia] | lia]); reflexivity)
             ltac:(rewrite Nat2Z.inj_add, Hlen0, Hlen1, !Z2Nat.id by (first [solve [clear - Rl0; lia] | solve [clear - Rl1; lia] | lia]); unfold uE in Hl01; exact Hl01)
             ltac:(rewrite Hlen0, Hlen1; first [solve [clear - Rl0 Rl1 Rl01 Hl01 Hc2; lia] | lia]) ltac:(rewrite Nat2Z.inj_add, Hlen0, Hlen1, !Z2Nat.id by (first [solve [clear - Rl0; lia] | solve [clear - Rl1; lia] | lia]); first [solve [clear - Rl01 Hl01 Hq6; lia] | solve [clear - Rl01 Hl01 Hq7; lia] | lia]) ltac:(clear; lia)
             ltac:(fold iov; first [solve [clear - Ri Hq3; lia] | solve [clear - Ri Hq4; lia] | (unfold uE in *; lia)])
             ltac:(rewrite Hlen0, Z2Nat.id by (first [solve [clear - Rl0; lia] | lia]); first [solve [clear - B0c; unfold uE in *; lia] | (unfold uE in *; lia)]) ltac:(rewrite Hlen1, Z2Nat.id by (first [solve [clear - Rl1; lia] | lia]); first [solve [clear - B1c; unfold uE in *; lia] | (unfold uE in *; lia)])).
    + intros kk Hkk. fold iov H1. destruct (Nat.lt_ge_cases kk 8) as [Hk8|Hk8]; [exact (Hava kk Hk8)|].
      destruct (Nat.lt_ge_cases kk 16) as [Hk16|Hk16].
      { replace (woff (lden E iov) kk) with (woff (lden E (laddc iov 8)) (kk - 8)); [apply Havb; first [solve [clear - Hk8 Hk16; lia] | solve [clear - Hk8 Hkk; lia] | lia]|].
        unfold woff. rewrite lden_laddc. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. first [solve [clear - Hk8; lia] | solve [clear - Hk16; lia] | solve [clear - Hk24; lia] | lia]. }
      destruct (Nat.lt_ge_cases kk 24) as [Hk24|Hk24].
      { replace (woff (lden E iov) kk) with (woff (lden E (laddc iov 16)) (kk - 16)); [apply Havc; first [solve [clear - Hk16 Hk24; lia] | lia]|].
        unfold woff. rewrite lden_laddc. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. first [solve [clear - Hk8; lia] | solve [clear - Hk16; lia] | solve [clear - Hk24; lia] | lia]. }
      { replace (woff (lden E iov) kk) with (woff (lden E (laddc iov 24)) (kk - 24)); [apply Havd; first [solve [clear - Hk24 Hkk; lia] | lia]|].
        unfold woff. rewrite lden_laddc. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. first [solve [clear - Hk8; lia] | solve [clear - Hk16; lia] | solve [clear - Hk24; lia] | lia]. }
    + fold H1. rewrite Hlen0. exact Havm0.
    + fold H1. rewrite Hlen1. exact Havm1.
    + apply lwf_ladd; assumption.
    + exact HK0.
    + intros E' ms' m'' Hd' Ha' Hkr. fold bsT in Hkr |- *.
      set (kv := s_next S) in *.
      set (kz := bv_unsigned (E' kv)) in *.
      assert (Hn' : s_next (wv_post S (ladd l0 l1) 1073741824) = Pos.succ (s_next S)) by reflexivity.
      assert (Hoff' : lden E' off = lden E off) by exact (lden_agree_wf _ E E' off Hwoff Ha').
      assert (Hlj' : lden E' lj = lden E lj) by exact (lden_agree_wf _ E E' lj Hwlj Ha').
      assert (Hi' : INV mem0 E' (wv_post S (ladd l0 l1) 1073741824) M FS model0).
      { apply (INV_agree mem0 E E' S _ M M FS model0 Hi Ha' ltac:(rewrite Hn'; lia) eq_refl (dn_wf _ _ _ _ _ _ _ _ _ Hd)). }
      assert (Hw' : shp_wf (s_next (wv_post S (ladd l0 l1) 1073741824)) (wv_shp (ShEmit (PD ch (SLit bs) off :: rest) kc) S) = true).
      { rewrite Hn'. cbn [wv_shp shp_wf forallb pend_wf pd_src pd_off]. apply andb_true_intro. split.
        - apply lwf_ladd; [exact (lwf_mono (s_next S) (Pos.succ (s_next S)) off ltac:(lia) Hwoff)|]. unfold lwf, lvar. cbn. rewrite andb_true_r. apply Pos.ltb_lt. lia.
        - exact (shp_wf_mono (s_next S) (Pos.succ (s_next S)) (ShEmit rest kc) ltac:(lia) Hwr). }
      assert (HOL : forall l0', wv_l0 img S F1 = Some l0' -> lwf (s_next S) l0' = true /\ bv_unsigned (lden E' l0') <= 1073741824 /\
                                                          1 <= bv_unsigned (E' (s_next S)) <= 1073741824).
      { intros l0' Hs. unfold wv_l0 in Hs. fold iov in Hs.
        assert (Hs' : Some l0 = Some l0') by (destruct F1; try discriminate Hs; rewrite H2 in Hs; cbn [Z.eqb Pos.eqb] in Hs; rewrite Hll0 in Hs; exact Hs).
        injection Hs' as <-. split; [exact Hwl0|]. rewrite (lden_agree_wf _ E E' l0 Hwl0 Ha'). fold (uE E l0). change (bv_unsigned (E' (s_next S))) with kz.
        rewrite Hlen0, Hlen1 in Hkr. rewrite Nat2Z.inj_add, !Z2Nat.id in Hkr by (first [solve [clear - Rl0; lia] | solve [clear - Rl1; lia] | lia]). unfold uE in *. lia. }
      eapply rzc_conseq.
      * apply (Pm_wvpost k IH S M FS _ a (ladd l0 l1) (wv_l0 img S F1) finals Hck model0 mem0 E' ms' m'' Hd' Hi'
                 (HAX_step E E' S (wv_post S (ladd l0 l1) 1073741824) M a mem0 (conj Haw HHA) (dn_wf _ _ _ _ _ _ _ _ _ Hd) Ha' ltac:(rewrite Hn'; lia)) Hw' HOL).
        intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' Hx'' Hw'' Ha''.
        exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' Hx'' Hw''
                 (agree_trans _ E E' E'' Ha' (agree_mono (s_next S) (s_next (wv_post S (ladd l0 l1) 1073741824)) E' E'' ltac:(rewrite Hn'; lia) Ha''))).
      * cbn [wv_shp shp_den List.map concat].
        assert (HR : concat (List.map (pend_evs E') rest) = REST).
        { unfold REST. f_equal. apply map_ext_in. intros q Hqin.
          rewrite forallb_forall in Hwr. exact (pend_evs_agree _ E E' q (Hwr q Hqin) Ha'). }
        rewrite HR. unfold K.
        assert (Hpk : pend_evs E' (PD ch (SLit bs) (ladd off (lvar kv))) =
                      List.map (WriteEv (Z_to_bv 64 ch)) (skipn (Z.to_nat kz) bsT) ++ List.map (WriteEv (Z_to_bv 64 ch)) (skipn (Z.to_nat (uE E off) + length bsT) msg)).
        { unfold pend_evs. cbn [pd_ch pd_src pd_off]. rewrite <- map_app. f_equal.
          assert (HsE : src_bytes E' (SLit bs) = msg) by exact (Hsrc E').
          rewrite HsE. unfold uE at 1. rewrite lden_ladd, lden_lvar, Hoff'. rewrite bv_add_unsigned. fold (uE E off) kz. unfold bv_wrap.
          rewrite Hlen0, Hlen1 in Hkr. rewrite Nat2Z.inj_add, !Z2Nat.id in Hkr by (first [solve [clear - Rl0; lia] | solve [clear - Rl1; lia] | lia]).
          rewrite Z.mod_small by (change (bv_modulus 64) with two64; pose proof (bv_unsigned_in_range _ (E' kv)) as Rkz; unfold two64 in *; lia).
          rewrite HlT, HbsT, skipn_firstn_comm, skipn_skipn.
          rewrite (skipn_split2 msg (Z.to_nat (uE E off + kz)) (length bs0 + length bs1 - Z.to_nat kz)).
          rewrite Hlen0, Hlen1. f_equal; [f_equal; f_equal; first [solve [clear - Roff Hkr; lia] | lia] | f_equal; first [solve [clear - Roff Rl0 Hkr; lia] | solve [clear - Roff Rl0 Rl1 Hkr; lia] | lia]].   (* [comment removed for export] *) }
        fold kv. rewrite Hpk, <- app_assoc. apply t_emit_app.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma Pm_splitP : forall n k, Pm k -> Pm (MSplitP n k).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct sh as [po kc|sa sb|lq loq hiq sa sb|lq jq sa sb]; try discriminate. destruct po as [|p rest]; try discriminate.
  destruct p as [ch [bs|pre j lj suf] off]; try discriminate.
  destruct (lin_eqb off (lconst 0)) eqn:Ho; [|discriminate]. apply lin_eqb_eq in Ho. subst off.
  assert (Hp : pend_evs E (PD ch (SLit bs) (lconst 0)) = pend_evs E (PD ch (SLit (firstn n bs)) (lconst 0)) ++ pend_evs E (PD ch (SLit (skipn n bs)) (lconst 0))).
  { unfold pend_evs. cbn [pd_ch pd_src pd_off src_bytes]. assert (H0 : Z.to_nat (uE E (lconst 0)) = O) by (unfold uE; rewrite lden_lconst; reflexivity).
    rewrite !H0. cbn [skipn].
    assert (Hl : forall (f : byte -> event) (g : Z -> byte) (l : list Z) (n0 : nat), List.map f (List.map g l) = List.map f (List.map g (firstn n0 l)) ++ List.map f (List.map g (skipn n0 l))).
    { intros f g l n0. rewrite <- List.map_app, <- List.map_app, firstn_skipn. reflexivity. }
    apply Hl. }
  assert (Heq : shp_den E (ShEmit (PD ch (SLit bs) (lconst 0) :: rest) kc) =
                shp_den E (ShEmit (PD ch (SLit (firstn n bs)) (lconst 0) :: PD ch (SLit (skipn n bs)) (lconst 0) :: rest) kc)).
  { cbn [shp_den List.map concat]. rewrite Hp, <- app_assoc. reflexivity. }
  rewrite Heq.
  assert (Hw' : shp_wf (s_next S) (ShEmit (PD ch (SLit (firstn n bs)) (lconst 0) :: PD ch (SLit (skipn n bs)) (lconst 0) :: rest) kc) = true).
  { cbn [shp_wf forallb pend_wf pd_src pd_off] in Hw |- *. apply andb_prop in Hw as [H1 H2]. rewrite H1, H2. reflexivity. }
  exact (IH S M FS _ a finals Hck model0 mem0 E ms model Hd Hi HX Hw' Hk).
Qed.

#[using="Hwx Himg Hect Hp4"] Lemma Pm_writev0 : forall k, Pm k -> Pm (MWritev0 k).
Proof. LiaFast.lf_pins (fun (Hwx Himg Hect Hp4 : LiaFast.U) => LiaFast.u0).
  intros k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (is_ecall t (s_pc S) && writev0_ok img S)%bool eqn:Hb; [|discriminate].
  apply andb_prop in Hb as [Hx Hok]. apply is_ecall_ok in Hx. unfold writev0_ok in Hok.
  set (iov := argl S 1) in *.
  destruct (a7c S) as [c7|] eqn:H7; [|discriminate]. destruct (arg S 0) as [c0|] eqn:H0; [|discriminate].
  destruct (arg S 2) as [c2|] eqn:H2; [|discriminate].
  destruct (load_at img (s_facts S) (s_rgs S) iov SZ8 false) as [[b|]|] eqn:Hlb; try discriminate.
  destruct (load_at img (s_facts S) (s_rgs S) (laddc iov 8) SZ8 false) as [[l|]|] eqn:Hll; try discriminate.
  repeat match type of Hok with ((_ && _)%bool = true) => apply andb_prop in Hok as [Hok ?Hq] end.
  rename Hok into H66. apply Z.eqb_eq in H66. subst c7.
  assert (Hch : c0 = 1 \/ c0 = 2).
  { match goal with Hq' : (Z.eqb c0 1 || Z.eqb c0 2)%bool = true |- _ => apply orb_prop in Hq' as [Hq'|Hq']; apply Z.eqb_eq in Hq'; auto end. }
  repeat match goal with
         | Hx' : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in Hx'
         | Hx' : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx'
         | Hx' : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in Hx'
         end.
  subst c2 l.
  pose proof Hi as Hi0. destruct Hi0 as (Hpv & Hfsw & Hfr & Hm0 & Hlen & Hlk & Hfs0 & Hfds & Hch1 & Hch2 & Hdv).
  assert (Hfch : fd_lookup (m_fds model0) (Z_to_bv 64 c0) = Some (FdChannel (Z_to_bv 64 c0))) by (destruct Hch as [->| ->]; assumption).
  apply (den_ecall segs cfg LIMIT model0 mem0 Hwx t E S M ms model _ Hect Hx Hd). intros model1 Hd1.
  set (H1 := Hof E M model1).
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd1)) as (_ & _ & _ & _ & HG0 & _ & HF0 & _).
  pose proof (dn_hoff _ _ _ _ _ _ _ _ _ Hd1) as Hhoff. fold H1 in HG0, Hhoff. cbn [restrict ms_mem] in HG0.
  pose proof (irange_sound E _ iov HF0) as Ri. pose proof (irange_sound E _ b HF0) as Rb.
  destruct (load_at_sound segs E img _ _ iov SZ8 false _ _ Himg HG0 HF0 Hlb) as (bs8a & Hra & Hva). specialize (Hva _ eq_refl).
  destruct (load_at_sound segs E img _ _ (laddc iov 8) SZ8 false _ _ Himg HG0 HF0 Hll) as (bs8b & Hrb & Hvb). specialize (Hvb _ eq_refl).
  rewrite ov_rdn in Hra, Hrb. cbn [nbytes] in Hra, Hrb.
  destruct (rdn_restrict_vis segs mem0 H1 (ms_mem ms) 8 _ bs8a Hhoff Hra) as [Hra' Hava].
  destruct (rdn_restrict_vis segs mem0 H1 (ms_mem ms) 8 _ bs8b Hhoff Hrb) as [Hrb' Havb].
  assert (Hl8a : length bs8a = 8%nat) by exact (rdn_length _ _ _ _ _ Hra').
  assert (Hl8b : length bs8b = 8%nat) by exact (rdn_length _ _ _ _ _ Hrb').
  assert (Hiov8 : lden E (laddc iov 8) = Z_to_bv 64 (bv_unsigned (lden E iov) + 8)) by (rewrite lden_laddc; f_equal; lia).
  apply (den_writev0 segs cfg LIMIT mem0 model0 E S M ms model1 _ c0 b (lconst 0) Hd1 H7 H0 H2 Hch Hfch
           ltac:(fold iov; rewrite Hra'; f_equal; rewrite Hva; symmetry; exact (ld8_bytes _ Hl8a))
           ltac:(fold iov; rewrite <- Hiov8; rewrite Hrb'; f_equal; rewrite Hvb; symmetry; exact (ld8_bytes _ Hl8b))
           ltac:(rewrite lden_lconst; reflexivity) ltac:(lia) ltac:(fold iov; lia)).
  - intros kk Hkk. fold iov H1. destruct (Nat.lt_ge_cases kk 8) as [Hk8|Hk8]; [exact (Hava kk Hk8)|].
    replace (woff (lden E iov) kk) with (woff (lden E (laddc iov 8)) (kk - 8)); [apply Havb; first [solve [clear - Hk8 Hk16; lia] | solve [clear - Hk8 Hkk; lia] | lia]|].
    unfold woff. rewrite lden_laddc. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. first [solve [clear - Hk8; lia] | solve [clear - Hk16; lia] | solve [clear - Hk24; lia] | lia].
  - intros ms' m'' Hd''.
    apply (IH _ _ _ _ _ finals Hck model0 mem0 E ms' m'' Hd'' (INV_same mem0 E S _ M FS model0 Hi eq_refl) (HAX_same E S _ M a mem0 HX eq_refl) Hw). exact Hk.
Qed.

(* [comment removed for export] *)
#[using="path0 data0 Hp4"] Lemma mod_pow_succ : forall u k r0, 0 <= u -> 0 <= k -> u mod 2 ^ k = r0 -> u mod 2 ^ (k + 1) = r0 \/ u mod 2 ^ (k + 1) = r0 + 2 ^ k.
Proof. LiaFast.lf_pins (fun (path0 data0 Hp4 : LiaFast.U) => LiaFast.u0).
  intros u k r0 Hu Hk H. assert (Hp : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2.
  rewrite Z.rem_mul_r by lia. rewrite H.
  assert (Hq : 0 <= (u / 2 ^ k) mod 2 < 2) by (apply Z.mod_pos_bound; lia).
  destruct (Z.eq_dec ((u / 2 ^ k) mod 2) 0) as [E0|E1]; [left; rewrite E0; lia | right; replace ((u / 2 ^ k) mod 2) with 1 by lia; lia].
Qed.
#[using="Hp4"] Lemma Pm_splitB : forall l k r0 ka kb, Pm ka -> Pm kb -> Pm (MSplitB l k r0 ka kb).
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros l k r0 ka kb IHa IHb S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (lwf (s_next S) l && Z.leb 0 k && Z.ltb k 64 && (Z.eqb k 0 && Z.eqb r0 0 || match lowb (s_facts S) l k with Some r => Z.eqb r r0 | None => false end))%bool eqn:Hc;
    [|discriminate].
  destruct (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts ka (add_fact S (FMod l (k + 1) r0)) M FS sh a) as [f1|] eqn:H1; [|discriminate].
  destruct (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts kb (add_fact S (FMod l (k + 1) (r0 + 2 ^ k))) M FS sh a) as [f2|] eqn:H2; [|discriminate].
  injection Hck as <-.
  apply andb_prop in Hc as [Hc Hlow]. apply andb_prop in Hc as [Hc Hk64]. apply andb_prop in Hc as [Hwl Hk0].
  apply Z.leb_le in Hk0. apply Z.ltb_lt in Hk64.
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF0 & _).
  assert (Hr0 : bv_unsigned (lden E l) mod 2 ^ k = r0).
  { apply orb_prop in Hlow as [Hlow|Hlow].
    - apply andb_prop in Hlow as [Hz Hr]. apply Z.eqb_eq in Hz, Hr. subst k r0. rewrite Z.pow_0_r, Z.mod_1_r. reflexivity.
    - destruct (lowb (s_facts S) l k) as [r|] eqn:Hlb; [|discriminate]. apply Z.eqb_eq in Hlow. subst r.
      exact (lowb_sound E _ l k r0 HF0 Hlb). }
  assert (Hn : forall f, s_next (add_fact S f) = s_next S) by reflexivity.
  pose proof (u_range E l) as Rl.
  destruct (mod_pow_succ (bv_unsigned (lden E l)) k r0 ltac:(lia) Hk0 Hr0) as [Hm|Hm].
  - apply (IHa (add_fact S (FMod l (k + 1) r0)) M FS sh a f1 H1 model0 mem0 E ms model).
    + apply den_addfact; [exact Hd|]. intros E' Ha'. cbn [fact_ok]. rewrite <- (lden_agree (s_next S) E E' l Hwl Ha'). exact Hm.
    + exact (INV_same mem0 E S _ M FS model0 Hi (Hn _)).
    + exact (HAX_same E S _ M a mem0 HX (Hn _)).
    + rewrite Hn. exact Hw.
    + intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin Hd'' Hi'' Hx'' Hw'' Ha''. rewrite Hn in Ha''.
      exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (in_or_app _ _ _ (or_introl Hin)) Hd'' Hi'' Hx'' Hw'' Ha'').
  - apply (IHb (add_fact S (FMod l (k + 1) (r0 + 2 ^ k))) M FS sh a f2 H2 model0 mem0 E ms model).
    + apply den_addfact; [exact Hd|]. intros E' Ha'. cbn [fact_ok]. rewrite <- (lden_agree (s_next S) E E' l Hwl Ha'). exact Hm.
    + exact (INV_same mem0 E S _ M FS model0 Hi (Hn _)).
    + exact (HAX_same E S _ M a mem0 HX (Hn _)).
    + rewrite Hn. exact Hw.
    + intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin Hd'' Hi'' Hx'' Hw'' Ha''. rewrite Hn in Ha''.
      exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (in_or_app _ _ _ (or_intror Hin)) Hd'' Hi'' Hx'' Hw'' Ha'').
Qed.
(* [comment removed for export] *)
#[using="path0 data0 Hp4"] Lemma testbit_mod_pow : forall u r j, 0 <= j -> u mod 2 ^ (j + 1) = r -> Z.testbit u j = Z.testbit r j.
Proof. LiaFast.lf_pins (fun (path0 data0 Hp4 : LiaFast.U) => LiaFast.u0).
  intros u r j Hj H. rewrite <- H. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
Qed.
#[using="Hp4"] Lemma Pm_selB : forall ka kb, Pm ka -> Pm kb -> Pm (MSelB ka kb).
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros ka kb IHa IHb S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct sh as [po kc|sa sb|lq loq hiq sa sb|lq jq sa sb]; try discriminate.
  destruct (Z.leb 0 jq) eqn:Hj; [|discriminate]. apply Z.leb_le in Hj.
  destruct (lowb (s_facts S) lq (jq + 1)) as [r|] eqn:Hlb; [|discriminate].
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF0 & _).
  pose proof (lowb_sound E _ lq (jq + 1) r HF0 Hlb) as Hm.
  cbn [shp_wf] in Hw. apply andb_prop in Hw as [Hw Hwb]. apply andb_prop in Hw as [Hwl Hwa].
  cbn [shp_den]. unfold uE. rewrite (testbit_mod_pow _ r jq Hj Hm).
  destruct (Z.testbit r jq).
  - exact (IHa S M FS sa a finals Hck model0 mem0 E ms model Hd Hi HX Hwa Hk).
  - exact (IHb S M FS sb a finals Hck model0 mem0 E ms model Hd Hi HX Hwb Hk).
Qed.

(* [comment removed for export] *)
#[using="Hp4"] Lemma Pm_sel : forall ka kb, Pm ka -> Pm kb -> Pm (MSel ka kb).
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros ka kb IHa IHb S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct sh as [po kc|sa sb|l lo hi sa sb|lq jq sa sb]; try discriminate.
  cbn [shp_wf] in Hw. apply andb_prop in Hw as [Hw Hwb]. apply andb_prop in Hw as [Hwl Hwa].
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF & _).
  pose proof (irange_sound E (s_facts S) l HF) as Hr.
  cbn [shp_den].
  destruct (Z.leb lo (fst (irange (s_facts S) l)) && Z.leb (snd (irange (s_facts S) l)) hi)%bool eqn:H1.
  - apply andb_prop in H1 as [H1 H2]. apply Z.leb_le in H1, H2.
    replace (Z.leb lo (uE E l) && Z.leb (uE E l) hi)%bool with true
      by (symmetry; apply andb_true_intro; split; apply Z.leb_le; unfold uE; lia).
    exact (IHa S M FS sa a finals Hck model0 mem0 E ms model Hd Hi HX Hwa Hk).
  - destruct (Z.ltb hi (fst (irange (s_facts S) l)) || Z.ltb (snd (irange (s_facts S) l)) lo)%bool eqn:H2; [|discriminate].
    replace (Z.leb lo (uE E l) && Z.leb (uE E l) hi)%bool with false
      by (symmetry; apply orb_prop in H2 as [H2|H2]; apply Z.ltb_lt in H2; apply andb_false_iff; [right | left]; apply Z.leb_gt; unfold uE; lia).
    exact (IHb S M FS sb a finals Hck model0 mem0 E ms model Hd Hi HX Hwb Hk).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fdedup_in : forall fs seen f, In f (fdedup seen fs) -> In f fs.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction fs as [|g r IH]; intros seen f H; [exact H|]. cbn [fdedup] in H. destruct (List.existsb (fact_eqb g) seen).
  - right. exact (IH seen f H).
  - destruct H as [<-|H]; [left; reflexivity | right; exact (IH _ f H)].
Qed.
#[using="Type"] Lemma den_gc : forall model0 mem0 E S M ms model (fs' : list fact), (forall f, In f fs' -> In f (s_facts S)) -> DEN segs LIMIT model0 mem0 E S M ms model ->
  DEN segs LIMIT model0 mem0 E (SST (s_pc S) (s_regs S) (s_rgs S) fs' (s_next S) (s_resv S)) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 mem0 E S M ms model fs' Hsub Hd. destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  constructor; try assumption.
  intros E' Ha'. destruct (Hsd E' Ha') as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  unfold sden0; cbn [s_pc s_regs s_rgs s_facts s_resv]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [|exact H8].
  apply Forall_forall. intros f Hf. rewrite Forall_forall in H7. exact (H7 f (Hsub f Hf)).
Qed.
#[using="Hp4 awf_mono aeqb_eq HA_agree"] Lemma Pm_loopW0 : forall zk body ks, Pm body -> Qm ks -> Pm (MLoopW0 zk body ks).
Proof. LiaFast.lf_pins (fun (Hp4 awf_mono aeqb_eq HA_agree : LiaFast.U) => LiaFast.u0).
  intros zk body ks IHb IHk S M FS sh a finals Hck. cbn [mcheck] in Hck.
  destruct (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts body S M FS sh a) as [fb1|]; [|discriminate].
  destruct (List.find (fun '(F, _, _, _, _) => Z.eqb (s_pc F) (s_pc S)) fb1) as [[[[[F1 M1] FS1] sh1] a1]|]; [|discriminate].
  destruct (wgen false S F1 FS FS1 sh sh1 zk) as [[[[[P0 n0] FP] shP] meas]|]; [|discriminate].
  match type of Hck with
  | context [went n0 S M FS sh ?P FP shP] => exact (Pm_loop P n0 FP shP meas body ks IHb IHk S M FS sh a finals Hck)
  end.
Qed.
(* [comment removed for export] *)
#[using="Hp4"] Lemma INV_entM : forall mem0 E S P MP σ FS FP model0 n0,
  INV mem0 E S (msubst σ MP) FS model0 -> params_fixed σ (pos_below n0) = true ->
  pv_okb pv hv n0 = true -> fs_ent FS FP σ = true -> fs_wf (s_next P) FP = true -> (n0 <= s_next P)%positive ->
  (s_next S <= n0)%positive ->
  INV mem0 (ecomp E σ) P MP FP model0.
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros mem0 E S P MP σ FS FP model0 n0 Hi Hpf Hpvk Hfe Hfw Hn1 HnS. unfold pv_okb in Hpvk. apply andb_prop in Hpvk as [Hpv0 Hhv0].
  set (E0 := ecomp E σ).
  assert (Ha : agree n0 E E0) by exact (agree_params n0 E σ Hpf).
  destruct Hi as (Hpv & Hfsw & Hfr & Hm0 & Hlen & Hlk & Hfs0 & Hfds & Hc1 & Hc2 & Hdv).
  assert (Hpv' : lden E0 pv = lden E pv) by exact (lden_agree_wf _ E E0 pv Hpv0 Ha).
  split; [exact (lwf_mono _ _ _ Hn1 Hpv0)|]. split; [exact Hfw|].
  split.
  { intros Hdr k Hk. destruct (Hfr Hdr k Hk) as (p & Hp & Hr). unfold msubst in Hp. cbn [sm_frz] in Hp.
    apply in_map_iff in Hp as (q & <- & Hq). exists q. split; [exact Hq|].
    unfold ppsubst in Hr. cbn [fst snd] in Hr. rewrite Hpv'. unfold E0. rewrite !uE_sub. exact Hr. }
  split.
  { split; [intros Hdr k Hk; rewrite Hpv'; exact (proj1 Hm0 Hdr k Hk)|].
    intros Hdr w Hw. rewrite Hpv' in Hw. destruct (proj2 Hm0 Hdr w Hw) as [(p & Hp & Hr) Hne]. split; [|exact Hne].
    unfold msubst in Hp. cbn [sm_frz] in Hp. apply in_map_iff in Hp as (q & <- & Hq). exists q. split; [exact Hq|].
    unfold ppsubst in Hr. cbn [fst snd] in Hr. unfold E0. rewrite !uE_sub. exact Hr. }
  split; [rewrite Hpv'; exact Hlen|]. split; [exact Hlk|]. split; [exact Hfs0|].
  split; [|split; [exact Hc1 | split; [exact Hc2 | exact (hv_inv_agree n0 E E0 S P Hdv Ha Hhv0 Hn1)]]].
  destruct FS as [|off FL| | |off FL]; destruct FP as [|off' FL'| | |off' FL']; cbn [fs_ent] in Hfe; try discriminate; [exact Hfds| |exact I|exact Hfds| ];
  (apply andb_prop in Hfe as [Ho Hf]; apply lin_eqb_eq in Ho, Hf;
   unfold E0; rewrite <- !lden_lsubst; rewrite <- Ho, <- Hf; exact Hfds).
Qed.
#[using="Hp4 aeqb_eq HA_msub"] Lemma Pm_joinL : forall body jpc k, Pm body -> Pm k -> Pm (MJoinL body jpc k).
Proof. LiaFast.lf_pins (fun (Hp4 aeqb_eq HA_msub : LiaFast.U) => LiaFast.u0).
  intros body jpc k IHb IHk S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts body S M FS sh a) as [fb|] eqn:Hb; [|discriminate].
  set (J := List.filter (fun '(F, _, _, _, _) => Z.eqb (s_pc F) jpc) fb) in *.
  set (O := List.filter (fun '(F, _, _, _, _) => negb (Z.eqb (s_pc F) jpc)) fb) in *.
  assert (HinO : forall F MF FSF shF aF, In (F, MF, FSF, shF, aF) fb -> Z.eqb (s_pc F) jpc = false -> In (F, MF, FSF, shF, aF) O).
  { intros F MF FSF shF aF Hin Hpc. unfold O. apply filter_In. split; [exact Hin|]. rewrite Hpc. reflexivity. }
  assert (HinJ : forall F MF FSF shF aF, In (F, MF, FSF, shF, aF) fb -> Z.eqb (s_pc F) jpc = true -> In (F, MF, FSF, shF, aF) J).
  { intros F MF FSF shF aF Hin Hpc. unfold J. apply filter_In. split; [exact Hin|]. exact Hpc. }
  destruct J as [|[[[[F0 M0] FS0] sh0] a0] Jr] eqn:HJ.
  - injection Hck as <-.
    apply (IHb S M FS sh a fb Hb model0 mem0 E ms model Hd Hi HX Hw).
    intros F MF FSF shF aF model0F mem0F EF msF modelF Hin HdF HiF HXF HwF HaF.
    destruct (Z.eqb (s_pc F) jpc) eqn:Hpc; [destruct (HinJ F MF FSF shF aF Hin Hpc)|].
    exact (Hk F MF FSF shF aF model0F mem0F EF msF modelF (HinO F MF FSF shF aF Hin Hpc) HdF HiF HXF HwF HaF).
  - set (n0 := max_next (List.map (fun '(F, _, _, _, _) => F) Jr) (s_next F0)) in *.
    destruct (genLA (List.map (fun '(F, MF, _, _, _) => (F, MF)) ((F0, M0, FS0, sh0, a0) :: Jr))
                    (List.map (fun '(_, _, _, _, aF) => alins aF) ((F0, M0, FS0, sh0, a0) :: Jr))) as [[[P0 MP] als]|] eqn:Hg; [|discriminate].
    set (P := join_fs_hull P0 FS0 ((F0, M0, FS0, sh0, a0) :: Jr)) in *.
    set (aP := aset a0 als) in *.
    destruct (forallb (fun '(F, MF, FSF, shF, aF) => let σ := matchLA F MF (alins aF) P MP (alins aP) in
                 entails F P σ && fixed_below σ n0 && Pos.leb (s_next F) n0 && fs_ent FSF FS0 σ && shp_ent shF sh0 σ &&
                 sm_eqbm σ MP MF && aeqb (asub σ aP) aF) ((F0, M0, FS0, sh0, a0) :: Jr) &&
              state_wf P && sm_wf (s_next P) MP && Pos.leb n0 (s_next P) && agok MP aP &&
              Pos.leb (s_next S) n0 && fs_wf (s_next P) FS0 && shp_wf (s_next P) sh0 && pv_okb pv hv n0 && awf (s_next P) aP)%bool eqn:Hc; [|discriminate].
    destruct (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts k P MP FS0 sh0 aP) as [fk|] eqn:Hk0; [|discriminate].
    injection Hck as <-.
    apply andb_prop in Hc as [Hc Hwa0]. apply andb_prop in Hc as [Hc Hpv0]. apply andb_prop in Hc as [Hc HwP].
    apply andb_prop in Hc as [Hc Hfw]. apply andb_prop in Hc as [Hc Hsn]. apply andb_prop in Hc as [Hc Hagk].
    apply andb_prop in Hc as [Hc HnP]. apply andb_prop in Hc as [Hc HmwP]. apply andb_prop in Hc as [Hall HswP].
    apply Pos.leb_le in Hsn. apply Pos.leb_le in HnP.
    rewrite forallb_forall in Hall.
    apply (IHb S M FS sh a fb Hb model0 mem0 E ms model Hd Hi HX Hw).
    intros F MF FSF shF aF model0F mem0F EF msF modelF Hin HdF HiF HXF HwF HaF.
    destruct (Z.eqb (s_pc F) jpc) eqn:Hpc.
    + pose proof (Hall _ (HinJ F MF FSF shF aF Hin Hpc)) as Hq. cbv beta zeta in Hq.
      set (σ := matchLA F MF (alins aF) P MP (alins aP)) in *.
      apply andb_prop in Hq as [Hq Hae]. apply andb_prop in Hq as [Hq Hsm]. apply andb_prop in Hq as [Hq Hse].
      apply andb_prop in Hq as [Hq Hfe]. apply andb_prop in Hq as [Hq HnF]. apply andb_prop in Hq as [Hent Hpf]. apply Pos.leb_le in HnF. rewrite fixed_below_eq in Hpf.
      apply sm_eqbm_eq in Hsm as [Hsm Hmk]. apply aeqb_eq in Hae.
      assert (HdF' : DEN segs LIMIT model0F mem0F EF F (msubst σ MP) msF modelF)
        by (replace (msubst σ MP) with MF by (symmetry; exact Hsm); exact HdF).
      assert (HiF' : INV mem0F EF F (msubst σ MP) FSF model0F)
        by (replace (msubst σ MP) with MF by (symmetry; exact Hsm); exact HiF).
      assert (HAF' : HA EF (msubst σ MP) (asub σ aP) mem0F)
        by (replace (msubst σ MP) with MF by (symmetry; exact Hsm); replace (asub σ aP) with aF by (symmetry; exact Hae); exact (proj2 HXF)).
      pose proof (den_ent_M segs LIMIT model0F mem0F EF F P MP msF modelF σ HdF' Hent HswP HmwP Hmk) as HdP.
      assert (HaP : agree n0 EF (ecomp EF σ)) by exact (agree_params n0 EF σ Hpf).
      pose proof (INV_entM mem0F EF F P MP σ FSF FS0 model0F n0 HiF' Hpf Hpv0 Hfe Hfw HnP HnF) as HiP.
      assert (HXP : HAX (ecomp EF σ) P MP aP mem0F)
        by exact (conj Hwa0 (HA_msub EF σ MP aP mem0F Hagk HAF')).
      rewrite <- (shp_den_ent EF shF sh0 σ Hse).
      apply (IHk P MP FS0 sh0 aP fk Hk0 model0F mem0F _ msF modelF HdP HiP HXP HwP).
      intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' HX'' Hw'' Ha''.
      apply (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (in_or_app _ _ _ (or_introl Hin'')) Hd'' Hi'' HX'' Hw'').
      apply (agree_trans _ E EF E'' HaF). apply (agree_trans _ EF (ecomp EF σ) E'').
      * exact (agree_mono (s_next S) n0 EF _ Hsn HaP).
      * exact (agree_mono (s_next S) (s_next P) _ E'' ltac:(lia) Ha'').
    + exact (Hk F MF FSF shF aF model0F mem0F EF msF modelF (in_or_app _ _ _ (or_intror (HinO F MF FSF shF aF Hin Hpc))) HdF HiF HXF HwF HaF).
Qed.
#[using="Hp4 aeqb_eq HA_msub"] Lemma Pm_joinG : forall gen body jpc k, Pm body -> Pm k -> Pm (MJoinG gen body jpc k).
Proof. LiaFast.lf_pins (fun (Hp4 aeqb_eq HA_msub : LiaFast.U) => LiaFast.u0).
  intros gen body jpc k IHb IHk S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts body S M FS sh a) as [fb|] eqn:Hb; [|discriminate].
  set (J := List.filter (fun '(F, _, _, _, _) => Z.eqb (s_pc F) jpc) fb) in *.
  set (O := List.filter (fun '(F, _, _, _, _) => negb (Z.eqb (s_pc F) jpc)) fb) in *.
  assert (HinO : forall F MF FSF shF aF, In (F, MF, FSF, shF, aF) fb -> Z.eqb (s_pc F) jpc = false -> In (F, MF, FSF, shF, aF) O).
  { intros F MF FSF shF aF Hin Hpc. unfold O. apply filter_In. split; [exact Hin|]. rewrite Hpc. reflexivity. }
  assert (HinJ : forall F MF FSF shF aF, In (F, MF, FSF, shF, aF) fb -> Z.eqb (s_pc F) jpc = true -> In (F, MF, FSF, shF, aF) J).
  { intros F MF FSF shF aF Hin Hpc. unfold J. apply filter_In. split; [exact Hin|]. exact Hpc. }
  destruct J as [|[[[[F0 M0] FS0] sh0] a0] Jr] eqn:HJ.
  - injection Hck as <-.
    apply (IHb S M FS sh a fb Hb model0 mem0 E ms model Hd Hi HX Hw).
    intros F MF FSF shF aF model0F mem0F EF msF modelF Hin HdF HiF HXF HwF HaF.
    destruct (Z.eqb (s_pc F) jpc) eqn:Hpc; [destruct (HinJ F MF FSF shF aF Hin Hpc)|].
    exact (Hk F MF FSF shF aF model0F mem0F EF msF modelF (HinO F MF FSF shF aF Hin Hpc) HdF HiF HXF HwF HaF).
  - set (n0 := max_next (List.map (fun '(F, _, _, _, _) => F) Jr) (s_next F0)) in *.
    destruct (gen (List.map (fun '(F, MF, _, _, _) => (F, MF)) ((F0, M0, FS0, sh0, a0) :: Jr))
                    (List.map (fun '(_, _, _, _, aF) => alins aF) ((F0, M0, FS0, sh0, a0) :: Jr))) as [[[P0 MP] als]|] eqn:Hg; [|discriminate].
    set (P := join_fs_hull P0 FS0 ((F0, M0, FS0, sh0, a0) :: Jr)) in *.
    set (aP := aset a0 als) in *.
    destruct (forallb (fun '(F, MF, FSF, shF, aF) => let σ := matchLA F MF (alins aF) P MP (alins aP) in
                 entails F P σ && fixed_below σ n0 && Pos.leb (s_next F) n0 && fs_ent FSF FS0 σ && shp_ent shF sh0 σ &&
                 sm_eqbm σ MP MF && aeqb (asub σ aP) aF) ((F0, M0, FS0, sh0, a0) :: Jr) &&
              state_wf P && sm_wf (s_next P) MP && Pos.leb n0 (s_next P) && agok MP aP &&
              Pos.leb (s_next S) n0 && fs_wf (s_next P) FS0 && shp_wf (s_next P) sh0 && pv_okb pv hv n0 && awf (s_next P) aP)%bool eqn:Hc; [|discriminate].
    destruct (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts k P MP FS0 sh0 aP) as [fk|] eqn:Hk0; [|discriminate].
    injection Hck as <-.
    apply andb_prop in Hc as [Hc Hwa0]. apply andb_prop in Hc as [Hc Hpv0]. apply andb_prop in Hc as [Hc HwP].
    apply andb_prop in Hc as [Hc Hfw]. apply andb_prop in Hc as [Hc Hsn]. apply andb_prop in Hc as [Hc Hagk].
    apply andb_prop in Hc as [Hc HnP]. apply andb_prop in Hc as [Hc HmwP]. apply andb_prop in Hc as [Hall HswP].
    apply Pos.leb_le in Hsn. apply Pos.leb_le in HnP.
    rewrite forallb_forall in Hall.
    apply (IHb S M FS sh a fb Hb model0 mem0 E ms model Hd Hi HX Hw).
    intros F MF FSF shF aF model0F mem0F EF msF modelF Hin HdF HiF HXF HwF HaF.
    destruct (Z.eqb (s_pc F) jpc) eqn:Hpc.
    + pose proof (Hall _ (HinJ F MF FSF shF aF Hin Hpc)) as Hq. cbv beta zeta in Hq.
      set (σ := matchLA F MF (alins aF) P MP (alins aP)) in *.
      apply andb_prop in Hq as [Hq Hae]. apply andb_prop in Hq as [Hq Hsm]. apply andb_prop in Hq as [Hq Hse].
      apply andb_prop in Hq as [Hq Hfe]. apply andb_prop in Hq as [Hq HnF]. apply andb_prop in Hq as [Hent Hpf]. apply Pos.leb_le in HnF. rewrite fixed_below_eq in Hpf.
      apply sm_eqbm_eq in Hsm as [Hsm Hmk]. apply aeqb_eq in Hae.
      assert (HdF' : DEN segs LIMIT model0F mem0F EF F (msubst σ MP) msF modelF)
        by (replace (msubst σ MP) with MF by (symmetry; exact Hsm); exact HdF).
      assert (HiF' : INV mem0F EF F (msubst σ MP) FSF model0F)
        by (replace (msubst σ MP) with MF by (symmetry; exact Hsm); exact HiF).
      assert (HAF' : HA EF (msubst σ MP) (asub σ aP) mem0F)
        by (replace (msubst σ MP) with MF by (symmetry; exact Hsm); replace (asub σ aP) with aF by (symmetry; exact Hae); exact (proj2 HXF)).
      pose proof (den_ent_M segs LIMIT model0F mem0F EF F P MP msF modelF σ HdF' Hent HswP HmwP Hmk) as HdP.
      assert (HaP : agree n0 EF (ecomp EF σ)) by exact (agree_params n0 EF σ Hpf).
      pose proof (INV_entM mem0F EF F P MP σ FSF FS0 model0F n0 HiF' Hpf Hpv0 Hfe Hfw HnP HnF) as HiP.
      assert (HXP : HAX (ecomp EF σ) P MP aP mem0F)
        by exact (conj Hwa0 (HA_msub EF σ MP aP mem0F Hagk HAF')).
      rewrite <- (shp_den_ent EF shF sh0 σ Hse).
      apply (IHk P MP FS0 sh0 aP fk Hk0 model0F mem0F _ msF modelF HdP HiP HXP HwP).
      intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' HX'' Hw'' Ha''.
      apply (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (in_or_app _ _ _ (or_introl Hin'')) Hd'' Hi'' HX'' Hw'').
      apply (agree_trans _ E EF E'' HaF). apply (agree_trans _ EF (ecomp EF σ) E'').
      * exact (agree_mono (s_next S) n0 EF _ Hsn HaP).
      * exact (agree_mono (s_next S) (s_next P) _ E'' ltac:(lia) Ha'').
    + exact (Hk F MF FSF shF aF model0F mem0F EF msF modelF (in_or_app _ _ _ (or_intror (HinO F MF FSF shF aF Hin Hpc))) HdF HiF HXF HwF HaF).
Qed.
#[using="Hp4 awf_mono aeqb_eq HA_agree"] Lemma Pm_loopG : forall gen body ks, Pm body -> Qm ks -> Pm (MLoopG gen body ks).
Proof. LiaFast.lf_pins (fun (Hp4 awf_mono aeqb_eq HA_agree : LiaFast.U) => LiaFast.u0).
  intros gen body ks IHb IHk S M FS sh a finals Hck. cbn [mcheck] in Hck.
  destruct (mcheck segs LIMIT t img pv FLlo FLhi dr hv apost anil aeqb awf acopy asub agok alins aset amod subs conts body S M FS sh a) as [fb1|]; [|discriminate].
  destruct (List.find (fun '(F, _, _, _, _) => Z.eqb (s_pc F) (s_pc S)) fb1) as [[[[[F1 M1] FS1] sh1] a1]|]; [|discriminate].
  destruct (gen S F1 FS FS1 sh sh1) as [[[[[P0 n0] FP] shP] meas]|]; [|discriminate].
  match type of Hck with
  | context [went n0 S M FS sh ?P FP shP] => exact (Pm_loop P n0 FP shP meas body ks IHb IHk S M FS sh a finals Hck)
  end.
Qed.
#[using="Type"] Lemma Pm_gc : forall nk xs k, Pm k -> Pm (MGc nk xs k).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros nk xs k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  set (xs' := xs ++ List.concat (List.map lin_vars (alins a))) in *.
  assert (Hn : s_next (gc_post nk xs' S M FS sh) = s_next S) by reflexivity.
  apply (IH (gc_post nk xs' S M FS sh) M FS sh a finals Hck model0 mem0 E ms model).
  - apply (den_gc model0 mem0 E S M ms model); [|exact Hd]. intros f Hf. apply fdedup_in in Hf. apply filter_In in Hf. exact (proj1 Hf).
  - exact (INV_same mem0 E S _ M FS model0 Hi Hn).
  - exact (HAX_same E S _ M a mem0 HX Hn).
  - rewrite Hn. exact Hw.
  - intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin Hd'' Hi'' Hx'' Hw'' Ha''. rewrite Hn in Ha''.
    exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin Hd'' Hi'' Hx'' Hw'' Ha'').
Qed.

(* [comment removed for export] *)
#[using="Hp4"] Lemma INV_blob : forall mem0 E S S' M M' FS model0 BL, INV mem0 E S M FS model0 -> s_next S' = s_next S -> sm_frz M' = sm_frz M ->
  sm_wf (s_next S) M = true -> INV mem0 E S' M' FS (with_blob BL model0).
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros mem0 E S S' M M' FS model0 BL Hi Hn Hfz Hwf.
  pose proof (INV_agree mem0 E E S S' M M' FS model0 Hi (agree_refl _ _) ltac:(rewrite Hn; apply Pos.le_refl) Hfz Hwf) as Hi'.
  destruct Hi' as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  assert (Hf : m_fds (with_blob BL model0) = m_fds model0) by reflexivity.
  assert (Hs : m_fs (with_blob BL model0) = m_fs model0) by reflexivity.
  unfold INV. rewrite Hf, Hs. repeat (split; [assumption|]). exact H11.
Qed.
#[using="Hp4 awf_mono HA_agree HA_mod"] Lemma Pm_blobnil : forall i k, Pm k -> Pm (MBlobNil i k).
Proof. LiaFast.lf_pins (fun (Hp4 awf_mono HA_agree HA_mod : LiaFast.U) => LiaFast.u0).
  intros i k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (nomark (sm_maps M)) eqn:Hnm; [|discriminate]. destruct (amod M _ a) eqn:Ham; [|discriminate].
  set (n := s_next S) in *. set (M' := with_maps M (ins_mark i (lvar n) (sm_maps M))) in *.
  set (S' := add_fact (bump S (Pos.succ n)) (FRange (lvar n) 4096 4096)) in *.
  set (E' := upd E n (Z_to_bv 64 4096)).
  assert (Ha : agree n E E') by exact (agree_upd n E _).
  assert (Hn' : s_next S' = Pos.succ n) by reflexivity.
  assert (Hle : (s_next S <= s_next S')%positive) by (rewrite Hn'; unfold n; lia).
  assert (HEn : E' n = Z_to_bv 64 4096) by (unfold E'; apply upd_same).
  pose proof (dn_wf _ _ _ _ _ _ _ _ _ Hd) as Hwf.
  assert (Hd1 : DEN segs LIMIT model0 mem0 E' S' M ms model).
  { unfold S'. apply den_addfact.
    - apply den_bump; [|unfold n; lia]. exact (den_agree segs LIMIT model0 mem0 E E' S M ms model Hd Ha).
    - intros E2 Ha2. cbn [fact_ok]. rewrite lden_lvar. rewrite <- (Ha2 n ltac:(cbn [bump add_fact s_next]; lia)). rewrite HEn.
      rewrite u_small64 by (unfold two64; lia). lia. }
  rewrite <- (shp_den_agree (s_next S) E E' sh Hw Ha).
  apply (IH S' M' FS sh a finals Hck model0 mem0 E' ms model).
  - apply (den_mark_ins segs LIMIT model0 mem0 E' S' M ms model i (lvar n) Hd1 Hnm).
    + rewrite Hn'. apply lwf_lvar. lia.
    + reflexivity.
    + unfold uE. rewrite lden_lvar, HEn. apply u_small64. unfold two64. lia.
  - exact (INV_agree mem0 E E' S S' M M' FS model0 Hi Ha Hle eq_refl Hwf).
  - pose proof (HAX_step E E' S S' M a mem0 HX Hwf Ha Hle) as [Hxw Hxh]. split; [exact Hxw | exact (HA_mod E' M M' a mem0 Ham Hxh)].
  - exact (shp_wf_mono _ _ sh Hle Hw).
  - intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin Hd'' Hi'' Hx'' Hw'' Ha''.
    apply (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin Hd'' Hi'' Hx'' Hw'').
    exact (agree_trans _ E E' E'' Ha (agree_mono _ _ E' E'' Hle Ha'')).
Qed.
#[using="Hsegb Hp4 HA_mod"] Lemma Pm_blobadd : forall i k, Pm k -> Pm (MBlobAdd i k).
Proof. LiaFast.lf_pins (fun (Hsegb Hp4 HA_mod : LiaFast.U) => LiaFast.u0).
  intros i k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (blobadd LIMIT (segments_reserved segs) S M i) as [[S' M']|] eqn:Hb; [|discriminate]. destruct (amod M M' a) eqn:Ham; [|discriminate].
  destruct (blobadd_parts _ _ _ _ _ _ _ Hb) as [Hn Hfz].
  apply (IH S' M' FS sh a finals Hck (with_blob (gden E (absorb_g M i) :: blob_of model0) model0) mem0 E ms model).
  - exact (den_blob_add segs LIMIT model0 mem0 Hsegb E S M ms model i S' M' Hd Hb).
  - exact (INV_blob mem0 E S S' M M' FS model0 _ Hi Hn Hfz (dn_wf _ _ _ _ _ _ _ _ _ Hd)).
  - destruct HX as [Hxw Hxh]. split; [rewrite Hn; exact Hxw | exact (HA_mod E M M' a mem0 Ham Hxh)].
  - rewrite Hn. exact Hw.
  - intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin Hd'' Hi'' Hx'' Hw'' Ha''. rewrite Hn in Ha''.
    exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin Hd'' Hi'' Hx'' Hw'' Ha'').
Qed.
#[using="Hp4 HA_mod"] Lemma Pm_alloww : forall j z k, Pm k -> Pm (MAllowW j z k).
Proof. LiaFast.lf_pins (fun (Hp4 HA_mod : LiaFast.U) => LiaFast.u0).
  intros j z k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (widen_ok LIMIT S M j z) eqn:Hok; [|discriminate]. destruct (amod M _ a) eqn:Ham; [|discriminate].
  set (M' := with_allow M (widen_nth j z (sm_allow M))) in *.
  apply (IH S M' FS sh a finals Hck model0 mem0 E ms model).
  - exact (den_allow_widen segs LIMIT model0 mem0 E S M ms model j z Hd Hok).
  - exact (INV_agree mem0 E E S S M M' FS model0 Hi (agree_refl _ _) (Pos.le_refl _) eq_refl (dn_wf _ _ _ _ _ _ _ _ _ Hd)).
  - destruct HX as [Hxw Hxh]. split; [exact Hxw | exact (HA_mod E M M' a mem0 Ham Hxh)].
  - exact Hw.
  - exact Hk.
Qed.

#[using="Type"] Lemma Pm_rgfront : forall i k, Pm k -> Pm (MRgFront i k).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros i k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  set (S' := with_rgs' S (nth_front i (s_rgs S))) in *.
  assert (Hn : s_next S' = s_next S) by reflexivity.
  apply (IH S' M FS sh a finals Hck model0 mem0 E ms model).
  - exact (den_rgs_front segs LIMIT model0 mem0 E S M ms model i Hd).
  - exact (INV_same mem0 E S S' M FS model0 Hi Hn).
  - exact (HAX_same E S S' M a mem0 HX Hn).
  - rewrite Hn. exact Hw.
  - intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin Hd'' Hi'' Hx'' Hw'' Ha''. rewrite Hn in Ha''.
    exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin Hd'' Hi'' Hx'' Hw'' Ha'').
Qed.
#[using="Hp4 HA_mod"] Lemma Pm_allowfront : forall i k, Pm k -> Pm (MAllowFront i k).
Proof. LiaFast.lf_pins (fun (Hp4 HA_mod : LiaFast.U) => LiaFast.u0).
  intros i k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (front_ok LIMIT S M i) eqn:Hok; [|discriminate]. destruct (amod M _ a) eqn:Ham; [|discriminate].
  set (M' := with_allow M (nth_front i (sm_allow M))) in *.
  apply (IH S M' FS sh a finals Hck model0 mem0 E ms model).
  - exact (den_allow_front segs LIMIT model0 mem0 E S M ms model i Hd Hok).
  - exact (INV_agree mem0 E E S S M M' FS model0 Hi (agree_refl _ _) (Pos.le_refl _) eq_refl (dn_wf _ _ _ _ _ _ _ _ _ Hd)).
  - destruct HX as [Hxw Hxh]. split; [exact Hxw | exact (HA_mod E M M' a mem0 Ham Hxh)].
  - exact Hw.
  - exact Hk.
Qed.

(* [comment removed for export] *)
#[using="path0 data0 Hp4"] Lemma eqv_lin_den : forall E fs tq l, Forall (fact_ok E) fs -> lden E (eqv_lin fs tq l) = lden E l.
Proof. LiaFast.lf_pins (fun (path0 data0 Hp4 : LiaFast.U) => LiaFast.u0).
  intros E fs tq l HF. unfold eqv_lin. pose proof (irange_sound E fs (lsub l tq) HF) as Ir.
  destruct (irange fs (lsub l tq)) as [lo hi] eqn:Hir. cbn [fst snd] in Ir. destruct (Z.eqb lo 0 && Z.eqb hi 0)%bool eqn:Heq; [|reflexivity].
  apply andb_prop in Heq as [H1 H2]. apply Z.eqb_eq in H1, H2. subst lo hi.
  assert (H0 : bv_unsigned (lden E (lsub l tq)) = 0) by lia.
  rewrite lden_lsub, bv_sub_unsigned in H0. unfold bv_wrap, bv_modulus in H0. change (2 ^ Z.of_N 64) with two64 in H0.
  pose proof (u_range E l) as Rl. pose proof (u_range E tq) as Rt.
  apply bv_eq.
  assert (Hd : (bv_unsigned (lden E l) - bv_unsigned (lden E tq)) mod two64 = 0) by exact H0.
  apply Z.mod_divide in Hd; [|unfold two64; lia]. destruct Hd as [q Hq]. unfold two64 in *. nia.
Qed.
#[using="path0 data0 Hp4"] Lemma regs_eqv : forall E fs tq R regs, Forall (fact_ok E) fs -> regs_ok E R regs -> regs_ok E (tmap (eqv_lin fs tq) R) regs.
Proof. LiaFast.lf_pins (fun (path0 data0 Hp4 : LiaFast.U) => LiaFast.u0).
  intros E fs tq R regs HF HR r. rewrite (HR r). unfold rget. destruct (rkey r) as [p|p|] eqn:Hk; try reflexivity;
    rewrite tget_tmap; destruct (tget _ R) as [l|]; cbn [option_map]; try reflexivity; symmetry; apply eqv_lin_den; exact HF.
Qed.
#[using="path0 data0 Hp4"] Lemma den_regeqv : forall model0 mem0 E S M ms model tq, DEN segs LIMIT model0 mem0 E S M ms model -> DEN segs LIMIT model0 mem0 E (regeqv S tq) M ms model.
Proof. LiaFast.lf_pins (fun (path0 data0 Hp4 : LiaFast.U) => LiaFast.u0).
  intros model0 mem0 E S M ms model tq Hd. destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  constructor; try assumption.
  intros E' Ha'. destruct (Hsd E' Ha') as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  unfold sden0; cbn [s_pc s_regs s_rgs s_facts s_resv regeqv]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [exact (regs_eqv E' _ tq _ _ H7 H4)|]. split; [exact H5|]. split; [exact H6|]. split; [exact H7 | exact H8].
Qed.
#[using="Hp4"] Lemma Pm_regeq : forall tq k, Pm k -> Pm (MRegEq tq k).
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros tq k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (lwf (s_next S) tq); [|discriminate].
  assert (Hn : s_next (regeqv S tq) = s_next S) by reflexivity.
  apply (IH (regeqv S tq) M FS sh a finals Hck model0 mem0 E ms model).
  - exact (den_regeqv model0 mem0 E S M ms model tq Hd).
  - exact (INV_same mem0 E S _ M FS model0 Hi Hn).
  - exact (HAX_same E S _ M a mem0 HX Hn).
  - rewrite Hn. exact Hw.
  - intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin Hd'' Hi'' Hx'' Hw'' Ha''. rewrite Hn in Ha''.
    exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin Hd'' Hi'' Hx'' Hw'' Ha'').
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma frz_same_msubst_m : forall E σ MP m0 m1, frz_same (ecomp E σ) MP m0 m1 -> frz_same E (msubst σ MP) m0 m1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E σ MP m0 m1 H p Hp w Hw. unfold msubst in Hp. cbn [sm_frz] in Hp. apply in_map_iff in Hp as (q & <- & Hq).
  unfold ppsubst in Hw. cbn [fst snd] in Hw. rewrite <- !uE_sub in Hw. exact (H q Hq w Hw).
Qed.
(* [comment removed for export] *)
#[using="Hp4"] Lemma INV_cov : forall mem0 mem0' E E' S S' M M' FS model0,
  INV mem0 E S M FS model0 -> agree (s_next S) E E' -> (s_next S <= s_next S')%positive -> frz_covs E M E' M' ->
  frz_same E M mem0 mem0' -> INV mem0' E' S' M' FS model0.
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros mem0 mem0' E E' S S' M M' FS model0 Hi Ha Hle Hcov Hfsm.
  destruct Hi as (Hpv & Hfsw & Hfr & Hm0 & Hlen & Hlk & Hfs0 & Hfds & Hc1 & Hc2 & Hdv).
  assert (Hpv' : lden E' pv = lden E pv) by exact (lden_agree_wf _ E E' pv Hpv Ha).
  split; [exact (lwf_mono _ _ _ Hle Hpv)|]. split.
  { destruct FS as [|off FL| | |off FL]; [reflexivity| |reflexivity|reflexivity|]; (cbn [fs_wf] in Hfsw |- *; apply andb_prop in Hfsw as [H1 H2];
    apply andb_true_intro; split; [exact (lwf_mono _ _ _ Hle H1) | exact (lwf_mono _ _ _ Hle H2)]). }
  split.
  { intros Hdr k Hk. destruct (Hfr Hdr k Hk) as (p & Hp & Hr). destruct (Hcov p Hp) as (p' & Hp' & H1 & H2). exists p'. split; [exact Hp'|].
    rewrite H1, H2. unfold uE in *. rewrite Hpv'. exact Hr. }
  split.
  { split; [intros Hdr k Hk; rewrite Hpv'; destruct (Hfr Hdr k Hk) as (p & Hp & Hr); rewrite (Hfsm p Hp _ Hr); exact (proj1 Hm0 Hdr k Hk)|].
    intros Hdr w Hw. rewrite Hpv' in Hw. destruct (proj2 Hm0 Hdr w Hw) as [(p & Hp & Hr) Hne]. split; [|rewrite (Hfsm p Hp _ Hr); exact Hne].
    destruct (Hcov p Hp) as (p' & Hp' & H1 & H2). exists p'. split; [exact Hp'|]. rewrite H1, H2. exact Hr. }
  split; [rewrite Hpv'; exact Hlen|]. split; [exact Hlk|]. split; [exact Hfs0|].
  split; [|split; [exact Hc1 | split; [exact Hc2 | exact (hv_inv_step E E' S S' Hdv Ha Hle)]]].
  destruct FS as [|off FL| | |off FL]; [exact Hfds| |exact I|exact Hfds|];
  cbn [fs_wf] in Hfsw; apply andb_prop in Hfsw as [W1 W2];
  rewrite (lden_agree_wf _ E E' _ W1 Ha), (lden_agree_wf _ E E' _ W2 Ha); exact Hfds.
Qed.

(* [comment removed for export] *)
#[using="Hp4 aeqb_eq HA_agree HA_msub HMUse HA_use"] Lemma Pm_use : forall j nb k, Pm k -> Pm (MUse j nb k).
Proof. LiaFast.lf_pins (fun (Hp4 aeqb_eq HA_agree HA_msub HMUse HA_use : LiaFast.U) => LiaFast.u0).
  intros j nb k IH S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (nth_error subs j) as [[[[T MT] aT] fins]|] eqn:Hj; [|discriminate].
  set (σ := matchLA S M (alins a) T MT (alins aT)) in *.
  destruct (entails S T σ && state_wf T && sm_wf (s_next T) MT && agok MT aT && sm_eqbm σ MT M && aeqb (asub σ aT) a &&
            Pos.leb nb (s_next T) && Pos.leb nb (s_next S) && fixed_below σ nb && use_bwf σ nb (s_next T) (s_next S) &&
            awf (s_next T) aT)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hc HawT]. apply andb_prop in Hc as [Hc Hbw]. apply andb_prop in Hc as [Hc Hpf]. rewrite fixed_below_eq in Hpf. apply andb_prop in Hc as [Hc HnbS].
  apply andb_prop in Hc as [Hc HnbT]. apply andb_prop in Hc as [Hc Hae]. apply andb_prop in Hc as [Hc Hsm]. apply andb_prop in Hc as [Hc Hagk].
  apply andb_prop in Hc as [Hc HmwT]. apply andb_prop in Hc as [Hent HwT].
  apply Pos.leb_le in HnbS, HnbT. apply sm_eqbm_eq in Hsm as [Hsm Hmk]. apply aeqb_eq in Hae.
  pose proof (use_bwf_spec σ nb (s_next T) (s_next S) Hbw) as Hbw'.
  assert (Hsubs : subs <> []) by (intros H; rewrite H in Hj; destruct j; discriminate).
  assert (Hd0 : DEN segs LIMIT model0 mem0 E S (msubst σ MT) ms model) by (rewrite Hsm; exact Hd).
  pose proof (den_ent_M segs LIMIT model0 mem0 E S T MT ms model σ Hd0 Hent HwT HmwT Hmk) as HdT.
  assert (HAT : HA (ecomp E σ) MT aT mem0).
  { apply (HA_msub E σ MT aT mem0 Hagk). rewrite Hsm, Hae. exact (proj2 HX). }
  apply (HMUse j T MT aT fins Hj model0 mem0 (ecomp E σ) ms model _ HdT HawT HAT).
  intros F MF aF mem0' E' ms' model' Hin HdF HawF HAF Ha' Hcov' Hfs'.
  destruct (all_some_spec _ _ _ Hck (F, MF, aF) Hin) as (o & Ho & Hsub'). cbv beta zeta in Ho.
  set (σ' := use_sig σ nb (s_next T) (s_next F) (s_next S)) in *.
  set (nx := use_next nb (s_next F) (s_next S)) in *.
  destruct (Pos.leb (s_next T) (s_next F) && awf nx (asub σ' aF) && marks_ok σ' (sm_maps MF))%bool eqn:Hb; [|discriminate].
  apply andb_prop in Hb as [Hb Hmk']. apply andb_prop in Hb as [HTF Hwa'']. apply Pos.leb_le in HTF.
  set (E2 := use_env E E' nb (s_next S)).
  assert (He2 : forall x, (x < s_next F)%positive -> lden E2 (svar σ' x) = E' x)
    by (intros x Hx; exact (use_sig_ecomp E E' σ nb (s_next T) (s_next F) (s_next S) x HnbT HnbS HTF Hpf Hbw' Ha' Hx)).
  assert (Hag2 : agree (s_next F) E' (ecomp E2 σ')) by (intros x Hx; unfold ecomp; symmetry; exact (He2 x Hx)).
  assert (Hsw : sig_wf σ' (s_next F) nx) by exact (use_sig_wf σ nb (s_next T) (s_next F) (s_next S) HnbS ltac:(lia) Hbw').
  pose proof (den_agree segs LIMIT model0 mem0' E' (ecomp E2 σ') F MF ms' model' HdF Hag2) as HdF2.
  pose proof (den_subst segs LIMIT model0 mem0' E2 σ' F MF nx ms' model' Hsw Hmk' HdF2) as HdS.
  assert (HnS : (s_next S <= nx)%positive) by exact (use_next_ge nb (s_next F) (s_next S) ltac:(lia)).
  assert (HaE2 : agree (s_next S) E E2) by exact (use_env_agree E E' nb (s_next S)).
  assert (HwfF : sm_wf (s_next F) MF = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ HdF).
  assert (Hcov2 : frz_covs E M E2 (msubst σ' MF)).
  { rewrite <- Hsm. apply (frz_covs_trans E (msubst σ MT) (ecomp E σ) MT E2 (msubst σ' MF) (frz_covs_msubst E σ MT)).
    apply (frz_covs_trans (ecomp E σ) MT E' MF E2 (msubst σ' MF) Hcov'). exact (frz_covs_inst E' E2 σ' (s_next F) MF HwfF He2). }
  assert (Hfs2 : frz_same E M mem0 mem0') by (rewrite <- Hsm; exact (frz_same_msubst_m E σ MT mem0 mem0' Hfs')).
  pose proof (INV_cov mem0 mem0' E E2 S (ssubst σ' nx F) M (msubst σ' MF) FS model0 Hi HaE2 HnS Hcov2 Hfs2) as HiS.
  assert (HXS : HAX E2 (ssubst σ' nx F) (msubst σ' MF) (asub σ' aF) mem0').
  { split; [exact Hwa''|]. apply (HA_use Hsubs E2 σ' MF aF mem0'). exact (HA_agree (s_next F) E' _ MF aF mem0' HwfF HawF Hag2 HAF). }
  rewrite <- (shp_den_agree (s_next S) E E2 sh Hw HaE2).
  apply (IH (ssubst σ' nx F) (msubst σ' MF) FS sh (asub σ' aF) o Ho model0 mem0' E2 ms' model' HdS HiS HXS (shp_wf_mono _ _ sh HnS Hw)).
  intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin'' Hd'' Hi'' Hx'' Hw'' Ha''.
  exact (Hk S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' (Hsub' _ Hin'') Hd'' Hi'' Hx'' Hw''
           (agree_trans _ E E2 E'' HaE2 (agree_mono _ _ E2 E'' HnS Ha''))).
Qed.

(* [comment removed for export] *)
#[using="Hp4"] Lemma INV_entM0 : forall mem0 E S P MP σ FS FP model0 n0,
  INV mem0 E S (msubst σ MP) FS model0 -> params_fixed σ (pos_below n0) = true ->
  pv_okb pv hv n0 = true -> fs_ent FS FP σ = true -> fs_wf (s_next P) FP = true -> (n0 <= s_next P)%positive ->
  INV mem0 (ecomp E σ) P MP FP model0.
Proof. LiaFast.lf_pins (fun (Hp4 : LiaFast.U) => LiaFast.u0).
  intros mem0 E S P MP σ FS FP model0 n0 Hi Hpf Hpvk Hfe Hfw Hn1. unfold pv_okb in Hpvk. apply andb_prop in Hpvk as [Hpv0 Hhv0].
  set (E0 := ecomp E σ).
  assert (Ha : agree n0 E E0) by exact (agree_params n0 E σ Hpf).
  destruct Hi as (Hpv & Hfsw & Hfr & Hm0 & Hlen & Hlk & Hfs0 & Hfds & Hc1 & Hc2 & Hdv).
  assert (Hpv' : lden E0 pv = lden E pv) by exact (lden_agree_wf _ E E0 pv Hpv0 Ha).
  split; [exact (lwf_mono _ _ _ Hn1 Hpv0)|]. split; [exact Hfw|].
  split.
  { intros Hdr k Hk. destruct (Hfr Hdr k Hk) as (p & Hp & Hr). unfold msubst in Hp. cbn [sm_frz] in Hp.
    apply in_map_iff in Hp as (q & <- & Hq). exists q. split; [exact Hq|].
    unfold ppsubst in Hr. cbn [fst snd] in Hr. rewrite Hpv'. unfold E0. rewrite !uE_sub. exact Hr. }
  split.
  { split; [intros Hdr k Hk; rewrite Hpv'; exact (proj1 Hm0 Hdr k Hk)|].
    intros Hdr w Hw. rewrite Hpv' in Hw. destruct (proj2 Hm0 Hdr w Hw) as [(p & Hp & Hr) Hne]. split; [|exact Hne].
    unfold msubst in Hp. cbn [sm_frz] in Hp. apply in_map_iff in Hp as (q & <- & Hq). exists q. split; [exact Hq|].
    unfold ppsubst in Hr. cbn [fst snd] in Hr. unfold E0. rewrite !uE_sub. exact Hr. }
  split; [rewrite Hpv'; exact Hlen|]. split; [exact Hlk|]. split; [exact Hfs0|].
  split; [|split; [exact Hc1 | split; [exact Hc2 | exact (hv_inv_agree n0 E E0 S P Hdv Ha Hhv0 Hn1)]]].
  destruct FS as [|off FL| | |off FL]; destruct FP as [|off' FL'| | |off' FL']; cbn [fs_ent] in Hfe; try discriminate; [exact Hfds| |exact I|exact Hfds| ];
  (apply andb_prop in Hfe as [Ho Hf]; apply lin_eqb_eq in Ho, Hf;
   unfold E0; rewrite <- !lden_lsubst; rewrite <- Ho, <- Hf; exact Hfds).
Qed.
(* [comment removed for export] *)
#[using="Hp4 aeqb_eq HA_msub HCont"] Lemma Pm_cont : forall j nb, Pm (MCont j nb).
Proof. LiaFast.lf_pins (fun (Hp4 aeqb_eq HA_msub HCont : LiaFast.U) => LiaFast.u0).
  intros j nb S M FS sh a finals Hck model0 mem0 E ms model Hd Hi HX Hw Hk. cbn [mcheck] in Hck.
  destruct (nth_error conts j) as [[[[[T MT] FST] shT] aT]|] eqn:Hj; [|discriminate].
  set (σ := matchLA S M (alins a) T MT (alins aT)) in *.
  destruct (entails S T σ && state_wf T && sm_wf (s_next T) MT && agok MT aT && sm_eqbm σ MT M && aeqb (asub σ aT) a &&
            fixed_below σ nb && Pos.leb nb (s_next T) && pv_okb pv hv nb && fs_ent FS FST σ && fs_wf (s_next T) FST &&
            shp_ent sh shT σ && shp_wf (s_next T) shT && awf (s_next T) aT)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hc HawT]. apply andb_prop in Hc as [Hc HwT']. apply andb_prop in Hc as [Hc Hse]. apply andb_prop in Hc as [Hc Hfw].
  apply andb_prop in Hc as [Hc Hfe]. apply andb_prop in Hc as [Hc Hpv0]. apply andb_prop in Hc as [Hc HnT]. apply andb_prop in Hc as [Hc Hpf]. rewrite fixed_below_eq in Hpf.
  apply andb_prop in Hc as [Hc Hae]. apply andb_prop in Hc as [Hc Hsm]. apply andb_prop in Hc as [Hc Hagk]. apply andb_prop in Hc as [Hc HmwT].
  apply andb_prop in Hc as [Hent HswT].
  apply Pos.leb_le in HnT. apply sm_eqbm_eq in Hsm as [Hsm Hmk]. apply aeqb_eq in Hae.
  assert (Hd' : DEN segs LIMIT model0 mem0 E S (msubst σ MT) ms model)
    by (replace (msubst σ MT) with M by (symmetry; exact Hsm); exact Hd).
  assert (Hi' : INV mem0 E S (msubst σ MT) FS model0)
    by (replace (msubst σ MT) with M by (symmetry; exact Hsm); exact Hi).
  assert (HA' : HA E (msubst σ MT) (asub σ aT) mem0)
    by (replace (msubst σ MT) with M by (symmetry; exact Hsm); replace (asub σ aT) with a by (symmetry; exact Hae); exact (proj2 HX)).
  pose proof (den_ent_M segs LIMIT model0 mem0 E S T MT ms model σ Hd' Hent HswT HmwT Hmk) as HdT.
  pose proof (INV_entM0 mem0 E S T MT σ FS FST model0 nb Hi' Hpf Hpv0 Hfe Hfw HnT) as HiT.
  assert (HXT : HAX (ecomp E σ) T MT aT mem0) by exact (conj HawT (HA_msub E σ MT aT mem0 Hagk HA')).
  rewrite <- (shp_den_ent E sh shT σ Hse).
  exact (HCont j (T, MT, FST, shT, aT) Hj model0 mem0 (ecomp E σ) ms model HdT HiT HXT HwT').
Qed.

#[using="Hwx Hsegb Hoff Hfs Hrespos Hreswf Ht Himg Hect Hp1 Hp2 Hp3 Hp4 Hp5 HFL HFLhi Hseg awf_mono aeqb_eq HA_nil HA_agree Hanode HA_copy HA_msub HA_mod HMUse HA_use HCont"] Theorem mchain_sound : forall ch, Pm ch.
Proof. LiaFast.lf_pins (fun (Hwx Hsegb Hoff Hfs Hrespos Hreswf Ht Himg Hect Hp1 Hp2 Hp3 Hp4 Hp5 HFL HFLhi Hseg awf_mono aeqb_eq HA_nil HA_agree Hanode HA_copy HA_msub HA_mod HMUse HA_use HCont : LiaFast.U) => LiaFast.u0).
  apply (@mchain_mut N Pm Qm).
  - exact Pm_end.
  - intros c k IH. exact (Pm_chain c k IH).
  - intros depth p ks IH. exact (Pm_segk depth p ks IH).
  - intros kerr IHe kok IHo. exact (Pm_open kerr kok IHe IHo).
  - intros i o ka IHa kb IHb. exact (Pm_read i o ka kb IHa IHb).
  - intros k IH. exact (Pm_close k IH).
  - intros fd cmd k IH. exact (Pm_ioctl fd cmd k IH).
  - intros B0 k IH. exact (Pm_writev B0 k IH).
  - exact Pm_exit.
  - intros P n0 FP shP k IH. exact (Pm_weaken P n0 FP shP k IH).
  - intros P n0 FP shP meas body IHb ks IHk. exact (Pm_loop P n0 FP shP meas body ks IHb IHk).
  - intros nk k IH. exact (Pm_call nk k IH).
  - exact Pm_void.
  - intros body IHb jpc k IHk. exact (Pm_join body jpc k IHb IHk).
  - intros zk body IHb ks IHk. exact (Pm_loopW zk body ks IHb IHk).
  - intros k IH. exact (Pm_pop k IH).
  - intros k1 IH1 k2 IH2. exact (Pm_alt k1 k2 IH1 IH2).
  - intros kerr IHe kok IHo. exact (Pm_opendir kerr kok IHe IHo).
  - intros k IH. exact (Pm_readdir k IH).
  - intros B0 k IH. exact (Pm_writev2 B0 k IH).
  - intros F0 F1 k IH. exact (Pm_writevC F0 F1 k IH).
  - intros k IH. exact (Pm_writev0 k IH).
  - intros ka IHa kb IHb. exact (Pm_sel ka kb IHa IHb).
  - intros i o k ka IHa kb IHb. exact (Pm_readH i o k ka kb IHa IHb).
  - intros op k IH. exact (Pm_sep op k IH).
  - intros l c ka IHa kb IHb. exact (Pm_split l c ka kb IHa IHb).
  - intros l k r0 ka IHa kb IHb. exact (Pm_splitB l k r0 ka kb IHa IHb).
  - intros ka IHa kb IHb. exact (Pm_selB ka kb IHa IHb).
  - intros j c ka IHa kb IHb. exact (Pm_splitG j c ka kb IHa IHb).
  - intros k IH. exact (Pm_concr k IH).
  - intros b o ka IHa kb IHb. exact (Pm_readB b o ka kb IHa IHb).
  - intros b o k ka IHa kb IHb. exact (Pm_readHB b o k ka kb IHa IHb).
  - intros r c ka IHa kb IHb. exact (Pm_splitR r c ka kb IHa IHb).
  - intros k IH. exact (Pm_concf k IH).
  - intros body IHb jpc shj k IHk. exact (Pm_joinS body jpc shj k IHb IHk).
  - intros Pn F0 F1 k IH. exact (Pm_writevL Pn F0 F1 k IH).
  - intros n k IH. exact (Pm_splitP n k IH).
  - intros kerr IHe kok IHo. exact (Pm_openLB kerr kok IHe IHo).
  - intros b o k IH. exact (Pm_readLB b o k IH).
  - intros nk xs k IH. exact (Pm_gc nk xs k IH).
  - intros zk body IHb ks IHk. exact (Pm_loopW0 zk body ks IHb IHk).
  - intros body IHb jpc k IHk. exact (Pm_joinL body jpc k IHb IHk).
  - intros gen body IHb ks IHk. exact (Pm_loopG gen body ks IHb IHk).
  - intros j nb k IH. exact (Pm_use j nb k IH).
  - intros j nb. exact (Pm_cont j nb).
  - intros gen body IHb jpc k IHk. exact (Pm_joinG gen body jpc k IHb IHk).
  - intros i k IH. exact (Pm_blobnil i k IH).
  - intros i k IH. exact (Pm_blobadd i k IH).
  - intros j z k IH. exact (Pm_alloww j z k IH).
  - intros i k IH. exact (Pm_rgfront i k IH).
  - intros i k IH. exact (Pm_allowfront i k IH).
  - intros t0 k IH. exact (Pm_regeq t0 k IH).
  - exact Qm_nil.
  - intros b sys k IHk r IHr. exact (Qm_cons b sys k r IHk IHr).
Qed.

End Sound.

(* [comment removed for export] *)
Lemma subs_nil_ok : forall {A : Type} (P : sst -> smodel -> A -> list (sst * smodel * A) -> Prop) j T MT aT fins,
  nth_error ([] : list (sst * smodel * A * list (sst * smodel * A))) j = Some (T, MT, aT, fins) -> P T MT aT fins.
Proof. intros A P j T MT aT fins H. destruct j; discriminate H. Qed.
Lemma subs_nil_use : forall {A : Type} (Q : Prop), ([] : list (sst * smodel * A * list (sst * smodel * A))) <> [] -> Q.
Proof. intros A Q H. exfalso. exact (H eq_refl). Qed.

(* [comment removed for export] *)
Lemma conts_nil_ok : forall {X : Type} (P : X -> Prop) j c, nth_error ([] : list X) j = Some c -> P c.
Proof. intros X P j c H. destruct j; discriminate H. Qed.

(* [comment removed for export] *)
Lemma HFL_of : forall lo hi d : Z, lo <= d <= hi -> lo <= d /\ (lo <= hi -> hi < FLT -> d <= hi).
Proof. intros lo hi d H. split; [lia | intros _ _; lia]. Qed.
(* [comment removed for export] *)
Lemma HFL_lb : forall lo d : Z, lo <= d -> lo <= d /\ (lo <= FLT -> FLT < FLT -> d <= FLT).
Proof. intros lo d H. split; [exact H | intros _ Hc; exfalso; lia]. Qed.
