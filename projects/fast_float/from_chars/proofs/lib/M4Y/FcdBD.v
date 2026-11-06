(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxImg FxPlan FxLoop FxFrame FxDrv FxCall FxWork FxWorkX FxGenA FxGenX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWorkX OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxGenA OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxGenX.
From OSSVerify.Proofs.fast_float.from_chars.lib.HX Require Import HxGen.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXB Require HxGenFp HxSplitB.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXB Require HxGenFp.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXB Require HxRebaseB.
Import OSSVerify.Proofs.fast_float.from_chars.lib.HXB.HxGenFp OSSVerify.Proofs.fast_float.from_chars.lib.HXB.HxSplitB OSSVerify.Proofs.fast_float.from_chars.lib.HXB.HxGenFp.HxLoopR OSSVerify.Proofs.fast_float.from_chars.lib.HXB.HxRebaseB.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_tmpl OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.

Module M4B_infd.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxImg FxPlan FxLoop FxFrame FxDrv FxCall FxWork.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
Local Open Scope Z_scope.

Fixpoint regs_pat (k : nat) (acc : tree lin) : tree lin :=
  match k with O => acc | S k' => regs_pat k' (tset (Pos.of_succ_nat k) (lvar (100 + Pos.of_nat k)) acc) end.
Definition rk (r : Z) : positive := bv_key (Z_to_bv 5 r).
Fixpoint rsets (R : tree lin) (l : list (Z * lin)) : tree lin :=
  match l with [] => R | (k, v) :: l' => rsets (rset R (rk k) v) l' end.
Fixpoint mk_imgs_acc (rs : list (Z * nat)) (t : tree Z) : tree Z :=
  match rs with [] => t | (lo, n) :: r => mk_imgs_acc r (mk_img_acc BSEGS n (Z.shiftr lo 3) t) end.
Lemma mk_imgs_acc_ok : forall rs t, Forall (fun r => 0 <= fst r) rs -> img_ok BSEGS t -> img_ok BSEGS (mk_imgs_acc rs t).
Proof.
  intros rs. induction rs as [|[lo n] rs IH]; intros t Hf Ht; cbn [mk_imgs_acc]; [exact Ht|].
  apply Forall_cons_iff in Hf as [Hx Hf']. cbn [fst] in Hx. apply IH; [exact Hf'|].
  apply mk_img_acc_ok; [apply Z.shiftr_nonneg; lia | exact Ht].
Qed.
Definition bk8 (z : Z) : list bval := List.map (fun j => BK (Z.land (Z.shiftr z (8 * Z.of_nat j)) 255)) (seq 0 8).

Definition TM : tree xi := Eval vm_compute in mk_tbl BSEGS 0x92788 210.
Definition IMGR : list (Z * nat) := [(0xde490, 1%nat); (0x227e0, 4%nat)].
Definition IMGW : tree Z := Eval vm_compute in mk_imgs_acc IMGR TEmpty.
Definition B : Z := 2 ^ 46.
Definition SHB : Z := 0x7fff8000.
Definition T := lvar 1. Definition L := lvar 2. Definition XV := lvar 3. Definition SP := lvar 4. Definition RA := lvar 5.
Definition FMT := lvar 6. Definition Y0 := lvar 7. Definition Y1 := lvar 8.
Definition TL := ladd T L. Definition V := XV. Definition VS := lvar 29.
Definition R0 : tree lin := rsets (regs_pat 31 TEmpty) [(10, T); (11, TL); (12, V); (13, FMT); (1, RA); (2, SP)].
Definition F0 : list fact :=
  [ FRange (lsub T (lscale 8 Y0)) 0 256; FRange (lsub (lscale 8 Y1) TL) 1 256; FRange (lsub Y1 Y0) 1 64; FRange L 1 128;
    FRange T 6537216 140737488355072; FRange Y0 800288 17592186044416; FRange Y1 800288 17592186044416; FRange V 17592186011648 140737488355320; FMod V 3 0; FRange (lsub (lscale 8 (lsub VS (lconst SHB))) V) 0 0; FRange VS 2201170702336 17594333495296;
    FRange SP 17592186011904 140737488355328; FMod SP 4 0; FBits FMT 18446744073709551610 0 ].
Definition RGS : list region :=
  [ RG T L RT TEmpty;                                    (* [comment removed for export] *)
    RG (ladd Y0 (lconst SHB)) (lsub Y1 Y0) RZ TEmpty;    (* [comment removed for export] *)
    RGz V 8 RW TEmpty;                                   (* [comment removed for export] *)
    RGz VS 1 RZ TEmpty;                                  (* [comment removed for export] *)
    RGz (laddc SP (-16)) 16 RW TEmpty;                   (* [comment removed for export] *)
    RGz (lconst 0xde490) 8 RO TEmpty;                    (* [comment removed for export] *)
    track (RGz (lconst 0xe6678) 8 RW TEmpty) 0 (bk8 SHB); (* [comment removed for export] *)
    RGz (lconst 0x227e0) 32 RO TEmpty ].                 (* [comment removed for export] *)
Definition P0 : sst := SST 0x92788 R0 RGS F0 200 RNone.

(* [comment removed for export] *)
Definition LV := Eval vm_compute in fx_explore TM IMGW 400 [0x928d8] P0 [].
Definition LA := Eval vm_compute in nth 0 (List.filter (fun s => Z.eqb (s_pc s) 0x928d8) LV) P0.
Definition PP := lvar 300.
Definition LSN_PL : sst := Eval vm_compute in
  SST 0x928d8 (rsets (s_regs LA) [(12, PP); (13, PP); (7, lvar 301); (28, lvar 302); (10, lvar 303)]) (s_rgs LA)
    (FRange (lsub TL PP) 1 128 :: FRange (lsub PP T) 0 128 :: F0) 310 RNone.
Definition LSN : loopspec := LS LSN_PL (lsub TL PP) (map Pos.of_nat (seq 1 299)) 400 [].
Definition NODES : list (Z * waction) := [ (0x928d8, WTmpl LSN_PL (PLoop LSN [])) ].
Definition P0RUN : plan := PRun 400 [0x928d8] [].

Definition KEEPR : list Z := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Fixpoint qregs (R : tree lin) (k : nat) (nx : positive) (acc : tree lin) : tree lin :=
  match k with
  | O => acc
  | S k' => qregs R k' nx (tset (Pos.of_succ_nat k)
                                (if existsb (Z.eqb (Z.of_nat k)) KEEPR then rget R (Pos.of_succ_nat k) else lvar (nx + Pos.of_nat k)) acc)
  end.
Definition drop_cont (R : region) : region := RG (rg_base R) (rg_size R) (rg_kind R) TEmpty.
(* [comment removed for export] *)
Definition Q : sst := SST 0 (qregs R0 31 200 TEmpty) (map_i (fun i R => if Nat.eqb i 6 then R else drop_cont R) 0 RGS) F0 240 RNone.
Definition RETS : list Z := [0x92a40].
From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 cert_refl_vm (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl _ $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Set Default Proof Mode "Ltac2".
Lemma INF_cert : all_fin (fin_q Q RETS (s_next P0)) (wstart TM IMGW (vars_below (s_next P0)) 10 P0 P0RUN NODES) = true.
Proof. cert_refl_vm constr:(true). Qed.
Set Default Proof Mode "Classic".
Lemma TM_eq : TM = mk_tbl BSEGS 0x92788 210.
Proof. vm_compute. reflexivity. Qed.
Lemma IMGW_ok : img_ok BSEGS IMGW.
Proof.
  change (img_ok BSEGS (mk_imgs_acc IMGR TEmpty)).
  apply mk_imgs_acc_ok; [repeat constructor; cbn; lia|]. intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.
Lemma RETS_ok : Forall (is_ret BSEGS) RETS.
Proof. unfold RETS. repeat constructor. exists (Z_to_bv 32 0x00008067). (split; [|split]); vm_refl_bv. Qed.
Theorem infd_ok : fn_ok BSEGS P0 Q RETS.
Proof.
  apply (fn_ok_of_wcert BSEGS TM IMGW 10 P0RUN NODES P0 Q RETS ltac:(rewrite TM_eq; apply mk_tbl_ok) IMGW_ok INF_cert).
  - intros P0' Q' H. cbn in H. destruct H.
  - intros fh H. cbn in H. destruct H.
  - intros P0' Q' H. cbn in H. destruct H.
  - intros P0' Q' pcQ H. cbn in H. destruct H.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - exact RETS_ok.
Qed.
End M4B_infd.

From OSSVerify.Proofs.fast_float.from_chars.lib.M4Y Require SpdBD.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition TM : tree xi := Eval vm_compute in mk_tbl BSEGS 0x90f3c 1555.
Definition IMGR : list (Z * nat) := [(0xde490, 1%nat); (0x22800, 32%nat); (0x10300, 0x30%nat); (0x229e0, 1302%nat); (0x25468, 0x2e%nat); (0x227e0, 4%nat)].
Definition IMGW : tree Z := Eval vm_compute in mk_imgs_acc IMGR TEmpty.
Definition FR0 : tree lin := rsets (regs_pat 31 TEmpty) [(10, T); (11, TL); (12, V); (13, FMT); (14, lconst 42949673006); (1, RA); (2, SP); (4, lconst TPV)].
Definition FF0 : list fact :=
  [ FRange (lsub T (lscale 8 Y0)) 0 256; FRange (lsub (lscale 8 Y1) TL) 1 256; FRange (lsub Y1 Y0) 1 64; FRange L 0 128;
    FRange Y0 ((IMG_END - 256) / 8) (KTOP / 8); FRange Y1 ((IMG_END - 256) / 8) (KTOP / 8);
    FRange (laddc SP (-4288)) KHI (KTOP - 4288); FMod SP 5 0; FMod RA 1 0;
    FRange (lsub (laddc SP (-4288)) (laddc FS 0xb09000)) 0 KTOP; FRange (lsub (laddc SP (-4288)) TL) 0 KTOP;
    FRange (lsub T (fsc AR4)) 0x200000 (2 ^ 64 - 128); FRange (lsub T (fsc 0x9000)) 0 (2 ^ 64 - 0x9000 - 256);
    spsh_fact 4288; FRange SPSH (SHB + KHI / 8) (SHB + (KTOP - 4288) / 8);
    FBits FMT 18446744073709551610 0; FRange FMT 1 5 ]
  ++ List.flat_map (fun '(X, n) => [FRange (lsub X (laddc SP 128)) 0 (2 ^ 64 - 4416 - n)]) [(CTX, 160); (THR, 80); (BLK, 32)]
  ++ two_class T 256 ++ v_facts ++ fks4_facts ++ rt_facts.
Definition FRGS : list region := SpdBD.RGS.
Definition FP0 : sst := SST 0x90f3c FR0 FRGS FF0 200 RNone.
(* [comment removed for export] *)
Definition CALLS : list Z := [0x92788; 0x92ad0].
Definition FRETS : list Z := [0x92440; 0x92a40; 0x945e0].
(* [comment removed for export] *)
Definition HEADS : list Z := [0x91454; 0x91738; 0x91968; 0x91b30; 0x91be8].
Definition NPCS : list Z := [0x912e4; 0x9168c; 0x91954; 0x919b8; 0x91830; 0x91a00; 0x91a84; 0x91af4; 0x91ab8; 0x91bcc; 0x91c38; 0x92074; 0x923bc; 0x92404; 0x91f7c].
(* [comment removed for export] *)
Definition RULEPCS : list Z := [0x919bc; 0x91bb4; 0x92240; 0x92324; 0x92444; 0x920b0].
Definition ALLST : list Z := NPCS ++ HEADS ++ CALLS ++ RULEPCS ++ [0x92440].
Definition PR : plan := PRun 400 ALLST [].
Definition ANC : list lin := [T; TL].
Definition JR (Ls : list sst) : sst := rjoin_r 200 ANC [] [] Ls.
Definition XNJ (pc : Z) : Z * xaction := (pc, xjoin JR (fun _ => PR)).
Definition XNL (pc : Z) : Z * xaction := (pc, xjoin JR (aloop TM IMGW ANC 400 ALLST)).
Definition XNG (pc : Z) (ks kp : Z) : Z * xaction :=
  (pc, xjoin JR (gloop TM IMGW (rk ks) (rk kp) TL [ladd Y0 (lconst SHB); ladd Y1 (lconst SHB)] [T; TL; lscale 8 Y0; lscale 8 Y1] 400 ALLST)).
(* [comment removed for export] *)
Definition add_rfacts (rfs : list (Z * Z * Z * Z)) (inv : sst) : sst :=
  SST (s_pc inv) (s_regs inv) (s_rgs inv)
      (List.map (fun '(k, sh, lo, hi) => FRange (laddc (rget (s_regs inv) (rk k)) sh) lo hi) rfs ++ s_facts inv) (s_next inv) (s_resv inv).
Definition aloop_rf (rfs : list (Z * Z * Z * Z)) (fuel : nat) (stops : list Z) (P : sst) : plan :=
  match aloop TM IMGW ANC fuel stops P with
  | PLoop (LS inv m ps fu st) ks => PLoop (LS (add_rfacts rfs inv) m ps fu st) ks
  | p => p
  end.
Definition XNLF (pc : Z) (rfs : list (Z * Z * Z * Z)) (fuel : nat) : Z * xaction := (pc, xjoin JR (aloop_rf rfs fuel ALLST)).
(* [comment removed for export] *)
Definition gen_rf (rfs : list (Z * Z * Z * Z)) (fuel : nat) (stops : list Z) (P : sst) : option loopspec :=
  match aloop_rf rfs fuel stops P with PLoop ls _ => Some ls | _ => None end.
Definition XNLR (pc : Z) (hooks : list (Z * (sst -> option sst))) (rfs : list (Z * Z * Z * Z)) (fuel : nat) : list (Z * xaction) :=
  [(pc, xjoin JR (fun _ => PFin)); (pc, XHand (hx_loopr TM IMGW (gen_rf rfs fuel ALLST) hooks))].
(* [comment removed for export] *)
Definition EXPH (pcb pcs : Z) : list (Z * (sst -> option sst)) := [(pcb, hook_bare [9]); (pcs, hook_sra63 TM)].
Definition XNI (pc : Z) : Z * xaction := (pc, XGenTs (fun here => (List.map (fun X => (xs_st X, xs_x X)) here, seq 0 (List.length here))) (fun _ => PR)).
Definition at_pc (pc : Z) (l : list xst) : list sst := List.map xs_st (List.filter (fun X => Z.eqb (s_pc (xs_st X)) pc) l).
Definition SUBR (pc : Z) : list (Z * xaction) := [(pc, XHand (hx_ssplitc pc 29 1)); XNI pc].   (* [comment removed for export] *)
Definition ADDR (pc : Z) : list (Z * xaction) := [(pc, XHand (hx_ssplitc pc 9 0)); XNI pc].    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition CS_INF : csite := mk_csite M4B_infd.P0 M4B_infd.Q KEEPK []
   [(VCopy 0, 0, RT); (VCopy 1, 0, RZ); (VCopy 2, 0, RW); (VCopy 3, 0, RZ); (VSub 5 88, 16, RW); (VSub 13 0x4490, 8, RO); (VSub 7 0, 8, RW); (VSub 6 0x127e0, 32, RO)].
Definition CS_SPD : csite := mk_csite SpdBD.P0 SpdBD.SPD_Q KEEPK [] (List.map (fun i => (VCopy i, 0, RW)) (seq 0 45)).
Definition XTAILS : list (Z * xaction) := [(0x92788, XFragK CS_INF 0x92a40); (0x92ad0, XFragK CS_SPD 0x945e0)].
Definition FQRGS : list region :=
  map_i (fun i R => if Nat.eqb i 15 then RGz (fsc 32) 8 RW TEmpty else if Nat.eqb i 25 then RGz (fsc 40) 8 RW TEmpty else R) 0 FRGS.
Definition FCD_Q : sst := SST 0 (regs_keep FR0 31 200 TEmpty) FQRGS FF0 250 RNone.
(* [comment removed for export] *)
Definition aloop_ff (ff : sst -> sst -> list fact) (fuel : nat) (stops : list Z) (P : sst) : plan :=
  match aloop TM IMGW ANC fuel stops P with
  | PLoop (LS inv m ps fu st) ks => PLoop (LS (SST (s_pc inv) (s_regs inv) (s_rgs inv) (ff P inv ++ s_facts inv) (s_next inv) (s_resv inv)) m ps fu st) ks
  | p => p
  end.
Definition XNLFF (pc : Z) (ff : sst -> sst -> list fact) (fuel : nat) : Z * xaction := (pc, xjoin JR (aloop_ff ff fuel ALLST)).
(* [comment removed for export] *)
Definition T48z : Z := 281474976710656.
Definition cnt_ff (kc kp : Z) (P inv : sst) : list fact :=
  let ci := rget (s_regs inv) (rk kc) in let pi := rget (s_regs inv) (rk kp) in
  let c0 := rget (s_regs P) (rk kc) in let p0 := rget (s_regs P) (rk kp) in
  [FRange (lsub (ladd ci pi) (ladd c0 p0)) 0 T48z; FRange (lsub c0 ci) 0 T48z].
Definition REBR (pc k : Z) : list (Z * xaction) := [(pc, XHand (hx_rebase pc k)); XNI pc].
Definition NODES1 : list (Z * xaction) :=
  [XNJ 0x912e4; XNL 0x91454; XNJ 0x9168c; XNG 0x91738 26 10; XNJ 0x91954; XNL 0x91968; XNJ 0x919b8] ++ SUBR 0x919bc
  ++ [XNJ 0x91830; XNJ 0x91a00; XNJ 0x91a84; XNJ 0x91af4] ++ XNLR 0x91b30 (EXPH 0x91b54 0x91b5c) [(9, 0, 0, 2684354559)] 400%nat
  ++ [XNJ 0x91ab8] ++ ADDR 0x91bb4 ++ [XNJ 0x91bcc; XNLFF 0x91be8 (cnt_ff 31 16) 400%nat; XNJ 0x91c38; XNJ 0x92074]
  ++ REBR 0x92240 29 ++ REBR 0x92324 29 ++ REBR 0x92444 29 ++ REBR 0x920b0 29 ++ [XNJ 0x923bc; XNJ 0x91f7c; XNJ 0x92404] ++ XTAILS.
Definition FP0RUN : plan := PR.
