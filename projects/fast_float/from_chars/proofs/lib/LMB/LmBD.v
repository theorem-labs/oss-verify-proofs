(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn M4B_lm.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_tmpl OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn OSSVerify.Proofs.fast_float.from_chars.lib.M4B_lm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition TM : tree xi := Eval vm_compute in mk_tbl BSEGS 0x9733c 1169.
Definition IMGR : list (Z * nat) := [(0xde490, 1%nat); (0xde4e8, 1%nat); (0x25360, 5%nat)].
Definition IMGW : tree Z := Eval vm_compute in mk_imgs_acc IMGR TEmpty.
Definition CALLS : list Z := [0x4b3d0; 0x4b5dc; 0x63d18; 0x981cc; 0x60884].
Definition NPCS : list Z := [0x97428; 0x97444; 0x97888; 0x97938; 0x97a8c; 0x97f9c; 0x97fd0; 0x98098; 0x98454].
Definition ALLST : list Z := NPCS ++ CALLS.
Definition ANC : list lin := [XA; XS; laddc XA 496; LEN].
Definition PR : plan := PRun 400 ALLST [].
Definition JR (Ls : list sst) : sst := rjoin_re 200 ANC [] [] Ls.
Definition XNJ (pc : Z) : Z * xaction := (pc, xjoin JR (fun _ => PR)).
Definition XNS (pc : Z) : Z * xaction := (pc, xjoin_each JR (fun _ => PR)).
Definition XNCF (pc : Z) (mf : list (Z * Z)) (mc : Z) (pa : list lin) : Z * xaction := (pc, xjoin JR (cloopf TM IMGW mf mc pa 400 ALLST)).
Fixpoint cellx (rgs : list region) (a : lin) : lin :=
  match rgs with
  | [] => lconst 0
  | R :: rs => match is_const (lsub a (rg_base R)) with
               | Some o => match tget (okey o) (rg_cont R) with Some (BV l 0) => l | Some (BK b) => lconst b | _ => cellx rs a end
               | None => cellx rs a end
  end.
(* [comment removed for export] *)
Definition MS1 (P : sst) (R : tree lin) : lin := lsub (cellx (s_rgs P) (laddc (rget (s_regs P) (rk 2)) 16)) (rget R (rk 20)).
Definition XNCGE (pc : Z) (mf : sst -> tree lin -> lin) (pa : list lin) : Z * xaction := (pc, xjoin_each JR (cloopg TM IMGW mf pa 400 ALLST)).
Definition XNTE (pc : Z) (kc : Z) (pa : list lin) : Z * xaction := (pc, xjoin_each JR (cloopt TM IMGW (rk kc) pa 400 ALLST)).
Definition ZI : lin := laddc SLOT5 608. Definition ZIS : lin := laddc SHSLOT5 76.
Definition RTV : list (vop * Z * rkind) := (VCopy 16, 0, RW) :: List.map (fun i => (VCopy i, 0, RW)) (seq 17 11) ++ [(VCopy 28, 0, RO); (VCopy 29, 0, RO)].
Definition CS_SM5 (c : Z) : csite := mk_csite SM5_P0 SM5_Q KEEPK SM5_QK
  ([(VSub 0 0, 2368 - c, RW); (VCopy 8, 0, RW); (VCopy 9, 0, RZ); (VCopy 10, 0, RZ); (VCopy 11, 0, RZ); (VCopy 12, 0, RW); (VCopy 14, 0, RW);
    (VCopy 15, 0, RW); (VCopy 16, 0, RW)] ++ List.map (fun i => (VCopy i, 0, RW)) (seq 17 11) ++ [(VCopy 28, 0, RO); (VCopy 29, 0, RO)]).
Definition CS_MMA (c : Z) : csite := mk_csite MMA_P0 MMA_Q KEEPK MM_QK
  ([(VSub 0 0, 2272 - c, RW); (VSub 12 32, 496, RW); (VCopy 1, 0, RW); (VCopy 13, 0, RT); (VCopy 14, 0, RW); (VCopy 4, 0, RT); (VCopy 3, 0, RT); (VCopy 5, 0, RT)] ++ RTV).
Definition CS_MMB (c : Z) : csite := mk_csite MMB_P0 MMB_Q KEEPK MM_QK
  ([(VSub 0 0, 2272 - c, RW); (VSub 12 608, 496, RW); (VSub 12 32, 496, RW); (VCopy 13, 0, RT); (VCopy 14, 0, RW)] ++ RTV).
Definition PRE (c : Z) : list (Z * xaction) := [(0x4b3d0, XCallK (CS_SM5 c)); XNJ 0x97428; (0x60884, XCallK (CS_MMA c)); XNJ 0x98454; XNCF 0x97888 [(11, 1); (17, 1)] (-63) [XA; XS]].
Definition BODY (c : Z) : list (Z * xaction) := [XNJ 0x97938; (0x60884, XCallK (CS_MMB c)); XNJ 0x98454; XNCF 0x97a8c [(11, 1); (13, 1)] (-63) [ZI; ZIS];
   (0x97f9c, XHand (hx_c2r 0x97f9c)); XNS 0x97f9c; XNCGE 0x97fd0 MS1 [XA; ZI]; XNTE 0x98098 14 [XA; XS]].
Definition NODES (c : Z) : list (Z * xaction) := PRE c ++ BODY c ++ BODY c ++ BODY c ++ BODY c.
Definition P0RUN : plan := PRun 600 ALLST [].
(* [comment removed for export] *)
Definition CS_SF5 (c : Z) : csite := mk_csite SF5_P0 SF5_Q KEEPK []
  ([(VSub 0 0, 2368 - c, RW); (VCopy 12, 0, RW); (VCopy 10, 0, RZ); (VCopy 14, 0, RW); (VCopy 6, 0, RO); (VCopy 16, 0, RW)] ++ List.map (fun i => (VCopy i, 0, RW)) (seq 17 11) ++ [(VCopy 28, 0, RO); (VCopy 29, 0, RO)]).
Definition P2RUN : plan := PRun 800 [0x4b5dc; 0x63d18; 0x97da0] [].
Definition XNJe (pc : Z) : Z * xaction := (pc, xjoin JR (fun _ => PRun 400 [0x97da0] [])).
Definition NODES2 (c : Z) : list (Z * xaction) := [(0x4b5dc, XCallK (CS_SF5 c)); XNJe 0x97d50; (0x97da0, XHand (hx_promote 0x97da0 10))].
