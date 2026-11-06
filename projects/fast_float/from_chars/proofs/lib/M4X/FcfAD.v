(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxImg FxPlan FxLoop FxFrame FxDrv FxCall FxWork FxWorkX FxGenA FxGenX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWorkX OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxGenA OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxGenX.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4A_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4A_kfn M4A_kfnf.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.M4A_tmpl OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfnf.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4A_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4X Require SpfA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition TM : tree xi := Eval vm_compute in mk_tbl ASEGS 0x97d00 1382.
Definition IMGR : list (Z * nat) := [(0xdcc10, 1%nat); (0x227f0, 32%nat); (0x10300, 0x30%nat); (0x229c0, 1302%nat); (0x255c0, 0x12%nat); (0x227d0, 4%nat)].
Definition IMGW : tree Z := Eval vm_compute in mk_imgs_acc IMGR TEmpty.
Definition F5 := lvar 22.
Definition FR0 : tree lin := rsets (regs_pat 31 TEmpty) [(10, T); (11, TL); (12, V); (13, FMT); (14, lconst 42949673006); (1, RA); (2, SP); (4, lconst TPV)].
Definition FF0 : list fact :=
  [ FRange (lsub T (lscale 8 Y0)) 0 256; FRange (lsub (lscale 8 Y1) TL) 1 256; FRange (lsub Y1 Y0) 1 64; FRange L 0 128;
    FRange Y0 ((IMG_END - 256) / 8) (KTOP / 8); FRange Y1 ((IMG_END - 256) / 8) (KTOP / 8);
    FRange (laddc SP (-4416)) KHI (KTOP - 4416); FMod SP 5 0; FMod RA 1 0;
    FRange (lsub (laddc SP (-4416)) (laddc FS 0xb09000)) 0 KTOP; FRange (lsub (laddc SP (-4416)) TL) 0 KTOP;
    FRange (lsub T (fsc AR4)) 0x200000 (2 ^ 64 - 128); FRange (lsub T (fsc 0x9000)) 0 (2 ^ 64 - 0x9000 - 256);
    spsh_fact 4416; FRange SPSH (SHB + KHI / 8) (SHB + (KTOP - 4416) / 8);
    FBits FMT 18446744073709551610 0; FRange FMT 1 5 ]
  ++ List.flat_map (fun '(X, n) => [FRange (lsub X SP) 0 (2 ^ 64 - 4416 - n)]) [(CTX, 160); (THR, 80); (BLK, 32)]
  ++ two_class T 256 ++ SpfA.v_facts_f ++ fks4_facts ++ rt_facts.
Definition FRGS : list region :=
  map_i (fun i R => if Nat.eqb i 4 then RGz (laddc SP (-4224)) 4096 RW TEmpty      (* [comment removed for export] *)
                    else if Nat.eqb i 5 then RGz (laddc SP (-128)) 128 RW TEmpty   (* [comment removed for export] *)
                    else if Nat.eqb i 41 then RGz SPSH 552 RZ TEmpty                (* [comment removed for export] *)
                    else R) 0 (firstn 45 SpfA.RGS).
Definition FP0 : sst := SST 0x97d00 FR0 FRGS FF0 200 RNone.
Definition NPCS : list Z := [0x98afc; 0x98da0; 0x98f30; 0x98df0; 0x97fec; 0x98114; 0x9831c; 0x983b8; 0x9859c; 0x985ac; 0x985f8; 0x984a8; 0x98630; 0x986ac; 0x9870c; 0x98740;
  0x986d8; 0x987c8; 0x987e0; 0x98828; 0x98b98; 0x98bd4; 0x98d30; 0x98e90; 0x98ae8; 0x98ee4].
Definition ALLST : list Z := NPCS ++ [0x98f2c; 0x99298; 0x995c4].
Definition ANC : list lin := [T; TL].
Definition PR : plan := PRun 400 ALLST [].
Definition JR (Ls : list sst) : sst := rjoin_r 200 ANC [] [] Ls.
Definition XNJ (pc : Z) : Z * xaction := (pc, xjoin JR (fun _ => PR)).
Definition XNL (pc : Z) : Z * xaction := (pc, xjoin JR (aloop TM IMGW ANC 400 ALLST)).
Definition XNG (pc : Z) (ks kp : Z) : Z * xaction :=
  (pc, xjoin JR (gloop TM IMGW (rk ks) (rk kp) TL [ladd Y0 (lconst SHB); ladd Y1 (lconst SHB)] [T; TL; lscale 8 Y0; lscale 8 Y1] 400 ALLST)).
Definition CS_INF : csite := mk_csite OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.M4A_inff.P0 OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.M4A_inff.Q KEEPK []
   [(VCopy 0, 0, RT); (VCopy 1, 0, RZ); (VCopy 2, 0, RW); (VCopy 3, 0, RZ); (VSub 4 4080, 16, RW); (VSub 13 0x3c10, 8, RO); (VSub 7 0, 8, RW)].
Definition SPFV : list (vop * Z * rkind) :=
  List.map (fun i => if Nat.eqb i 4 then (VSub 4 0, 3904, RW) else if Nat.eqb i 5 then (VSub 4 3992, 104, RW)
                     else if Nat.eqb i 41 then (VSub 41 0, 536, RZ) else if Nat.eqb i 45 then (VSub 4 3904, 88, RW) else (VCopy i, 0, RW)) (seq 0 46).
Definition CS_SPF : csite := mk_csite SpfA.P0 SpfA.SPF_Q KEEPK [] SPFV.
Definition NODES1 : list (Z * xaction) := [XNJ 0x97fec; XNL 0x98114; XNJ 0x9831c; XNG 0x983b8 24 10; XNJ 0x9859c; XNL 0x985ac; XNJ 0x985f8; XNJ 0x984a8;
  XNJ 0x98630; XNJ 0x986ac; XNJ 0x9870c; XNL 0x98740; XNJ 0x986d8; XNJ 0x987c8; XNL 0x987e0; XNJ 0x98828; XNJ 0x98b98; XNJ 0x98da0; XNJ 0x98f30; XNJ 0x98df0; XNJ 0x98bd4; XNJ 0x98d30; XNJ 0x98e90; XNJ 0x98ae8;
  (0x99298, XCall CS_INF); (0x995c4, XCall CS_SPF); XNJ 0x98ff0; XNJ 0x98afc; XNJ 0x98ee4].
Definition FQRGS : list region :=
  map_i (fun i R => if Nat.eqb i 15 then RGz (fsc 32) 8 RW TEmpty else if Nat.eqb i 25 then RGz (fsc 40) 8 RW TEmpty else R) 0 FRGS.
Definition FCF_Q : sst := SST 0 (regs_keep FR0 31 200 TEmpty) FQRGS FF0 250 RNone.
Definition FP0RUN : plan := PRun 300 ALLST [].
Definition FRETS : list Z := [0x98f2c].

