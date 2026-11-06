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
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_tmpl OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition TM : tree xi := Eval vm_compute in mk_tbl BSEGS 0x9a970 2503.
Definition IMGR : list (Z * nat) := [(0xde490, 1%nat); (0xde4e8, 1%nat); (0x22800, 32%nat); (0x10300, 0x30%nat); (0x229e0, 1302%nat); (0x255e0, 0x12%nat); (0x227e0, 4%nat)].
Definition IMGW : tree Z := Eval vm_compute in mk_imgs_acc IMGR TEmpty.
Definition F5 := lvar 22.
Definition R0 : tree lin := rsets (regs_pat 31 TEmpty) [(10, T); (11, TL); (12, V); (13, FMT); (14, lconst 42949673006); (15, lconst 0); (1, RA); (2, SP); (4, lconst TPV)].
(* [comment removed for export] *)
Definition v_facts_f : list fact :=
  [FRange V KHI (KTOP - 8); FMod V 3 4; FRange (lsub (lscale 8 (lsub VS (lconst SHB))) (laddc V (-4))) 0 0; FRange VS (SHB + KHI / 8) (SHB + KTOP / 8)].
Definition F0 : list fact :=
  [ FRange (lsub T (lscale 8 Y0)) 0 256; FRange (lsub (lscale 8 Y1) TL) 1 256; FRange (lsub Y1 Y0) 1 64; FRange L 1 128;
    FRange Y0 ((IMG_END - 256) / 8) (KTOP / 8); FRange Y1 ((IMG_END - 256) / 8) (KTOP / 8);
    FRange (laddc SP (-4288)) KHI (KTOP - 4288); FMod SP 5 0; FMod RA 1 0;
    FRange (lsub (laddc SP (-4288)) (laddc FS 0xb09000)) 0 KTOP;     (* [comment removed for export] *)
    FRange (lsub (laddc SP (-4288)) TL) 0 KTOP;                       (* [comment removed for export] *)
    FRange (lsub T (fsc AR4)) 0x200000 (2 ^ 64 - 128);                 (* [comment removed for export] *)
    FRange (lsub T (fsc 0x9000)) 0 (2 ^ 64 - 0x9000 - 256);            (* [comment removed for export] *)
    spsh_fact 4288; FRange SPSH (SHB + KHI / 8) (SHB + (KTOP - 4288) / 8);   (* [comment removed for export] *)
    FBits FMT 18446744073709551610 0; FRange FMT 1 5 ]     (* [comment removed for export] *)
  ++ List.flat_map (fun '(X, n) => [FRange (lsub X (laddc SP 128)) 0 (2 ^ 64 - 4416 - n)]) [(CTX, 160); (THR, 80); (BLK, 32)]
  ++ two_class T 256 ++ v_facts_f ++ fks4_facts ++ rt_facts.
Definition RGS : list region :=
  [ RG T L RT TEmpty;                                    (* [comment removed for export] *)
    RG (ladd Y0 (lconst SHB)) (lsub Y1 Y0) RZ TEmpty;    (* [comment removed for export] *)
    RGz V 4 RW TEmpty;                                   (* [comment removed for export] *)
    RGz VS 1 RZ TEmpty;                                  (* [comment removed for export] *)
    RGz (laddc SP (-4096)) (4096 - 104) RW TEmpty;       (* [comment removed for export] *)
    RGz (laddc SP (-104)) 104 RW TEmpty;                 (* [comment removed for export] *)
    RGz (lconst 0x10000) 0x2e000 RO TEmpty;              (* [comment removed for export] *)
    track (RGz (lconst 0xe6678) 12 RW TEmpty) 0 (bk8 SHB ++ bkn 4 1);  (* [comment removed for export] *)
    RGz (lconst (SHB + 0x4500)) 32 RZ TEmpty;            (* [comment removed for export] *)
    RGz (lconst (SHB + 0x2060)) 0x30 RZ TEmpty;          (* [comment removed for export] *)
    RGz (lconst (SHB + 0x453c)) 1302 RZ TEmpty;          (* [comment removed for export] *)
    RGz (lconst (SHB + 0x4abc)) 0x12 RZ TEmpty;          (* [comment removed for export] *)
    RGz (lconst 0xe2af8) 4 RO TEmpty ]                   (* [comment removed for export] *)
  ++ relro_rgs ++ fks4_split ++ fks5_whole ++ [fs_hdr] ++ rt_rgs
  ++ [ RGz SPSH 536 RZ TEmpty;                          (* [comment removed for export] *)
       fk3sh; tbl10sh; pow5tabsh ].                     (* [comment removed for export] *)
Definition P0 : sst := SST 0x9a970 R0 RGS F0 200 RNone.
Definition SPF_QRGS : list region :=
  map_i (fun i R => if Nat.eqb i 15 then RGz (fsc 32) 8 RW TEmpty
                    else if Nat.eqb i 25 then RGz (fsc 40) 8 RW TEmpty else R) 0 RGS.
Definition SPF_Q : sst := SST 0 (regs_keep R0 31 200 TEmpty) SPF_QRGS F0 250 RNone.
