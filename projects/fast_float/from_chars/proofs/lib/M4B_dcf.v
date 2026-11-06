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
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxImg FxPlan FxLoop FxFrame FxDrv FxCall FxWork.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_tmpl OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition IPTR := lvar 25. Definition ILEN := lvar 26. Definition FPTR := lvar 27. Definition FLEN := lvar 28.
Definition NDC_NEED : Z := 2768.
Definition DCF_ENTRY : Z := 0x94394.
Definition DCF_EXIT : Z := 0x94404.
Definition DCF_R0 : tree lin :=
  rsets (regs_pat 31 TEmpty) [(2, SP); (9, SP); (4, lconst TPV); (23, laddc SLOT4 32)].
Definition dcf_spans (frac : bool) : list bval :=
  bv8 IPTR ++ bv8 ILEN ++ (if frac then bv8 FPTR ++ bv8 FLEN else List.repeat (BK 0) 16).
Definition DCF_RGS (post : bool) (frac : bool) : list region :=
  [ RG T L RT TEmpty;                                                        (* [comment removed for export] *)
    RG (ladd Y0 (lconst SHB)) (lsub Y1 Y0) RZ TEmpty;                        (* [comment removed for export] *)
    RGz (laddc SP (- NDC_NEED)) NDC_NEED RW TEmpty;                          (* [comment removed for export] *)
    RGz SPSH 365 RZ TEmpty;                                                  (* [comment removed for export] *)
    RG (laddc SLOT4 32) (lconst 984) RW TEmpty;                              (* [comment removed for export] *)
    (if post then RG SHSLOT4 (lconst 128) RW TEmpty
     else track (RG SHSLOT4 (lconst 128) RW TEmpty) 4 (List.repeat (BK 0) 63));   (* [comment removed for export] *)
    track (RGz (fsc 32) 8 RW TEmpty) 0 (bv8 (if post then lvar 229 else laddc H4 1));  (* [comment removed for export] *)
    RG (fsc FL4) P4 RZ TEmpty;                                               (* [comment removed for export] *)
    track (RG (ladd (fsc FL4) P4) (lconst 1) RZ TEmpty) 0 [BK 1];           (* [comment removed for export] *)
    RG (ladd (fsc (FL4 + 1)) P4) (laddc (lscale (-1) P4) 1023) RZ TEmpty;   (* [comment removed for export] *)
    RG (fsc AR4) (lscale 1024 P4) RW TEmpty;                                 (* [comment removed for export] *)
    RG (ladd (fsc (AR4 + 1024)) (lscale 1024 P4)) (laddc (lscale (-1024) P4) (1024 * 1023)) RW TEmpty;   (* [comment removed for export] *)
    RG (fsh AR4) (lscale 128 P4) RW TEmpty;                                  (* [comment removed for export] *)
    RG (ladd (fsh (AR4 + 1024)) (lscale 128 P4)) (laddc (lscale (-128) P4) (128 * 1023)) RW TEmpty;   (* [comment removed for export] *)
    fk3sh ]                                                                  (* [comment removed for export] *)
  ++ (if post then [ track (RGz (fsc 40) 8 RW TEmpty) 0 (bv8 (lvar 230)); RGz (fsc FL5) 512 RZ TEmpty;
                     RGz (fsc AR5) (2 ^ 20) RW TEmpty; RGz (fsh AR5) (2 ^ 17) RW TEmpty ] else fks5_whole)   (* [comment removed for export] *)
  ++ [fs_hdr; sb_uar] ++ rt_rgs ++ relro_rgs                                 (* [comment removed for export] *)
  ++ [ RGz (lconst 0x10000) 0x2e000 RO TEmpty; tbl10sh; pow5tabsh;         (* [comment removed for export] *)
       RGz (laddc SP 144) 8 RW TEmpty;                                        (* [comment removed for export] *)
       (if post then RGz (laddc SP 104) 32 RW TEmpty
        else track (RGz (laddc SP 104) 32 RW TEmpty) 0 (dcf_spans frac)) ].   (* [comment removed for export] *)
Definition dcf_facts (frac : bool) : list fact :=
  [ FMod SP 4 0; FRange (laddc SP (- NDC_NEED)) KHI (KTOP - NDC_NEED - 152); spsh_fact NDC_NEED;
    FRange (laddc (lvar 124) 342) 0 700; FRange (laddc (lvar 125) 49152) 0 32768;
    FRange SPSH SHB KHI; FRange Y0 0 (KTOP / 8); FRange Y1 0 (KTOP / 8); FRange ILEN 0 128;
    FRange L 1 128; FRange (lsub T (lscale 8 Y0)) 0 256; FRange (lsub (lscale 8 Y1) TL) 1 256;
    FRange (lsub (laddc SP (- NDC_NEED)) TL) 0 KTOP;                          (* [comment removed for export] *)
    FRange (lsub T (fsc AR4)) 0x200000 (2 ^ 64 - 128);                        (* [comment removed for export] *)
    FRange (lsub T (fsc 0x9000)) 0 (2 ^ 64 - 0x9000 - 256);                  (* [comment removed for export] *)
    FRange (lsub (laddc SP (- NDC_NEED)) (laddc FS 0xb09000)) 0 KTOP;         (* [comment removed for export] *)
    FRange (lsub IPTR T) 0 256; FRange (lsub TL (ladd IPTR ILEN)) 0 256; FRange P4 0 1023; FMod (lsub H4 P4) 10 0 ]
  ++ (if frac then [FRange (lsub FPTR T) 0 256; FRange (lsub TL (ladd FPTR FLEN)) 0 256; FRange FLEN 0 128] else [])
  ++ two_class T 256                                                           (* [comment removed for export] *)
  ++ rt_facts
  (* [comment removed for export] *)
  ++ List.flat_map (fun '(X, n) => [FRange (lsub X (laddc SP 384)) 0 (2 ^ 64 - 4416 - n)]) [(CTX, 160); (THR, 80); (BLK, 32)].
Definition DCF_P0 (frac : bool) : sst := SST DCF_ENTRY DCF_R0 (DCF_RGS false frac) (dcf_facts frac) 200 RNone.
(* [comment removed for export] *)
Definition KEEPF : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27].
Fixpoint regs_keepf (R : tree lin) (k : nat) (nx : positive) (acc : tree lin) : tree lin :=
  match k with
  | O => acc
  | S k' => regs_keepf R k' nx (tset (Pos.of_succ_nat k)
                                     (if existsb (Z.eqb (Z.of_nat k)) KEEPF then rget R (Pos.of_succ_nat k) else lvar (nx + Pos.of_nat k)) acc)
  end.
Definition DCF_QR : tree lin := rset (regs_keepf DCF_R0 31 240 TEmpty) (rk 24) (laddc (lvar 124) 1).
Definition DCF_Q (frac : bool) : sst := SST 0 DCF_QR (DCF_RGS true frac) (dcf_facts frac) 280 RNone.
Definition KEEPFK : list positive := List.map rk KEEPF.
Lemma DCF_wf : forall frac, state_wf (DCF_P0 frac) = true /\ state_wf (DCF_Q frac) = true /\ shape_eqb (s_rgs (DCF_P0 frac)) (s_rgs (DCF_Q frac)) = true.
Proof. intros [|]; vm_compute; repeat split. Qed.
