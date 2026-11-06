(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value, segment CL piece A2 (the key path, B 0x83b1c..0x83c88 and
   0x83d6c): the symbolic states of the piece's straight runs over B_prog_tbl (no lemma about the program here).
   Numerals: 0x5f0, 0x600, 0x64c, 0x670, 0x6dc, 0x700, 0x760, 0xa7c (DERIVED: exv_pc offsets from ex_value's entry,
   neutral listing); 34, 58, 91, 123 (WORD: ASCII the code compares); 1 .. 27 (WORD: register numbers); 32 .. 36
   (DERIVED: symbolic atom numbers past the 32 registers); 3, 61, 2 ^ 60 (WORD: the shift / UBSan operands B uses);
   0, 8, 16, 24, 32, 36, 40, 48, 56, 72, 80, 88, 120, 128, 136, 144, 152, 160 (LENGTH: struct ex / node fields and B's
   spill slots); 4096, 255, 2 ^ 46, 2 ^ 47, 2 ^ 64 (LENGTH: value and address-space bounds). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_Loop_exw.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* ---- the pcs (DERIVED offsets from ex_value's entry, neutral listing) ---- *)
Definition A2_LK : Z := exv_pc 0x5f0.   (* B 0x83b1c, the LK cut *)
Definition A2_W1 : Z := exv_pc 0x600.   (* B 0x83b2c, after the first ex_ws *)
Definition A2_S : Z := exv_pc 0x64c.    (* B 0x83b78, after ex_string *)
Definition A2_K : Z := exv_pc 0x670.    (* B 0x83b9c, the keys word loaded *)
Definition A2_C : Z := exv_pc 0x6dc.    (* B 0x83c08, after strcmp *)
Definition A2_W2 : Z := exv_pc 0x700.   (* B 0x83c2c, after the second ex_ws *)
Definition A2_LR : Z := exv_pc 0x760.   (* B 0x83c8c, the LR cut *)
Definition A2_CX : Z := exv_pc 0xa7c.   (* B 0x83fa8, the CX cut *)
Definition A2_WS : Z := B_prog_sigma AS_ex_ws.
Definition A2_STR : Z := B_prog_sigma AS_ex_string.
Definition A2_CMP : Z := B_prog_sigma AS___wrap_strcmp.

(* the shadow address of atom m + c, as `srli 3 / add s9` builds it *)
Definition a2_shx (m : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 25 0).
Definition A2_SB : sv := SOff 25 0.
Definition a2_regs : list sv := sr_set (sr_set sr_atoms 22%bv (a2_shx 19 8)) 23%bv (SOff 19 8).
Definition a2_fb : list (nat * afact) :=
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (19%nat, mkAF (2 ^ 46) (2 ^ 47 - 40) 3);
    (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ].
Definition a2_SHq : shent := mkSHE 19 0 40.

(* R0 / R1: the LK cut, c = 91 (to LR) / c = 123 (to the first ex_ws) *)
Definition ss_a2_r0 : sstate := mkSS A2_LK sr_atoms [] None (mkFacts ((27%nat, mkAF 91 91 0) :: a2_fb) [] []).
Definition ss_a2_r1 : sstate := mkSS A2_LK (sr_set sr_atoms 27%bv (SLit 123)) [] None (mkFacts a2_fb [] []).

(* R2 / R5: after an ex_ws (B 0x83b2c / 0x83c2c); 32 = p, 33 = end, 34 = the byte at p. One shape for both:
   pa: p >= end; pb: p < end and the byte is not c; pc: p < end and the byte is c (c = 34 at R2, 58 at R5) *)
Definition a2_r5_s1 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 120 152 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 18 0)); YP09.mkChunk 144 (CVal 8 (a2_shx 19 0))].
Definition a2_r5_q : YP09.region :=
  YP09.mkRegion (Some 19%nat) 0 16 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition a2_r2_fp : list (nat * afact) :=
  (32%nat, mkAF 4096 (2 ^ 47 - 2) 0) :: (33%nat, mkAF 4096 (2 ^ 47 - 2) 0) :: a2_fb.
Definition ss_a2_pa (pc : Z) : sstate := mkSS pc a2_regs [a2_r5_s1; a2_r5_q] None
  (mkFacts a2_r2_fp [mkAC BC_GEU (SOff 32 0) (SOff 33 0)] []).
Definition ss_a2_pb (pc c : Z) : sstate := mkSS pc a2_regs
  [a2_r5_s1; a2_r5_q; YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))]] None
  (mkFacts ((34%nat, mkAF 0 255 0) :: a2_r2_fp) [mkAC BC_LTU (SOff 32 0) (SOff 33 0); mkAC BC_NE (SOff 34 0) (SLit c)] []).
Definition ss_a2_pc (pc c : Z) : sstate := mkSS pc a2_regs
  [a2_r5_s1; a2_r5_q; YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit c))]] None
  (mkFacts a2_r2_fp [mkAC BC_LTU (SOff 32 0) (SOff 33 0)] []).
Definition a2_SH2a : list shent := [a2_SHq].
Definition a2_SH2b : list shent := [a2_SHq; mkSHE 32 0 1].

(* R3: after ex_string; a0 = -1 / a0 = 0 with fl = 1 / a0 = 0 with fl = 0. The key compare in two runs (the node's
   keys word and the key slot need not be apart): R3c (B 0x83b78 -> 0x83b9c: 32 = vv, 33 = keys) and R3d (B 0x83b9c
   -> strcmp: 32 = keys, 33 = the slot keys + 8 i, 34 = i, 35 = the key pointer, 36 = the scratch) *)
Definition a2_r3_s1x : YP09.region := YP09.mkRegion (Some 9%nat) 120 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 18 0))].
Definition ss_a2_r3a : sstate := mkSS A2_S (sr_set a2_regs 10%bv (SLit (2 ^ 64 - 1))) [a2_r3_s1x] None (mkFacts a2_fb [] []).
Definition ss_a2_r3b : sstate := mkSS A2_S (sr_set (sr_set a2_regs 10%bv (SLit 0)) 24%bv (SLit 1)) [] None (mkFacts a2_fb [] []).
Definition a2_r3c_rc : smem :=
  [ YP09.mkRegion (Some 9%nat) 40 160 0 0
      [ YP09.mkChunk 40 (CVal 8 (a2_shx 32 32)); YP09.mkChunk 48 (CVal 8 (SOff 32 32));
        YP09.mkChunk 152 (CVal 8 (SOff 32 0)) ];
    YP09.mkRegion (Some 32%nat) 32 40 0 0 [YP09.mkChunk 32 (CVal 8 (SOff 33 0))] ].
Definition ss_a2_r3c : sstate := mkSS A2_S (sr_set (sr_set a2_regs 10%bv (SLit 0)) 24%bv (SLit 0)) a2_r3c_rc None
  (mkFacts ((32%nat, mkAF 4096 (2 ^ 47 - 56) 3) :: (33%nat, mkAF 0 (2 ^ 64 - 1) 0) :: a2_fb) [] []).
Definition a2_SH3c : list shent := [mkSHE 32 0 56].
Definition a2_r3d_rc : smem :=
  [ YP09.mkRegion (Some 9%nat) 16 144 0 0
      [ YP09.mkChunk 16 (CVal 8 (a2_shx 19 24)); YP09.mkChunk 24 (CVal 8 (SOff 19 24));
        YP09.mkChunk 32 (CVal 8 (SLit (2 ^ 60))); YP09.mkChunk 128 (CVal 8 (SAlu ALU_SUB (SOff 33 0) (SOff 32 0)));
        YP09.mkChunk 136 (CVal 8 (SOff 34 0)) ];
    YP09.mkRegion (Some 33%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 35 0))];
    YP09.mkRegion (Some 19%nat) 24 32 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 36 0))] ].
Definition a2_r3d_fc : list (nat * afact) :=
  (32%nat, mkAF 4096 (2 ^ 47 - 8) 3) :: (33%nat, mkAF 4096 (2 ^ 47 - 8) 3) :: (34%nat, mkAF 0 (2 ^ 47) 0) ::
  (35%nat, mkAF 0 (2 ^ 64 - 1) 0) :: (36%nat, mkAF 0 (2 ^ 64 - 1) 0) :: a2_fb.
Definition a2_cnd_i : acond := mkAC BC_EQ (SAlu ALU_SRL (SOff 34 (2 ^ 60)) (SLit 61)) (SLit 0).
Definition ss_a2_r3d : sstate := mkSS A2_K (sr_set a2_regs 11%bv (SOff 32 0)) a2_r3d_rc None
  (mkFacts a2_r3d_fc [mkAC BC_GEU (SOff 33 0) (SOff 32 0); a2_cnd_i] []).
Definition a2_SH3d : list shent := [a2_SHq; mkSHE 33 0 8].

(* R4: after strcmp; a0 = 0 / a0 <> 0 (in->differs := 1; 32 = the result, 33 = in->differs before) *)
Definition ss_a2_r4a : sstate := mkSS A2_C (sr_set a2_regs 10%bv (SLit 0)) [] None (mkFacts a2_fb [] []).
Definition ss_a2_r4b : sstate := mkSS A2_C (sr_set a2_regs 10%bv (SOff 32 0))
  [ YP09.mkRegion (Some 9%nat) 72 88 0 0 [YP09.mkChunk 72 (CVal 8 (a2_shx 19 32)); YP09.mkChunk 80 (CVal 8 (SOff 19 32))];
    YP09.mkRegion (Some 19%nat) 32 36 32 36 [YP09.mkChunk 32 (CVal 4 (SOff 33 0))] ] None
  (mkFacts ((32%nat, mkAF 1 (2 ^ 64 - 1) 0) :: (33%nat, mkAF 0 1 0) :: a2_fb) [] []).
