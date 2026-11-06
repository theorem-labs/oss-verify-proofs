From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import ReacDecodeLib SlotUp
  reac_frame_inspect_c reac_decode_c reac_upstream_channels_c reac_upstream_decode_c.
Import ListNotations.
Open Scope Z_scope.

Definition q_umalloc (F : bvmap 5 word) (fc : bv 32) (gp tp : word) (m0 : word -> option byte)
    (Sp len frame : Z) (ms : machine_state) : Prop :=
  exists R, ms = MS R F (Z_to_bv 64 0x147c4) fc None m0 (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x1318c /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 8 = Z_to_bv 64 (frame + 50) /\ reg_get R 10 = Z_to_bv 64 (up_olen len) /\
    reg_get R 19 = Z_to_bv 64 (upstream_result len) /\ reg_get R 21 = Z_to_bv 64 (up_olen len) /\
    reg_get R 25 = Z_to_bv 64 len /\ reg_get R 26 = Z_to_bv 64 frame.

Definition q_ucrt (F : bvmap 5 word) (fc : bv 32) (gp tp : word) (m0 : word -> option byte)
    (Sp len frame out : Z) (fr : list byte) (ms : machine_state) : Prop :=
  exists R m', ms = MS R F (Z_to_bv 64 0x132f8) fc None m' (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x13290 /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 8 = Z_to_bv 64 (frame + 50) /\ reg_get R 10 = Z_to_bv 64 (frame + 50) /\
    reg_get R 11 = Z_to_bv 64 out /\ reg_get R 12 = Z_to_bv 64 (upstream_result len) /\
    reg_get R 13 = Z_to_bv 64 12 /\ reg_get R 19 = Z_to_bv 64 (upstream_result len) /\
    reg_get R 20 = Z_to_bv 64 out /\ reg_get R 25 = Z_to_bv 64 len /\ reg_get R 26 = Z_to_bv 64 frame /\
    up_ok frame out len fr = true /\
    munch [(out, out + up_olen len)] m0 m' /\ wmono rsegs m0 m' /\
    bytes_at rsegs m' frame fr /\ bytes_at rsegs m' out (braid_out fr (upstream_result len) 12).

Definition q_ufree (F : bvmap 5 word) (fc : bv 32) (gp tp : word) (m0 : word -> option byte)
    (Sp len frame out lo : Z) (ms : machine_state) : Prop :=
  exists R m', ms = MS R F (Z_to_bv 64 0x14684) fc None m' (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x132ac /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 8 = Z_to_bv 64 (frame + 50) /\ reg_get R 10 = Z_to_bv 64 out /\
    reg_get R 25 = Z_to_bv 64 len /\ reg_get R 26 = Z_to_bv 64 frame /\
    munch [(lo, Sp); (out, out + up_olen len)] m0 m' /\ wmono rsegs m0 m'.
