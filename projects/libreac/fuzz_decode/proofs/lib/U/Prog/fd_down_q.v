From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import ReacDecodeLib reac_frame_inspect_c
  reac_decode_c.
Import ListNotations.
Open Scope Z_scope.

Definition FILL : byte := Z_to_bv 8 0xa5.

Definition fd_olen (nch ns : Z) : Z := if (0 <? nch) && (0 <? ns) then 3 * nch * ns else 1.
Definition fd_fits (nch ns : Z) : Z := if (0 <? nch) && (0 <? ns) && (nch * ns <? 481) then 1 else 0.
Definition pokz (len : Z) (bs : list byte) (nch ns : Z) : Z :=
  if inspect_wf len bs && ((0 <? nch) && (0 <? ns) && (nch * ns <? 481)) then 1 else 0.
Definition dres (len : Z) (bs : list byte) (nch ns : Z) : Z := if decode_ok len bs nch ns then ns else -1.
Definition dout (len : Z) (bs : list byte) (nch ns : Z) : list byte :=
  if decode_ok len bs nch ns then braid_out bs nch ns else repeat FILL (Z.to_nat (fd_olen nch ns)).

Definition q_dmalloc (F : bvmap 5 word) (fc : bv 32) (gp tp : word) (m0 : word -> option byte)
    (Sp mode nch ns len frame lo : Z) (fr junk8 : list byte) (ms : machine_state) : Prop :=
  exists R m', ms = MS R F (Z_to_bv 64 0x14df4) fc None m' (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x12f74 /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 9 = Z_to_bv 64 len /\ reg_get R 10 = Z_to_bv 64 (fd_olen nch ns) /\
    reg_get R 18 = Z_to_bv 64 (fd_fits nch ns) /\ reg_get R 19 = Z_to_bv 64 mode /\
    reg_get R 23 = Z_to_bv 64 (fd_olen nch ns) /\ reg_get R 25 = Z_to_bv 64 frame /\
    munch [(Sp + 40, Sp + 56)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
    rw_cells rsegs m' (Sp + 40) [C8 (Z_to_bv 64 nch); C8 (Z_to_bv 64 ns)] /\
    rw_cells rsegs m' (Sp + 8) [CB 32 junk8] /\
    bytes_at rsegs m' (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) /\ bytes_at rsegs m' frame fr /\
    stk rsegs m' lo Sp.

Definition dcells (m : word -> option byte) (Sp len frame nch ns : Z) (junk : list byte) : Prop :=
  rw_cells rsegs m (Sp + 8)
    [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 frame); CB 16 junk; C8 (Z_to_bv 64 nch); C8 (Z_to_bv 64 ns)].

Definition q_dJ (F : bvmap 5 word) (fc : bv 32) (gp tp : word) (m0 : word -> option byte)
    (Sp mode nch ns len frame out lo : Z) (fr : list byte) (ms : machine_state) : Prop :=
  exists R m' junk, ms = MS R F (Z_to_bv 64 0x130ec) fc None m' (seg_rom rsegs) /\
    reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 9 = Z_to_bv 64 len /\ reg_get R 10 = Z_to_bv 64 (dres len fr nch ns) /\
    reg_get R 19 = Z_to_bv 64 mode /\ reg_get R 22 = Z_to_bv 64 out /\
    reg_get R 23 = Z_to_bv 64 (fd_olen nch ns) /\ reg_get R 24 = Z_to_bv 64 (pokz len fr nch ns) /\
    reg_get R 25 = Z_to_bv 64 frame /\
    munch [(lo, Sp + 56); (out, out + fd_olen nch ns)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo Sp /\ dcells m' Sp len frame nch ns junk /\
    bytes_at rsegs m' (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) /\ bytes_at rsegs m' frame fr /\
    bytes_at rsegs m' out (dout len fr nch ns) /\ wr_at rsegs m' out (fd_olen nch ns).

Definition q_dcrt (F : bvmap 5 word) (fc : bv 32) (gp tp : word) (m0 : word -> option byte)
    (Sp mode nch ns len frame out lo : Z) (fr : list byte) (ms : machine_state) : Prop :=
  exists R m' junk, ms = MS R F (Z_to_bv 64 0x134e4) fc None m' (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x13124 /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 9 = Z_to_bv 64 len /\ reg_get R 10 = Z_to_bv 64 (frame + 50) /\ reg_get R 11 = Z_to_bv 64 out /\
    reg_get R 12 = Z_to_bv 64 nch /\ reg_get R 13 = Z_to_bv 64 ns /\ reg_get R 18 = Z_to_bv 64 (frame + 50) /\
    reg_get R 19 = Z_to_bv 64 mode /\ reg_get R 22 = Z_to_bv 64 out /\
    reg_get R 23 = Z_to_bv 64 (fd_olen nch ns) /\ reg_get R 24 = Z_to_bv 64 (pokz len fr nch ns) /\
    reg_get R 25 = Z_to_bv 64 frame /\
    decode_ok len fr nch ns = true /\ ns <= 12 /\
    munch [(lo, Sp + 56); (out, out + fd_olen nch ns)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo Sp /\ dcells m' Sp len frame nch ns junk /\
    bytes_at rsegs m' (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) /\ bytes_at rsegs m' frame fr /\
    bytes_at rsegs m' out (braid_out fr nch ns) /\ wr_at rsegs m' out (fd_olen nch ns).

Definition q_dfree (F : bvmap 5 word) (fc : bv 32) (gp tp : word) (m0 : word -> option byte)
    (Sp len frame out olen lo : Z) (fr : list byte) (ms : machine_state) : Prop :=
  exists R m', ms = MS R F (Z_to_bv 64 0x14cb4) fc None m' (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x13298 /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 8 = Z_to_bv 64 len /\ reg_get R 10 = Z_to_bv 64 out /\
    reg_get R 18 = Z_to_bv 64 (frame + 50) /\ reg_get R 25 = Z_to_bv 64 frame /\
    munch [(lo, Sp + 56); (out, out + olen)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
    bytes_at rsegs m' frame fr /\ stk rsegs m' lo Sp.
