From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** owed_seg7 (fuzz_codec.c:372-395; 148 bytes at 0x150d0, leaf, no frame). Called by check_text_seg7 at
    0x14d60 (a0 = c, 0 <= c < 256) and owed_counter_text at 0x14f04 (a0 = the char & 0xff, or ' '). Its
    case-folding test ((c ^ g) & 0xdf) is exact only for c < 256. Reads GLYPH (RELRO) and the glyph strings
    (.rodata); returns owed_seg7_spec c; writes a0-a6. *)
Definition OWED_SEG7 : Z := 0x150d0.

Definition owed_seg7_pre (a0 : word) (m : word -> option byte) (c : Z) : Prop :=
  0 <= c < 256 /\
  a0 = Z_to_bv 64 c /\
  relro_img m /\
  mem_inv rsegs m.

Definition owed_seg7_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : Z),
    owed_seg7_pre a0 m c ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' a4' a5' a6' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (owed_seg7_spec c)) a1' a2' a3' a4' a5' a6' a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 OWED_SEG7) fc None m (seg_rom rsegs)).
