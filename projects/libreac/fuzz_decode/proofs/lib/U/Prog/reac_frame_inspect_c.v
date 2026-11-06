From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Img0.
Open Scope Z_scope.

Definition REAC_FRAME_INSPECT : Z := 0x13950.

Definition inspect_byte (bs : list byte) (i : nat) : Z := bv_unsigned (nth i bs (Z_to_bv 8 0)).

Definition inspect_wf (len : Z) (bs : list byte) : bool :=
  (len =? 1492) && (inspect_byte bs 12 =? 0x88) && (inspect_byte bs 13 =? 0x19)
  && (inspect_byte bs 1490 =? 0xC2) && (inspect_byte bs 1491 =? 0xEA).

Definition inspect_counter (bs : list byte) : Z := inspect_byte bs 14 + 256 * inspect_byte bs 15.

Definition inspect_result (len : Z) (bs : list byte) : Z :=
  if inspect_wf len bs then 2^32 + inspect_counter bs else 0.

Definition reac_frame_inspect_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte),
    (bv_unsigned a1 = 1492 ->
       length bs = 1492%nat /\ bytes_at rsegs m (bv_unsigned a0) bs /\ bv_unsigned a0 <> 0) ->
    evt rsegs
      (fun ms' => exists a1' a2' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (inspect_result (bv_unsigned a1) bs)) a1' a2'
                       a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_FRAME_INSPECT) fc None m (seg_rom rsegs)).
