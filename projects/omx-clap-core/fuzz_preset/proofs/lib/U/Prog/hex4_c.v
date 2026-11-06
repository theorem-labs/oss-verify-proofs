From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition HEX4 : Z := 0x1740c.

Definition hexval (b : byte) : option Z :=
  if (48 <=? bv_unsigned b) && (bv_unsigned b <=? 57) then Some (bv_unsigned b - 48)
  else if (97 <=? bv_unsigned b) && (bv_unsigned b <=? 102) then Some (bv_unsigned b - 87)
  else if (65 <=? bv_unsigned b) && (bv_unsigned b <=? 70) then Some (bv_unsigned b - 55)
  else None.

Definition hex4 (bs : list byte) : option Z :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: _ =>
      match hexval b0, hexval b1, hexval b2, hexval b3 with
      | Some h0, Some h1, Some h2, Some h3 => Some (4096 * h0 + 256 * h1 + 16 * h2 + h3)
      | _, _, _, _ => None
      end
  | _ => None
  end.

Definition hex4_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p o : Z) (b0 b1 b2 b3 : byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 o ->
    p <> 0 -> bytes_at rsegs m p [b0; b1; b2; b3] ->
    o <> 0 -> o mod 4 = 0 -> wr_at rsegs m o 4 ->
    (o + 4 <= p \/ p + 4 <= o) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(o, o + 4)] m m' /\ wmono rsegs m m' /\
         match hex4 [b0; b1; b2; b3] with
         | Some h => r = Z_to_bv 64 0 /\ bytes_at rsegs m' o (le4 (Z_to_bv 64 h))
         | None => r = Z_to_bv 64 (-1) /\ m' = m
         end)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 HEX4) fc None m (seg_rom rsegs)).
