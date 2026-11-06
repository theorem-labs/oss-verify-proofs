From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition EX_HEX4 : Z := 0x15234.

Definition ex_hexval (b : byte) : option Z :=
  if (48 <=? bv_unsigned b) && (bv_unsigned b <=? 57) then Some (bv_unsigned b - 48)
  else if (97 <=? bv_unsigned b) && (bv_unsigned b <=? 102) then Some (bv_unsigned b - 87)
  else if (65 <=? bv_unsigned b) && (bv_unsigned b <=? 70) then Some (bv_unsigned b - 55)
  else None.

Definition ex_hex4_val (x : list byte) : option Z :=
  match x with
  | b0 :: b1 :: b2 :: b3 :: _ =>
      match ex_hexval b0, ex_hexval b1, ex_hexval b2, ex_hexval b3 with
      | Some h0, Some h1, Some h2, Some h3 => Some (4096 * h0 + 256 * h1 + 16 * h2 + h3)
      | _, _, _, _ => None
      end
  | _ => None
  end.

Definition ex_hex4_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p out : Z) (b0 b1 b2 b3 : byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 out ->
    p <> 0 -> bytes_at rsegs m p [b0; b1; b2; b3] ->
    wr_at rsegs m out 4 -> out mod 4 = 0 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(out, out + 4)] m m' /\ wmono rsegs m m' /\
         match ex_hex4_val [b0; b1; b2; b3] with
         | Some v => r = Z_to_bv 64 0 /\ bytes_at rsegs m' out (le4 (Z_to_bv 64 v))
         | None => r = Z_to_bv 64 (-1) /\ m' = m
         end)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EX_HEX4) fc None m (seg_rom rsegs)).
