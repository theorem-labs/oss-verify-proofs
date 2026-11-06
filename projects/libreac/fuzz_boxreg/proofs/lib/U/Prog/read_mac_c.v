From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition READ_MAC : Z := 0x138f0.
Definition READ_MAC_FRAME : Z := 32.
Definition MAC_BASE : Z := 0x10398.

Definition mac_base : list byte := map (Z_to_bv 8) [0; 0x40; 0xab; 0; 0].

Definition apart (a n b k : Z) : Prop := n = 0 \/ k = 0 \/ a + n <= b \/ b + k <= a.

Definition read_mac_used (full : word) (n : Z) : Z :=
  if bv_unsigned full =? 0 then Z.min 1 n else Z.min 6 n.

Definition read_mac_out (full : word) (pl : list byte) : list byte :=
  if bv_unsigned full =? 0 then mac_base ++ firstn 1 (pl ++ [Z_to_bv 8 0])
  else firstn 6 (pl ++ repeat (Z_to_bv 8 0) 6).

Definition read_mac_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo c p n mac : Z) (pl junk : list byte),
    a0 = Z_to_bv 64 c -> a2 = Z_to_bv 64 mac -> c mod 8 = 0 ->
    rw_cells rsegs m c [C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 n)] ->
    rw_cells rsegs m mac [CB 6 junk] ->
    bytes_at rsegs m p pl -> Z.of_nat (length pl) = n ->
    (1 <= n -> 1 <= p /\ p + n < 2^64) ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + READ_MAC_FRAME <= bv_unsigned sp ->
    apart c 16 mac 6 -> apart c 16 p n -> apart mac 6 p n -> apart mac 6 MAC_BASE 5 ->
    apart c 16 (bv_unsigned sp - READ_MAC_FRAME) READ_MAC_FRAME ->
    apart mac 6 (bv_unsigned sp - READ_MAC_FRAME) READ_MAC_FRAME ->
    apart p n (bv_unsigned sp - READ_MAC_FRAME) READ_MAC_FRAME ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - READ_MAC_FRAME, bv_unsigned sp); (c, c + 16); (mac, mac + 6)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         mem_inv rsegs m' /\
         rw_cells rsegs m' c [C8 (Z_to_bv 64 (p + read_mac_used a1 n)); C8 (Z_to_bv 64 (n - read_mac_used a1 n))] /\
         rw_cells rsegs m' mac [CB 6 (read_mac_out a1 pl)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 READ_MAC) fc None m (seg_rom rsegs)).
