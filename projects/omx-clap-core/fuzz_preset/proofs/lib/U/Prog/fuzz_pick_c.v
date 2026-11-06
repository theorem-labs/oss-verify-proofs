From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes check_reject_clean_starved_c.
Open Scope Z_scope.

(* Measured in the symtab of the #102 twin agents/pau-preset-102/omx-clap-core/unstripped/fuzz_preset/fuzz_preset.ubsan
   (sha256 27566683952ebd54...), the unstripped twin of the pinned fuzz_preset.ubsan 45b0357d18ff66cd... (facts 8f3e7e1a07f1):
     fuzz_pick FUNC LOCAL 0x152d0 size 100 (25 instructions, 0x152d0..0x15330).
   A LEAF: no stack frame (sp is never written), no store, no call. Its one memory access is the load `lbu t0, 0(a6)` at
   0x15300. Its only reference in .text is the `jal fuzz_pick` at 0x13e50 in check_reject_clean_starved (the compact starved
   write's pick); no data word holds 0x152d0.
   The code (fuzz.h: h = 5381; h = h * 33 + p[i] over the len bytes, size_t; return n ? h % n : 0):
     a3 := 5381; if a1 = 0 go to the tail; a4 := (a0 <> 0); a5, a6 := a0;
     loop at 0x152e8: the UBSan pointer-overflow check (bltu a5, a0; seqz a7, a5; xor a7, a4, a7; beqz a7; beqz a0), each
       arm to the trap `unimp` at 0x15330; then a3 := (a3 << 5) + a3 + byte (a6) mod 2 ^ 64, a1 -= 1, a5 += 1, a6 += 1;
       loop while a1 <> 0;
     tail at 0x1531c: a0 := (a2 = 0 ? 0 : a3 remu a2); ret.
   So a0 is djb2 (5381, 33 * h + c mod 2 ^ 64) over the bytes, mod n, and 0 when n = 0: check_reject_clean_starved_c.pick.
   Under the premises (0 < d, d + n < 2 ^ 62) a5 = d + i is never below a0 = d and never 0, and a0 <> 0, so the trap
   0x15330 is not reached.  Written: a0, a1 (counted down to 0), a3, a4, a5, a6, a7, t0; kept: every other register, the
   memory, F and fc.  The premises are those of the tfuzz_pick_specX (lib/A/PRH_FnCheck.v at
   commit 593b31473a09) in the U form: the bytes are a byte list x at d (Mem.bytes_at, the
   form of check_reject_clean_starved_c's tb) and the hash runs over zb x. *)
Definition FUZZ_PICK : Z := 0x152d0.

Definition fuzz_pick_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (d n k : Z) (x : list byte),
    a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 k ->
    0 <= k < 2 ^ 64 -> n <= 3 * 2 ^ 20 -> 0 < d -> d + n < 2 ^ 62 ->
    Z.of_nat (length x) = n -> bytes_at rsegs m d x ->
    evt rsegs
      (fun ms' => exists a1' a3' a4' a5' a6' a7' t0' : word,
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (pick (zb x) k)) a1' a2 a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FUZZ_PICK) fc None m (seg_rom rsegs)).
