From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** owe_sysex (fuzz_codec.c:101-111; out of line in the UBSan image only: 164 bytes at 0x1554c, frame 0x20,
    calls memcpy at 0x15594). Called by LLVMFuzzerTestOneInput at 0x14670 (SCRIBBLE: a1 = d->device,
    a2 = 0x40, a3 = its pl[10], a4 = 2 + d->chars) and 0x14b70 (SYSEX: a1 = k.a & 0xff, a2 = k.b & 0xff,
    a3 = &k.bytes, a4 = k.n), a0 = &k. It writes want[0..n + 5) = owe_sx, want_len = n + 5 and
    want_display, not want_key; its bound trap on want[4 + n] needs n <= 19. *)
Definition OWE_SYSEX : Z := 0x1554c.
Definition OWE_SYSEX_DEPTH : Z := 0x20.

Definition owe_sysex_pre (sp a0 a1 a2 a3 a4 : word) (m : word -> option byte) (lo dev fn : Z) (k : kcall) (pl : list byte) : Prop :=
  rw_cells rsegs m (bv_unsigned a0) (kcall_cells k) /\
  kcall_wf k /\
  bv_unsigned a0 mod 8 = 0 /\
  arg_zx 8 a1 dev /\
  arg_zx 8 a2 fn /\
  bytes_at rsegs m (bv_unsigned a3) pl /\
  bv_unsigned a4 = Z.of_nat (length pl) /\
  (length pl <= 19)%nat /\
  disj (bv_unsigned a3) (Z.of_nat (length pl)) (bv_unsigned a0 + 144) 40 /\
  bv_unsigned sp <= bv_unsigned a0 /\
  bv_unsigned sp <= bv_unsigned a3 /\
  mem_inv rsegs m /\
  stk rsegs m lo (bv_unsigned sp) /\
  lo + OWE_SYSEX_DEPTH <= bv_unsigned sp.

Definition owe_sysex_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo dev fn : Z) (k : kcall) (pl : list byte),
    owe_sysex_pre sp a0 a1 a2 a3 a4 m lo dev fn k pl ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - OWE_SYSEX_DEPTH, bv_unsigned sp); (bv_unsigned a0 + 144, bv_unsigned a0 + 184)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         let '(w, dp) := owe_sx dev fn (zb pl) in
         rw_cells rsegs m' (bv_unsigned a0)
           (kcall_cells (set_want k (bz w ++ skipn (length w) (k_want k)) (Z.of_nat (length w)) dp)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 OWE_SYSEX) fc None m (seg_rom rsegs)).
