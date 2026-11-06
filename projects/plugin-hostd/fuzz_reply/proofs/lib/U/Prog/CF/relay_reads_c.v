From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import relay_source_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Open Scope Z_scope.

Definition RELAY_READS : Z := 0x15350.
Definition RELAY_READS_K : Z := 16.

Definition relay_reads_r (fd : Z) (es : list rentry) : Z :=
  match src_find fd es with Some (_, e) => if re_eof e =? 0 then 1 else 0 | None => 0 end.

Definition relay_reads_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo fd : Z) (g : word) (es : list rentry),
    bv_unsigned a0 <> 0 ->
    bv_unsigned a0 mod 8 = 0 ->
    -2^31 <= fd < 2^31 ->
    bytes_at rsegs m (bv_unsigned a0) (le4 (Z_to_bv 64 fd)) ->
    Z.of_nat (length es) < 2^31 ->
    bytes_at rsegs m G_NSRC (le4 (Z_to_bv 64 (Z.of_nat (length es)))) ->
    bytes_at rsegs m G_SRC (le8 g) ->
    src_table m (bv_unsigned g) es ->
    Forall (fun e => -2^31 <= re_eof e < 2^31) es ->
    (es <> [] -> bv_unsigned g <> 0 /\ bv_unsigned g mod 8 = 0) ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RELAY_READS_K <= bv_unsigned sp ->
    (bv_unsigned a0 + 4 <= bv_unsigned sp - RELAY_READS_K \/ bv_unsigned sp <= bv_unsigned a0) ->
    (G_NSRC + 4 <= bv_unsigned sp - RELAY_READS_K \/ bv_unsigned sp <= G_NSRC) ->
    (G_SRC + 8 <= bv_unsigned sp - RELAY_READS_K \/ bv_unsigned sp <= G_SRC) ->
    (es <> [] ->
     bv_unsigned g + 56 * Z.of_nat (length es) <= bv_unsigned sp - RELAY_READS_K \/ bv_unsigned sp <= bv_unsigned g) ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (relay_reads_r fd es))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RELAY_READS_K, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RELAY_READS) fc None m (seg_rom rsegs)).
