(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_dview Z_drep.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel RefFlushBlk13.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).

Definition Z_TR_INIT : Z := 0x1ad54.
Definition Z_TR_FLUSH_BITS : Z := 0x1b098.
Definition Z_TR_FLUSH_BLOCK : Z := 0x1b29c.
(* [comment removed for export] *)
Definition Z_TRFB_STACK : Z := 512.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition tr_init_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (s : deflate_state) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(dl_As L, dl_As L + DS_SIZE)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ DST m' L (tr_init s).

Definition tr_init_stmt : Prop :=
  forall (L : dlay) (s : deflate_state)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DSTi m L s -> mem_inv psegs m ->
  a0 = wz (dl_As L) ->
  evt psegs (tr_init_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_TR_INIT) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition tr_flush_bits_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (s : deflate_state) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(dl_As L, dl_As L + DS_SIZE); (dl_Ab L, dl_Ab L + DS_PEND)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ DST m' L (tr_flush_bits s).

Definition tr_flush_bits_stmt : Prop :=
  forall (L : dlay) (s : deflate_state)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L s -> mem_inv psegs m ->
  BINV DS_PEND s -> ds_pending (tr_flush_bits s) <= DS_PEND ->
  a0 = wz (dl_As L) ->
  evt psegs (tr_flush_bits_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_TR_FLUSH_BITS) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fb_buf_ok (buf : option Z) (len : Z) : Prop :=
  match buf with Some off => 0 <= off /\ off + len <= 65536 | None => True end.

Definition tr_flush_block_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (s : deflate_state) (buf : option Z) (len last : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + DS_SIZE); (dl_Ab L, dl_Ab L + DS_PEND)] m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ DREP m' L (tr_flush_block s buf len last).

Definition tr_flush_block_stmt : Prop :=
  forall (L : dlay) (s : deflate_state) (buf : option Z) (len last lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DREP m L s -> mem_inv psegs m -> relro_clean m ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> bv_unsigned sp mod 16 = 0 ->
  dlay_below L lo (bv_unsigned sp) ->
  BINV DS_PEND s -> fb_safe s buf len last -> fb_buf_ok buf len -> 0 <= len < 2^64 -> 0 <= last <= 1 ->
  a0 = wz (dl_As L) -> a1 = wz (match buf with Some off => dl_Aw L + off | None => 0 end) -> a2 = wz len -> a3 = wz last ->
  evt psegs (tr_flush_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s buf len last lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_TR_FLUSH_BLOCK) fc None m (seg_rom psegs)).
