From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem.
Import ListNotations.
Open Scope Z_scope.

(* The demo image of U/Prog/T/WMem.v, at 0x1010:
     0x1010 auipc a5, 0x41        a5 = 0x42010
     0x1014 addi  a5, a5, 0xb8    a5 = 0x420c8 = W_BASE_UBSAN + OFF_g_q
     0x1018 slli  a1, a1, 2
     0x101c add   a5, a5, a1      a5 = &g_q[a1]
     0x1020 lw    a0, 0(a5)       a0 = g_q[a1], sign-extended
   The load address is the literal 0x420c8 (inside the world) plus the scaled index, so the hook reads
   sub B (60872 + (i << 2)) 4 once lia has the index bound; lw's value is its s32_at. One [replace] puts the
   offset into the model's form OFF_g_q + 4 * i, which is TWorld's Q_at. *)
Lemma demo_load_idx : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (B : list byte) (i : Z),
  wmem demo_segs m B -> 0 <= i < 1024 ->
  evt demo_segs
    (fun ms' => exists a1' a5', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_swrap 32 (Q_at B i))) a1' a2 a3 a4 a5'
                                              a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                          F (Z_to_bv 64 0x1024) fc None m (seg_rom demo_segs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1010) fc None m (seg_rom demo_segs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m B i WM Hi.
  wk_facts.
  do 4 step.                              (* auipc, addi, slli, add: a5 = Z_to_bv 64 (270552 + Z.shiftl i' 2) *)
  step.                                   (* lw a0, 0(a5): a0 = Z_to_bv 64 (s32_at B (60872 + Z.shiftl i' 2)) *)
  lazymatch goal with |- context [s32_at B ?k] =>
    replace k with (OFF_g_q + 4 * i)
      by (rewrite ?unsigned_lit by lia; rewrite ?Z.shiftl_mul_pow2 by lia; unfold OFF_g_q; lia)
  end.
  apply evt_done. hnf. do 2 eexists. reflexivity.
Qed.

(* ---- an indexed STORE and LOAD of a struct-array field: OW.t[n].state = v, then a0 = OW.t[n].state ----
   A made-up 32-byte code image at 0x1000; a4 holds the index n, a1 the value v:
     0x1000 auipc a5, 0x42        a5 = 0x43000
     0x1004 addi  a5, a5, 0x230   a5 = 0x43220 = W_BASE_UBSAN + OFF_OW
     0x1008 slli  a3, a4, 4       a3 = n << 4
     0x100c slli  a4, a4, 2       a4 = n << 2
     0x1010 sub   a4, a3, a4      a4 = 12 * n
     0x1014 add   a5, a5, a4      a5 = W_BASE_UBSAN + OFF_OW + 12 * n
     0x1018 sw    a1, 4(a5)       OW.t[n].state = v
     0x101c lw    a0, 4(a5)       a0 = OW.t[n].state, sign-extended
   Both accesses are at (274992 + (bv_unsigned (Z_to_bv 64 (n' << 4)) - bv_unsigned (Z_to_bv 64 (n' << 2)))) + 4,
   n' = bv_unsigned (Z_to_bv 64 n): two literals with the wrapped index between them, which wk_offset cannot read.
   The hooks rewrite it to W_BASE_UBSAN + (65316 + 12 * n) (wk_idx_norm), prove the access inside the world by lia
   from the bound on n, and name the offset A_OW_t_state n in the new world and in the loaded value. *)
Module DemoIdxImg.
Import Stdlib.Strings.String Stdlib.Strings.PrimString.
Definition seg : Segment := {|
  seg_base := 0x1000%N; seg_size := 32%N; seg_perms := "r-x"%string;
  seg_bytes := ["972704009387072293164700131727003387e640b387e70023a2b70003a54700"%pstring] |}.
End DemoIdxImg.
Definition idx_segs : list Segment := [DemoIdxImg.seg].

(* The stored value Z_to_bv 64 v is open: the length side goal of the store goes by length_le4 and lia
   (wk_len_side), so nothing computes on it. The footprint MU and mem_inv are carried across the store. *)
Lemma demo_store_idx : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (B : list byte) (n v : Z),
  wmem idx_segs m B -> mem_inv idx_segs m -> 0 <= n < OW_t_N ->
  evt idx_segs
    (fun ms' => exists a0' a3' a4' a5' m',
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 v) a2 a3' a4' a5' a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1020) fc None m' (seg_rom idx_segs) /\
       a0' = Z_to_bv 64 (OW_t_state (set_OW_t_state B n v) n) /\
       wmem idx_segs m' (set_OW_t_state B n v) /\ mem_inv idx_segs m' /\
       munch [(W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 v) a2 a3 (Z_to_bv 64 n) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1000) fc None m (seg_rom idx_segs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m B n v
    WM MI Hn.
  pose proof (munch_refl [(W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MU.
  do 6 step.                              (* auipc, addi, slli, slli, sub, add *)
  step.                                   (* sw a1, 4(a5): the world is now upd B (A_OW_t_state n) (put 4 v) *)
  step.                                   (* lw a0, 4(a5): a0 = Z_to_bv 64 (s32_at (upd B ..) (A_OW_t_state n)) *)
  apply evt_done. hnf. do 5 eexists. split; [reflexivity|]. split; [reflexivity|]. split; [|split]; eassumption.
Qed.
