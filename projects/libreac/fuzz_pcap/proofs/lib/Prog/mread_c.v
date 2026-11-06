From OSSVerify.libreac.fuzz_pcap Require Symbols.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel.
Import ListNotations.
Open Scope Z_scope.

Definition MREAD_FN : Z := Eval compute in Symbols.Plain.s_mread.
Definition MREAD_K : Z := 48.

Definition mread_t (l n q : Z) : Z := Z.min l (n - q).
Definition mread_rem2 (l n q : Z) : Z := Z.min (n - q - mread_t l n q) 1024.

Definition mread_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h d l : word) (b : Z) (Fc : list byte) (md : word) (q : Z) (pv nx : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0' a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ a0' = wz (mread_t (bv_unsigned l) (Z.of_nat (length Fc)) q)
    /\ munch [(bv_unsigned sp - MREAD_K, bv_unsigned sp); (bv_unsigned d, bv_unsigned d + mread_t (bv_unsigned l) (Z.of_nat (length Fc)) q); (bv_unsigned h, bv_unsigned h + 1304)] m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned d)
         (firstn (Z.to_nat (mread_t (bv_unsigned l) (Z.of_nat (length Fc)) q)) (skipn (Z.to_nat q) Fc))
    /\ mfile m' (bv_unsigned h) b Fc
         (if bv_unsigned l >? Z.of_nat (length Fc) - q then wz 24 else wz 8) md
         (q + mread_t (bv_unsigned l) (Z.of_nat (length Fc)) q + mread_rem2 (bv_unsigned l) (Z.of_nat (length Fc)) q)
         (Some (0, mread_rem2 (bv_unsigned l) (Z.of_nat (length Fc)) q)) pv nx.

Definition mread_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo b : Z) (Fc : list byte)
         (md : word) (q : Z) (rb : option (Z * Z)) (pv nx : word) (junk : list byte),
    mfile m (bv_unsigned a0) b Fc (wz 8) md q rb pv nx -> rlen rb = 0 ->
    rw_cells rsegs m (bv_unsigned a1) [CB (Z.to_nat (bv_unsigned a2)) junk] -> 1 <= bv_unsigned a2 ->
    (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + 1304 <= bv_unsigned a1) ->
    (bv_unsigned a1 + bv_unsigned a2 <= b \/ b + Z.of_nat (length Fc) <= bv_unsigned a1) ->
    (bv_unsigned a1 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a1) ->
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + MREAD_K <= bv_unsigned sp ->
    bv_unsigned a0 + 1304 <= lo -> b + Z.of_nat (length Fc) <= lo ->
    evt rsegs (mread_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 b Fc md q pv nx lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 MREAD_FN) fc None m (seg_rom rsegs)).
