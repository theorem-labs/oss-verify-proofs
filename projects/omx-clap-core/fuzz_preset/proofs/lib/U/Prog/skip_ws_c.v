From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjIn.
Import ListNotations.
Open Scope Z_scope.

Definition SKIP_WS : Z := 0x162e0.

Definition ws (b : byte) : bool :=
  (bv_unsigned b =? 32) || (bv_unsigned b =? 9) || (bv_unsigned b =? 10) || (bv_unsigned b =? 13).

Fixpoint ws_len (bs : list byte) : nat :=
  match bs with
  | b :: bs' => if ws b then S (ws_len bs') else O
  | [] => O
  end.

Definition skip_ws_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (q text len p d : Z) (txt : list byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(q, q + 8)] m m' /\ wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\
    pj_in_ok rsegs m' q text len (p + Z.of_nat (ws_len (skipn (Z.to_nat (p - text)) txt))) d txt.

Definition skip_ws_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q text len p d : Z) (txt : list byte),
    a0 = Z_to_bv 64 q ->
    pj_in_ok rsegs m q text len p d txt ->
    evt rsegs (skip_ws_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m q text len p d txt)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SKIP_WS) fc None m (seg_rom rsegs)).
