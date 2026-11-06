From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import CtrlParsed disco_classify_c GateModel.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_DISCO_GATE_SHOULD_PUSH : Z := 0x15414.
Definition REAC_DISCO_GATE_SHOULD_PUSH_K : Z := 64.

Definition gsp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lo g s now : Z) (G S : list byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (snd (gate_model G S now))) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - REAC_DISCO_GATE_SHOULD_PUSH_K, bv_unsigned sp); (g, g + 264)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    rw_cells rsegs m' g [CB 264 (fst (gate_model G S now))] /\ gate_ok (fst (gate_model G S now)) /\
    bytes_at rsegs m' s S.

Definition reac_disco_gate_should_push_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo g s now : Z) (G S : list byte),
    a0 = Z_to_bv 64 g -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 now -> 0 <= now < 2 ^ 64 ->
    0 < g -> g mod 8 = 0 -> rw_cells rsegs m g [CB 264 G] -> gate_ok G ->
    0 < s -> s mod 4 = 0 -> length S = 24%nat -> bytes_at rsegs m s S ->
    (g + 264 <= s \/ s + 24 <= g) ->
    (g + 264 <= bv_unsigned sp - REAC_DISCO_GATE_SHOULD_PUSH_K \/ bv_unsigned sp <= g) ->
    (s + 24 <= bv_unsigned sp - REAC_DISCO_GATE_SHOULD_PUSH_K \/ bv_unsigned sp <= s) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_DISCO_GATE_SHOULD_PUSH_K <= bv_unsigned sp ->
    mem_inv rsegs m ->
    evt rsegs (gsp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo g s now G S)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_DISCO_GATE_SHOULD_PUSH) fc None m (seg_rom rsegs)).
