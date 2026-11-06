(* Modified by Theorem Labs, 2026-10: the image-B (fuzz_decode.asan-ubsan) text of lib/A/Prog/diginet_personality_of_F.v, proof of diginet_personality_of_contract_F (lib/B/Prog/diginet_personality_of_F_c.v) in the leaf form of proofs/libreac/fuzz_decode/lib/B/Prog/check_braid_F.v at recipes commit 88154566652a, path for path with lib/U/Prog/diginet_personality_of.v (the UBSan walk: image B's 14 words are the UBSan image's but for the two auipc / addi pairs) at this image's table address. *)
(* Proof of diginet_personality_of_contract_F (image B, entry 0x82938). Three paths: desk 1 returns 0x9ab20
   (0x8293c taken, 0x82958-0x82960), desk 2 returns 0x9ab38 (0x82940-0x82954), any other desk returns 0 (0x82944
   taken, 0x82964-0x82968). The UBSan trap word 0x8296c is refuted on the desk-2 path: the check 0x82950 `beqz a0`
   tests the constant 0x9ab38 that 0x82948-0x8294c form, so it is decided not taken (if_false) without a premise. The
   code makes no data access, so no step needs an rng fact. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import diginet_personality_of_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* the model's result for each desk value the binary tests *)
Lemma personality_of_cases_B : forall d,
  diginet_personality_of d = if d =? 1 then Some 0 else if d =? 2 then Some 1 else None.
Proof.
  intros d. unfold diginet_personality_of, personalities, DIGINET_DESK_CONTROL24, DIGINET_DESK_PROCONTROL.
  cbn [personality_find dp_desk]. rewrite (Z.eqb_sym 1 d), (Z.eqb_sym 2 d). reflexivity.
Qed.

Theorem diginet_personality_of_holds_F : diginet_personality_of_contract_F.
Proof.
  unfold diginet_personality_of_contract_F, DIGINET_PERSONALITY_OF.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m desk HD.
  rewrite personality_of_cases_B.
  (* 0x82938 addi a1, zero, 1; 0x8293c beq a0, a1 *)
  step. step. if_cases HB.
  - (* desk 1: 0x82958 auipc, 0x8295c addi, 0x82960 ret *)
    zify_cond HB.
    assert (E : desk = 1) by (Z.div_mod_to_equations; lia). subst desk. cbn [Z.eqb Pos.eqb].
    step. step. step. apply evtF_done. do 2 eexists. reflexivity.
  - zify_cond HB.
    assert (N1 : desk <> 1) by (intro; subst; apply HB; reflexivity).
    rewrite (proj2 (Z.eqb_neq desk 1) N1).
    (* 0x82940 addi a1, zero, 2; 0x82944 bne a0, a1 *)
    step. step. if_cases H2.
    + (* any other desk: 0x82964 addi a0, zero, 0, 0x82968 ret *)
      zify_cond H2.
      assert (N2 : desk <> 2) by (intro; subst; apply H2; reflexivity).
      rewrite (proj2 (Z.eqb_neq desk 2) N2).
      step. step. apply evtF_done. do 2 eexists. reflexivity.
    + (* desk 2: 0x82948 auipc, 0x8294c addi, 0x82950 beqz a0 (the UBSan check, not taken), 0x82954 ret *)
      zify_cond H2.
      assert (E : desk = 2) by (Z.div_mod_to_equations; lia). subst desk. cbn [Z.eqb Pos.eqb].
      step. step. step. if_false. step. apply evtF_done. do 2 eexists. reflexivity.
Qed.
