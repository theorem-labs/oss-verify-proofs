(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/diginet_meter_segments.v, with its module paths, module names and addresses changed; 35 of its 74 lines of code are new or changed and 123 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the image-B (fuzz_decode.asan-ubsan) text of lib/A/Prog/diginet_meter_segments_F.v, proof of diginet_meter_segments_contract_F (lib/B/Prog/diginet_meter_segments_F_c.v) in the leaf form of proofs/libreac/fuzz_decode/lib/B/Prog/check_braid_F.v at recipes commit 88154566652a, step for step with lib/Prog/diginet_meter_segments.v (the plain walk, whose pure lemmas it uses). *)
(* Proof of diginet_meter_segments_contract_F (image B, entry 0x82dc8). The 14 words are image A's word for word, so
   the walk is image A's with StepF's step at the image-B pcs: `loop` (0x82dcc-0x82de8) by induction on the fuel of
   DgnLib.v's meter_count, then `fin` (0x82dec-0x82dfc). The code makes no data access, so no step needs an rng fact,
   and it has no UBSan trap word. The pure facts (srlw_small, land1_bit, mc_go, mc_stop, mc_range, fin_eq,
   meter_fin) are the plain walk's lemmas; they name no image. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Step ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import diginet_meter_segments_F_c.
(* the plain walk: only its pure lemmas are used, by their qualified names *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require diginet_meter_segments_dec.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import ExecF StepF.
Open Scope Z_scope.

Module P := OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog.diginet_meter_segments_dec.

(* the branch condition of a stepped evtF goal, decided by a closed computation or by a given tactic *)
Ltac brF b := lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b by (vm_compute; reflexivity); cbv iota
  end.
Ltac brF_by b tac := lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b by tac; cbv iota
  end.

Section Walk.
Variables (RNG : ExecF.footprint)
  (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mask : Z).

Local Abbreviation ST pc a0 a1 a2 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom tfibsegs)).

(* 0x82dcc with n in a1 (n < 14, fuel f = 14 - n) to 0x82dec with a2 = meter_count mask n f *)
Lemma loopF : forall (Q : machine_state -> Prop) f n (a2 : word),
  0 <= mask < 2 ^ 16 -> 0 <= n < 14 -> n + Z.of_nat f = 14 ->
  (forall a1' : word, evtF tfibsegs RNG Q (ST 0x85f38 (Z_to_bv 64 mask) a1' (Z_to_bv 64 (meter_count mask n f)))) ->
  evtF tfibsegs RNG Q (ST 0x85f18 (Z_to_bv 64 mask) (Z_to_bv 64 n) a2).
Proof.
  intros Q f; induction f as [|f IH]; intros n a2 HM Hn Hf K; [lia|].
  pose proof (P.shiftr_range mask n HM ltac:(lia)) as R.
  step. step. step.
  rewrite (unsigned_lit mask), (unsigned_lit n) by lia. rewrite (P.srlw_small mask n) by lia.
  rewrite (unsigned_lit (Z.shiftr mask n)) by lia. rewrite (P.land1_bit mask n) by lia.
  destruct (Z.testbit mask n) eqn:B.
  - (* bit n set: n += 1, and on to the next round unless n = 14 *)
    brF false. rewrite (P.mc_go mask n f Hn B) in K.
    step. step. step.
    rewrite (unsigned_lit n) by lia. rewrite (P.swrap_small (n + 1)) by lia.
    destruct (Z.eq_dec n 13) as [E13|N13].
    + subst n. brF false. step.
      assert (f = O) by lia. subst f.
      exact (K (Z_to_bv 64 (13 + 1))).
    + brF_by true ltac:(unfold bv_eqb; rewrite !unsigned_lit by lia;
                        rewrite (proj2 (Z.eqb_neq _ _)) by lia; reflexivity).
      exact (IH (n + 1) (Z_to_bv 64 14) HM ltac:(lia) ltac:(lia) K).
  - (* bit n clear: a2 = n *)
    brF true. rewrite (P.mc_stop mask n f ltac:(lia) B) in K.
    step. exact (K (Z_to_bv 64 n)).
Qed.

(* 0x82dec with a2 = n to the return *)
Lemma finF : forall n (a1 : word), 0 <= mask < 2 ^ 16 -> 0 <= n <= 14 ->
  evtF tfibsegs RNG
    (fun ms' => exists a1' a2' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (P.fin_val mask n)) a1' a2' a3
                     a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m (seg_rom tfibsegs))
    (ST 0x85f38 (Z_to_bv 64 mask) a1 (Z_to_bv 64 n)).
Proof.
  intros n a1 HM Hn.
  step. step. step. step. step. apply evtF_done.
  rewrite (P.fin_eq mask n HM Hn). do 2 eexists. reflexivity.
Qed.

End Walk.

Theorem diginet_meter_segments_holds_F : diginet_meter_segments_contract_F.
Proof.
  unfold diginet_meter_segments_contract_F, DIGINET_METER_SEGMENTS_PC.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mask HM.
  step.
  apply (loopF RNG ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mask
           _ 14%nat 0 a2 HM ltac:(lia) ltac:(lia)).
  intros a1'. rewrite P.meter_fin.
  pose proof (P.mc_range mask 14%nat 0 ltac:(lia) ltac:(lia)) as R.
  exact (finF RNG ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mask
           (meter_count mask 0 14) a1' HM ltac:(lia)).
Qed.
