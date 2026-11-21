(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_checksum_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk FuzzMem U0FuzzBase U0Fuzz_code U0FuzzIface U0FuzzStmt
  U0Fuzz_adler U0Fuzz_crc U0Fuzz_cop U0Fuzz_gen U0Fuzz_comb U0Fuzz_adlc
  U0FuzzA U0FuzzB U0FuzzC U0FuzzD.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.cks Require Import CkTables CkModel CkMathCrc CkMathAdler CkHarness.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac xfer K H H2 :=
  lazymatch type of K with keeps_cs ?ra ?rb =>
    lazymatch type of H with getr _ ?i = ?v =>
      assert (H2 : getr rb i = v) by (rewrite (K i) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact H)
    end
  end.
Ltac retok := apply ret_ok_even; reflexivity.

Lemma chunk_arith : forall n b q, 1 <= b -> 0 <= n -> q = n / b ->
  (0 + q * b <= n < 0 + (q + 1) * b) /\ n mod b = n - q * b /\ 0 <= q * b.
Proof.
  intros n b q Hb Hn Hq.
  pose proof (Z.div_mod n b ltac:(lia)) as E. pose proof (Z.mod_pos_bound n b ltac:(lia)) as R.
  assert (Hq0 : 0 <= q) by (rewrite Hq; apply Z.div_pos; lia).
  rewrite <- Hq in E. nia.
Qed.

Section MAIN.
Context {RCa1 : RunCtx}.
  Variables (mem : word -> option byte) (sp ret : word) (rom : word -> option byte).
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : FR <= bv_unsigned sp.
  Hypothesis Hstk : store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - FR)) (Z.to_nat FR) = true.
  Hypothesis Himg : img_ok mem.

  #[local] Abbreviation usp := (bv_unsigned sp).
  #[local] Abbreviation W8 v := (word_to_le_bytes 8 v).
  #[local] Abbreviation M13r := (m13 mem (bv_unsigned sp)).

  Lemma keeps_cs_of : forall regs r,
    lkeeps hk regs r -> getr r 1 = getr regs 1 -> getr r 2 = getr regs 2 -> getr r 8 = getr regs 8 ->
    getr r 9 = getr regs 9 -> getr r 18 = getr regs 18 -> getr r 19 = getr regs 19 ->
    getr r 20 = getr regs 20 -> getr r 21 = getr regs 21 -> getr r 22 = getr regs 22 ->
    getr r 23 = getr regs 23 -> getr r 24 = getr regs 24 -> getr r 25 = getr regs 25 ->
    getr r 26 = getr regs 26 -> getr r 27 = getr regs 27 -> keeps_cs regs r.
  Proof.
    intros regs r K E1 E2 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 x Hx. cbv [callee_saved In] in Hx.
    repeat (destruct Hx as [<-|Hx]; [ first [ assumption | apply K; cbv [hk In]; (first [solve [liafast_keep_section; tauto] | tauto]) ] |]).
    destruct Hx.
  Qed.

  Lemma M13_slots : forall regs,
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (M13r regs) (Z_to_bv 64 (usp - 8)) 8 = Some (W8 (getr regs 1)) /\
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (M13r regs) (Z_to_bv 64 (usp - 16)) 8 = Some (W8 (getr regs 8)) /\
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (M13r regs) (Z_to_bv 64 (usp - 24)) 8 = Some (W8 (getr regs 9)) /\
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (M13r regs) (Z_to_bv 64 (usp - 32)) 8 = Some (W8 (getr regs 18)) /\
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (M13r regs) (Z_to_bv 64 (usp - 40)) 8 = Some (W8 (getr regs 19)) /\
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (M13r regs) (Z_to_bv 64 (usp - 48)) 8 = Some (W8 (getr regs 20)) /\
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (M13r regs) (Z_to_bv 64 (usp - 56)) 8 = Some (W8 (getr regs 21)) /\
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (M13r regs) (Z_to_bv 64 (usp - 64)) 8 = Some (W8 (getr regs 22)) /\
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (M13r regs) (Z_to_bv 64 (usp - 72)) 8 = Some (W8 (getr regs 23)) /\
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (M13r regs) (Z_to_bv 64 (usp - 80)) 8 = Some (W8 (getr regs 24)) /\
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (M13r regs) (Z_to_bv 64 (usp - 88)) 8 = Some (W8 (getr regs 25)) /\
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (M13r regs) (Z_to_bv 64 (usp - 96)) 8 = Some (W8 (getr regs 26)) /\
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (M13r regs) (Z_to_bv 64 (usp - 104)) 8 = Some (W8 (getr regs 27)).
  Proof.
    intros regs. pose proof (u64_range sp). unfold FR in Hsp. unfold m13.
    repeat split; rdn_solve.
  Qed.

  Lemma ro_apart : RO_HI <= usp - 240 \/ usp <= RO_LO.
  Proof.
    pose proof (u64_range sp). unfold FR in Hsp, Hstk.
    destruct (store_ok_off_ro mem (usp - 240) (Z.to_nat 240) Hstk ltac:(lia)
                ltac:(change (Z.of_nat (Z.to_nat 240)) with 240; lia) ltac:(change (Z.of_nat (Z.to_nat 240)) with 240; lia) Himg);
      change (Z.of_nat (Z.to_nat 240)) with 240 in *; lia.
  Qed.

  Lemma stk112 : store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (usp - 112)) 112 = true.
  Proof.
    pose proof (u64_range sp). unfold FR in Hsp, Hstk.
    eapply (store_ok_sub (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (usp - 240)) _ (Z.to_nat 240) 112%nat);
      [ u_norm; change (Z.of_nat (Z.to_nat 240)) with 240; lia | exact Hstk | u_norm; lia
      | u_norm; change (Z.of_nat (Z.to_nat 240)) with 240; change (Z.of_nat 112) with 112; lia ].
  Qed.

  Lemma M13_img : forall regs, img_ok (M13r regs).
  Proof.
    intros regs. pose proof (u64_range sp). unfold FR in Hsp.
    apply m13_img; [lia | apply stk112 | exact Himg].
  Qed.

  Lemma M13_frame : forall regs, frame_mod mem (M13r regs) (FRR sp).
  Proof.
    intros regs. pose proof (u64_range sp). unfold FR in Hsp.
    eapply frame_mod_weaken; [| apply m13_frame; lia].
    intros a [Ha _]. cbn [outside]. split; [|exact I]. unfold FRR, FR, in_rng in *. rewrite !u64_lit in Ha |- * by lia. lia.
  Qed.

  Lemma fm_sub : forall m m' z k, frame_mod m m' [(Z_to_bv 64 z, k)] -> usp - 240 <= z -> z + k <= usp -> 0 <= k ->
    frame_mod m m' (FRR sp).
  Proof.
    intros m m' z k Hf Hlo Hhi Hk. pose proof (u64_range sp). unfold FR in Hsp.
    eapply frame_mod_weaken; [| exact Hf].
    intros a [Ha _]. cbn [outside]. split; [|exact I]. unfold FRR, FR, in_rng in *. rewrite !u64_lit in Ha |- * by lia. lia.
  Qed.

  Lemma slot_ok : forall m z, mem_grows mem m -> usp - 240 <= z -> z + 8 <= usp -> store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 z) 8 = true.
  Proof.
    intros m z Hg Hlo Hhi. eapply (stk_ok8 mem); [exact Hstk | exact Hsp | exact Hg | unfold FR; lia | lia].
  Qed.

  Lemma callee_ok : forall m (k : nat), mem_grows mem m -> Z.of_nat k <= 128 ->
    store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 112 - Z.of_nat k)) k = true.
  Proof.
    intros m k Hg Hk. pose proof (u64_range sp). unfold FR in Hsp, Hstk.
    eapply store_ok_mono; [exact Hg|].
    eapply (store_ok_sub (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (usp - 240)) _ (Z.to_nat 240) k);
      [ u_norm; change (Z.of_nat (Z.to_nat 240)) with 240; lia | exact Hstk | u_norm; lia
      | u_norm; change (Z.of_nat (Z.to_nat 240)) with 240; lia ].
  Qed.

  Lemma img_frame : forall m m', img_ok m -> frame_mod m m' (FRR sp) -> img_ok m'.
  Proof.
    intros m m' Hi [Ho _] i Hri. pose proof (u64_range sp). pose proof ro_apart. unfold FR in Hsp.
    rewrite Ho; [apply Hi; exact Hri|].
    cbn [outside FRR]. split; [|exact I]. unfold FRR, FR, in_rng, RO_LO, RO_HI in *. rewrite !u64_lit by lia. lia.
  Qed.

  Lemma slot_frame : forall m m' z k s, frame_mod m m' [(Z_to_bv 64 z, k)] -> usp - 240 <= z -> z + k <= usp - 112 -> 0 <= k ->
    usp - 112 <= s -> s + 8 <= usp -> rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m' (Z_to_bv 64 s) 8 = rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 s) 8.
  Proof.
    intros m m' z k s Hf Hlo Hhi Hk Hs1 Hs2. pose proof (u64_range sp). unfold FR in Hsp.
    apply (frame_mod_rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m m' _ 8 (Z_to_bv 64 s) Hf).
    - intros i Hi. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite (u64_lit s) by lia. rewrite !u64_lit by lia.
      change (Z.of_nat 8) with 8 in Hi. lia.
    - rewrite u64_lit by lia. change (Z.of_nat 8) with 8. lia.
  Qed.

  Lemma prefix_run : forall regs (data : word) (n : Z),
    getr regs 2 = sp -> getr regs 10 = data -> getr regs 11 = Z_to_bv 64 n ->
    exists r m4,
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14210 : word) mem rom) (mkst r (0x14274 : word) m4 rom)
      /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 (bv_unsigned data)
      /\ getr r 10 = Z_to_bv 64 1 /\ getr r 19 = Z_to_bv 64 0
      /\ lkeeps hk regs r
      /\ frame_mod (M13r regs) m4 [(Z_to_bv 64 (usp - 240), 128%Z)]
      /\ frame_mod mem m4 (FRR sp) /\ img_ok m4
      /\ (forall s, usp - 112 <= s -> s + 8 <= usp -> rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m4 (Z_to_bv 64 s) 8 = rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (M13r regs) (Z_to_bv 64 s) 8).
  Proof.
    intros regs data n R2 R10 R11. pose proof (u64_range sp). pose proof Hsp as Hsp'. unfold FR in Hsp'.
    assert (R2' : getr regs 2 = Z_to_bv 64 usp) by (rewrite R2; apply word_zv).
    pose proof (M13_frame regs) as HMf. pose proof (M13_img regs) as HMi.
    destruct (prologue_run mem sp rom Hsp Hstk regs data n R2' R10 R11)
      as (r1 & M1 & P1 & P2 & P8 & P9 & P10 & P11 & P12 & K1).
    destruct (u0_crc32_null r1 (M13r regs) rom (0x14260%bv : word) (usp - 112) P1 ltac:(retok) P2 P11 ltac:(lia)
                ltac:(replace (usp - 112 - 112) with (usp - 112 - Z.of_nat 112) by lia;
                      apply callee_ok; [apply m13_grows | change (Z.of_nat 112) with 112; lia]))
      as (r2 & m2 & M2 & V2 & K2 & F2).
    xfer K2 P2 Q2. xfer K2 P8 Q8. xfer K2 P9 Q9.
    assert (Hf2 : frame_mod mem m2 (FRR sp)).
    { eapply frame_mod_trans_same; [exact HMf|]. eapply fm_sub; [exact F2 | lia | lia | lia]. }
    destruct (segB rom r2 m2 _ V2) as (r3 & M3 & A1 & A19 & A10 & A11 & A12 & A2 & A8 & A9 & K3).
    rewrite Q2 in A2. rewrite Q8 in A8. rewrite Q9 in A9.
    destruct (u0_adler32_null r3 m2 rom (0x14274%bv : word) (usp - 112) A1 ltac:(retok) A2 A11 A12 ltac:(lia)
                ltac:(replace (usp - 112 - 128) with (usp - 112 - Z.of_nat 128) by lia;
                      apply callee_ok; [exact (proj2 Hf2) | change (Z.of_nat 128) with 128; lia]))
      as (r4 & m4 & M4 & V4 & K4 & F4).
    replace (usp - 112 - 128) with (usp - 240) in F4 by lia.
    xfer K4 A2 B2. xfer K4 A8 B8. xfer K4 A9 B9. xfer K4 A19 B19.
    assert (Hf4 : frame_mod mem m4 (FRR sp)).
    { eapply frame_mod_trans_same; [exact Hf2|]. eapply fm_sub; [exact F4 | lia | lia | lia]. }
    exists r4, m4. split.
    { eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|]. exact M4. }
    split; [exact B2|]. split; [exact B8|]. split; [rewrite B9; apply word_zv|]. split; [exact V4|]. split; [exact B19|].
    split.
    { intros x Hx. rewrite (K4 x) by (revert Hx; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K3 x Hx).
      rewrite (K2 x) by (revert Hx; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). apply (K1 x Hx). }
    split.
    { eapply frame_mod_trans_same.
      - eapply frame_mod_weaken; [| exact F2].
        intros a [Ha _]. cbn [outside]. split; [|exact I]. unfold in_rng in *. rewrite !u64_lit in Ha |- * by lia. lia.
      - exact F4. }
    split; [exact Hf4|]. split; [exact (img_frame mem m4 Himg Hf4)|].
    intros s Hs1 Hs2.
    rewrite (slot_frame m2 m4 (usp - 240) 128 s F4) by lia.
    apply (slot_frame (M13r regs) m2 (usp - 112 - 112) 112 s F2); lia.
  Qed.

  Lemma fuzz_trivial : forall regs (data : word) (n : Z),
    getr regs 1 = ret -> getr regs 2 = sp -> getr regs 10 = data -> getr regs 11 = Z_to_bv 64 n ->
    1 <= bv_unsigned data -> 0 <= n < two64 -> (n = 0 \/ 1048576 < n) ->
    exists regs' mem',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14210 : word) mem rom) (mkst regs' ret mem' rom)
      /\ keeps_cs regs regs' /\ getr regs' 10 = Z_to_bv 64 0 /\ frame_mod mem mem' (FRR sp).
  Proof.
    intros regs data n R1 R2 R10 R11 Hdata Hn Hout. pose proof (u64_range sp). pose proof (u64_range data).
    destruct (prefix_run regs data n R2 R10 R11) as (r4 & m4 & M4 & B2 & B8 & B9 & B10 & B19 & K4 & F4 & Hf4 & Hi4 & SL).
    destruct (segC_out rom r4 m4 (bv_unsigned data) n B9 B8 ltac:(lia) Hn Hout) as (r5 & M5 & C2 & K5).
    rewrite B2 in C2.
    pose proof (M13_slots regs) as (E1 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
    destruct (epilogue_run sp ret rom Hret r5 m4 (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18)
                (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
                (getr regs 25) (getr regs 26) (getr regs 27) C2 R1
                ltac:(rewrite SL by lia; exact E1) ltac:(rewrite SL by lia; exact E8)
                ltac:(rewrite SL by lia; exact E9) ltac:(rewrite SL by lia; exact E18)
                ltac:(rewrite SL by lia; exact E19) ltac:(rewrite SL by lia; exact E20)
                ltac:(rewrite SL by lia; exact E21) ltac:(rewrite SL by lia; exact E22)
                ltac:(rewrite SL by lia; exact E23) ltac:(rewrite SL by lia; exact E24)
                ltac:(rewrite SL by lia; exact E25) ltac:(rewrite SL by lia; exact E26)
                ltac:(rewrite SL by lia; exact E27))
      as (r6 & M6 & Q10 & Z1 & Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27 & K6).
    exists r6, m4. split; [|split; [|split]].
    - eapply msteps_trans; [exact M4|]. eapply msteps_trans; [exact M5|]. exact M6.
    - apply keeps_cs_of; try assumption.
      + intros x Hx. rewrite (K6 x Hx). rewrite (K5 x Hx). apply (K4 x Hx).
      + rewrite Z2, R2. symmetry. apply word_zv.
    - exact Q10.
    - exact Hf4.
  Qed.

  Lemma fuzz_main : forall regs (data : word) (n : Z),
    getr regs 1 = ret -> getr regs 2 = sp -> getr regs 10 = data -> getr regs 11 = Z_to_bv 64 n ->
    1 <= n <= 1048576 -> 1 <= bv_unsigned data -> bv_unsigned data + n < 2 ^ 64 ->
    (forall i, 0 <= i < n -> exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned data + i)) 1 = Some [b]) ->
    bv_unsigned data + n <= usp - 240 ->
    exists regs' mem',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14210 : word) mem rom) (mkst regs' ret mem' rom)
      /\ keeps_cs regs regs' /\ getr regs' 10 = Z_to_bv 64 0 /\ frame_mod mem mem' (FRR sp).
  Proof.
    intros regs data n R1 R2 R10 R11 Hn Hdata Hnw Hrd Hapart.
    pose proof (u64_range sp). pose proof (u64_range data). pose proof Hsp as Hsp'. unfold FR in Hsp'.
    pose proof ro_apart as Hro.
    set (udata := bv_unsigned data) in *.
    destruct (prefix_run regs data n R2 R10 R11) as (r4 & m4 & M4 & B2 & B8 & B9 & B10 & B19 & K4 & F4 & Hf4 & Hi4 & SL).
    fold udata in B9.
    destruct (Hrd 0 ltac:(lia)) as [bb Hbb]. rewrite Z.add_0_r in Hbb.
    assert (Hb0 : bv_unsigned bb = hb0 mem data) by (unfold hb0; symmetry; exact (byte_at_rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem udata bb Hbb)).
    assert (Hbb' : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m4 (Z_to_bv 64 udata) 1 = Some [bb]).
    { rewrite <- Hbb. apply (frame_mod_rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem m4 (FRR sp) 1 (Z_to_bv 64 udata) Hf4).
      - intros i Hi. cbn [outside FRR]. split; [|exact I]. unfold in_rng, FR.
        rewrite (u64_lit udata) by lia. rewrite !u64_lit by lia. lia.
      - rewrite u64_lit by lia. change (Z.of_nat 1) with 1. lia. }
    remember (hB mem data) as Bv eqn:HBv.
    pose proof (hB_range mem data) as HBr. rewrite <- HBv in HBr.
    destruct (segC_in sp rom Hsp r4 m4 udata n (Z_to_bv 64 1) bb (hb0 mem data) Bv B9 B8 B2 B10 B19
                ltac:(lia) ltac:(lia) Hn
                ltac:(apply slot_ok; [exact (proj2 Hf4) | lia | lia]) Hbb' Hb0 ltac:(rewrite HBv; reflexivity))
      as (r5 & M5 & C1 & C10 & C18 & C19 & C20 & C26 & C2 & C8 & C9 & K5).
    set (M0 := wbytes m4 (Z_to_bv 64 (usp - 112)) (word_to_le_bytes 8 (Z_to_bv 64 1))) in M5.
    assert (HU : u0H mem sp data n M0).
    { constructor.
      - exact Hn.
      - exact Hdata.
      - exact Hnw.
      - lia.
      - exact Hrd.
      - exact Hstk.
      - exact Himg.
      - exact Hapart.
      - subst M0. apply fm_w8; [exact Hsp | exact Hf4 | unfold FR; lia | lia].
      - subst M0. apply img_ok_wbytes; [exact Hi4 | |]; rewrite lenW8; change (Z.of_nat 8) with 8; u_norm;
          unfold RO_LO, RO_HI in *; lia.
      - subst M0. rdn_solve. }
    pose proof (minv_M0_ mem sp data n M0 HU) as HM.
    assert (HM0i : img_ok M0) by exact (UM0i _ _ _ _ _ HU).
    destruct (u0_crc32_combine_gen r5 M0 rom (0x142b0%bv : word) Bv C1 ltac:(retok) C10 ltac:(lia) HM0i)
      as (r6 & M6 & V6 & K6).
    remember (crc32_combine_gen Bv) as OPv eqn:HOPv.
    pose proof (OPv_range Bv OPv HOPv) as HOPr.
    xfer K6 C2 D2'. xfer K6 C8 D8. xfer K6 C9 D9. xfer K6 C18 D18. xfer K6 C19 D19. xfer K6 C20 D20. xfer K6 C26 D26.
    destruct (segD rom r6 M0 OPv n V6 D8 D19 HOPr Hn)
      as (r7 & M7 & E27 & E22 & E19 & E24 & E21 & E2 & E8 & E9 & E18 & E20 & E26 & K7).
    rewrite D2' in E2. rewrite D9 in E9. rewrite D18 in E18. rewrite D20 in E20. rewrite D26 in E26.
    remember (Z.to_nat (n / Bv)) as k eqn:Hkdef.
    assert (Hk : Z.of_nat k = n / Bv) by (rewrite Hkdef, Z2Nat.id; [reflexivity | apply Z.div_pos; lia]).
    destruct (chunk_arith n Bv (Z.of_nat k) ltac:(lia) ltac:(lia) Hk) as (Hkb & Hmod & Hk0).
    pose proof harness_crc_init as HCI. rewrite <- (HD_0 mem data) in HCI.
    assert (HCRH : CRH sp data n Bv OPv r7 0 (crc32_spec 0 (HD mem data 0))).
    { rewrite HCI. unfold CRH. fold udata. repeat split; assumption. }
    destruct (crc_loop mem sp data n M0 rom HU Bv OPv HBv HOPv k r7 M0 0 HCRH HM ltac:(lia) Hkb)
      as (r8 & m8 & M8 & HM8 & K8 & F11 & F18 & F2 & F8 & F9 & F19 & F20 & F22 & F26).
    rewrite Z.add_0_l in F11, F18.
    assert (Hoffq : 0 <= Z.of_nat k * Bv <= n) by lia.
    destruct (phase2 mem sp data n M0 rom HU Bv HBv r8 m8 (Z.of_nat k * Bv)
                F11 F18 F2 F8 F9 F19 F20 F22 F26 HM8 Hoffq ltac:(lia) Hmod)
      as (r9 & m9 & M9 & HM9 & K9 & G2 & G8 & G9 & G19 & G20 & G21 & G26 & G27).
    destruct (phase3 mem sp data n M0 rom HU Bv HBv k r9 m9 G2 G8 G9 G19 G20 G21 G26 G27 HM9 ltac:(lia))
      as (r10 & m10 & M10 & HM10 & K10 & J2).
    pose proof (M13_slots regs) as (S1 & S8 & S9 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27).
    assert (SL0 : forall s, usp - 104 <= s -> s + 8 <= usp ->
              rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m10 (Z_to_bv 64 s) 8 = rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (M13r regs) (Z_to_bv 64 s) 8).
    { intros s Hs1 Hs2. rewrite (minv_slot_ mem sp data n M0 HU m10 s HM10) by lia.
      subst M0. rewrite rdn_wbytes_out_Z; [apply SL; lia|].
      rewrite lenW8. change (Z.of_nat 8) with 8. lia. }
    destruct (epilogue_run sp ret rom Hret r10 m10 (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18)
                (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
                (getr regs 25) (getr regs 26) (getr regs 27) J2 R1
                ltac:(rewrite SL0 by lia; exact S1) ltac:(rewrite SL0 by lia; exact S8)
                ltac:(rewrite SL0 by lia; exact S9) ltac:(rewrite SL0 by lia; exact S18)
                ltac:(rewrite SL0 by lia; exact S19) ltac:(rewrite SL0 by lia; exact S20)
                ltac:(rewrite SL0 by lia; exact S21) ltac:(rewrite SL0 by lia; exact S22)
                ltac:(rewrite SL0 by lia; exact S23) ltac:(rewrite SL0 by lia; exact S24)
                ltac:(rewrite SL0 by lia; exact S25) ltac:(rewrite SL0 by lia; exact S26)
                ltac:(rewrite SL0 by lia; exact S27))
      as (r12 & M12 & Q10 & Z1 & Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27 & K12).
    exists r12, m10. split; [|split; [|split]].
    - eapply msteps_trans; [exact M4|]. eapply msteps_trans; [exact M5|]. eapply msteps_trans; [exact M6|].
      eapply msteps_trans; [exact M7|]. eapply msteps_trans; [exact M8|]. eapply msteps_trans; [exact M9|].
      eapply msteps_trans; [exact M10|]. exact M12.
    - apply keeps_cs_of; try assumption.
      + intros x Hx.
        rewrite (K12 x Hx). rewrite (K10 x Hx). rewrite (K9 x Hx). rewrite (K8 x Hx).
        rewrite (K7 x Hx). rewrite (K6 x) by (revert Hx; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K5 x Hx). apply (K4 x Hx).
      + rewrite Z2, R2. symmetry. apply word_zv.
    - exact Q10.
    - exact (minv_total_ mem sp data n M0 HU m10 HM10).
  Qed.
End MAIN.


Theorem u0_fuzz {RCa1 : RunCtx}  : u0_fuzz_stmt.
Proof.
  intros regs mem rom ret sp data n R1 Hret R2 R10 R11 Hn Hdata Hnw Hsp Hrd Hstk Hapart Himg.
  pose proof (u64_range data).
  assert (Hnr : 0 <= n < two64) by lia.
  change [(Z_to_bv 64 (bv_unsigned sp - 240), 240%Z)] with (FRR sp).
  pose proof (img_ok_of_hyp mem Himg) as Himg'.
  destruct (Z.le_gt_cases 1 n) as [H1|H1]; [destruct (Z.le_gt_cases n 1048576) as [H2|H2]|].
  -
    exact (fuzz_main mem sp ret rom Hret Hsp Hstk Himg' regs data n R1 R2 R10 R11 ltac:(lia) Hdata Hnw
             ltac:(apply Hrd; lia) ltac:(apply Hapart; lia)).
  - apply (fuzz_trivial mem sp ret rom Hret Hsp Hstk Himg' regs data n R1 R2 R10 R11 Hdata Hnr). lia.
  - apply (fuzz_trivial mem sp ret rom Hret Hsp Hstk Himg' regs data n R1 R2 R10 R11 Hdata Hnr). lia.
Qed.
