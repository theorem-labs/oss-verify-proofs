(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)

From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Tgt_checksum_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk FuzzMem U0FuzzBase U0Fuzz_code U0FuzzIface U0FuzzStmt U0Fuzz_crc.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.cks Require Import CkTables CkModel CkMathCrc CkMathAdler CkHarness.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation W8 v := (word_to_le_bytes 8 v).


Definition hk : list reg := [3; 4]%bv.

Definition R128 (sp : word) : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp - 240), 128%Z)].

Definition MINV (sp : word) (M0 m : word -> option byte) : Prop := frame_mod M0 m (R128 sp) /\ img_ok m.

Definition HD {RCa1 : RunCtx}  (mem : word -> option byte) (data : word) (k : Z) : list Z :=
  bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem (bv_unsigned data) (Z.to_nat k).
Definition CHK {RCa1 : RunCtx}  (mem : word -> option byte) (data : word) (off k : Z) : list Z :=
  bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem (bv_unsigned data + off) (Z.to_nat k).
Definition hb0 {RCa1 : RunCtx}  (mem : word -> option byte) (data : word) : Z := byte_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem (bv_unsigned data).
Definition hB {RCa1 : RunCtx}  (mem : word -> option byte) (data : word) : Z := if hb0 mem data =? 0 then 1 else hb0 mem data.

Record u0H {RCa1 : RunCtx}  (mem : word -> option byte) (sp data : word) (n : Z) (M0 : word -> option byte) : Prop := U0H {
  Un     : 1 <= n <= 1048576;
  Udata  : 1 <= bv_unsigned data;
  Unw    : bv_unsigned data + n < 2 ^ 64;
  Usp    : 240 <= bv_unsigned sp;
  Urd    : forall i, 0 <= i < n -> exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned data + i)) 1 = Some [b];
  Ustk   : store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 240)) 240 = true;
  Uimg   : img_ok mem;
  Uapart : bv_unsigned data + n <= bv_unsigned sp - 240;
  UM0f   : frame_mod mem M0 (FRR sp);
  UM0i   : img_ok M0;
  UM0s   : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M0 (Z_to_bv 64 (bv_unsigned sp - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)) }.
Arguments U0H {RCa1}.

Lemma HD_bytes {RCa1 : RunCtx}  : forall mem data k, bytes (HD mem data k).
Proof. intros. unfold HD, bytes. apply bytes_at_range. Qed.
Lemma CHK_bytes {RCa1 : RunCtx}  : forall mem data off k, bytes (CHK mem data off k).
Proof. intros. unfold CHK, bytes. apply bytes_at_range. Qed.
Lemma CHK_len {RCa1 : RunCtx}  : forall mem data off k, 0 <= k -> Zlen (CHK mem data off k) = k.
Proof. intros. unfold CHK, Zlen. rewrite bytes_at_length. lia. Qed.
Lemma HD_0 {RCa1 : RunCtx}  : forall mem data, HD mem data 0 = [].
Proof. intros. reflexivity. Qed.
Lemma hb0_range {RCa1 : RunCtx}  : forall mem data, 0 <= hb0 mem data < 256.
Proof. intros. unfold hb0. apply byte_at_range. Qed.
Lemma hB_range {RCa1 : RunCtx}  : forall mem data, 1 <= hB mem data <= 256.
Proof. intros. unfold hB. pose proof (hb0_range mem data). destruct (Z.eqb_spec (hb0 mem data) 0); lia. Qed.



Section INV.
Context {RCa1 : RunCtx}.
  Variables (mem : word -> option byte) (sp data : word) (n : Z) (M0 : word -> option byte).
  Hypothesis HU : u0H mem sp data n M0.
  #[local] Abbreviation usp := (bv_unsigned sp).
  #[local] Abbreviation udata := (bv_unsigned data).

  Ltac ranges := pose proof (u64_range data); pose proof (u64_range sp); destruct HU.

  Lemma minv_M0_ : MINV sp M0 M0.
  Proof. split; [apply frame_mod_refl | exact (UM0i _ _ _ _ _ HU)]. Qed.

  Lemma minv_img_ : forall m, MINV sp M0 m -> img_ok m.
  Proof. intros m [_ H]; exact H. Qed.

  Lemma minv_grows_ : forall m, MINV sp M0 m -> mem_grows mem m.
  Proof.
    intros m [[_ Hg] _]. destruct (UM0f _ _ _ _ _ HU) as [_ Hg0]. eapply mem_grows_trans; [exact Hg0 | exact Hg].
  Qed.

  Lemma minv_stk_ : forall m z (k : nat), MINV sp M0 m -> usp - 240 <= z -> z + Z.of_nat k <= usp ->
    store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 z) k = true.
  Proof.
    intros m z k HM Hlo Hhi. pose proof (minv_grows_ m HM) as Hg. ranges.
    eapply store_ok_mono; [exact Hg|].
    eapply (store_ok_sub (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (usp - 240)) _ 240 k);
      [ u_norm; lia | exact Ustk0 | u_norm; lia | u_norm; change (Z.of_nat 240) with 240; lia ].
  Qed.

  Lemma minv_rd_ : forall m, MINV sp M0 m -> forall i, 0 <= i < n ->
    exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (udata + i)) 1 = Some [b].
  Proof.
    intros m HM. pose proof (minv_grows_ m HM) as Hg. ranges.
    apply (readable_grows (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem m udata n); [exact Hg | exact Urd0].
  Qed.

  Lemma minv_rd_off_ : forall m off k, MINV sp M0 m -> 0 <= off -> off + k <= n -> forall i, 0 <= i < k ->
    exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (udata + off + i)) 1 = Some [b].
  Proof.
    intros m off k HM Hoff Hk i Hi. rewrite <- Z.add_assoc. apply (minv_rd_ m HM). lia.
  Qed.

  Lemma minv_bytes_ : forall m off k, MINV sp M0 m -> 0 <= off -> 0 <= k -> off + k <= n ->
    bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (udata + off) (Z.to_nat k) = bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem (udata + off) (Z.to_nat k).
  Proof.
    intros m off k [[Ho _] _] Hoff Hk Hn. ranges. destruct UM0f0 as [Ho0 _].
    apply bytes_at_ext. intros i Hi.
    assert (E1 : m (Z_to_bv 64 (udata + off + i)) = M0 (Z_to_bv 64 (udata + off + i))).
    { apply Ho. cbn [outside R128]. split; [|exact I]. unfold in_rng. rewrite !u64_lit by lia. lia. }
    rewrite E1. apply Ho0. cbn [outside FRR]. split; [|exact I]. unfold in_rng, FR. rewrite !u64_lit by lia. lia.
  Qed.

  Lemma frame_off_ro_ : RO_HI <= usp - 240 \/ usp <= RO_LO.
  Proof.
    ranges.
    destruct (store_ok_off_ro mem (usp - 240) 240%nat Ustk0 ltac:(lia)
                ltac:(change (Z.of_nat 240%nat) with 240; lia) ltac:(change (Z.of_nat 240%nat) with 240; lia) Uimg0);
      change (Z.of_nat 240%nat) with 240 in *; lia.
  Qed.

  Lemma minv_frame_ : forall m m' z k, MINV sp M0 m ->
    frame_mod m m' [(Z_to_bv 64 z, k)] -> usp - 240 <= z -> z + k <= usp - 112 -> 0 <= k -> MINV sp M0 m'.
  Proof.
    intros m m' z k [Hf Hi] Hf' Hlo Hhi Hk. pose proof frame_off_ro_ as Hro. ranges.
    assert (W : forall a, outside a (R128 sp) -> outside a [(Z_to_bv 64 z, k)]).
    { intros a [Ha _]. cbn [outside]. split; [|exact I]. unfold R128, in_rng in *.
      rewrite !u64_lit in Ha |- * by lia. lia. }
    split.
    - eapply frame_mod_trans_same; [exact Hf|]. eapply frame_mod_weaken; [exact W | exact Hf'].
    - intros i Hri. destruct Hf' as [Ho' _]. rewrite Ho'; [apply Hi; exact Hri|].
      cbn [outside]. split; [|exact I]. unfold in_rng, RO_LO, RO_HI in *. rewrite !u64_lit by lia. lia.
  Qed.

  Lemma minv_slot_ : forall m z, MINV sp M0 m -> usp - 112 <= z -> z + 8 <= usp ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 z) 8 = rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M0 (Z_to_bv 64 z) 8.
  Proof.
    intros m z [[Ho _] _] Hlo Hhi. ranges.
    apply rdn_ext; [rewrite u64_lit by lia; change (Z.of_nat 8) with 8; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia. change (Z.of_nat 8) with 8 in Hx.
    apply Ho. cbn [outside R128]. split; [|exact I]. unfold in_rng. rewrite u64_lit by lia. lia.
  Qed.

  Lemma minv_ld0_ : forall m, MINV sp M0 m -> rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 112)) 8 = Some (W8 (Z_to_bv 64 1)).
  Proof.
    intros m HM. rewrite (minv_slot_ m (usp - 112) HM) by lia. exact (UM0s _ _ _ _ _ HU).
  Qed.

  Lemma minv_total_ : forall m, MINV sp M0 m -> frame_mod mem m (FRR sp).
  Proof.
    intros m [Hf _]. ranges.
    eapply frame_mod_trans_same; [exact UM0f0|]. eapply frame_mod_weaken; [| exact Hf].
    intros a [Ha _]. cbn [outside R128]. split; [|exact I]. unfold FRR, FR, R128, in_rng in *.
    rewrite !u64_lit in Ha |- * by lia. lia.
  Qed.
End INV.


Section MAIN.
Context {RCa1 : RunCtx}.
  Variables (mem : word -> option byte) (sp ret : word) (rom : word -> option byte).
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : FR <= bv_unsigned sp.
  Hypothesis Hstk : store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - FR)) (Z.to_nat FR) = true.

  #[local] Abbreviation usp := (bv_unsigned sp).

  Ltac grows := repeat (first [ apply mem_grows_refl | eapply mem_grows_trans; [| apply wbytes_grows] ]).
  Ltac okslot := eapply (stk_ok8 mem); [exact Hstk | exact Hsp | grows | unfold FR; lia | lia].

  Ltac post :=
    repeat split; gres; rwR;
    first [ reflexivity | assumption | lia | f_equal; lia | bveq | solve_lkeeps ].

  Lemma prologue_run : forall regs (vdata : word) (n : Z),
    getr regs 2 = Z_to_bv 64 usp -> getr regs 10 = vdata -> getr regs 11 = Z_to_bv 64 n ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14210 : word) mem rom) (mkst r (0x14ce4 : word) (m13 mem usp regs) rom)
      /\ getr r 1 = (0x14260%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
      /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = vdata
      /\ getr r 10 = Z_to_bv 64 0 /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = Z_to_bv 64 0
      /\ lkeeps hk regs r.
  Proof.
    intros regs vdata n R2 R10 R11. pose proof (u64_range sp). unfold FR in Hsp.
    eexists. split.
    - stepz F_141b0 D_141b0.
      stepsd F_141b4 D_141b4 (Z_to_bv 64 (usp - 8)) (getr regs 1) ltac:(okslot).
      stepsd F_141b8 D_141b8 (Z_to_bv 64 (usp - 16)) (getr regs 8) ltac:(okslot).
      stepsd F_141bc D_141bc (Z_to_bv 64 (usp - 24)) (getr regs 9) ltac:(okslot).
      stepsd F_141c0 D_141c0 (Z_to_bv 64 (usp - 32)) (getr regs 18) ltac:(okslot).
      stepsd F_141c4 D_141c4 (Z_to_bv 64 (usp - 40)) (getr regs 19) ltac:(okslot).
      stepsd F_141c8 D_141c8 (Z_to_bv 64 (usp - 48)) (getr regs 20) ltac:(okslot).
      stepsd F_141cc D_141cc (Z_to_bv 64 (usp - 56)) (getr regs 21) ltac:(okslot).
      stepsd F_141d0 D_141d0 (Z_to_bv 64 (usp - 64)) (getr regs 22) ltac:(okslot).
      stepsd F_141d4 D_141d4 (Z_to_bv 64 (usp - 72)) (getr regs 23) ltac:(okslot).
      stepsd F_141d8 D_141d8 (Z_to_bv 64 (usp - 80)) (getr regs 24) ltac:(okslot).
      stepsd F_141dc D_141dc (Z_to_bv 64 (usp - 88)) (getr regs 25) ltac:(okslot).
      stepsd F_141e0 D_141e0 (Z_to_bv 64 (usp - 96)) (getr regs 26) ltac:(okslot).
      stepsd F_141e4 D_141e4 (Z_to_bv 64 (usp - 104)) (getr regs 27) ltac:(okslot).
      stepz F_141e8 D_141e8. stepz F_141ec D_141ec.
      stepz F_141f0 D_141f0. stepz F_141f4 D_141f4. stepz F_141f8 D_141f8.
      stepz F_141fc D_141fc.
      apply mst_refl.
    - unfold hk. post.
  Qed.

  Ltac ld_slot F D slot vv Hrd :=
    chain_step;
    [ reflexivity
    | eapply step_ld with (v := vv);
      [ exact F | reflexivity | exact D
      | gres; imm_norm; rwR; rewrite zv_addi; rdn_at slot; exact Hrd
      | apply bytes_le_to_Z_8 ]
    | step_simpl; vnorm ].

  Lemma epilogue_run : forall regs M (vra v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : word),
    getr regs 2 = Z_to_bv 64 (usp - 112) -> vra = ret ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 8)) 8 = Some (W8 vra) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 16)) 8 = Some (W8 v8) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 24)) 8 = Some (W8 v9) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 32)) 8 = Some (W8 v18) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 40)) 8 = Some (W8 v19) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 48)) 8 = Some (W8 v20) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 56)) 8 = Some (W8 v21) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 64)) 8 = Some (W8 v22) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 72)) 8 = Some (W8 v23) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 80)) 8 = Some (W8 v24) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 88)) 8 = Some (W8 v25) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 96)) 8 = Some (W8 v26) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 104)) 8 = Some (W8 v27) ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x144c4 : word) M rom) (mkst r ret M rom)
      /\ getr r 10 = Z_to_bv 64 0 /\ getr r 1 = vra /\ getr r 2 = Z_to_bv 64 usp
      /\ getr r 8 = v8 /\ getr r 9 = v9 /\ getr r 18 = v18 /\ getr r 19 = v19 /\ getr r 20 = v20
      /\ getr r 21 = v21 /\ getr r 22 = v22 /\ getr r 23 = v23 /\ getr r 24 = v24 /\ getr r 25 = v25
      /\ getr r 26 = v26 /\ getr r 27 = v27
      /\ lkeeps hk regs r.
  Proof.
    intros regs M vra v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 R2 Hra
           E1 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27.
    pose proof (u64_range sp). unfold FR in Hsp.
    eexists. split.
    - stepz F_14464 D_14464.
      ld_slot F_14468 D_14468 (Z_to_bv 64 (usp - 8)) vra E1.
      ld_slot F_1446c D_1446c (Z_to_bv 64 (usp - 16)) v8 E8.
      ld_slot F_14470 D_14470 (Z_to_bv 64 (usp - 24)) v9 E9.
      ld_slot F_14474 D_14474 (Z_to_bv 64 (usp - 32)) v18 E18.
      ld_slot F_14478 D_14478 (Z_to_bv 64 (usp - 40)) v19 E19.
      ld_slot F_1447c D_1447c (Z_to_bv 64 (usp - 48)) v20 E20.
      ld_slot F_14480 D_14480 (Z_to_bv 64 (usp - 56)) v21 E21.
      ld_slot F_14484 D_14484 (Z_to_bv 64 (usp - 64)) v22 E22.
      ld_slot F_14488 D_14488 (Z_to_bv 64 (usp - 72)) v23 E23.
      ld_slot F_1448c D_1448c (Z_to_bv 64 (usp - 80)) v24 E24.
      ld_slot F_14490 D_14490 (Z_to_bv 64 (usp - 88)) v25 E25.
      ld_slot F_14494 D_14494 (Z_to_bv 64 (usp - 96)) v26 E26.
      ld_slot F_14498 D_14498 (Z_to_bv 64 (usp - 104)) v27 E27.
      stepz F_1449c D_1449c.
      stepret F_144a0 D_144a0 ret ltac:(rwR; exact Hra).
      apply mst_refl.
    - unfold hk. post.
  Qed.

  Lemma segB : forall regs m (v : word),
    getr regs 10 = v ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14260 : word) m rom) (mkst r (0x1545c : word) m rom)
      /\ getr r 1 = (0x14274%bv : word) /\ getr r 19 = v
      /\ getr r 10 = Z_to_bv 64 0 /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = Z_to_bv 64 0
      /\ getr r 2 = getr regs 2 /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9
      /\ lkeeps hk regs r.
  Proof.
    intros regs m v R10. eexists. split.
    - stepz F_14200 D_14200. stepz F_14204 D_14204. stepz F_14208 D_14208. stepz F_1420c D_1420c.
      stepz F_14210 D_14210. apply mst_refl.
    - unfold hk. post.
  Qed.


  Lemma segC_out : forall regs m (udata n : Z),
    getr regs 9 = Z_to_bv 64 udata -> getr regs 8 = Z_to_bv 64 n ->
    1 <= udata < two64 -> 0 <= n < two64 -> (n = 0 \/ 1048576 < n) ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14274 : word) m rom) (mkst r (0x144c4 : word) m rom)
      /\ getr r 2 = getr regs 2
      /\ lkeeps hk regs r.
  Proof.
    intros regs m udata n R9 R8 Hd Hn Hout.
    eexists. split.
    - stepb_ft F_14214 D_14214 ltac:(rwR; rewrite zc_eq by lia; apply Z.eqb_neq; lia).
      stepz F_14218 D_14218. stepz F_1421c D_1421c. stepz F_14220 D_14220.
      stepb_tk F_14224 D_14224
        ltac:(rwR; rewrite zc_ltu_mod; apply Z.ltb_lt;
              destruct Hout as [-> | Hbig];
              [ reflexivity
              | replace (n + 18446744073708503039) with ((n - 1048577) + 1 * two64) by lia;
                rewrite Z_mod_plus_full, !Z.mod_small by lia; lia ]).
      apply mst_refl.
    - unfold hk. post.
  Qed.

  Ltac lbu_at F D Hb :=
    chain_step;
    [ reflexivity
    | eapply step_lbu; [exact F | reflexivity | exact D | gres; imm_norm; rwR; rewrite ?zv_addi, ?v_addi_0; rdn_at_hyp Hb ]
    | step_simpl; vnorm ].

  Lemma segC_in : forall regs m (udata n : Z) (va0 : word) (bb : byte) (b0v Bv : Z),
    getr regs 9 = Z_to_bv 64 udata -> getr regs 8 = Z_to_bv 64 n -> getr regs 2 = Z_to_bv 64 (usp - 112) ->
    getr regs 10 = va0 -> getr regs 19 = Z_to_bv 64 0 ->
    1 <= udata -> udata + 1 <= usp - 112 -> 1 <= n <= 1048576 ->
    store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 112)) 8 = true ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 udata) 1 = Some [bb] -> bv_unsigned bb = b0v -> Bv = (if b0v =? 0 then 1 else b0v) ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14274 : word) m rom)
                           (mkst r (0x14cf0 : word) (wbytes m (Z_to_bv 64 (usp - 112)) (W8 va0)) rom)
      /\ getr r 1 = (0x142b0%bv : word) /\ getr r 10 = Z_to_bv 64 Bv
      /\ getr r 18 = Z_to_bv 64 0 /\ getr r 19 = Z_to_bv 64 0 /\ getr r 20 = Z_to_bv 64 Bv
      /\ getr r 26 = Z_to_bv 64 4294967295
      /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
      /\ lkeeps hk regs r.
  Proof.
    intros regs m udata n va0 bb b0v Bv R9 R8 R2 R10 R19 Hd Hdu Hn Hst Hb Hbv HB.
    pose proof (u64_range sp). unfold FR in Hsp. pose proof (u8_rangeZ bb) as Hbb.
    assert (Hb' : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (wbytes m (Z_to_bv 64 (usp - 112)) (W8 va0)) (Z_to_bv 64 udata) 1 = Some [bb]).
    { rewrite rdn_wbytes_out_Z; [exact Hb|]. rewrite lenW8. change (Z.of_nat 8) with 8. change (Z.of_nat 1) with 1. lia. }
    eexists. split.
    - stepb_ft F_14214 D_14214 ltac:(rwR; rewrite zc_eq by lia; apply Z.eqb_neq; lia).
      stepz F_14218 D_14218. stepz F_1421c D_1421c. stepz F_14220 D_14220.
      stepb_ft F_14224 D_14224 ltac:(rwR; rewrite zc_ltu by lia; apply Z.ltb_ge; lia).
      stepsd F_14228 D_14228 (Z_to_bv 64 (usp - 112)) va0 ltac:(exact Hst).
      stepz F_1422c D_1422c.
      lbu_at F_14230 D_14230 Hb'.
      stepi F_14234 D_14234; znorm. zval 0 ltac:(rewrite zv_srli by lia; reflexivity).
      stepz F_14238 D_14238.
      stepi F_1423c D_1423c; znorm. zval 4294967295 ltac:(rewrite zv_srli_mod; reflexivity).
      stepi F_14240 D_14240; znorm. zval (if bv_unsigned bb <? 1 then 1 else 0) ltac:(apply zv_sltiu; lia).
      stepz F_14244 D_14244.
      zval Bv ltac:(f_equal; rewrite HB, <- Hbv;
                    destruct (Z.ltb_spec (bv_unsigned bb) 1), (Z.eqb_spec (bv_unsigned bb) 0); lia).
      stepz F_14248 D_14248. stepz F_1424c D_1424c.
      apply mst_refl.
    - unfold hk. post.
  Qed.

  Ltac fix_auipc := match goal with |- context [regupd _ _ (v_auipc ?p ?i)] => wlit_closed (v_auipc p i) end.

  Lemma segD : forall regs m (OP n : Z),
    getr regs 10 = Z_to_bv 64 OP -> getr regs 8 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 0 ->
    0 <= OP < two32 -> 1 <= n <= 1048576 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x142b0 : word) m rom) (mkst r (0x142cc : word) m rom)
      /\ getr r 27 = Z_to_bv 64 0 /\ getr r 22 = Z_to_bv 64 0 /\ getr r 19 = Z_to_bv 64 n
      /\ getr r 24 = Z_to_bv 64 OP /\ getr r 21 = Z_to_bv 64 66717
      /\ getr r 2 = getr regs 2 /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = getr regs 9
      /\ getr r 18 = getr regs 18 /\ getr r 20 = getr regs 20 /\ getr r 26 = getr regs 26
      /\ lkeeps hk regs r.
  Proof.
    intros regs m OP n R10 R8 R19 HOP Hn.
    eexists. split.
    - stepz F_14250 D_14250.
      stepi F_14254 D_14254; znorm. zval 0 ltac:(rewrite zv_srli by lia; reflexivity).
      stepz F_14258 D_14258.
      stepz F_1425c D_1425c. rewrite (mod_small_32 n), (sx32_small n) by lia.
      stepi F_14260 D_14260; znorm. fix_auipc.
      stepz F_14264 D_14264. rewrite (mod_small_32 OP) by lia.
      stepz F_14268 D_14268.
      apply mst_refl.
    - unfold hk. post.
  Qed.
End MAIN.
