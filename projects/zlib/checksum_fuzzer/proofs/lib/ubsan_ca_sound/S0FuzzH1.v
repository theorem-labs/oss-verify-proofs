(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)

From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk FuzzMem S0FuzzBase S0Fuzz_code S0FuzzIface S0FuzzStmt
  S0Fuzz_cop S0Fuzz_gen S0Fuzz_comb S0Fuzz_adlc.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.cks Require Import CkTables CkModel CkMathCrc CkMathAdler CkHarness.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma gen_fold : forall k, 0 <= k -> x2nmodp k 3 = crc32_combine_gen k.
Proof.
  (* 1.4: crc32_combine_gen64 is 0 at a negative length *)
  intros k Hk. unfold crc32_combine_gen, crc32_combine_gen64. rewrite (proj2 (Z.ltb_ge k 0)) by lia.
  reflexivity.
Qed.

Section MAIN.
Context {RCa1 : RunCtx}.
  Variables (mem : word -> option byte) (sp ret : word) (rom : word -> option byte).
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : FR <= bv_unsigned sp.
  Hypothesis Hstk : store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - FR)) (Z.to_nat FR) = true.

  #[local] Abbreviation usp := (bv_unsigned sp).
  #[local] Abbreviation W8 v := (word_to_le_bytes 8 v).

  Definition M13 (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
      (Z_to_bv 64 (usp - 8)) (W8 (getr regs 1)))
      (Z_to_bv 64 (usp - 16)) (W8 (getr regs 8)))
      (Z_to_bv 64 (usp - 24)) (W8 (getr regs 9)))
      (Z_to_bv 64 (usp - 32)) (W8 (getr regs 18)))
      (Z_to_bv 64 (usp - 40)) (W8 (getr regs 19)))
      (Z_to_bv 64 (usp - 48)) (W8 (getr regs 20)))
      (Z_to_bv 64 (usp - 56)) (W8 (getr regs 21)))
      (Z_to_bv 64 (usp - 64)) (W8 (getr regs 22)))
      (Z_to_bv 64 (usp - 72)) (W8 (getr regs 23)))
      (Z_to_bv 64 (usp - 80)) (W8 (getr regs 24)))
      (Z_to_bv 64 (usp - 88)) (W8 (getr regs 25)))
      (Z_to_bv 64 (usp - 96)) (W8 (getr regs 26)))
      (Z_to_bv 64 (usp - 104)) (W8 (getr regs 27)).

  Ltac grows := repeat (first [ apply mem_grows_refl | eapply mem_grows_trans; [| apply wbytes_grows] ]).
  Ltac okslot := eapply (stk_ok8 mem); [exact Hstk | exact Hsp | grows | unfold FR; lia | lia].

  Lemma M13_frame : forall regs, frame_mod mem (M13 regs) (FRR sp).
  Proof.
    intros. unfold M13. pose proof (u64_range sp). unfold FR in Hsp.
    repeat (apply fm_w8; [unfold FR; lia | | unfold FR; lia | lia]). apply frame_mod_refl.
  Qed.


  Definition hk : list reg := [3; 4]%bv.

  Ltac post :=
    repeat split; gres; rwR;
    first [ reflexivity | assumption | lia | f_equal; lia | bveq | solve_lkeeps ].

  Lemma prologue_run : forall regs (vdata : word) (n : Z),
    getr regs 2 = Z_to_bv 64 usp -> getr regs 10 = vdata -> getr regs 11 = Z_to_bv 64 n ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x141f0 : word) mem rom) (mkst r (0x14be4 : word) (M13 regs) rom)
      /\ getr r 1 = (0x14240%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
      /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = vdata
      /\ getr r 10 = Z_to_bv 64 0 /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = Z_to_bv 64 0
      /\ lkeeps hk regs r.
  Proof.
    intros regs vdata n R2 R10 R11. pose proof (u64_range sp). unfold FR in Hsp.
    eexists. split.
    - stepz F_14190 D_14190.
      stepsd F_14194 D_14194 (Z_to_bv 64 (usp - 8)) (getr regs 1) ltac:(okslot).
      stepsd F_14198 D_14198 (Z_to_bv 64 (usp - 16)) (getr regs 8) ltac:(okslot).
      stepsd F_1419c D_1419c (Z_to_bv 64 (usp - 24)) (getr regs 9) ltac:(okslot).
      stepsd F_141a0 D_141a0 (Z_to_bv 64 (usp - 32)) (getr regs 18) ltac:(okslot).
      stepsd F_141a4 D_141a4 (Z_to_bv 64 (usp - 40)) (getr regs 19) ltac:(okslot).
      stepsd F_141a8 D_141a8 (Z_to_bv 64 (usp - 48)) (getr regs 20) ltac:(okslot).
      stepsd F_141ac D_141ac (Z_to_bv 64 (usp - 56)) (getr regs 21) ltac:(okslot).
      stepsd F_141b0 D_141b0 (Z_to_bv 64 (usp - 64)) (getr regs 22) ltac:(okslot).
      stepsd F_141b4 D_141b4 (Z_to_bv 64 (usp - 72)) (getr regs 23) ltac:(okslot).
      stepsd F_141b8 D_141b8 (Z_to_bv 64 (usp - 80)) (getr regs 24) ltac:(okslot).
      stepsd F_141bc D_141bc (Z_to_bv 64 (usp - 88)) (getr regs 25) ltac:(okslot).
      stepsd F_141c0 D_141c0 (Z_to_bv 64 (usp - 96)) (getr regs 26) ltac:(okslot).
      stepsd F_141c4 D_141c4 (Z_to_bv 64 (usp - 104)) (getr regs 27) ltac:(okslot).
      stepz F_141c8 D_141c8. stepz F_141cc D_141cc.
      stepz F_141d0 D_141d0. stepz F_141d4 D_141d4. stepz F_141d8 D_141d8.
      stepz F_141dc D_141dc.
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
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 8)) 8 = Some (W8 vra) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 16)) 8 = Some (W8 v8) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 24)) 8 = Some (W8 v9) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 32)) 8 = Some (W8 v18) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 40)) 8 = Some (W8 v19) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 48)) 8 = Some (W8 v20) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 56)) 8 = Some (W8 v21) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 64)) 8 = Some (W8 v22) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 72)) 8 = Some (W8 v23) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 80)) 8 = Some (W8 v24) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 88)) 8 = Some (W8 v25) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 96)) 8 = Some (W8 v26) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 104)) 8 = Some (W8 v27) ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x14480 : word) M rom) (mkst r ret M rom)
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
    - stepz F_14420 D_14420.
      ld_slot F_14424 D_14424 (Z_to_bv 64 (usp - 8)) vra E1.
      ld_slot F_14428 D_14428 (Z_to_bv 64 (usp - 16)) v8 E8.
      ld_slot F_1442c D_1442c (Z_to_bv 64 (usp - 24)) v9 E9.
      ld_slot F_14430 D_14430 (Z_to_bv 64 (usp - 32)) v18 E18.
      ld_slot F_14434 D_14434 (Z_to_bv 64 (usp - 40)) v19 E19.
      ld_slot F_14438 D_14438 (Z_to_bv 64 (usp - 48)) v20 E20.
      ld_slot F_1443c D_1443c (Z_to_bv 64 (usp - 56)) v21 E21.
      ld_slot F_14440 D_14440 (Z_to_bv 64 (usp - 64)) v22 E22.
      ld_slot F_14444 D_14444 (Z_to_bv 64 (usp - 72)) v23 E23.
      ld_slot F_14448 D_14448 (Z_to_bv 64 (usp - 80)) v24 E24.
      ld_slot F_1444c D_1444c (Z_to_bv 64 (usp - 88)) v25 E25.
      ld_slot F_14450 D_14450 (Z_to_bv 64 (usp - 96)) v26 E26.
      ld_slot F_14454 D_14454 (Z_to_bv 64 (usp - 104)) v27 E27.
      stepz F_14458 D_14458.
      stepret F_1445c D_1445c ret ltac:(rwR; exact Hra).
      apply mst_refl.
    - unfold hk. post.
  Qed.

  Section InRange.
    Variables (data : word) (n : Z).
    Hypothesis HF : fzH mem sp data n.
    Hypothesis Hapart : bv_unsigned data + n <= bv_unsigned sp - 192.
    Hypothesis CRCZ : S0_crc32_z_stmt.
    Hypothesis CRCW : S0_crc32_stmt.
    Hypothesis CRCW0 : S0_crc32_null_stmt.
    Hypothesis ADLZ : S0_adler32_z_stmt.
    Hypothesis ADLW : S0_adler32_stmt.
    Hypothesis ADLW0 : S0_adler32_null_stmt.

    #[local] Abbreviation udata := (bv_unsigned data).

    Definition D (k : Z) : list Z := bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem udata (Z.to_nat k).
    Definition b0 : Z := byte_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem udata.
    Definition B : Z := if b0 =? 0 then 1 else b0.

    Lemma b0_range : 0 <= b0 < 256.
    Proof. unfold b0. apply byte_at_range. Qed.
    Lemma B_range : 1 <= B <= 256.
    Proof. unfold B. pose proof b0_range. destruct (Z.eqb_spec b0 0); lia. Qed.
    Lemma D_bytes : forall k, bytes (D k).
    Proof. intros. unfold D, bytes. apply bytes_at_range. Qed.
    Lemma D_app : forall a b, 0 <= a -> 0 <= b -> D (a + b) = D a ++ bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (udata + a) (Z.to_nat b).
    Proof. intros. unfold D. apply bytes_at_appZ; lia. Qed.

    Ltac ranges := pose proof (u64_range data); pose proof (u64_range sp); pose proof (Fn _ _ _ _ HF);
                   pose proof (Fnw _ _ _ _ HF); pose proof (Fdata _ _ _ _ HF); pose proof B_range;
                   unfold FR in Hsp.

    Section WithM0.
      Variable M0 : word -> option byte.
      Hypothesis HM0f : frame_mod mem M0 (FRR sp).
      Hypothesis HM0i : img_ok M0.

      Definition R80 : list (word * Z) := [(Z_to_bv 64 (usp - 192), 80%Z)].
      Definition MINV (m : word -> option byte) : Prop := frame_mod M0 m R80 /\ img_ok m.

      Lemma minv_M0 : MINV M0.
      Proof. split; [apply frame_mod_refl | exact HM0i]. Qed.

      Lemma minv_img : forall m, MINV m -> img_ok m.
      Proof. intros m [_ H]; exact H. Qed.

      Lemma minv_grows : forall m, MINV m -> mem_grows mem m.
      Proof.
        intros m [[_ Hg] _]. destruct HM0f as [_ Hg0]. eapply mem_grows_trans; [exact Hg0 | exact Hg].
      Qed.

      Lemma minv_stk : forall m z (k : nat), MINV m -> usp - 192 <= z -> z + Z.of_nat k <= usp ->
        store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 z) k = true.
      Proof.
        intros m z k HM Hlo Hhi. ranges.
        eapply store_ok_mono; [apply minv_grows; exact HM|].
        eapply (store_ok_sub (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (usp - FR)) _ (Z.to_nat FR) k);
          [ unfold FR; u_norm; lia | exact Hstk | unfold FR; u_norm; lia | unfold FR; u_norm; lia ].
      Qed.

      Lemma minv_rd : forall m, MINV m -> forall i, 0 <= i < n ->
        exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (udata + i)) 1 = Some [b].
      Proof.
        intros m HM. apply (readable_grows (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem m udata n); [apply minv_grows; exact HM | exact (Frd _ _ _ _ HF)].
      Qed.

      Lemma minv_rd_off : forall m off k, MINV m -> 0 <= off -> off + k <= n -> forall i, 0 <= i < k ->
        exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (udata + off + i)) 1 = Some [b].
      Proof.
        intros m off k HM Hoff Hk i Hi. rewrite <- Z.add_assoc. apply (minv_rd m HM). lia.
      Qed.

      Lemma minv_bytes : forall m off k, MINV m -> 0 <= off -> 0 <= k -> off + k <= n ->
        bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (udata + off) (Z.to_nat k) = bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (udata + off) (Z.to_nat k).
      Proof.
        intros m off k [[Ho _] _] Hoff Hk Hn. destruct HM0f as [Ho0 _]. ranges.
        apply bytes_at_ext. intros i Hi.
        assert (E1 : m (Z_to_bv 64 (udata + off + i)) = M0 (Z_to_bv 64 (udata + off + i))).
        { apply Ho. cbn [outside R80]. split; [|exact I]. unfold in_rng. rewrite !u64_lit by lia. lia. }
        rewrite E1. apply Ho0. cbn [outside FRR]. split; [|exact I]. unfold in_rng, FR. rewrite !u64_lit by lia. lia.
      Qed.

      Lemma minv_frame : forall m m' z k, MINV m ->
        frame_mod m m' [(Z_to_bv 64 z, k)] -> usp - 192 <= z -> z + k <= usp - 112 -> 0 <= k -> MINV m'.
      Proof.
        intros m m' z k [Hf Hi] Hf' Hlo Hhi Hk. ranges.
        pose proof (frame_off_ro mem sp data n HF) as Hro. unfold FR in Hro.
        assert (W : forall a, outside a R80 -> outside a [(Z_to_bv 64 z, k)]).
        { intros a [Ha _]. cbn [outside]. split; [|exact I]. unfold R80, in_rng in *.
          rewrite !u64_lit in Ha |- * by lia. lia. }
        split.
        - eapply frame_mod_trans_same; [exact Hf|]. eapply frame_mod_weaken; [exact W | exact Hf'].
        - intros i Hri. destruct Hf' as [Ho' _]. rewrite Ho'; [apply Hi; exact Hri|].
          cbn [outside]. split; [|exact I]. unfold in_rng, RO_LO, RO_HI in *. rewrite !u64_lit by lia. lia.
      Qed.

      Lemma minv_slot : forall m z, MINV m -> usp - 112 <= z -> z + 8 <= usp ->
        rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 z) 8 = rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M0 (Z_to_bv 64 z) 8.
      Proof.
        intros m z [[Ho _] _] Hlo Hhi. ranges.
        apply rdn_ext; [rewrite u64_lit by lia; change (Z.of_nat 8) with 8; lia|].
        intros x Hx. rewrite u64_lit in Hx by lia. change (Z.of_nat 8) with 8 in Hx.
        apply Ho. cbn [outside R80]. split; [|exact I]. unfold in_rng. rewrite u64_lit by lia. lia.
      Qed.


      Ltac lbu_at F D Hb :=
        chain_step;
        [ reflexivity
        | eapply step_lbu; [exact F | reflexivity | exact D | gres; imm_norm; rwR; rewrite ?zv_addi; rdn_at_hyp Hb ]
        | step_simpl; vnorm ].

      Lemma segB : forall regs m,
        getr regs 10 = Z_to_bv 64 0 ->
        exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x14240 : word) m rom) (mkst r (0x151d8 : word) m rom)
          /\ getr r 1 = (0x14254%bv : word) /\ getr r 19 = Z_to_bv 64 0
          /\ getr r 10 = Z_to_bv 64 0 /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = Z_to_bv 64 0
          /\ getr r 2 = getr regs 2 /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9
          /\ lkeeps hk regs r.
      Proof.
        intros regs m R10. eexists. split.
        - stepz F_141e0 D_141e0. stepz F_141e4 D_141e4. stepz F_141e8 D_141e8. stepz F_141ec D_141ec.
          stepz F_141f0 D_141f0. apply mst_refl.
        - unfold hk. post.
      Qed.

      Lemma segC : forall regs m (bb : byte) (Bv : Z),
        getr regs 10 = Z_to_bv 64 1 -> getr regs 8 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 udata ->
        getr regs 19 = Z_to_bv 64 0 ->
        rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 udata) 1 = Some [bb] -> bv_unsigned bb = b0 -> Bv = B ->
        exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x14254 : word) m rom) (mkst r (0x14bf0 : word) m rom)
          /\ getr r 1 = (0x1428c%bv : word) /\ getr r 10 = Z_to_bv 64 Bv
          /\ getr r 18 = Z_to_bv 64 1 /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 22 = Z_to_bv 64 0
          /\ getr r 26 = Z_to_bv 64 4294967295
          /\ getr r 2 = getr regs 2 /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
          /\ lkeeps hk regs r.
      Proof.
        intros regs m bb Bv R10 R8 R9 R19 Hb Hbv HB. ranges. pose proof (u8_rangeZ bb) as Hbb.
        eexists. split.
        - stepz F_141f4 D_141f4. stepz F_141f8 D_141f8. stepz F_141fc D_141fc.
          stepb_ft F_14200 D_14200 ltac:(rewrite zc_ltu by lia; apply Z.ltb_ge; lia).
          stepz F_14204 D_14204. stepz F_14208 D_14208.
          lbu_at F_1420c D_1420c Hb.
          stepi F_14210 D_14210; znorm. zval 4294967295 ltac:(rewrite zv_srli_mod; reflexivity).
          stepz F_14214 D_14214.
          stepi F_14218 D_14218; znorm. zval 0 ltac:(rewrite zv_srli by lia; reflexivity).
          stepi F_1421c D_1421c; znorm. zval (if bv_unsigned bb <? 1 then 1 else 0) ltac:(apply zv_sltiu; lia).
          stepz F_14220 D_14220.
          zval Bv ltac:(f_equal; rewrite HB; unfold B; rewrite <- Hbv;
                        destruct (Z.ltb_spec (bv_unsigned bb) 1), (Z.eqb_spec (bv_unsigned bb) 0); lia).
          stepz F_14224 D_14224. stepz F_14228 D_14228.
          apply mst_refl.
        - unfold hk. post.
      Qed.

      Lemma segD : forall regs m (OP : Z),
        getr regs 10 = Z_to_bv 64 OP -> getr regs 8 = Z_to_bv 64 n -> getr regs 22 = Z_to_bv 64 0 ->
        0 <= OP < two32 ->
        exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1428c : word) m rom) (mkst r (0x142a0 : word) m rom)
          /\ getr r 25 = Z_to_bv 64 0 /\ getr r 21 = Z_to_bv 64 OP /\ getr r 19 = Z_to_bv 64 n
          /\ getr r 23 = Z_to_bv 64 0
          /\ getr r 2 = getr regs 2 /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = getr regs 9
          /\ getr r 18 = getr regs 18 /\ getr r 20 = getr regs 20 /\ getr r 22 = Z_to_bv 64 0
          /\ getr r 26 = getr regs 26
          /\ lkeeps hk regs r.
      Proof.
        intros regs m OP R10 R8 R22 HOP. ranges.
        eexists. split.
        - stepz F_1422c D_1422c. stepz F_14230 D_14230. stepz F_14234 D_14234.
          rewrite (mod_small_32 OP) by lia.
          stepz F_14238 D_14238. rewrite (mod_small_32 n), (sx32_small n) by lia.
          stepz F_1423c D_1423c.
          apply mst_refl.
        - unfold hk. post.
      Qed.

      Section LOOPS.
        Variables (Bv OPv : Z).
        Hypothesis HBv : Bv = B.
        Hypothesis HOPv : OPv = crc32_combine_gen Bv.

        Lemma Bv_range : 1 <= Bv <= 256.
        Proof. rewrite HBv. apply B_range. Qed.
        Lemma OPv_range : 0 <= OPv < two32.
        Proof. rewrite HOPv. apply crc32_combine_gen_range. Qed.
        Lemma OPv_nz : OPv mod two32 <> 0.
        Proof. rewrite HOPv. pose proof Bv_range. apply crc32_combine_gen_nz. lia. Qed.

        Definition CH (off k : Z) : list Z := bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (udata + off) (Z.to_nat k).
        Lemma CH_bytes : forall off k, bytes (CH off k).
        Proof. intros. unfold CH, bytes. apply bytes_at_range. Qed.
        Lemma CH_len : forall off k, 0 <= k -> Zlen (CH off k) = k.
        Proof. intros. unfold CH, Zlen. rewrite bytes_at_length. lia. Qed.
        Lemma D_CH : forall off k, 0 <= off -> 0 <= k -> D (off + k) = D off ++ CH off k.
        Proof. intros. unfold CH. apply D_app; lia. Qed.

        Definition CRH (r : bvmap 5 word) (off C : Z) : Prop :=
          getr r 2 = Z_to_bv 64 (usp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\
          getr r 18 = Z_to_bv 64 1 /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\
          getr r 21 = Z_to_bv 64 OPv /\ getr r 22 = Z_to_bv 64 0 /\ getr r 26 = Z_to_bv 64 4294967295 /\
          getr r 25 = Z_to_bv 64 off /\ getr r 23 = Z_to_bv 64 C.

        Lemma crc_exit : forall regs m off C,
          CRH regs off C -> 0 <= off <= n -> n < off + Bv -> 0 <= C < two32 ->
          exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x142a0 : word) m rom) (mkst r (0x14320 : word) m rom)
            /\ getr r 10 = Z_to_bv 64 off /\ getr r 23 = Z_to_bv 64 C
            /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
            /\ getr r 18 = Z_to_bv 64 1 /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv
            /\ getr r 22 = Z_to_bv 64 0 /\ getr r 26 = Z_to_bv 64 4294967295
            /\ lkeeps hk regs r.
        Proof.
          intros regs m off C (R2 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R26 & R25 & R23) Hoff Hexit HC.
          ranges. pose proof Bv_range.
          eexists. split.
          - stepz F_14240 D_14240. stepz F_14244 D_14244.
            rewrite (mod_small_32 (off + Bv)), (sx32_small (off + Bv)) by lia.
            stepz F_14248 D_14248. stepz F_1424c D_1424c. rewrite (mod_small_32 off) by lia.
            stepb_tk F_14250 D_14250 ltac:(rwR; rewrite zc_ltu by lia; apply Z.ltb_lt; lia).
            apply mst_refl.
          - unfold hk. post.
        Qed.

        Lemma crc_iter : forall regs m off C,
          CRH regs off C -> MINV m -> 0 <= off -> off + Bv <= n -> C = crc32_spec 0 (D off) ->
          exists r m', msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x142a0 : word) m rom) (mkst r (0x142a0 : word) m' rom)
            /\ CRH r (off + Bv) (crc32_spec 0 (D (off + Bv))) /\ MINV m' /\ lkeeps hk regs r.
        Proof.
          intros regs m off C (R2 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R26 & R25 & R23) HM Hoff Hin HC.
          ranges. pose proof Bv_range as HB'. pose proof OPv_range as HOP'. pose proof OPv_nz as HOPnz.
          assert (HCr : 0 <= C < two32) by (rewrite HC; apply crc32_spec_range, D_bytes).
          assert (S1 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x142a0 : word) m rom) (mkst r (0x14580 : word) m rom)
            /\ getr r 1 = (0x142c8%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
            /\ getr r 10 = Z_to_bv 64 0 /\ getr r 11 = Z_to_bv 64 (udata + off) /\ getr r 12 = Z_to_bv 64 Bv
            /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\ getr r 18 = Z_to_bv 64 1
            /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 OPv
            /\ getr r 22 = Z_to_bv 64 0 /\ getr r 26 = Z_to_bv 64 4294967295
            /\ getr r 25 = Z_to_bv 64 (off + Bv) /\ getr r 23 = Z_to_bv 64 C /\ getr r 24 = Z_to_bv 64 (udata + off)
            /\ lkeeps hk regs r).
          { eexists. split.
            - stepz F_14240 D_14240. stepz F_14244 D_14244.
              rewrite (mod_small_32 (off + Bv)), (sx32_small (off + Bv)) by lia.
              stepz F_14248 D_14248. stepz F_1424c D_1424c. rewrite (mod_small_32 off) by lia.
              stepb_ft F_14250 D_14250 ltac:(rwR; rewrite zc_ltu by lia; apply Z.ltb_ge; lia).
              stepz F_14254 D_14254. stepz F_14258 D_14258. stepz F_1425c D_1425c. stepz F_14260 D_14260.
              stepz F_14264 D_14264.
              apply mst_refl.
            - unfold hk. post. }
          destruct S1 as (r1 & M1 & A1 & A2 & A10 & A11 & A12 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A26 & A25 & A23 & A24 & K1).
          destruct (CRCZ r1 m rom (0x142c8%bv : word) (usp - 112) 0 (udata + off) Bv
                      A1 ltac:(apply ret_ok_even; reflexivity) A2 A10 A11 A12
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(apply (minv_stk m); [exact HM | lia | change (Z.of_nat 80) with 80; lia])
                      ltac:(intros _; lia) ltac:(apply minv_img; exact HM)
                      ltac:(apply (minv_rd_off m off Bv HM); lia))
            as (r2 & m2 & M2 & V2 & K2 & F2).
          rewrite (minv_bytes m off Bv HM) in V2 by lia. change (bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (udata + off) (Z.to_nat Bv)) with (CH off Bv) in V2.
          set (crc3 := crc32_z_model (udata + off) 0 (CH off Bv)) in V2.
          assert (Hc3 : 0 <= crc3 < two32) by (subst crc3; apply crc32_z_model_range, CH_bytes).
          assert (HM2 : MINV m2) by (eapply (minv_frame m m2); [exact HM | exact F2 | lia | lia | lia]).
          assert (S3 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst r2 (0x142c8%bv : word) m2 rom) (mkst r (0x14ca4 : word) m2 rom)
            /\ getr r 1 = (0x142d8%bv : word) /\ getr r 10 = Z_to_bv 64 C /\ getr r 11 = Z_to_bv 64 crc3
            /\ getr r 12 = Z_to_bv 64 OPv
            /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
            /\ getr r 18 = Z_to_bv 64 1 /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv
            /\ getr r 21 = Z_to_bv 64 OPv /\ getr r 22 = Z_to_bv 64 0 /\ getr r 26 = Z_to_bv 64 4294967295
            /\ getr r 25 = Z_to_bv 64 (off + Bv) /\ getr r 23 = Z_to_bv 64 C /\ getr r 24 = Z_to_bv 64 (udata + off)
            /\ lkeeps hk r2 r).
          { pose proof (K2 2%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as B2. pose proof (K2 8%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as B8.
            pose proof (K2 9%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as B9. pose proof (K2 18%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as B18.
            pose proof (K2 19%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as B19. pose proof (K2 20%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as B20.
            pose proof (K2 21%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as B21. pose proof (K2 22%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as B22.
            pose proof (K2 23%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as B23. pose proof (K2 24%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as B24.
            pose proof (K2 25%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as B25. pose proof (K2 26%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as B26.
            rewrite A2 in B2. rewrite A8 in B8. rewrite A9 in B9. rewrite A18 in B18. rewrite A19 in B19.
            rewrite A20 in B20. rewrite A21 in B21. rewrite A22 in B22. rewrite A23 in B23. rewrite A24 in B24.
            rewrite A25 in B25. rewrite A26 in B26.
            eexists. split.
            - stepz F_14268 D_14268. rewrite <- (mod32_land crc3), (mod_small_32 crc3) by lia.
              stepz F_1426c D_1426c. stepz F_14270 D_14270. stepz F_14274 D_14274.
              apply mst_refl.
            - unfold hk. post. }
          destruct S3 as (r3 & M3 & B1 & B10 & B11 & B12 & B2 & B8 & B9 & B18 & B19 & B20 & B21 & B22 & B26 & B25 & B23 & B24 & K3).
          destruct (cop_run m2 rom (0x142d8%bv : word) ltac:(apply ret_ok_even; reflexivity) r3 C crc3 OPv
                      B1 B10 B11 B12 HCr ltac:(lia) ltac:(lia) HOPnz) as (r4 & M4 & V4 & K4).
          set (crc4 := crc32_combine_op C crc3 OPv) in V4.
          assert (Hc4 : 0 <= crc4 < two32) by (subst crc4; apply crc32_combine_op_range; lia).
          assert (S5 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst r4 (0x142d8%bv : word) m2 rom) (mkst r (0x14580 : word) m2 rom)
            /\ getr r 1 = (0x142f0%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
            /\ getr r 10 = Z_to_bv 64 C /\ getr r 11 = Z_to_bv 64 (udata + off) /\ getr r 12 = Z_to_bv 64 Bv
            /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\ getr r 18 = Z_to_bv 64 1
            /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 OPv
            /\ getr r 22 = Z_to_bv 64 0 /\ getr r 26 = Z_to_bv 64 4294967295
            /\ getr r 25 = Z_to_bv 64 (off + Bv) /\ getr r 27 = Z_to_bv 64 crc4 /\ getr r 24 = Z_to_bv 64 (udata + off)
            /\ lkeeps hk r4 r).
          { pose proof (K4 2%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as C2. pose proof (K4 8%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as C8.
            pose proof (K4 9%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as C9. pose proof (K4 18%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as C18.
            pose proof (K4 19%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as C19. pose proof (K4 20%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as C20.
            pose proof (K4 21%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as C21. pose proof (K4 22%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as C22.
            pose proof (K4 23%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as C23. pose proof (K4 24%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as C24.
            pose proof (K4 25%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as C25. pose proof (K4 26%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as C26.
            rewrite B2 in C2. rewrite B8 in C8. rewrite B9 in C9. rewrite B18 in C18. rewrite B19 in C19.
            rewrite B20 in C20. rewrite B21 in C21. rewrite B22 in C22. rewrite B23 in C23. rewrite B24 in C24.
            rewrite B25 in C25. rewrite B26 in C26.
            eexists. split.
            - stepz F_14278 D_14278. stepz F_1427c D_1427c. rewrite (mod_small_32 crc4) by lia.
              stepz F_14280 D_14280. stepz F_14284 D_14284. stepz F_14288 D_14288. stepz F_1428c D_1428c.
              apply mst_refl.
            - unfold hk. post. }
          destruct S5 as (r5 & M5 & C1 & C2 & C10 & C11 & C12 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C26 & C25 & C27 & C24 & K5).
          destruct (CRCZ r5 m2 rom (0x142f0%bv : word) (usp - 112) C (udata + off) Bv
                      C1 ltac:(apply ret_ok_even; reflexivity) C2 C10 C11 C12
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(apply (minv_stk m2); [exact HM2 | lia | change (Z.of_nat 80) with 80; lia])
                      ltac:(intros _; lia) ltac:(apply minv_img; exact HM2)
                      ltac:(apply (minv_rd_off m2 off Bv HM2); lia))
            as (r6 & m6 & M6 & V6 & K6 & F6).
          rewrite (minv_bytes m2 off Bv HM2) in V6 by lia. change (bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (udata + off) (Z.to_nat Bv)) with (CH off Bv) in V6.
          assert (HM6 : MINV m6) by (eapply (minv_frame m2 m6); [exact HM2 | exact F6 | lia | lia | lia]).
          assert (E1 : crc32_z_model (udata + off) C (CH off Bv) = crc4).
          { subst crc4 crc3. rewrite HOPv.
            replace (crc32_combine_gen Bv) with (crc32_combine_gen (Zlen (CH off Bv))) by (rewrite CH_len by lia; reflexivity).
            apply harness_assert1; [apply CH_bytes | exact HCr | rewrite CH_len by lia; lia]. }
          rewrite E1 in V6.
          assert (S7 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst r6 (0x142f0%bv : word) m6 rom) (mkst r (0x142a0 : word) m6 rom)
            /\ CRH r (off + Bv) crc4 /\ lkeeps hk r6 r).
          { pose proof (K6 2%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as E2. pose proof (K6 8%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as E8.
            pose proof (K6 9%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as E9. pose proof (K6 18%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as E18.
            pose proof (K6 19%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as E19. pose proof (K6 20%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as E20.
            pose proof (K6 21%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as E21. pose proof (K6 22%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as E22.
            pose proof (K6 25%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as E25. pose proof (K6 26%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as E26.
            pose proof (K6 27%bv ltac:(cbv; (first [solve [liafast_keep_section; tauto] | tauto]))) as E27.
            rewrite C2 in E2. rewrite C8 in E8. rewrite C9 in E9. rewrite C18 in E18. rewrite C19 in E19.
            rewrite C20 in E20. rewrite C21 in E21. rewrite C22 in E22. rewrite C25 in E25. rewrite C26 in E26.
            rewrite C27 in E27.
            eexists. split.
            - stepz F_14290 D_14290. stepz F_14294 D_14294. rewrite (mod_small_32 crc4) by lia.
              stepz F_14298 D_14298.
              stepb_tk F_1429c D_1429c ltac:(rwR; apply c_eq_refl).
              apply mst_refl.
            - unfold CRH, hk. post. }
          destruct S7 as (r7 & M7 & H7 & K7).
          exists r7, m6. split; [|split; [|split]].
          - eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|].
            eapply msteps_trans; [exact M3|]. eapply msteps_trans; [exact M4|].
            eapply msteps_trans; [exact M5|]. eapply msteps_trans; [exact M6|]. exact M7.
          - replace (crc32_spec 0 (D (off + Bv))) with crc4; [exact H7|].
            subst crc4. rewrite <- E1. rewrite HC, D_CH by lia.
            apply harness_crc_stream; [apply D_bytes | apply CH_bytes].
          - exact HM6.
          - intros x Hx. rewrite (K7 x Hx). rewrite (K6 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])).
            rewrite (K5 x Hx). rewrite (K4 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])).
            rewrite (K3 x Hx). rewrite (K2 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). apply (K1 x Hx).
        Qed.

        Lemma crc_loop : forall (k : nat) regs m off,
          CRH regs off (crc32_spec 0 (D off)) -> MINV m -> 0 <= off ->
          off + Z.of_nat k * Bv <= n < off + (Z.of_nat k + 1) * Bv ->
          exists r m', msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x142a0 : word) m rom) (mkst r (0x14320 : word) m' rom)
            /\ MINV m' /\ lkeeps hk regs r
            /\ getr r 10 = Z_to_bv 64 (off + Z.of_nat k * Bv)
            /\ getr r 23 = Z_to_bv 64 (crc32_spec 0 (D (off + Z.of_nat k * Bv)))
            /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
            /\ getr r 18 = Z_to_bv 64 1 /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv
            /\ getr r 22 = Z_to_bv 64 0 /\ getr r 26 = Z_to_bv 64 4294967295.
        Proof.
          induction k as [|k IH]; intros regs m off HR HM Hoff Hk.
          - change (Z.of_nat 0) with 0 in *. pose proof Bv_range.
            assert (HCr : 0 <= crc32_spec 0 (D off) < two32) by (apply crc32_spec_range, D_bytes).
            destruct (crc_exit regs m off _ HR ltac:(lia) ltac:(lia) HCr)
              as (r & M & V10 & V23 & V2 & V8 & V9 & V18 & V19 & V20 & V22 & V26 & K).
            exists r, m. rewrite Z.mul_0_l, Z.add_0_r.
            split; [exact M|]. split; [exact HM|]. split; [exact K|]. repeat split; assumption.
          - pose proof Bv_range.
            assert (Hk' : off + Bv + Z.of_nat k * Bv <= n < off + Bv + (Z.of_nat k + 1) * Bv) by (rewrite Nat2Z.inj_succ in Hk; lia).
            destruct (crc_iter regs m off _ HR HM Hoff ltac:(lia) eq_refl) as (r1 & m1 & M1 & HR1 & HM1 & K1).
            destruct (IH r1 m1 (off + Bv) HR1 HM1 ltac:(lia) Hk')
              as (r & m' & M & HM' & K & V10 & V23 & V2 & V8 & V9 & V18 & V19 & V20 & V22 & V26).
            exists r, m'. replace (off + Z.of_nat (S k) * Bv) with (off + Bv + Z.of_nat k * Bv) by lia.
            split; [eapply msteps_trans; [exact M1 | exact M]|].
            split; [exact HM'|]. split; [eapply lkeeps_trans; [exact K1 | exact K]|].
            repeat split; assumption.
        Qed.

        Ltac xfer K H H2 :=
          lazymatch type of K with keeps_cs ?ra ?rb =>
            lazymatch type of H with getr _ ?i = ?v =>
              assert (H2 : getr rb i = v) by (rewrite (K i) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact H)
            end
          end.

        Ltac retok := apply ret_ok_even; reflexivity.

        Lemma phase2 : forall regs m offq,
          getr regs 10 = Z_to_bv 64 offq -> getr regs 23 = Z_to_bv 64 (crc32_spec 0 (D offq)) ->
          getr regs 2 = Z_to_bv 64 (usp - 112) -> getr regs 8 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 udata ->
          getr regs 18 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 n -> getr regs 20 = Z_to_bv 64 Bv ->
          getr regs 22 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 4294967295 ->
          MINV m -> 0 <= offq <= n -> n - offq < Bv -> n mod Bv = n - offq ->
          exists r m', msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x14320 : word) m rom) (mkst r (0x143e0 : word) m' rom)
            /\ MINV m' /\ lkeeps hk regs r
            /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
            /\ getr r 18 = Z_to_bv 64 1 /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv
            /\ getr r 21 = Z_to_bv 64 (n - offq) /\ getr r 26 = Z_to_bv 64 4294967295.
        Proof.
          intros regs m offq R10 R23 R2 R8 R9 R18 R19 R20 R22 R26 HM Hoff HT Hmod.
          ranges. pose proof Bv_range as HB'.
          set (C := crc32_spec 0 (D offq)) in R23.
          assert (HCr : 0 <= C < two32) by (subst C; apply crc32_spec_range, D_bytes).
          set (T := n - offq) in *.
          assert (S1 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x14320 : word) m rom) (mkst r (0x14580 : word) m rom)
            /\ getr r 1 = (0x14334%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
            /\ getr r 10 = Z_to_bv 64 C /\ getr r 11 = Z_to_bv 64 (udata + offq) /\ getr r 12 = Z_to_bv 64 T
            /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\ getr r 18 = Z_to_bv 64 1
            /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T
            /\ getr r 22 = Z_to_bv 64 0 /\ getr r 26 = Z_to_bv 64 4294967295
            /\ lkeeps hk regs r).
          { eexists. split.
            - stepz F_142c0 D_142c0.
              stepi F_142c4 D_142c4. 1: gres; rwR; rewrite u64_lit by lia; lia. znorm.
              zval T ltac:(unfold v_remu; rewrite !u64_lit by lia; rewrite Hmod; reflexivity).
              stepz F_142c8 D_142c8. stepz F_142cc D_142cc. stepz F_142d0 D_142d0.
              apply mst_refl.
            - unfold hk. post. }
          destruct S1 as (r1 & M1 & A1 & A2 & A10 & A11 & A12 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A26 & K1).
          destruct (CRCZ r1 m rom (0x14334%bv : word) (usp - 112) C (udata + offq) T
                      A1 ltac:(retok) A2 A10 A11 A12
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(apply (minv_stk m); [exact HM | lia | change (Z.of_nat 80) with 80; lia])
                      ltac:(intros _; lia) ltac:(apply minv_img; exact HM)
                      ltac:(apply (minv_rd_off m offq T HM); lia))
            as (r2 & m2 & M2 & V2 & K2 & F2).
          rewrite (minv_bytes m offq T HM) in V2 by lia. change (bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (udata + offq) (Z.to_nat T)) with (CH offq T) in V2.
          assert (ECRC : crc32_z_model (udata + offq) C (CH offq T) = crc32_spec 0 (D n)).
          { subst C. replace (D n) with (D (offq + T)) by (f_equal; lia). rewrite D_CH by lia.
            apply harness_crc_stream; [apply D_bytes | apply CH_bytes]. }
          rewrite ECRC in V2. set (CRC := crc32_spec 0 (D n)) in V2.
          assert (HCRC : 0 <= CRC < two32) by (subst CRC; apply crc32_spec_range, D_bytes).
          assert (HM2 : MINV m2) by (eapply (minv_frame m m2); [exact HM | exact F2 | lia | lia | lia]).
          xfer K2 A2 B2. xfer K2 A8 B8. xfer K2 A9 B9. xfer K2 A18 B18. xfer K2 A19 B19. xfer K2 A20 B20.
          xfer K2 A21 B21. xfer K2 A22 B22. xfer K2 A26 B26.
          assert (S3 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst r2 (0x14334%bv : word) m2 rom) (mkst r (0x14be4 : word) m2 rom)
            /\ getr r 1 = (0x1434c%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
            /\ getr r 10 = Z_to_bv 64 0 /\ getr r 11 = Z_to_bv 64 udata /\ getr r 12 = Z_to_bv 64 n
            /\ getr r 23 = Z_to_bv 64 CRC /\ getr r 24 = Z_to_bv 64 (sx32 CRC)
            /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\ getr r 18 = Z_to_bv 64 1
            /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T
            /\ getr r 22 = Z_to_bv 64 0 /\ getr r 26 = Z_to_bv 64 4294967295
            /\ lkeeps hk r2 r).
          { eexists. split.
            - stepz F_142d4 D_142d4. stepz F_142d8 D_142d8. rewrite (mod_small_32 CRC) by lia.
              stepz F_142dc D_142dc. stepz F_142e0 D_142e0. stepz F_142e4 D_142e4. stepz F_142e8 D_142e8.
              apply mst_refl.
            - unfold hk. post. }
          destruct S3 as (r3 & M3 & B1 & B2' & B10 & B11 & B12 & B23 & B24 & B8' & B9' & B18' & B19' & B20' & B21' & B22' & B26' & K3).
          destruct (CRCW r3 m2 rom (0x1434c%bv : word) (usp - 112) 0 udata n n
                      B1 ltac:(retok) B2' B10 B11 B12
                      ltac:(lia) ltac:(rewrite Z.mod_small; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(apply (minv_stk m2); [exact HM2 | lia | change (Z.of_nat 80) with 80; lia])
                      ltac:(intros _; lia) ltac:(apply minv_img; exact HM2)
                      (minv_rd m2 HM2))
            as (r4 & m4 & M4 & V4 & K4 & F4).
          rewrite <- (Z.add_0_r udata) in V4. rewrite (minv_bytes m2 0 n HM2) in V4 by lia.
          rewrite (Z.add_0_r udata) in V4. change (bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem udata (Z.to_nat n)) with (D n) in V4.
          rewrite (crc32_z_model_spec udata 0 (D n) (D_bytes n)) in V4. fold CRC in V4.
          assert (HM4 : MINV m4) by (eapply (minv_frame m2 m4); [exact HM2 | exact F4 | lia | lia | lia]).
          xfer K4 B2' C2. xfer K4 B8' C8. xfer K4 B9' C9. xfer K4 B18' C18. xfer K4 B19' C19. xfer K4 B20' C20.
          xfer K4 B21' C21. xfer K4 B22' C22. xfer K4 B26' C26. xfer K4 B23 C23. xfer K4 B24 C24.
          assert (S5 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst r4 (0x1434c%bv : word) m4 rom) (mkst r (0x14d18 : word) m4 rom)
            /\ getr r 1 = (0x1436c%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
            /\ getr r 10 = Z_to_bv 64 CRC /\ getr r 11 = Z_to_bv 64 CRC /\ getr r 12 = Z_to_bv 64 n
            /\ getr r 22 = Z_to_bv 64 CRC /\ getr r 23 = Z_to_bv 64 CRC
            /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\ getr r 18 = Z_to_bv 64 1
            /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T
            /\ getr r 26 = Z_to_bv 64 4294967295
            /\ lkeeps hk r4 r).
          { eexists. split.
            - stepz F_142ec D_142ec. rewrite (mod_small_32 CRC) by lia.
              stepb_ft F_142f0 D_142f0 ltac:(rwR; apply c_eq_refl).
              stepz F_142f4 D_142f4. rewrite <- (mod32_land CRC), (mod_small_32 CRC) by lia.
              stepz F_142f8 D_142f8. rewrite <- (mod32_land CRC), (mod_small_32 CRC) by lia.
              stepz F_142fc D_142fc. stepz F_14300 D_14300. stepz F_14304 D_14304. stepz F_14308 D_14308.
              apply mst_refl.
            - unfold hk. post. }
          destruct S5 as (r5 & M5 & C1 & D2 & D10 & D11 & D12 & D22 & D23 & D8 & D9 & D18 & D19 & D20 & D21 & D26 & K5).
          destruct (comb_run m4 rom (0x1436c%bv : word) ltac:(retok) ltac:(apply minv_img; exact HM4)
                      r5 CRC CRC n C1 D10 D11 D12 HCRC ltac:(lia) ltac:(lia)) as (r6 & M6 & V6 & K6).
          set (X1 := crc32_combine CRC CRC n) in V6.
          xfer K6 D2 E2. xfer K6 D8 E8. xfer K6 D9 E9. xfer K6 D18 E18. xfer K6 D19 E19. xfer K6 D20 E20.
          xfer K6 D21 E21. xfer K6 D22 E22. xfer K6 D23 E23. xfer K6 D26 E26.
          assert (S7 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst r6 (0x1436c%bv : word) m4 rom) (mkst r (0x14d18 : word) m4 rom)
            /\ getr r 1 = (0x14380%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
            /\ getr r 10 = Z_to_bv 64 CRC /\ getr r 11 = Z_to_bv 64 CRC /\ getr r 12 = Z_to_bv 64 n
            /\ getr r 22 = Z_to_bv 64 CRC /\ getr r 23 = Z_to_bv 64 CRC /\ getr r 24 = Z_to_bv 64 X1
            /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\ getr r 18 = Z_to_bv 64 1
            /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T
            /\ getr r 26 = Z_to_bv 64 4294967295
            /\ lkeeps hk r6 r).
          { eexists. split.
            - stepz F_1430c D_1430c. stepz F_14310 D_14310. stepz F_14314 D_14314. stepz F_14318 D_14318.
              stepz F_1431c D_1431c. apply mst_refl.
            - unfold hk. post. }
          destruct S7 as (r7 & M7 & E1 & F2' & F10 & F11 & F12 & F22 & F23 & F24 & F8 & F9 & F18 & F19 & F20 & F21 & F26 & K7).
          destruct (comb_run m4 rom (0x14380%bv : word) ltac:(retok) ltac:(apply minv_img; exact HM4)
                      r7 CRC CRC n E1 F10 F11 F12 HCRC ltac:(lia) ltac:(lia)) as (r8 & M8 & V8 & K8).
          fold X1 in V8.
          xfer K8 F2' G2. xfer K8 F8 G8. xfer K8 F9 G9. xfer K8 F18 G18. xfer K8 F19 G19. xfer K8 F20 G20.
          xfer K8 F21 G21. xfer K8 F22 G22. xfer K8 F23 G23. xfer K8 F24 G24. xfer K8 F26 G26.
          assert (S9 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst r8 (0x14380%bv : word) m4 rom) (mkst r (0x14bf0 : word) m4 rom)
            /\ getr r 1 = (0x1438c%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
            /\ getr r 10 = Z_to_bv 64 n
            /\ getr r 22 = Z_to_bv 64 CRC /\ getr r 23 = Z_to_bv 64 CRC
            /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\ getr r 18 = Z_to_bv 64 1
            /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T
            /\ getr r 26 = Z_to_bv 64 4294967295
            /\ lkeeps hk r8 r).
          { eexists. split.
            - stepb_ft F_14320 D_14320 ltac:(rwR; apply c_eq_refl).
              stepz F_14324 D_14324. stepz F_14328 D_14328. apply mst_refl.
            - unfold hk. post. }
          destruct S9 as (r9 & M9 & G1 & H2' & H10 & H22 & H23 & H8 & H9 & H18 & H19 & H20 & H21 & H26 & K9).
          destruct (gen_run m4 rom (0x1438c%bv : word) ltac:(retok) ltac:(apply minv_img; exact HM4)
                      r9 n G1 H10 ltac:(lia)) as (r10 & M10 & V10 & K10).
          rewrite (gen_fold n ltac:(lia)) in V10. set (OP2 := crc32_combine_gen n) in V10.
          assert (HOP2 : 0 <= OP2 < two32) by (subst OP2; apply crc32_combine_gen_range).
          assert (HOP2nz : OP2 mod two32 <> 0) by (subst OP2; apply crc32_combine_gen_nz; lia).
          xfer K10 H2' I2. xfer K10 H8 I8. xfer K10 H9 I9. xfer K10 H18 I18. xfer K10 H19 I19. xfer K10 H20 I20.
          xfer K10 H21 I21. xfer K10 H22 I22. xfer K10 H23 I23. xfer K10 H26 I26.
          assert (S11 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst r10 (0x1438c%bv : word) m4 rom) (mkst r (0x14ca4 : word) m4 rom)
            /\ getr r 1 = (0x143a0%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
            /\ getr r 10 = Z_to_bv 64 CRC /\ getr r 11 = Z_to_bv 64 CRC /\ getr r 12 = Z_to_bv 64 OP2
            /\ getr r 22 = Z_to_bv 64 CRC /\ getr r 23 = Z_to_bv 64 CRC /\ getr r 24 = Z_to_bv 64 OP2
            /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\ getr r 18 = Z_to_bv 64 1
            /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T
            /\ getr r 26 = Z_to_bv 64 4294967295
            /\ lkeeps hk r10 r).
          { eexists. split.
            - stepz F_1432c D_1432c. rewrite <- (mod32_land OP2), (mod_small_32 OP2) by lia.
              stepz F_14330 D_14330. stepz F_14334 D_14334. stepz F_14338 D_14338. stepz F_1433c D_1433c.
              apply mst_refl.
            - unfold hk. post. }
          destruct S11 as (r11 & M11 & I1 & J2 & J10 & J11 & J12 & J22 & J23 & J24 & J8 & J9 & J18 & J19 & J20 & J21 & J26 & K11).
          destruct (cop_run m4 rom (0x143a0%bv : word) ltac:(retok) r11 CRC CRC OP2 I1 J10 J11 J12 HCRC ltac:(lia) ltac:(lia) HOP2nz)
            as (r12 & M12 & V12 & K12).
          set (Y := crc32_combine_op CRC CRC OP2) in V12.
          xfer K12 J2 L2. xfer K12 J8 L8. xfer K12 J9 L9. xfer K12 J18 L18. xfer K12 J19 L19. xfer K12 J20 L20.
          xfer K12 J21 L21. xfer K12 J22 L22. xfer K12 J23 L23. xfer K12 J24 L24. xfer K12 J26 L26.
          assert (S13 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst r12 (0x143a0%bv : word) m4 rom) (mkst r (0x14ca4 : word) m4 rom)
            /\ getr r 1 = (0x143b4%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
            /\ getr r 10 = Z_to_bv 64 CRC /\ getr r 11 = Z_to_bv 64 CRC /\ getr r 12 = Z_to_bv 64 OP2
            /\ getr r 22 = Z_to_bv 64 CRC /\ getr r 23 = Z_to_bv 64 CRC /\ getr r 24 = Z_to_bv 64 OP2 /\ getr r 25 = Z_to_bv 64 Y
            /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\ getr r 18 = Z_to_bv 64 1
            /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T
            /\ getr r 26 = Z_to_bv 64 4294967295
            /\ lkeeps hk r12 r).
          { eexists. split.
            - stepz F_14340 D_14340. stepz F_14344 D_14344. stepz F_14348 D_14348. stepz F_1434c D_1434c.
              stepz F_14350 D_14350. apply mst_refl.
            - unfold hk. post. }
          destruct S13 as (r13 & M13 & L1 & N2 & N10 & N11 & N12 & N22 & N23 & N24 & N25 & N8 & N9 & N18 & N19 & N20 & N21 & N26 & K13).
          destruct (cop_run m4 rom (0x143b4%bv : word) ltac:(retok) r13 CRC CRC OP2 L1 N10 N11 N12 HCRC ltac:(lia) ltac:(lia) HOP2nz)
            as (r14 & M14 & V14 & K14).
          fold Y in V14.
          xfer K14 N2 O2. xfer K14 N8 O8. xfer K14 N9 O9. xfer K14 N18 O18. xfer K14 N19 O19. xfer K14 N20 O20.
          xfer K14 N21 O21. xfer K14 N22 O22. xfer K14 N23 O23. xfer K14 N24 O24. xfer K14 N25 O25. xfer K14 N26 O26.
          assert (S15 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst r14 (0x143b4%bv : word) m4 rom) (mkst r (0x14d18 : word) m4 rom)
            /\ getr r 1 = (0x143c8%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
            /\ getr r 10 = Z_to_bv 64 CRC /\ getr r 11 = Z_to_bv 64 CRC /\ getr r 12 = Z_to_bv 64 n
            /\ getr r 22 = Z_to_bv 64 CRC /\ getr r 23 = Z_to_bv 64 CRC /\ getr r 24 = Z_to_bv 64 OP2
            /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\ getr r 18 = Z_to_bv 64 1
            /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T
            /\ getr r 26 = Z_to_bv 64 4294967295
            /\ lkeeps hk r14 r).
          { eexists. split.
            - stepb_ft F_14354 D_14354 ltac:(rwR; apply c_eq_refl).
              stepz F_14358 D_14358. stepz F_1435c D_1435c. stepz F_14360 D_14360. stepz F_14364 D_14364.
              apply mst_refl.
            - unfold hk. post. }
          destruct S15 as (r15 & M15 & O1 & P2 & P10 & P11 & P12 & P22 & P23 & P24 & P8 & P9 & P18 & P19 & P20 & P21 & P26 & K15).
          destruct (comb_run m4 rom (0x143c8%bv : word) ltac:(retok) ltac:(apply minv_img; exact HM4)
                      r15 CRC CRC n O1 P10 P11 P12 HCRC ltac:(lia) ltac:(lia)) as (r16 & M16 & V16 & K16).
          fold X1 in V16.
          xfer K16 P2 Q2. xfer K16 P8 Q8. xfer K16 P9 Q9. xfer K16 P18 Q18. xfer K16 P19 Q19. xfer K16 P20 Q20.
          xfer K16 P21 Q21. xfer K16 P22 Q22. xfer K16 P23 Q23. xfer K16 P24 Q24. xfer K16 P26 Q26.
          assert (S17 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst r16 (0x143c8%bv : word) m4 rom) (mkst r (0x14ca4 : word) m4 rom)
            /\ getr r 1 = (0x143dc%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
            /\ getr r 10 = Z_to_bv 64 CRC /\ getr r 11 = Z_to_bv 64 CRC /\ getr r 12 = Z_to_bv 64 OP2
            /\ getr r 25 = Z_to_bv 64 X1
            /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\ getr r 18 = Z_to_bv 64 1
            /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T
            /\ getr r 26 = Z_to_bv 64 4294967295
            /\ lkeeps hk r16 r).
          { eexists. split.
            - stepz F_14368 D_14368. stepz F_1436c D_1436c. stepz F_14370 D_14370. stepz F_14374 D_14374.
              stepz F_14378 D_14378. apply mst_refl.
            - unfold hk. post. }
          destruct S17 as (r17 & M17 & Q1 & U2 & U10 & U11 & U12 & U25 & U8 & U9 & U18 & U19 & U20 & U21 & U26 & K17).
          destruct (cop_run m4 rom (0x143dc%bv : word) ltac:(retok) r17 CRC CRC OP2 Q1 U10 U11 U12 HCRC ltac:(lia) ltac:(lia) HOP2nz)
            as (r18 & M18 & V18 & K18).
          fold Y in V18.
          assert (E5 : X1 = Y) by (subst X1 Y OP2; apply harness_assert5; reflexivity).
          xfer K18 U2 Wv2. xfer K18 U8 Wv8. xfer K18 U9 Wv9. xfer K18 U18 Wv18. xfer K18 U19 Wv19. xfer K18 U20 Wv20.
          xfer K18 U21 Wv21. xfer K18 U25 Wv25. xfer K18 U26 Wv26.
          assert (S19 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst r18 (0x143dc%bv : word) m4 rom) (mkst r (0x143e0 : word) m4 rom)
            /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
            /\ getr r 18 = Z_to_bv 64 1 /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv
            /\ getr r 21 = Z_to_bv 64 T /\ getr r 26 = Z_to_bv 64 4294967295
            /\ lkeeps hk r18 r).
          { eexists. split.
            - stepb_ft F_1437c D_1437c ltac:(rwR; rewrite E5; apply c_eq_refl). apply mst_refl.
            - unfold hk. post. }
          destruct S19 as (r19 & M19 & X2 & X8 & X9 & X18 & X19 & X20 & X21 & X26 & K19).
          exists r19, m4. split.
          { eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|].
            eapply msteps_trans; [exact M4|]. eapply msteps_trans; [exact M5|]. eapply msteps_trans; [exact M6|].
            eapply msteps_trans; [exact M7|]. eapply msteps_trans; [exact M8|]. eapply msteps_trans; [exact M9|].
            eapply msteps_trans; [exact M10|]. eapply msteps_trans; [exact M11|]. eapply msteps_trans; [exact M12|].
            eapply msteps_trans; [exact M13|]. eapply msteps_trans; [exact M14|]. eapply msteps_trans; [exact M15|].
            eapply msteps_trans; [exact M16|]. eapply msteps_trans; [exact M17|]. eapply msteps_trans; [exact M18|].
            exact M19. }
          split; [exact HM4|]. split.
          { intros x Hx.
            rewrite (K19 x Hx). rewrite (K18 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K17 x Hx).
            rewrite (K16 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K15 x Hx).
            rewrite (K14 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K13 x Hx).
            rewrite (K12 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K11 x Hx).
            rewrite (K10 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K9 x Hx).
            rewrite (K8 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K7 x Hx).
            rewrite (K6 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K5 x Hx).
            rewrite (K4 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K3 x Hx).
            rewrite (K2 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). apply (K1 x Hx). }
          repeat split; assumption.
        Qed.
      End LOOPS.
    End WithM0.
  End InRange.
End MAIN.
