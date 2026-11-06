(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import ListFacts. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StreamExec StreamSim MmapSim StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import MallocDefs Code_enframe_src13.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import EnframeArith EnframeBase_src13.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Abbreviation MSEGS_src13 := Plain.M.loaded_segments.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Run2.
Context {fx : FPState}.
  Variables (mem0 : word -> option byte) (c : word) (g M W idx n h3 o16 stride start off : Z).
  Variables (rom : word -> option byte).
  Hypothesis H : efH mem0 c g M W idx n h3 o16 stride start off.

  Ltac facts :=
    pose proof (stride_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (Sge & Smod & S31);
    pose proof (off_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (O1 & O2 & O3 & O4);
    pose proof (start_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (T1 & T2 & T3 & T4 & T5);
    pose proof (Hg _ _ _ _ _ _ _ _ _ _ _ _ H) as Gg;
    pose proof (HM _ _ _ _ _ _ _ _ _ _ _ _ H) as GM;
    pose proof (HW _ _ _ _ _ _ _ _ _ _ _ _ H) as GW;
    pose proof (Hidx _ _ _ _ _ _ _ _ _ _ _ _ H) as Gidx;
    pose proof (Hn _ _ _ _ _ _ _ _ _ _ _ _ H) as Gn;
    pose proof (Hdisj _ _ _ _ _ _ _ _ _ _ _ _ H) as Gdisj;
    pose proof (OK _ _ _ _ _ _ _ _ _ _ _ _ H) as GOK.

  Ltac gsym := rewrite !getr_other by assumption; reflexivity.

  (* [comment removed for export] *)
  Ltac sok :=
    repeat (eapply store_ok_mono;
            [ first [ apply wbytes_grows | apply grows_mD | apply grows_mE | apply grows_mE1 | apply grows_mF
                    | eassumption ] | ]);
    lazymatch goal with
    | GOK : store_ok _ mem0 _ _ = true |- store_ok _ mem0 _ ?k = true =>
        eapply (store_ok_sub MSEGS_src13 mem0 (Z_to_bv 64 (start - 3)) _ (Z.to_nat (stride - 1)) k);
        [ rewrite u64_lit, Z2Nat.id by lia; lia
        | exact GOK
        | rewrite !u64_lit by lia; lia
        | rewrite !u64_lit, Z2Nat.id by lia; simpl (Z.of_nat _); lia ]
    end.

  (* [comment removed for export] *)
  Ltac sidez :=
    rewrite ?length_wle2, ?length_wle4; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ];
    rewrite ?u64_lit by lia; lia.

  (* [comment removed for export] *)
  Ltac peel := rewrite rdn_wbytes_out; [ | sidez | sidez | sidez ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma blockD_run : forall regs,
    getr regs 15 = Z_to_bv 64 start -> getr regs 17 = Z_to_bv 64 off ->
    getr regs 10 = Z_to_bv 64 g -> getr regs 16 = Z_to_bv 64 M ->
    exists regs',
      msteps MSEGS_src13 (mkst regs (0xb6cf8%bv : word) mem0 rom)
                   (mkst regs' (0xb6d1c%bv : word) (mD start off mem0) rom)
      /\ keeps_cs regs regs' /\ getr regs' 13 = Z_to_bv 64 (start + 16 * off)
      /\ getr regs' 16 = Z_to_bv 64 M
      /\ (forall r : reg, r <> 13%bv -> r <> 16%bv -> getr regs' r = getr regs r).
  Proof.
    intros regs R15 R17 R10 R16. facts.
    pose proof (RM _ _ _ _ _ _ _ _ _ _ _ _ H) as LM.
    destruct (Z.eq_dec off 0) as [Hz|Hz].
    { (* [comment removed for export] *)
      eexists. split; [|split; [|split; [|split]]].
      - cbv delta [mD] beta. rewrite (proj2 (Z.eqb_eq _ _) Hz).
        stepn F_b6b40 D_b6b40. rewrite R15.
        stepb_tk F_b6b44 D_b6b44 ltac:(rewrite R17, c_eq_lit by lia; apply Z.eqb_eq; exact Hz).
        apply mst_refl.
      - solve_kcs.
      - gres. f_equal; lia.
      - gres. exact R16.
      - intros r ? ?. gsym. }
    (* [comment removed for export] *)
    eexists. split; [|split; [|split; [|split]]].
    - cbv delta [mD] beta. rewrite (proj2 (Z.eqb_neq _ _) Hz).
      stepn F_b6b40 D_b6b40. rewrite R15.
      stepb_ft F_b6b44 D_b6b44 ltac:(rewrite R17, c_eq_lit by lia; apply Z.eqb_neq; exact Hz).
      stepn F_b6b48 D_b6b48.
      stepn F_b6b4c D_b6b4c. rewrite R17, v_slliw_lit by lia. change (2 ^ 4) with 16.
      stepn F_b6b50 D_b6b50. rewrite R15, v_add_lit by lia.
      stb F_b6b54 D_b6b54 (Z_to_bv 64 (start - 3)) (Z_to_bv 8 224)
        ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(sok).
      sth F_b6b58 D_b6b58 (Z_to_bv 64 (start - 2)) (Z_to_bv 64 off) ltac:(sok).
      stb F_b6b5c D_b6b5c (Z_to_bv 64 (start + 16 * off - 4)) (Z_to_bv 8 0)
        ltac:(reflexivity) ltac:(sok).
      ldd F_b6b60 D_b6b60 (Z_to_bv 64 M)
        ltac:(peel; peel; peel; exact LM).
      apply mst_refl.
    - solve_kcs.
    - gres. f_equal; lia.
    - gres. reflexivity.
    - intros r ? ?. gsym.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Notation PP := (start + 16 * off).
  Local Notation EE := (start + stride - 4).
  Local Notation RR := (stride - 4 - n - 16 * off).
  Local Notation QQ := (stride * idx / 16 + off).

  Lemma qq_eq : (PP - M - 16) / 2 ^ 4 = QQ.
  Proof.
    facts. change (2 ^ 4) with 16.
    replace (start + 16 * off - M - 16) with (stride * idx + off * 16) by lia.
    rewrite Z.div_add by lia. reflexivity.
  Qed.

  Lemma qq_range : 0 <= QQ < 65536.
  Proof.
    facts.
    pose proof (div_le_self (stride * idx) 16 ltac:(lia) ltac:(lia)).
    assert (stride * idx / 16 < 65536 - 255); [|lia].
    apply Z.div_lt_upper_bound; lia.
  Qed.

  Lemma blockE1_run : forall regs m,
    getr regs 13 = Z_to_bv 64 PP -> getr regs 15 = Z_to_bv 64 start ->
    getr regs 14 = Z_to_bv 64 stride -> getr regs 16 = Z_to_bv 64 M ->
    getr regs 12 = Z_to_bv 64 n -> getr regs 11 = Z_to_bv 64 idx ->
    mem_grows mem0 m ->
    exists regs',
      msteps MSEGS_src13 (mkst regs (0xb6d1c%bv : word) m rom)
                   (mkst regs' (0xb6d40%bv : word) (mE1 idx stride start off m) rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 10 = Z_to_bv 64 EE /\ getr regs' 12 = Z_to_bv 64 (n + PP)
      /\ getr regs' 14 = Z_to_bv 64 (start + stride) /\ getr regs' 16 = Z_to_bv 64 RR
      /\ (forall r : reg, r <> 10%bv -> r <> 12%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv ->
                          getr regs' r = getr regs r).
  Proof.
    intros regs m R13 R15 R14 R16 R12 R11 Gm. facts. pose proof qq_range as Qr.
    eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
    - cbv delta [mE1] beta.
      stepn F_b6b64 D_b6b64. rewrite R15, R14, v_add_lit by lia.
      stepn F_b6b68 D_b6b68. rewrite R13, R16, v_subw_lit by lia.
      stepn F_b6b6c D_b6b6c. rewrite R12, R13, v_add_lit by lia.
      stepn F_b6b70 D_b6b70. rewrite v_addi_lit by lia.
      stepn F_b6b74 D_b6b74. rewrite v_addi_lit by lia.
      stepn F_b6b78 D_b6b78. rewrite v_srli_lit by lia.
      replace (start + 16 * off - M + -16) with (PP - M - 16) by lia. rewrite qq_eq.
      stepn F_b6b7c D_b6b7c. rewrite v_subw_lit by lia.
      stb F_b6b80 D_b6b80 (Z_to_bv 64 (start + 16 * off - 3)) (Z_to_bv 8 idx)
        ltac:(apply sb_byte_small; lia) ltac:(sok).
      sth F_b6b84 D_b6b84 (Z_to_bv 64 (start + 16 * off - 2)) (Z_to_bv 64 QQ) ltac:(sok).
      apply mst_refl.
    - solve_kcs.
    - gres. f_equal; lia.
    - gres. reflexivity.
    - gres. reflexivity.
    - gres. f_equal; lia.
    - intros r ? ? ? ? ?. gsym.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma blockE2_run : forall regs m,
    getr regs 16 = Z_to_bv 64 RR -> getr regs 10 = Z_to_bv 64 EE ->
    getr regs 12 = Z_to_bv 64 (n + PP) -> getr regs 14 = Z_to_bv 64 (start + stride) ->
    mem_grows mem0 m ->
    exists regs',
      msteps MSEGS_src13 (mkst regs (0xb6d40%bv : word) (mE1 idx stride start off m) rom)
                   (mkst regs' (0xb6d74%bv : word) (mE idx n stride start off m) rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 10 = Z_to_bv 64 (res_code RR)
      /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> getr regs' r = getr regs r).
  Proof.
    intros regs m R16 R10 R12 R14 Gm. facts.
    destruct (Z.eq_dec RR 0) as [Hr0|Hr0].
    { eexists. split; [|split; [|split]].
      - cbv delta [mE] beta zeta. rewrite (proj2 (Z.eqb_eq _ _) Hr0).
        stepb_tk F_b6b88 D_b6b88 ltac:(rewrite R16, c_eq_lit by lia; apply Z.eqb_eq; exact Hr0).
        stepn F_b6bb0 D_b6bb0. stepn F_b6bb4 D_b6bb4.
        apply mst_refl.
      - solve_kcs.
      - gres. unfold res_code. rewrite Hr0. reflexivity.
      - intros r ? ? ?. gsym. }
    destruct (Z.lt_ge_cases RR 5) as [Hr5|Hr5].
    { eexists. split; [|split; [|split]].
      - cbv delta [mE] beta zeta. rewrite (proj2 (Z.eqb_neq _ _) Hr0), (proj2 (Z.ltb_lt _ _) Hr5).
        stepb_ft F_b6b88 D_b6b88 ltac:(rewrite R16, c_eq_lit by lia; apply Z.eqb_neq; exact Hr0).
        stepn F_b6b8c D_b6b8c. rewrite R10, R12, v_subw_lit by lia.
        replace (EE - (n + PP)) with RR by lia.
        stepn F_b6b90 D_b6b90. rewrite v_subw_lit by lia.
        stepn F_b6b94 D_b6b94. rewrite R10, v_add_neg by lia.
        stepn F_b6b98 D_b6b98.
        stb F_b6b9c D_b6b9c (Z_to_bv 64 (start + 16 * off + n)) (Z_to_bv 8 0) ltac:(reflexivity) ltac:(sok).
        stepb_tk F_b6ba0 D_b6ba0 ltac:(rewrite c_lts_lit by lia; apply Z.ltb_lt; exact Hr5).
        stepn F_b6bb8 D_b6bb8.
        apply mst_refl.
      - solve_kcs.
      - gres. unfold res_code. rewrite (proj2 (Z.ltb_lt _ _) Hr5). reflexivity.
      - intros r ? ? ?. gsym. }
    eexists. split; [|split; [|split]].
    - cbv delta [mE] beta zeta. rewrite (proj2 (Z.eqb_neq _ _) Hr0), (proj2 (Z.ltb_ge _ _) Hr5).
      stepb_ft F_b6b88 D_b6b88 ltac:(rewrite R16, c_eq_lit by lia; apply Z.eqb_neq; exact Hr0).
      stepn F_b6b8c D_b6b8c. rewrite R10, R12, v_subw_lit by lia.
      replace (EE - (n + PP)) with RR by lia.
      stepn F_b6b90 D_b6b90. rewrite v_subw_lit by lia.
      stepn F_b6b94 D_b6b94. rewrite R10, v_add_neg by lia.
      stepn F_b6b98 D_b6b98.
      stb F_b6b9c D_b6b9c (Z_to_bv 64 (start + 16 * off + n)) (Z_to_bv 8 0) ltac:(reflexivity) ltac:(sok).
      stepb_ft F_b6ba0 D_b6ba0 ltac:(rewrite c_lts_lit by lia; apply Z.ltb_ge; exact Hr5).
      stb F_b6ba4 D_b6ba4 (Z_to_bv 64 (start + stride - 4 - 5)) (Z_to_bv 8 0) ltac:(reflexivity) ltac:(sok).
      stw F_b6ba8 D_b6ba8 (Z_to_bv 64 (start + stride - 4 - 4)) (Z_to_bv 64 RR) ltac:(sok).
      stepn F_b6bac D_b6bac.
      apply mst_refl.
    - solve_kcs.
    - gres. unfold res_code. rewrite (proj2 (Z.ltb_ge _ _) Hr5). reflexivity.
    - intros r ? ? ?. gsym.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma blockF_run : forall regs m (ret : word),
    getr regs 13 = Z_to_bv 64 PP -> getr regs 10 = Z_to_bv 64 (res_code RR) ->
    getr regs 1 = ret -> ret_ok ret ->
    rdn MSEGS_src13 m (Z_to_bv 64 (start + 16 * off - 3)) 1 = Some [Z_to_bv 8 idx] ->
    mem_grows mem0 m ->
    exists regs',
      msteps MSEGS_src13 (mkst regs (0xb6d74%bv : word) m rom)
                   (mkst regs' ret (mF idx n stride start off m) rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 10 = Z_to_bv 64 PP.
  Proof.
    intros regs m ret R13 R10 R1 Hret Rd Gm. facts.
    assert (Hrc : 0 <= res_code RR <= 5) by (unfold res_code; destruct (RR <? 5) eqn:E; [apply Z.ltb_lt in E|]; lia).
    eexists. split; [|split].
    - cbv delta [mF] beta.
      ldbu F_b6bbc D_b6bbc ltac:(rdn_at (Z_to_bv 64 (start + 16 * off - 3)); exact Rd).
      rewrite (u8_lit idx) by lia.
      stepn F_b6bc0 D_b6bc0. rewrite v_andi_31, u64_lit, Z.mod_small by lia.
      stepn F_b6bc4 D_b6bc4. rewrite R10, v_slli_lit by lia.
      stepn F_b6bc8 D_b6bc8. rewrite v_or_lit by lia. rewrite lor_shift5 by lia.
      stb F_b6bcc D_b6bcc (Z_to_bv 64 (start + 16 * off - 3)) (Z_to_bv 8 (idx + 32 * res_code RR))
        ltac:(apply sb_byte_small; lia) ltac:(sok).
      stepn F_b6bd0 D_b6bd0. rewrite R13.
      stepret F_b6bd4 D_b6bd4 ret ltac:(exact R1).
      apply mst_refl.
    - solve_kcs.
    - gres. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_idx : forall m,
    rdn MSEGS_src13 (mE idx n stride start off m) (Z_to_bv 64 (start + 16 * off - 3)) 1 = Some [Z_to_bv 8 idx].
  Proof.
    intros m. facts.
    assert (E1 : rdn MSEGS_src13 (mE1 idx stride start off m) (Z_to_bv 64 (start + 16 * off - 3)) 1
                 = Some [Z_to_bv 8 idx]).
    { cbv delta [mE1] beta. peel. apply (rdn_wbytes_hit MSEGS_src13 [Z_to_bv 8 idx]). sidez. }
    cbv delta [mE] beta zeta.
    destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [exact E1|].
    destruct (Z.ltb_spec RR 5) as [Hr5|Hr5]; [peel; exact E1|].
    peel. peel. peel. exact E1.
  Qed.

End Run2.
