(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.Ubsan OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMhEnframe_run2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z.ListFacts OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z.RefEnframeArith OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.PuKeep.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
#[local] Ltac not_kept ::= not_kept_fast.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


Section Run2.
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
        eapply (store_ok_sub RSEGS mem0 (Z_to_bv 64 (start - 3)) _ (Z.to_nat (stride - 1)) k);
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
      msteps RSEGS (mkst regs (0x67c0c%bv : word) mem0 rom)
                   (mkst regs' (0x67c30%bv : word) (mD start off mem0) rom)
      /\ keeps_cs regs regs' /\ getr regs' 13 = Z_to_bv 64 (start + 16 * off)
      /\ getr regs' 16 = Z_to_bv 64 M
      /\ (forall r : reg, r <> 13%bv -> r <> 16%bv -> getr regs' r = getr regs r).
  Proof using H stride o16 h3 n idx W c.
    intros regs R15 R17 R10 R16. facts.
    pose proof (RM _ _ _ _ _ _ _ _ _ _ _ _ H) as LM.
    destruct (Z.eq_dec off 0) as [Hz|Hz].
    { (* [comment removed for export] *)
      eexists. split; [|split; [|split; [|split]]].
      - cbv delta [mD] beta. rewrite (proj2 (Z.eqb_eq _ _) Hz).
        stepn F_67bb8 D_67bb8. rewrite R15.
        stepb_tk F_67bbc D_67bbc ltac:(rewrite R17, c_eq_lit by lia; apply Z.eqb_eq; exact Hz).
        pu_refl.
      - solve_kcs.
      - gres. f_equal; lia.
      - gres. exact R16.
      - intros r ? ?. gsym. }
    (* [comment removed for export] *)
    eexists. split; [|split; [|split; [|split]]].
    - cbv delta [mD] beta. rewrite (proj2 (Z.eqb_neq _ _) Hz).
      stepn F_67bb8 D_67bb8. rewrite R15.
      stepb_ft F_67bbc D_67bbc ltac:(rewrite R17, c_eq_lit by lia; apply Z.eqb_neq; exact Hz).
      stepn F_67bc0 D_67bc0.
      stepn F_67bc4 D_67bc4. rewrite R17, v_slliw_lit by lia. change (2 ^ 4) with 16.
      stepn F_67bc8 D_67bc8. rewrite R15, v_add_lit by lia.
      stb F_67bcc D_67bcc (Z_to_bv 64 (start - 3)) (Z_to_bv 8 224)
        ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(sok).
      sth F_67bd0 D_67bd0 (Z_to_bv 64 (start - 2)) (Z_to_bv 64 off) ltac:(sok).
      stb F_67bd4 D_67bd4 (Z_to_bv 64 (start + 16 * off - 4)) (Z_to_bv 8 0)
        ltac:(reflexivity) ltac:(sok).
      ldd F_67bd8 D_67bd8 (Z_to_bv 64 M)
        ltac:(peel; peel; peel; exact LM).
      pu_refl.
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
  Proof using H o16 h3 n W g c mem0.
    facts. change (2 ^ 4) with 16.
    replace (start + 16 * off - M - 16) with (stride * idx + off * 16) by lia.
    rewrite Z.div_add by lia. reflexivity.
  Qed.

  Lemma qq_range : 0 <= QQ < 65536.
  Proof using H start o16 h3 n W M g c mem0.
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
      msteps RSEGS (mkst regs (0x67c30%bv : word) m rom)
                   (mkst regs' (0x67c54%bv : word) (mE1 idx stride start off m) rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 10 = Z_to_bv 64 EE /\ getr regs' 12 = Z_to_bv 64 (n + PP)
      /\ getr regs' 14 = Z_to_bv 64 (start + stride) /\ getr regs' 16 = Z_to_bv 64 RR
      /\ (forall r : reg, r <> 10%bv -> r <> 12%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv ->
                          getr regs' r = getr regs r).
  Proof using H o16 h3 W g c.
    intros regs m R13 R15 R14 R16 R12 R11 Gm. facts. pose proof qq_range as Qr.
    eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
    - cbv delta [mE1] beta.
      stepn F_67bdc D_67bdc. rewrite R15, R14, v_add_lit by lia.
      stepn F_67be0 D_67be0. rewrite R13, R16, v_subw_lit by lia.
      stepn F_67be4 D_67be4. rewrite R12, R13, v_add_lit by lia.
      stepn F_67be8 D_67be8. rewrite v_addi_lit by lia.
      stepn F_67bec D_67bec. rewrite v_addi_lit by lia.
      stepn F_67bf0 D_67bf0. rewrite v_srli_lit by lia.
      replace (start + 16 * off - M + -16) with (PP - M - 16) by lia. rewrite qq_eq.
      stepn F_67bf4 D_67bf4. rewrite v_subw_lit by lia.
      stb F_67bf8 D_67bf8 (Z_to_bv 64 (start + 16 * off - 3)) (Z_to_bv 8 idx)
        ltac:(apply sb_byte_small; lia) ltac:(sok).
      sth F_67bfc D_67bfc (Z_to_bv 64 (start + 16 * off - 2)) (Z_to_bv 64 QQ) ltac:(sok).
      pu_refl.
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
      msteps RSEGS (mkst regs (0x67c54%bv : word) (mE1 idx stride start off m) rom)
                   (mkst regs' (0x67c88%bv : word) (mE idx n stride start off m) rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 10 = Z_to_bv 64 (res_code RR)
      /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> getr regs' r = getr regs r).
  Proof using H o16 h3 W M g c.
    intros regs m R16 R10 R12 R14 Gm. facts.
    destruct (Z.eq_dec RR 0) as [Hr0|Hr0].
    { eexists. split; [|split; [|split]].
      - cbv delta [mE] beta zeta. rewrite (proj2 (Z.eqb_eq _ _) Hr0).
        stepb_tk F_67c00 D_67c00 ltac:(rewrite R16, c_eq_lit by lia; apply Z.eqb_eq; exact Hr0).
        stepn F_67c28 D_67c28. stepn F_67c2c D_67c2c.
        pu_refl.
      - solve_kcs.
      - gres. unfold res_code. rewrite Hr0. reflexivity.
      - intros r ? ? ?. gsym. }
    destruct (Z.lt_ge_cases RR 5) as [Hr5|Hr5].
    { eexists. split; [|split; [|split]].
      - cbv delta [mE] beta zeta. rewrite (proj2 (Z.eqb_neq _ _) Hr0), (proj2 (Z.ltb_lt _ _) Hr5).
        stepb_ft F_67c00 D_67c00 ltac:(rewrite R16, c_eq_lit by lia; apply Z.eqb_neq; exact Hr0).
        stepn F_67c04 D_67c04. rewrite R10, R12, v_subw_lit by lia.
        replace (EE - (n + PP)) with RR by lia.
        stepn F_67c08 D_67c08. rewrite v_subw_lit by lia.
        stepn F_67c0c D_67c0c. rewrite R10, v_add_neg by lia.
        stepn F_67c10 D_67c10.
        stb F_67c14 D_67c14 (Z_to_bv 64 (start + 16 * off + n)) (Z_to_bv 8 0) ltac:(reflexivity) ltac:(sok).
        stepb_tk F_67c18 D_67c18 ltac:(rewrite c_lts_lit by lia; apply Z.ltb_lt; exact Hr5).
        stepn F_67c30 D_67c30.
        pu_refl.
      - solve_kcs.
      - gres. unfold res_code. rewrite (proj2 (Z.ltb_lt _ _) Hr5). reflexivity.
      - intros r ? ? ?. gsym. }
    eexists. split; [|split; [|split]].
    - cbv delta [mE] beta zeta. rewrite (proj2 (Z.eqb_neq _ _) Hr0), (proj2 (Z.ltb_ge _ _) Hr5).
      stepb_ft F_67c00 D_67c00 ltac:(rewrite R16, c_eq_lit by lia; apply Z.eqb_neq; exact Hr0).
      stepn F_67c04 D_67c04. rewrite R10, R12, v_subw_lit by lia.
      replace (EE - (n + PP)) with RR by lia.
      stepn F_67c08 D_67c08. rewrite v_subw_lit by lia.
      stepn F_67c0c D_67c0c. rewrite R10, v_add_neg by lia.
      stepn F_67c10 D_67c10.
      stb F_67c14 D_67c14 (Z_to_bv 64 (start + 16 * off + n)) (Z_to_bv 8 0) ltac:(reflexivity) ltac:(sok).
      stepb_ft F_67c18 D_67c18 ltac:(rewrite c_lts_lit by lia; apply Z.ltb_ge; exact Hr5).
      stb F_67c1c D_67c1c (Z_to_bv 64 (start + stride - 4 - 5)) (Z_to_bv 8 0) ltac:(reflexivity) ltac:(sok).
      stw F_67c20 D_67c20 (Z_to_bv 64 (start + stride - 4 - 4)) (Z_to_bv 64 RR) ltac:(sok).
      stepn F_67c24 D_67c24.
      pu_refl.
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
    rdn RSEGS m (Z_to_bv 64 (start + 16 * off - 3)) 1 = Some [Z_to_bv 8 idx] ->
    mem_grows mem0 m ->
    exists regs',
      msteps RSEGS (mkst regs (0x67c88%bv : word) m rom)
                   (mkst regs' ret (mF idx n stride start off m) rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 10 = Z_to_bv 64 PP.
  Proof using H o16 h3 W M g c.
    intros regs m ret R13 R10 R1 Hret Rd Gm. facts.
    assert (Hrc : 0 <= res_code RR <= 5) by (unfold res_code; destruct (RR <? 5) eqn:E; [apply Z.ltb_lt in E|]; lia).
    eexists. split; [|split].
    - cbv delta [mF] beta.
      ldbu F_67c34 D_67c34 ltac:(rdn_at (Z_to_bv 64 (start + 16 * off - 3)); exact Rd).
      rewrite (u8_lit idx) by lia.
      stepn F_67c38 D_67c38. rewrite v_andi_31, u64_lit, Z.mod_small by lia.
      stepn F_67c3c D_67c3c. rewrite R10, v_slli_lit by lia.
      stepn F_67c40 D_67c40. rewrite v_or_lit by lia. rewrite lor_shift5 by lia.
      stb F_67c44 D_67c44 (Z_to_bv 64 (start + 16 * off - 3)) (Z_to_bv 8 (idx + 32 * res_code RR))
        ltac:(apply sb_byte_small; lia) ltac:(sok).
      stepn F_67c48 D_67c48. rewrite R13.
      stepret F_67c4c D_67c4c ret ltac:(exact R1).
      pu_refl.
    - solve_kcs.
    - gres. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_idx : forall m,
    rdn RSEGS (mE idx n stride start off m) (Z_to_bv 64 (start + 16 * off - 3)) 1 = Some [Z_to_bv 8 idx].
  Proof using H o16 h3 W M g c mem0.
    intros m. facts.
    assert (E1 : rdn RSEGS (mE1 idx stride start off m) (Z_to_bv 64 (start + 16 * off - 3)) 1
                 = Some [Z_to_bv 8 idx]).
    { cbv delta [mE1] beta. peel. apply (rdn_wbytes_hit RSEGS [Z_to_bv 8 idx]). sidez. }
    cbv delta [mE] beta zeta.
    destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [exact E1|].
    destruct (Z.ltb_spec RR 5) as [Hr5|Hr5]; [peel; exact E1|].
    peel. peel. peel. exact E1.
  Qed.

End Run2.
End FPGen1.
End UbMhEnframe_run2.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframe_run1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMhEnframe.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z.ListFacts OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z.RefEnframeArith OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframe_run1 UbMhEnframe_run2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


Section Enframe.
  Variables (mem0 : word -> option byte) (c : word) (g M W idx n h3 o16 stride start off : Z).
  Hypothesis H : efH mem0 c g M W idx n h3 o16 stride start off.

  Ltac facts :=
    pose proof (stride_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (Sge & Smod & S31);
    pose proof (off_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (O1 & O2 & O3 & O4);
    pose proof (start_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (T1 & T2 & T3 & T4 & T5);
    pose proof (Hidx _ _ _ _ _ _ _ _ _ _ _ _ H) as Gidx;
    pose proof (Hn _ _ _ _ _ _ _ _ _ _ _ _ H) as Gn.

  Local Notation PP := (start + 16 * off).
  Local Notation EE := (start + stride - 4).
  Local Notation RR := (stride - 4 - n - 16 * off).
  Local Notation QQ := (stride * idx / 16 + off).

  (* [comment removed for export] *)
  Definition memF : memT :=
    mF idx n stride start off (mE idx n stride start off (mD start off mem0)).

  Definition RGN : list (word * Z) := [(Z_to_bv 64 (start - 3), stride - 1)].

  Ltac sidez :=
    rewrite ?length_wle2, ?length_wle4; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ];
    rewrite ?u64_lit by lia; lia.
  Ltac peel := rewrite rdn_wbytes_out; [ | sidez | sidez | sidez ].
  Ltac miss := rewrite wbytes_miss; [ | sidez | sidez ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma fm_layer : forall m a bs,
    start - 3 <= a -> a + Z.of_nat (length bs) <= start + stride - 4 ->
    frame_mod m (wbytes m (Z_to_bv 64 a) bs) RGN.
  Proof.
    intros m a bs Ha Hb. facts.
    eapply frame_mod_weaken; [| apply frame_mod_wbytes; rewrite u64_lit by lia; lia].
    intros x [Hx _]. split; [|exact I]. intros Hin. apply Hx.
    unfold in_rng in *. rewrite !u64_lit in * by lia. lia.
  Qed.

  Lemma fm_step : forall m m' a bs,
    frame_mod mem0 m RGN ->
    m' = wbytes m (Z_to_bv 64 a) bs ->
    start - 3 <= a -> a + Z.of_nat (length bs) <= start + stride - 4 ->
    frame_mod mem0 m' RGN.
  Proof.
    intros m m' a bs Hm -> Ha Hb. eapply frame_mod_trans_same; [exact Hm | apply fm_layer; assumption].
  Qed.

  Lemma frame_memF : frame_mod mem0 memF RGN.
  Proof.
    facts. unfold memF.
    assert (FD : frame_mod mem0 (mD start off mem0) RGN).
    { cbv delta [mD] beta. destruct (Z.eqb_spec off 0) as [Hz|Hz]; [apply frame_mod_refl|].
      eapply fm_step; [| reflexivity | lia | cbn [length]; lia].
      eapply fm_step; [| reflexivity | lia | rewrite length_wle2; cbn; lia].
      eapply fm_step; [apply frame_mod_refl | reflexivity | lia | cbn [length]; lia]. }
    set (m1 := mD start off mem0) in *. clearbody m1.
    assert (FE1 : frame_mod mem0 (mE1 idx stride start off m1) RGN).
    { cbv delta [mE1] beta.
      eapply fm_step; [| reflexivity | lia | rewrite length_wle2; cbn; lia].
      eapply fm_step; [exact FD | reflexivity | lia | cbn [length]; lia]. }
    assert (FE : frame_mod mem0 (mE idx n stride start off m1) RGN).
    { cbv delta [mE] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [exact FE1|].
      destruct (Z.ltb_spec RR 5) as [Hr5|Hr5].
      - eapply fm_step; [exact FE1 | reflexivity | lia | cbn [length]; lia].
      - eapply fm_step; [| reflexivity | lia | rewrite length_wle4; cbn; lia].
        eapply fm_step; [| reflexivity | lia | cbn [length]; lia].
        eapply fm_step; [exact FE1 | reflexivity | lia | cbn [length]; lia]. }
    cbv delta [mF] beta.
    eapply fm_step; [exact FE | reflexivity | lia | cbn [length]; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma post_memF : enframe_post memF idx n stride start off.
  Proof.
    facts. pose proof (qq_range _ _ _ _ _ _ _ _ _ _ _ _ H) as Qr.
    pose proof (R4 _ _ _ _ _ _ _ _ _ _ _ _ H) as L4.
    assert (Hrc : 0 <= res_code RR <= 5)
      by (unfold res_code; destruct (Z.ltb_spec RR 5); lia).
    unfold memF. set (m1 := mD start off mem0).
    (* [comment removed for export] *)
    assert (M4 : m1 (Z_to_bv 64 (PP - 4)) = Some (Z_to_bv 8 0)).
    { subst m1. cbv delta [mD] beta. destruct (Z.eqb_spec off 0) as [Hz|Hz].
      - rewrite <- L4. f_equal. f_equal. lia.
      - replace (PP - 4) with (start + 16 * off - 4) by lia. apply wbytes_hit1. }
    assert (M3 : off <> 0 -> m1 (Z_to_bv 64 (start - 3)) = Some (Z_to_bv 8 224)).
    { intros Hz. subst m1. cbv delta [mD] beta. rewrite (proj2 (Z.eqb_neq _ _) Hz).
      miss. miss. apply wbytes_hit1. }
    assert (M2 : off <> 0 -> rdn RSEGS m1 (Z_to_bv 64 (start - 2)) 2
                           = Some (word_to_le_bytes 2 (Z_to_bv 64 off))).
    { intros Hz. subst m1. cbv delta [mD] beta. rewrite (proj2 (Z.eqb_neq _ _) Hz).
      peel. apply (rdn_wbytes_hit RSEGS (word_to_le_bytes 2 (Z_to_bv 64 off))). sidez. }
    clearbody m1.
    set (m2 := mE idx n stride start off m1).
    cbv delta [mF] beta.
    split.
    - (* [comment removed for export] *) miss.
      subst m2. cbv delta [mE mE1] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [miss; miss; exact M4|].
      destruct (Z.ltb_spec RR 5) as [Hr5|Hr5]; [miss; miss; miss; exact M4|].
      miss. miss. miss. miss. miss. exact M4.
    - (* [comment removed for export] *) apply wbytes_hit1.
    - (* [comment removed for export] *) peel.
      subst m2. cbv delta [mE mE1] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0].
      + apply (rdn_wbytes_hit RSEGS (word_to_le_bytes 2 (Z_to_bv 64 QQ))). sidez.
      + destruct (Z.ltb_spec RR 5) as [Hr5|Hr5].
        * peel. apply (rdn_wbytes_hit RSEGS (word_to_le_bytes 2 (Z_to_bv 64 QQ))). sidez.
        * peel. peel. peel. apply (rdn_wbytes_hit RSEGS (word_to_le_bytes 2 (Z_to_bv 64 QQ))). sidez.
    - (* [comment removed for export] *) intros Hr. miss.
      subst m2. cbv delta [mE] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [lia|].
      destruct (Z.ltb_spec RR 5) as [Hr5|Hr5]; [apply wbytes_hit1|].
      miss. destruct (Z.eq_dec RR 5) as [H5|H5].
      + replace (start + stride - 4 - 5) with (PP + n) by lia. apply wbytes_hit1.
      + miss. apply wbytes_hit1.
    - (* [comment removed for export] *) intros Hr. miss.
      subst m2. cbv delta [mE] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [lia|].
      destruct (Z.ltb_spec RR 5) as [Hr5|Hr5]; [lia|].
      miss. replace (EE - 5) with (start + stride - 4 - 5) by lia. apply wbytes_hit1.
    - (* [comment removed for export] *) intros Hr. peel.
      subst m2. cbv delta [mE] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [lia|].
      destruct (Z.ltb_spec RR 5) as [Hr5|Hr5]; [lia|].
      replace (EE - 4) with (start + stride - 4 - 4) by lia.
      apply (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 RR))). sidez.
    - (* [comment removed for export] *) intros Hz. miss.
      subst m2. cbv delta [mE mE1] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [miss; miss; exact (M3 Hz)|].
      destruct (Z.ltb_spec RR 5) as [Hr5|Hr5]; [miss; miss; miss; exact (M3 Hz)|].
      miss. miss. miss. miss. miss. exact (M3 Hz).
    - (* [comment removed for export] *) intros Hz. peel.
      subst m2. cbv delta [mE mE1] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [peel; peel; exact (M2 Hz)|].
      destruct (Z.ltb_spec RR 5) as [Hr5|Hr5]; [peel; peel; peel; exact (M2 Hz)|].
      peel. peel. peel. peel. peel. exact (M2 Hz).
    - lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma enframe_run : forall regs rom (ret : word),
    getr regs 1 = ret -> ret_ok ret ->
    getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 idx ->
    getr regs 12 = Z_to_bv 64 n -> getr regs 13 = c ->
    exists regs',
      msteps RSEGS (mkst regs (0x67b54%bv : word) mem0 rom) (mkst regs' ret memF rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 10 = Z_to_bv 64 PP.
  Proof.
    intros regs rom ret R1 Hret R10 R11 R12 R13. facts.
    (* [comment removed for export] *)
    destruct (blockA_run _ _ _ _ _ _ _ _ _ _ _ _ rom H regs R10) as (r1 & RUN1 & K1 & A14 & P1).
    assert (A10 : getr r1 10 = Z_to_bv 64 g) by (rewrite P1 by discriminate; exact R10).
    assert (A11 : getr r1 11 = Z_to_bv 64 idx) by (rewrite P1 by discriminate; exact R11).
    assert (A12 : getr r1 12 = Z_to_bv 64 n) by (rewrite P1 by discriminate; exact R12).
    assert (A13 : getr r1 13 = c) by (rewrite P1 by discriminate; exact R13).
    assert (A1 : getr r1 1 = ret) by (rewrite P1 by discriminate; exact R1).
    (* [comment removed for export] *)
    destruct (blockB_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r1 A10 A11 A12 A13 A14)
      as (r2 & RUN2 & K2 & (B15 & B16 & B17 & B5 & B6 & B7 & P2)).
    assert (B10 : getr r2 10 = Z_to_bv 64 g) by (rewrite P2 by discriminate; exact A10).
    assert (B11 : getr r2 11 = Z_to_bv 64 idx) by (rewrite P2 by discriminate; exact A11).
    assert (B12 : getr r2 12 = Z_to_bv 64 n) by (rewrite P2 by discriminate; exact A12).
    assert (B14 : getr r2 14 = Z_to_bv 64 stride) by (rewrite P2 by discriminate; exact A14).
    assert (B1 : getr r2 1 = ret) by (rewrite P2 by discriminate; exact A1).
    (* [comment removed for export] *)
    destruct (blockC_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r2 B17 B5 B6) as (r3 & RUN3 & K3 & C17 & P3).
    assert (C10 : getr r3 10 = Z_to_bv 64 g) by (rewrite P3 by discriminate; exact B10).
    assert (C11 : getr r3 11 = Z_to_bv 64 idx) by (rewrite P3 by discriminate; exact B11).
    assert (C12 : getr r3 12 = Z_to_bv 64 n) by (rewrite P3 by discriminate; exact B12).
    assert (C14 : getr r3 14 = Z_to_bv 64 stride) by (rewrite P3 by discriminate; exact B14).
    assert (C15 : getr r3 15 = Z_to_bv 64 start) by (rewrite P3 by discriminate; exact B15).
    assert (C16 : getr r3 16 = Z_to_bv 64 M) by (rewrite P3 by discriminate; exact B16).
    assert (C1 : getr r3 1 = ret) by (rewrite P3 by discriminate; exact B1).
    (* [comment removed for export] *)
    destruct (blockD_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r3 C15 C17 C10 C16) as (r4 & RUN4 & K4 & D13 & D16 & P4).
    assert (D11 : getr r4 11 = Z_to_bv 64 idx) by (rewrite P4 by discriminate; exact C11).
    assert (D12 : getr r4 12 = Z_to_bv 64 n) by (rewrite P4 by discriminate; exact C12).
    assert (D14 : getr r4 14 = Z_to_bv 64 stride) by (rewrite P4 by discriminate; exact C14).
    assert (D15 : getr r4 15 = Z_to_bv 64 start) by (rewrite P4 by discriminate; exact C15).
    assert (D1 : getr r4 1 = ret) by (rewrite P4 by discriminate; exact C1).
    set (m1 := mD start off mem0) in *.
    assert (G1 : mem_grows mem0 m1) by (subst m1; apply grows_mD).
    (* [comment removed for export] *)
    destruct (blockE1_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r4 m1 D13 D15 D14 D16 D12 D11 G1)
      as (r5 & RUN5 & K5 & E10 & E12 & E14 & E16 & P5).
    assert (E13 : getr r5 13 = Z_to_bv 64 PP) by (rewrite P5 by discriminate; exact D13).
    assert (E1' : getr r5 1 = ret) by (rewrite P5 by discriminate; exact D1).
    (* [comment removed for export] *)
    destruct (blockE2_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r5 m1 E16 E10 E12 E14 G1)
      as (r6 & RUN6 & K6 & F10 & P6).
    assert (F13 : getr r6 13 = Z_to_bv 64 PP) by (rewrite P6 by discriminate; exact E13).
    assert (F1 : getr r6 1 = ret) by (rewrite P6 by discriminate; exact E1').
    (* [comment removed for export] *)
    assert (G2 : mem_grows mem0 (mE idx n stride start off m1))
      by (eapply mem_grows_trans; [exact G1 | apply grows_mE]).
    destruct (blockF_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r6 _ ret F13 F10 F1 Hret
                (rd_idx _ _ _ _ _ _ _ _ _ _ _ _ H m1) G2)
      as (r7 & RUN7 & K7 & Z10).
    exists r7. split; [|split].
    - unfold memF. fold m1.
      eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
      eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|]. exact RUN7.
    - repeat (eapply keeps_cs_trans; [eassumption|]); first [assumption | apply keeps_cs_refl].
    - exact Z10.
  Qed.
End Enframe.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem ref_enframe :
  forall regs mem rom (ret c : word) (g M W idx n h3 o16 stride start off : Z),
    efH mem c g M W idx n h3 o16 stride start off ->
    getr regs 1 = ret -> ret_ok ret ->
    getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 idx ->
    getr regs 12 = Z_to_bv 64 n -> getr regs 13 = c ->
    exists regs' mem',
      msteps RSEGS (mkst regs (0x67b54%bv : word) mem rom) (mkst regs' ret mem' rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 10 = Z_to_bv 64 (start + 16 * off)
      /\ frame_mod mem mem' [(Z_to_bv 64 (start - 3), stride - 1)]
      /\ enframe_post mem' idx n stride start off.
Proof.
  intros regs mem rom ret c g M W idx n h3 o16 stride start off EH R1 Hret R10 R11 R12 R13.
  destruct (enframe_run mem c g M W idx n h3 o16 stride start off EH regs rom ret R1 Hret R10 R11 R12 R13)
    as (regs' & RUN & K & A0).
  exists regs', (memF mem idx n stride start off). split; [|split; [|split; [|split]]].
  - exact RUN.
  - exact K.
  - exact A0.
  - exact (frame_memF mem c g M W idx n h3 o16 stride start off EH).
  - exact (post_memF mem c g M W idx n h3 o16 stride start off EH).
Qed.
End FPGen1.
End UbMhEnframe.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhCount OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhBudget OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnfr OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKTop OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKNest OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotW5 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase UbMhEnframe OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhExt OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhList OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN.UbMhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2.UbMhNest OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhCover OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK.UbMhAcct OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhCount.UbMhCountSpec OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhBudget OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA.UbMhGetMeta OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2.UbMhSzc OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnfr OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA.UbMhEfh OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKTop OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKNest OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhKX OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS.UbMhMSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA.UbMhASpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2.UbMhASlotW1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotW5.UbMhASlotW4 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotW5.UbMhASlotW4b OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKF.UbMhASlotT1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKF.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PuAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Ltac mh_lia_nx := rnfix; first [ solve [hclr; lean zlia] | pa_arith_concl; lia_goal_ok; lia_hsep; first [ with_img1f_ zlia | with_img1_ zlia | lia_pairs; with_img2 zlia ] ].
#[local] Ltac lia ::= first [ solve [ rnfix; pa_tiers ltac:(zlia) ] | solve [ rnfix; pa_big; lia_goal_ok; lia_hsep; pa_tierB ltac:(zlia) ] | mh_lia_nx ].
#[local] Ltac lia_fast ::= first [ solve [ rnfix; pa_tiers ltac:(zlia) ] | solve [ rnfix; pa_big; lia_goal_ok; lia_hsep; pa_tierB ltac:(zlia) ] | first [ solve [ clear_disj; rnfix; zlia ] | solve [ with_disj1 ltac:(rnfix; zlia) ] | lia ] ].
Section Facts.
  Context {RN : mh_run}.
  Context {fx : FPState}.

  Lemma slot_stride_0 : forall l sc, slot_stride 0 l sc = 16 * size_class sc.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. intros l sc. unfold slot_stride, UNIT. cbn [Z.eqb negb andb]. reflexivity. Qed.

  Lemma pru_small : forall x, 0 < x <= 4096 -> page_round_up_Z x = 4096.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros x Hx. unfold page_round_up_Z, page_size.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    nia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma size_class_24 : size_class 24 = 146.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma hx_single : forall st L g, WF st L -> is_group st g -> g_sc st g < 48 -> s_kind st g = GTop -> g_lastidx st g = 0 ->
    size_class (g_sc st g) <= 255 -> g_stride st g - 4 - (16 * size_class (g_sc st g) - 4) < 16 * size_class (g_sc st g).
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros st L g W Hg Hsc K L0 S255. pose proof (wG_each st L (WF_groups st L W) g Hg) as WG.
    assert (SCR : 0 <= g_sc st g < 48) by (split; [unfold g_sc, w_sizeclass; apply Z.mod_pos_bound; lia | exact Hsc]).
    pose proof (size_class_pos (g_sc st g) SCR) as [P1 P2].
    destruct (wg_single st L g WG K Hsc L0) as [U|[E1 E2]]; [unfold UNIT in U; lia|].
    pose proof (wg_kind st L g WG) as KD. rewrite K in KD. destruct KD as (ML & _).
    unfold UNIT in E1, E2. rewrite pru_small in E1 by lia.
    assert (ES : g_stride st g = g_maplen st g * 4096 - 16).
    { unfold g_stride, slot_stride. rewrite L0.
      replace (negb (g_maplen st g =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia). cbn [andb Z.eqb]. unfold UNIT. reflexivity. }
    rewrite ES. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma metaU_apart_span : forall st L M x g, WF st L -> REP st M -> metaU st x -> is_group st g ->
    x + 40 <= g_mem st g \/ gspan st g <= x.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros st L M x g W R U Hg.
    destruct (metaU_area st L W x U) as (ar & k & Har & Hk & Ex & _ & _ & _ & Lo & Hi & _).
    destruct (Z.lt_ge_cases (g_mem st g) (x + 40)) as [A|A]; [|left; exact A].
    destruct (Z.lt_ge_cases x (gspan st g)) as [B|B]; [|right; exact B].
    exfalso. set (y := Z.max (g_mem st g) ar).
    apply (ge_area st (WF_geom st L W) g y Hg).
    - pose proof (gspan_gt st L W g Hg). subst y. lia.
    - exists ar. split; [exact Har|]. subst y. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma zero_run_other : forall size r (Mx : mem) a (x : word),
    0 <= a -> a + Z.of_nat r * size < 2 ^ 64 -> 0 <= size ->
    (forall k, (k < r)%nat -> bv_unsigned x <> a + Z.of_nat k * size) -> zero_run size Mx a r x = Mx x.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros size r. induction r as [|r IH]; intros Mx a x Ha Hr Hs NK; cbn [zero_run]; [reflexivity|].
    rewrite IH; [| lia | rewrite Nat2Z.inj_succ in Hr; lia | exact Hs |].
    - apply wbytes_other1 || idtac. cbn [wbytes]. destruct (bv_eqb x (Z_to_bv 64 a)) eqn:E; [|reflexivity].
      exfalso. apply (NK 0%nat ltac:(lia)). unfold bv_eqb in E. apply Z.eqb_eq in E. rewrite E, u_Z2bv by (rewrite Nat2Z.inj_succ in Hr; nia). lia.
    - intros k Hk E. apply (NK (S k) ltac:(lia)). rewrite Nat2Z.inj_succ. lia.
  Qed.

  Lemma zero_run_at : forall size r (Mx : mem) a k,
    0 <= a -> a + Z.of_nat r * size < 2 ^ 64 -> 1 <= size -> (k < r)%nat ->
    zero_run size Mx a r (Z_to_bv 64 (a + Z.of_nat k * size)) = Some (Z_to_bv 8 0).
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros size r. induction r as [|r IH]; intros Mx a k Ha Hr Hs Hk; [lia|]. cbn [zero_run].
    destruct k as [|k].
    - rewrite zero_run_other; [| lia | rewrite Nat2Z.inj_succ in Hr; lia | lia |].
      + replace (a + Z.of_nat 0 * size) with a by lia. apply byte_hit.
      + intros k' Hk' E. rewrite u_Z2bv in E by (rewrite Nat2Z.inj_succ in Hr; nia). nia.
    - replace (a + Z.of_nat (S k) * size) with (a + size + Z.of_nat k * size) by (rewrite Nat2Z.inj_succ; lia).
      apply IH; [lia | rewrite Nat2Z.inj_succ in Hr; lia | lia | lia].
  Qed.

  Lemma zero_run_diff : forall size r (Mx : mem) a y,
    0 <= a -> a + Z.of_nat r * size < 2 ^ 64 -> 1 <= size -> 0 <= y < 2 ^ 64 ->
    zero_run size Mx a r (Z_to_bv 64 y) <> Mx (Z_to_bv 64 y) -> exists k, (k < r)%nat /\ y = a + Z.of_nat k * size.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros size r. induction r as [|r IH]; intros Mx a y Ha Hr Hs Hy NE; cbn [zero_run] in NE; [exfalso; exact (NE eq_refl)|].
    rewrite Nat2Z.inj_succ in Hr.
    destruct (Z.eq_dec y a) as [->|NEa]; [exists 0%nat; split; lia|].
    assert (EW : wbytes Mx (Z_to_bv 64 a) [Z_to_bv 8 0] (Z_to_bv 64 y) = Mx (Z_to_bv 64 y)).
    { cbn [wbytes]. replace (bv_eqb (Z_to_bv 64 y) (Z_to_bv 64 a)) with false; [reflexivity|].
      symmetry. unfold bv_eqb. apply Z.eqb_neq. rewrite !u_Z2bv by nia. exact NEa. }
    destruct (decide (zero_run size (wbytes Mx (Z_to_bv 64 a) [Z_to_bv 8 0]) (a + size) r (Z_to_bv 64 y) =
                      wbytes Mx (Z_to_bv 64 a) [Z_to_bv 8 0] (Z_to_bv 64 y))) as [E|NE2].
    - exfalso. apply NE. rewrite E. exact EW.
    - destruct (IH _ (a + size) y ltac:(lia) ltac:(lia) Hs Hy NE2) as (k & Hk & E).
      exists (S k). split; [lia|]. rewrite Nat2Z.inj_succ. lia.
  Qed.

  Lemma zbv_mod64 : forall x, Z_to_bv 64 (x mod 2 ^ 64) = Z_to_bv 64 x.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. intros x. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Z.mod_mod by lia. reflexivity. Qed.

  Lemma byte_peel : forall (Mx : mem) a v b bs, byte_at Mx a v ->
    a < b \/ b + Z.of_nat (length bs) <= a -> 0 <= a < 2 ^ 64 -> 0 <= b -> b + Z.of_nat (length bs) < 2 ^ 64 ->
    byte_at (wbytes Mx (Z_to_bv 64 b) bs) a v.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros Mx a v b bs B D Ha Hb Hbn. unfold byte_at in *. destruct D as [D|D].
    - rewrite wbytes_below; [exact B | rewrite u_Z2bv by lia; lia | rewrite !u_Z2bv by lia; lia].
    - rewrite wbytes_above; [exact B | rewrite !u_Z2bv by lia; lia].
  Qed.

  Lemma byte_zero_run : forall size r (Mx : mem) a0 a v,
    0 <= a0 -> a0 + Z.of_nat r * size < 2 ^ 64 -> 1 <= size -> 0 <= a < 2 ^ 64 ->
    (a < a0 \/ a0 + (Z.of_nat r - 1) * size < a) -> byte_at Mx a v -> byte_at (zero_run size Mx a0 r) a v.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros size r Mx a0 a v H0 Hr Hs Ha D B. unfold byte_at in *. rewrite zero_run_other; [exact B | lia | lia | lia |].
    intros k Hk E. rewrite u_Z2bv in E by lia.
    assert (Z.of_nat k * size <= (Z.of_nat r - 1) * size) by (apply Z.mul_le_mono_nonneg_r; lia). nia.
  Qed.

  Lemma cell_zero_run : forall size r (Mx : mem) a0 a n v,
    0 <= a0 -> a0 + Z.of_nat r * size < 2 ^ 64 -> 1 <= size -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    (a + Z.of_nat n <= a0 \/ a0 + (Z.of_nat r - 1) * size < a) ->
    cell Mx a n v -> cell (zero_run size Mx a0 r) a n v.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros size r Mx a0 a n v H0 Hr Hs Ha Han D C. unfold cell in *.
    rewrite (rdn_agreeZ Mx (zero_run size Mx a0 r) a n Ha Han); [exact C|].
    intros y Hy. apply zero_run_other; [lia | lia | lia |]. intros k Hk E. rewrite u_Z2bv in E by lia.
    assert (Z.of_nat k * size <= (Z.of_nat r - 1) * size) by (apply Z.mul_le_mono_nonneg_r; lia). nia.
  Qed.

  Lemma lor224_facts : forall b8 a, 0 <= b8 < 256 -> 0 <= a < 32 ->
    0 <= Z.lor (Z.land b8 224) a < 256 /\ Z.lor (Z.land b8 224) a mod 32 = a.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros b8 a Hb Ha.
    assert (L224 : 0 <= Z.land b8 224 <= 224) by (split; [apply Z.land_nonneg; lia | rewrite Z.land_comm; apply UbMhASlotW5.UbMhASlotW4b.land_le_l'; lia]).
    assert (L0 : Z.land a (Z.land b8 224) = 0).
    { apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.bits_0.
      destruct (Z.lt_ge_cases n 5) as [LT5|GE5].
      - replace (Z.testbit 224 n) with false; [rewrite !Bool.andb_false_r; reflexivity|].
        symmetry. assert (E : exists k, (k < 5)%nat /\ n = Z.of_nat k) by (exists (Z.to_nat n); split; lia). destruct E as (k & Hk & ->).
        enum_nat k 5%nat ltac:(reflexivity).
      - rewrite (testbit_high 5 a n) by lia. reflexivity. }
    assert (LO : Z.lor (Z.land b8 224) a = a + Z.land b8 224).
    { rewrite Z.lor_comm. rewrite (Z.add_nocarry_lxor _ _ L0). symmetry. apply Z.lxor_lor. exact L0. }
    assert (M224 : (Z.land b8 224) mod 32 = 0).
    { rewrite <- land_ones_mod with (k := 5) by lia. change (2 ^ 5 - 1) with 31. rewrite <- Z.land_assoc.
      change (Z.land 224 31) with 0. apply Z.land_0_r. }
    rewrite LO. split; [lia|].
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End Facts.

(* [comment removed for export] *)
Section ASN.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M : mem) (mdl : Model)
            (regs : bvmap 5 word) (rom : word -> option byte) (sp sc req : Z) (d : nat)
            (F : kfam) (bi bo : bool).
  Hypothesis HL : kfam_laws RSEGS F.
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis HLG : LEDGER st (m_vmmaps mdl).
  Hypothesis NJ : nojunk st.
  Hypothesis Hh : m_halted mdl = None.
  Hypothesis Hlz : m_vm_lazy mdl = [].
  Hypothesis Hmat : m_vm_materialized mdl = [].
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hd : dle (dbound (16 * size_class sc)) d.
  Hypothesis Hlimbo : zlen (s_limbo st) + Z.of_nat d + 1 <= 8.
  Hypothesis Hreq : 0 <= req /\ req + 4 <= 16 * size_class sc.
  Hypothesis HBUD : PHI L + MBASE <= vm_limit (m_vmmaps mdl).
  Hypothesis R10 : getr regs 10 = Z_to_bv 64 sc.
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 req.
  Hypothesis R2 : getr regs 2 = Z_to_bv 64 sp.
  Hypothesis Rra : ret_ok (getr regs 1).
  Hypothesis R4 : getr regs 4 = Z_to_bv 64 TPV.
  Hypothesis Hsp : CEIL + ASSTK d <= sp /\ sp < 2 ^ 64.
  Hypothesis DEF : defined M (sp - ASSTK d) sp.
  Hypothesis HQ : forall c', as_ok st L sc req d sp regs M mdl rom c' -> kfx F bi c'.
  Hypothesis HQF : forall c', as_fail st L sc d sp regs M mdl rom c' -> Kf F c'.
  Hypothesis IHd : forall d', (d' < d)%nat -> AS_SPEC3 d'.

  #[local] Notation PT := (pt st L M mdl regs sp sc d).
  #[local] Notation PTE := (ptE st L M mdl regs sp sc d).
  #[local] Notation GBR := (gbr st L M mdl regs sp sc req d).
  #[local] Notation WOKa := (WOK L sp d).

  (* [comment removed for export] *)
  Hypothesis HL_E : forall s1 Mc mdl1 r g idx,
    PTE s1 Mc mdl1 r -> s_limbo s1 = s_limbo st ->
    head_of (s_alist s1 sc) = g -> is_group s1 g -> g_sc s1 g = sc -> 0 <= idx <= g_lastidx s1 g ->
    s_slot s1 g idx = SJunk 0 -> only_junk s1 g idx -> req + 4 <= g_stride s1 g -> (16 * size_class sc <= g_stride s1 g \/ 4080 <= g_stride s1 g) ->
    getr r 10 = Z_to_bv 64 idx ->
    kat RSEGS (mkCfg (mkst r (0x67b10%bv : word) Mc rom) mdl1) (kfx F bi).

  Lemma scl_rng : 1 <= size_class sc <= 8191. Proof using Hsc d. clear - Hsc d. pose proof (size_class_pos sc Hsc). lia. Qed.
  Lemma stk272 : 288 <= ASSTK d. Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. apply ASSTK_ge. Qed.

  (* [comment removed for export] *)
  Lemma nest_tail : forall s3 M3 mdl3 r3 r4 r5 r6 r7 (M5 : mem) (g' idx' j m cnt off b3 b8 arm : Z),
    let strideH := g_stride s3 g' in
    let start := g_slot_start s3 g' idx' in
    let n_e := 16 * size_class j - 4 in
    let p := start + 16 * off in
    let M6 := m_nz M5 m p 0 b3 (size_class sc) cnt in
    let MF := m_com M6 m p sc cnt (cnt - 1) (c_usage (s_ctx s3) sc) 0 b8 in
    WF s3 L -> REP s3 M3 -> is_group s3 g' -> 0 <= idx' <= g_lastidx s3 g' -> s_slot s3 g' idx' = SJunk 0 -> g_sc s3 g' = j -> 0 <= j < 48 -> sc < j ->
    only_junk s3 g' idx' -> s_alist s3 sc = [] -> s_limbo s3 = m :: s_limbo st ->
    metaU s3 m -> ~ is_group s3 m -> ~ listed s3 m -> ~ fresh s3 m -> s_meta s3 m = meta_zero -> ~ In m (s_limbo st) ->
    pt st L M mdl regs sp sc d s3 M3 mdl3 r3 ->
    2 <= cnt <= 32 -> 16 * size_class sc * cnt + 16 <= 2048 -> 16 * size_class sc * cnt + 16 <= 16 * size_class j -> 16 * size_class j <= strideH ->
    enframe_post M5 idx' n_e strideH start off ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (start - 3 <= a < start + strideH - 4) -> M5 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)) ->
    mem_grows M3 M5 ->
    0 <= b3 < 256 /\ b3 mod 32 = idx' -> M5 (Z_to_bv 64 (p - 3)) = Some (Z_to_bv 8 b3) ->
    0 <= b8 < 256 -> M6 (Z_to_bv 64 (p + 8)) = Some (Z_to_bv 8 b8) ->
    arm + 24 <= m -> m + 40 <= arm + 4096 -> defined M3 arm (arm + 4096) ->
    cell M3 m 8 0 -> cell M3 (m + 8) 8 0 -> cell M3 (m + 32) 8 0 ->
    keeps_but [1; 10; 11; 12; 13; 18]%bv r3 r4 -> keeps_cs r4 r5 -> keeps_but [11; 12; 25]%bv r5 r6 -> keeps_but [8; 10; 11; 12; 13; 14]%bv r6 r7 ->
    getr r7 10 = Z_to_bv 64 0 ->
    kat RSEGS (mkCfg (mkst r7 (0x67b10%bv : word) MF rom) mdl3) (kfx F bi).
  Proof using HL_E Hsp Hreq Hsc req. clear - HL_E Hsp Hreq Hsc req.
    intros s3 M3 mdl3 r3 r4 r5 r6 r7 M5 g' idx' j m cnt off b3 b8 arm strideH start n_e p M6 MF W3 RP3 Hg3 Hidx3 Hsl3 Hgsc3 J48 SCJ OJ3 Hnil3 EL3' Um3 NG3 NL3 NF3 Zm3 NLm
           P3 CNT Hle FIT STR POST M5eq G5 Hb3 B5 Hb8 B8 Alo Ahi DEFar Cm0 Cm8 Cm32 K4 KCS K6 K7 O10.
    pose proof P3 as [_ _ _ _ _ _ _ _ _ _ _ BL3' LM3' MU3' FR3' DF3' SK3 T2' T8 T20 T21 T22 T23 KB3].
    pose proof scl_rng as SCL. pose proof (size_class_pos j J48) as [SJ1 SJ2].
    assert (LIM3 : In m (s_limbo s3)) by (rewrite EL3'; left; reflexivity).
    destruct (metaU_rng s3 L W3 m Um3) as (MR1 & MR2 & MR8).
    pose proof (wG_each s3 L (WF_groups s3 L W3) g' Hg3) as WG'.
    pose proof (glast_rng s3 g') as GL'. pose proof (wg_stride s3 L g' WG') as [S16' Smod']. pose proof (wg_mem s3 L g' WG') as (GM1 & GM2 & GM3).
    pose proof (Pr _ _ _ _ _ _ POST) as (PR1 & PR2 & PR3). unfold P_r in PR1. unfold P_q in PR3.
    pose proof (slot_in_span s3 L W3 g' idx' Hg3 Hidx3) as [SP1 SP2]. fold start in SP1.
    assert (Ese : g_slot_end s3 g' idx' = start + strideH - 4) by (unfold g_slot_end, IB; reflexivity).
    rewrite Ese in SP2.
    destruct (group_range s3 L W3 g' Hg3) as [GR1 GR2].
    assert (OFF16 : 16 * off <= strideH - 16 * size_class j) by (subst n_e; lia).
    assert (PEND : p + 12 + 16 * size_class sc * cnt <= start + strideH - 4) by (first [clear - OFF16 Enreq FIT | clear - OFF16 FIT]; subst p; zlia).
    assert (Pst : start <= p) by (subst p; lia).
    pose proof (metaU_apart_span s3 L M3 m g' W3 RP3 Um3 Hg3) as APART.
    pose proof (group_bytes_defined s3 L M3 8 g' W3 RP3 (wg_depth s3 L g' WG') Hg3) as DEFg.
    assert (DEFg5 : defined M5 (g_mem s3 g') (gspan s3 g')) by (eapply defined_grows; [exact G5 | exact DEFg]).
    assert (DEFar5 : defined M5 arm (arm + 4096)) by (eapply defined_grows; [exact G5 | exact DEFar]).
    assert (G6 : mem_grows M5 M6) by (unfold M6, m_nz, m_nz1; eapply mem_grows_trans; [|apply zero_run_grows]; eapply mem_grows_trans; apply wbytes_grows).
    assert (SZr : Z.of_nat (Z.to_nat (cnt + 1)) = cnt + 1) by lia.
    assert (SC16 : 16 <= 16 * size_class sc) by lia.
    assert (AG5 : forall a k, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 -> (a + Z.of_nat k <= start - 3 \/ start + strideH - 4 <= a) ->
                  rdn RSEGS M5 (Z_to_bv 64 a) k = rdn RSEGS M3 (Z_to_bv 64 a) k).
    { intros a k Ha Hk D. apply rdn_agreeZ; [lia | lia |]. intros y Hy. apply M5eq; clear - Ha Hk D Hy; zlia. }
    assert (ZR : forall a n v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (a + Z.of_nat n <= p + 12 \/ p + 12 + cnt * (16 * size_class sc) < a) ->
                 cell (m_nz1 M5 m p 0 b3) a n v -> cell M6 a n v).
    { intros a n v Ha Hn D C. unfold M6, m_nz.
      assert (X1 : (cnt + 1) * (16 * size_class sc) = cnt * (16 * size_class sc) + 16 * size_class sc) by lia.
      assert (X2 : cnt * (16 * size_class sc) = 16 * size_class sc * cnt) by lia.
      apply cell_zero_run; rewrite ?SZr; [unfold HEAPLO in *; lia | ceil; lia | lia | lia | lia | | exact C].
      replace (cnt + 1 - 1) with cnt by lia. exact D. }
    assert (APd : forall a n, m <= a -> a + n <= m + 40 -> 0 <= n -> a + n <= p + 12 \/ p + 12 + cnt * (16 * size_class sc) < a).
    { intros a n Ha Hn Hn0. destruct APART as [A|A]; [left | right]; clear - A Ha Hn Hn0 SP1 SP2 Pst PEND; zlia. }
    assert (GF : mem_grows M6 MF) by (unfold MF, m_com, ctx_usage, ctx_active, CTX; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    assert (G3F : mem_grows M3 MF) by (eapply mem_grows_trans; [exact G5|]; eapply mem_grows_trans; [exact G6 | exact GF]).
    pose proof (end_byte_zero_gen s3 L M3 W3 RP3 0 0 0 8 g' idx' (wg_depth s3 L g' WG') Hg3 Hidx3) as ENDZ. rewrite Ese in ENDZ.
    pose proof (metaU_rng s3 L W3 m Um3) as MRR.
    destruct (lor224_facts b8 (cnt - 1) Hb8 ltac:(lia)) as [AI1 AI2].
    (* [comment removed for export] *)
    assert (BWR : forall y, 0 <= y < 2 ^ 64 -> MF (Z_to_bv 64 y) <> M3 (Z_to_bv 64 y) ->
                   (m <= y < m + 40) \/ (start - 3 <= y < start + strideH - 4) \/
                   (ctx_usage sc <= y < ctx_usage sc + 8) \/ (ctx_active sc <= y < ctx_active sc + 8)).
    { intros y Hy NE.
      destruct (decide (MF (Z_to_bv 64 y) = M6 (Z_to_bv 64 y))) as [EF|NEF].
      2:{ ceil; unfold MF, m_com, AVc, FRc, AVc', Wn, AIb, ctx_usage, ctx_active, CTX, HEAPLO in *.
          rewrite <- (w2le1 (Z.lor (Z.land b8 224) (cnt - 1))) in NEF by exact AI1. wdiff2 NEF M6 y. }
      rewrite EF in NE.
      destruct (decide (M6 (Z_to_bv 64 y) = M5 (Z_to_bv 64 y))) as [E6|NE6].
      2:{ unfold M6, m_nz in NE6.
          destruct (decide (zero_run (16 * size_class sc) (m_nz1 M5 m p 0 b3) (p + 12) (Z.to_nat (cnt + 1)) (Z_to_bv 64 y) = m_nz1 M5 m p 0 b3 (Z_to_bv 64 y))) as [EZ|NEZ].
          - rewrite EZ in NE6. ceil; unfold m_nz1, HEAPLO in *. rewrite <- (w2le1 (b3 mod 32 + 192)) in NE6 by lia. wdiff2 NE6 M5 y.
          - (* [comment removed for export] *)
            pose proof ceil_rng as CRN.
            assert (ZA1 : 0 <= p + 12) by (clear - Pst SP1 GM1; zlia).
            assert (ZA2 : p + 12 + Z.of_nat (Z.to_nat (cnt + 1)) * (16 * size_class sc) < 2 ^ 64) by (rewrite SZr; clear - PEND SP2 GR2 CRN SCL; zlia).
            assert (ZA3 : 1 <= 16 * size_class sc) by (clear - SCL; zlia).
            destruct (zero_run_diff (16 * size_class sc) (Z.to_nat (cnt + 1)) (m_nz1 M5 m p 0 b3) (p + 12) y ZA1 ZA2 ZA3 Hy NEZ) as (k & Hk & Ey).
            assert (KM : Z.of_nat k * (16 * size_class sc) <= cnt * (16 * size_class sc)) by (apply Z.mul_le_mono_nonneg_r; (first [ (clear MRR APART PR3 GM2 Smod' MR8 FR3' Hb3; lia) | lia ])).
            destruct (Z.lt_ge_cases y (start + strideH - 4)) as [LT|GE]; [right; left; lia|].
            (* [comment removed for export] *)
            exfalso. assert (Ey' : y = start + strideH - 4) by (clear - Ey KM PEND GE; zlia).
            apply NE. rewrite EF || idtac. unfold M6, m_nz. rewrite Ey.
            rewrite (zero_run_at (16 * size_class sc) (Z.to_nat (cnt + 1)) (m_nz1 M5 m p 0 b3) (p + 12) k ZA1 ZA2 ZA3 Hk).
            rewrite <- Ey, Ey'. symmetry. exact ENDZ. }
      rewrite E6 in NE.
      destruct (decide (start - 3 <= y < start + strideH - 4)) as [IN|OUT]; [right; left; exact IN|].
      exfalso. apply NE. apply M5eq; [exact Hy | exact OUT]. }
    (* [comment removed for export] *)
    ceil; unfold ctx_usage, ctx_active, CTX, HEAPLO in *.
    assert (HMmeta : rep_meta MF m (MR m m (UbMhASlotKNest.p s3 g' idx' off) (UbMhASlotKTop.av_of (cnt - 1)) (UbMhASlotKTop.fr_of cnt (cnt - 1)) (UbMhASlotKNest.W sc cnt))).
    { replace (UbMhASlotKNest.p s3 g' idx' off) with p by reflexivity.
      replace (UbMhASlotKTop.av_of (cnt - 1)) with (AVc' (cnt - 1)) by (unfold UbMhASlotKTop.av_of, UbMhASlotKTop.brange, AVc'; change (2 ^ 1) with 2; reflexivity).
      replace (UbMhASlotKTop.fr_of cnt (cnt - 1)) with (FRc cnt (cnt - 1)) by (unfold UbMhASlotKTop.fr_of, UbMhASlotKTop.brange, FRc; reflexivity).
      replace (UbMhASlotKNest.W sc cnt) with (Wn sc cnt 0) by (unfold UbMhASlotKNest.W, mkW, Wn; change (0 mod 4096) with 0; lia).
      unfold MF, m_com, ctx_usage, ctx_active, CTX. constructor; cbn [mr_prev mr_next mr_mem mr_avail mr_freed mr_W]; cellw. }
    assert (B6m4 : byte_at M6 (p - 4) 0).
    { unfold M6, m_nz. apply byte_zero_run; rewrite ?SZr; [(first [ (clear H0 BWR AI2 MRR AG5 APART PR3 GM2 Smod' MR8 FR3' Hb3 HL_E; lia) | lia ]) | nia | (first [ (clear H0 AI2 MRR AG5 APART PR3 GM2 Smod' MR8 FR3' Hb3; lia) | lia ]) | (first [ (clear H0 BWR AI2 MRR AG5 APART PR3 GM2 Smod' MR8 FR3' Hb3 HL_E; lia) | lia ]) | left; (first [ (clear H0 BWR AI2 MRR AG5 APART PR3 GM2 Smod' MR8 FR3' Hb3 HL_E; lia) | lia ]) |].
      unfold m_nz1. apply byte_peel; [|cbn; lia | lia | lia | cbn; lia]. apply byte_peel; [| rewrite length_N_to_le_bytes; cbn; lia | lia | lia | rewrite length_N_to_le_bytes; cbn; lia].
      exact (Pm4 _ _ _ _ _ _ POST). }
    assert (B6m3 : byte_at M6 (p - 3) (idx' + 32 * 6)).
    { unfold M6, m_nz. apply byte_zero_run; rewrite ?SZr; [(first [ (clear H0 BWR AI2 MRR AG5 APART PR3 GM2 Smod' MR8 FR3' Hb3 HL_E; lia) | lia ]) | nia | (first [ (clear H0 AI2 MRR AG5 APART PR3 GM2 Smod' MR8 FR3' Hb3; lia) | lia ]) | (first [ (clear H0 BWR AI2 MRR AG5 APART PR3 GM2 Smod' MR8 FR3' Hb3 HL_E; lia) | lia ]) | left; (first [ (clear H0 BWR AI2 MRR AG5 APART PR3 GM2 Smod' MR8 FR3' Hb3 HL_E; lia) | lia ]) |].
      unfold m_nz1, byte_at. replace (idx' + 32 * 6) with (b3 mod 32 + 192) by lia. apply byte_hit. }
    Ltac bpeel := apply byte_peel; [ | wd_lenlit; rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | lia | wd_lenlit; rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
    assert (HMh4 : byte_at MF (p - 4) 0) by (unfold MF, m_com, ctx_usage, ctx_active, CTX; do 11 bpeel; exact B6m4).
    assert (HMh3 : byte_at MF (p - 3) (idx' + 32 * 6)) by (unfold MF, m_com, ctx_usage, ctx_active, CTX; do 11 bpeel; exact B6m3).
    assert (HMh2 : cell MF (p - 2) 2 (inband s3 g' p)).
    { change p with (UbMhEnfr.p s3 g' idx' off) at 2. rewrite (UbMhEnfr.e_inband s3 L g' idx' off W3 Hg3). fold strideH.
      unfold MF, m_com, ctx_usage, ctx_active, CTX. do 11 peel. apply ZR; [lia | cbn; lia | left; cbn; lia |]. unfold m_nz1. peel. peel. exact (Pm2 _ _ _ _ _ _ POST). }
    assert (HMp : cell MF p 8 m) by (unfold MF, m_com, ctx_usage, ctx_active, CTX; cellw).
    assert (HMai : exists b, 0 <= b < 256 /\ byte_at MF (p + 8) b /\ b mod 32 = cnt - 1).
    { exists (AIb (cnt - 1) b8). unfold AIb. split; [exact AI1|]. split; [|exact AI2].
      unfold MF, m_com, AIb, ctx_usage, ctx_active, CTX. do 5 bpeel. unfold byte_at. apply byte_hit. }
    assert (HMz : forall k, 0 <= k <= cnt -> byte_at MF (p + 12 + 16 * size_class sc * k) 0).
    { intros k Hk. assert (KM : 0 <= 16 * size_class sc * k <= 16 * size_class sc * cnt) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
      unfold MF, m_com, ctx_usage, ctx_active, CTX. do 11 bpeel. unfold M6, m_nz, byte_at.
      replace (p + 12 + 16 * size_class sc * k) with (p + 12 + Z.of_nat (Z.to_nat k) * (16 * size_class sc)) by lia.
      apply zero_run_at; rewrite ?SZr; [(first [ (clear H0 BWR AI2 MRR AG5 APART PR3 GM2 Smod' MR8 FR3' Hb3 HL_E; lia) | lia ]) | nia | (first [ (clear HMai H0 AI2 MRR AG5 APART PR3 GM2 Smod' MR8 FR3' Hb3; lia) | lia ]) | (first [ (clear H0 BWR MRR APART PR3 GM2 Smod' MR8 FR3' Hb3 HL_E; lia) | lia ])]. }
    assert (HMusage : cell MF (700056 + 464 + 8 * sc) 8 ((c_usage (s_ctx s3) sc + cnt) mod 2 ^ 64)).
    { unfold MF, m_com, ctx_usage, ctx_active, CTX. do 10 peel. unfold cell. rewrite zbv_mod64. apply cell_hit; cbn; lia. }
    assert (HMact : cell MF (700056 + 80 + 8 * sc) 8 m) by (unfold MF, m_com, ctx_usage, ctx_active, CTX; cellw).
    pose proof (Z.mod_pos_bound (c_usage (s_ctx s3) sc + cnt) (2 ^ 64) ltac:(lia)) as UR'.
    assert (Hptr : ptr_ok s3 g' idx' p).
    { apply (UbMhEnfr.t_ptr_ok s3 L M5 g' idx' n_e off W3 Hg3 Hidx3 ltac:(subst n_e; lia) POST).
      intros S48 KT L0 S255. rewrite Hgsc3 in *. subst n_e. rewrite <- Hgsc3. apply (hx_single s3 L g' W3 Hg3); rewrite ?Hgsc3; assumption. }
    destruct (newnest_close s3 L M3 MF m g' idx' off sc cnt (cnt - 1) ((c_usage (s_ctx s3) sc + cnt) mod 2 ^ 64)
                W3 RP3 Um3 NG3 NL3 NF3 Hg3 Hidx3 Hsl3 Hsc ltac:(rewrite Hgsc3; lia) Hnil3 ltac:(lia) ltac:(lia) UR' (proj1 PR2)
                ltac:(rewrite slot_stride_0; unfold UNIT; lia) ltac:(rewrite slot_stride_0; unfold UNIT; lia) ltac:(intros; lia) Hptr
                sp sp ltac:(ceil; pose proof stk272; lia)
                ltac:(intros y Hy NE; unfold UbMhASlotKNest.b_wr; destruct (BWR y Hy NE) as [A|[A|[A|A]]]; [left; exact A | right; left; exact A | right; right; left; unfold ctx_usage, CTX; exact A | right; right; right; left; unfold ctx_active, CTX; exact A])
                G3F HMmeta HMh4 HMh3 HMh2 HMp HMai
                ltac:(intros k Hk _; rewrite slot_stride_0; exact (HMz k Hk))
                HMusage HMact) as [W4 RP4].
    set (s4 := UbMhASlotKNest.st' s3 m g' idx' off sc cnt (cnt - 1) ((c_usage (s_ctx s3) sc + cnt) mod 2 ^ 64)) in *.
    pose proof (newnest_facts s3 m g' idx' off sc cnt (cnt - 1) ((c_usage (s_ctx s3) sc + cnt) mod 2 ^ 64) Hsc ltac:(lia))
      as (Gm4 & Sm4 & Lm4 & STm4 & _ & SCm4 & _ & _ & _ & AL4 & _ & LB4 & RG4 & BK4 & SO4 & IG4).
    fold s4 in Gm4, Sm4, Lm4, STm4, SCm4, AL4, LB4, RG4, BK4, SO4, IG4.
    (* [comment removed for export] *)
    assert (P4 : PTE s4 MF mdl3 r7).
    { apply (ptE_step st L M mdl regs sp sc req d Hsc Hreq Hsp s3 M3 mdl3 r3 s4 MF r7 P3 W4 RP4 RG4 BK4 eq_refl eq_refl).
      - intros k Hk. change (s_alist s4 k) with (s_alist (UbMhASlotKNest.st' s3 m g' idx' off sc cnt (cnt - 1) ((c_usage (s_ctx s3) sc + cnt) mod 2 ^ 64)) k).
        rewrite UbMhASlotKNest.e_alist. destruct (Z.eqb_spec k sc); [lia | reflexivity].
      - intros x Hx. apply UbMhASlotKNest.e_meta_old. intros ->. exact (NLm Hx).
      - intros x Ux. exact Ux.
      - exact G3F.
      - intros a Ha NE. destruct (BWR a Ha NE) as [A|[A|[A|A]]].
        + apply (meta_WOK L sp d s3 m a W3 Um3). exact A.
        + destruct (Z.lt_ge_cases a start) as [LO|HI].
          * apply (gcell_WOK L sp d s3 g' a W3 Hg3). apply (UbMhEnfr.junk_hdr_cell s3 L g' idx' Hidx3 Hsl3). fold start. lia.
          * apply (garbage_WOK L sp d s3 g' idx' a W3 Hg3). apply (UbMhEnfr.junk_garbage s3 L g' idx' Hidx3 Hsl3). fold start strideH. lia.
        + apply ctx_WOK. unfold CTX_END, CTX. lia.
        + apply ctx_WOK. unfold CTX_END, CTX. lia.
      - kept_rw K7. kept_rw K6. rewrite (KCS 2%bv ltac:(inCS)). kept_rw K4. reflexivity.
      - kept_rw K7. kept_rw K6. rewrite (KCS 20%bv ltac:(inCS)). kept_rw K4. reflexivity.
      - eapply keeps_big; [|exact K7|reflexivity]. eapply keeps_big; [|exact K6|reflexivity].
        apply (keeps_cs_big _ r4); [|exact KCS]. eapply keeps_big; [exact KB3 | exact K4 | reflexivity]. }
    (* [comment removed for export] *)
    apply (HL_E s4 MF mdl3 r7 m 0 P4).
    - rewrite LB4, EL3'. unfold zremove. cbn [List.filter]. rewrite Z.eqb_refl. cbn [negb]. apply zremove_notin. exact NLm.
    - rewrite AL4. reflexivity.
    - exact Gm4.
    - exact SCm4.
    - rewrite Lm4. lia.
    - exact Sm4.
    - intros x k o Hx Hk E. destruct (proj1 (IG4 x) Hx) as [->|Hx3].
      + split; [reflexivity|]. change (s_slot s4 m k) with (s_slot (UbMhASlotKNest.st' s3 m g' idx' off sc cnt (cnt - 1) ((c_usage (s_ctx s3) sc + cnt) mod 2 ^ 64)) m k) in E.
        rewrite UbMhASlotKNest.e_slot_m in E. unfold UbMhASlotKTop.nslot_of in E.
        destruct (Z.eqb_spec k 0); [lia|]. destruct (k <=? cnt - 1); discriminate E.
      + exfalso. assert (Hxm : x <> m) by (intros ->; exact (NG3 Hx3)).
        change (s_slot s4 x k) with (s_slot (UbMhASlotKNest.st' s3 m g' idx' off sc cnt (cnt - 1) ((c_usage (s_ctx s3) sc + cnt) mod 2 ^ 64)) x k) in E.
        change (g_lastidx s4 x) with (g_lastidx (UbMhASlotKNest.st' s3 m g' idx' off sc cnt (cnt - 1) ((c_usage (s_ctx s3) sc + cnt) mod 2 ^ 64)) x) in Hk.
        rewrite (UbMhASlotKNest.e_glast s3 m g' idx' off sc cnt (cnt - 1) _ NG3 Hg3 Hidx3 Hsl3 Hsc ltac:(rewrite Hgsc3; lia) ltac:(lia) ltac:(lia) UR' x Hx3) in Hk.
        destruct (decide (x = g' /\ k = idx')) as [[-> ->]|NEQ].
        * rewrite (UbMhASlotKNest.e_slot_hi s3 m g' idx' off sc cnt (cnt - 1) _ NG3 Hg3) in E. discriminate E.
        * rewrite UbMhASlotKNest.e_slot_old in E; [| exact Hxm | lia].
          destruct (OJ3 x k o Hx3 Hk E) as [-> ->]. apply NEQ. split; reflexivity.
    - rewrite STm4, slot_stride_0. lia.
    - left. rewrite STm4, slot_stride_0. lia.
    - exact O10.
  Qed.

  (* [comment removed for export] *)
  Lemma L_N : forall s2 M2 mdl2 r m cnt,
    GBR s2 M2 mdl2 r m cnt -> 16 * size_class sc * cnt + 16 <= 2048 ->
    (bo = true -> bi = true \/ agf s2) ->
    kat RSEGS (mkCfg (mkst r (0x675c0%bv : word) M2 rom) mdl2) (kfx F bo).
  Proof using HL_E IHd HQF HQ DEF Hsp R4 Rra R2 HBUD Hreq Hlimbo Hd Hsc HL. clear - HL_E IHd HQF HQ DEF Hsp R4 Rra R2 HBUD Hreq Hlimbo Hd Hsc HL.
    intros s2 M2 mdl2 r m cnt GB Hle SIDE.
    destruct GB as (P2 & NJ2 & EL2 & Hnil & Um & Zm & NLm & G9 & G10 & G11 & G18 & G19 & G24 & G25 & G14 & G12 & C1 & C2 & C3 & C4).
    pose proof P2 as [W2 RP2 LG2 Hh2 Hlz2 Hmat2 Hfs2 Hfds2 Hlim2 Hcan2 Herr2 BL2 LM2 MU2 FR2 DF2 SK2 Q2 Q8 Q20 Q21 Q22 Q23 KB].
    pose proof scl_rng as SCL. pose proof stk272 as S272.
    assert (CNT2 : 2 <= cnt) by (destruct (Z.eq_dec cnt 1) as [E|NE]; [pose proof (C4 E); lia | lia]).
    assert (S1016 : 16 * size_class sc <= 1016) by nia.
    (* [comment removed for export] *)
    destruct (aNcls M2 (size_class sc) cnt ltac:(lia) ltac:(lia) ltac:(lia) (rc_tab_ctz s2 M2 (rp_statics s2 M2 RP2)) (sz_img_of_REP s2 M2 RP2)
                r rom G14 G25) as (r1 & RUN1 & E10 & E18 & E11 & E1 & K1).
    eapply kat_msteps; [exact Hh2 | exact Hlz2 | exact RUN1 |].
    set (nreq := ncls_n (size_class sc) cnt) in *. set (j := size_to_class nreq) in *.
    assert (Enreq : nreq + 4 = 16 * size_class sc * cnt + 16) by (subst nreq; unfold ncls_n; lia).
    assert (Hnreq : 0 <= nreq < MMAP_THRESHOLD) by (unfold MMAP_THRESHOLD; nia).
    pose proof (size_to_class_rng nreq Hnreq) as J48. fold j in J48.
    pose proof (size_to_class_fits nreq Hnreq) as FIT. fold j in FIT.
    assert (SCJ : sc < j).
    { destruct (Z.lt_ge_cases sc j) as [LT|GE]; [exact LT|]. exfalso.
      pose proof (size_class_mono j sc ltac:(lia) GE ltac:(lia)). nia. }
    (* [comment removed for export] *)
    assert (T2 : 2 * (16 * size_class sc) + 16 <= 16 * size_class j) by nia.
    pose proof (dbound_host 0 0 (16 * size_class sc) (16 * size_class j) ltac:(lia) T2) as DH.
    unfold dle in Hd.
    assert (XD : exists d', d = S d') by (destruct d as [|d0]; [exfalso; lia | exists d0; reflexivity]).
    destruct XD as (d' & Ed).
    pose proof (IHd d' ltac:(rewrite Ed; lia)) as IH.
    assert (Er2 : getr r1 2 = Z_to_bv 64 (sp - 144)) by (kept_rw K1; exact Q2).
    pose proof (ASSTK_S d') as AS'. rewrite <- Ed in AS'.
    apply (kat_of_kfx F bo). replace (0x672b0%bv : word) with (Z_to_bv 64 AS_ENTRY) by (apply bv_eq; reflexivity).
    apply (IH F bi bo s2 L M2 mdl2 r1 rom (sp - 144) j nreq HL SIDE W2 RP2 LG2 NJ2 Hh2 Hlz2 Hmat2 J48).
    { unfold dle. lia. }
    { rewrite EL2. rewrite zlen_cons. rewrite Ed, Nat2Z.inj_succ in Hlimbo. lia. }
    { lia. }
    { rewrite Hlim2. exact HBUD. }
    { exact E10. }
    { exact E11. }
    { exact Er2. }
    { rewrite E1. apply ret_ok_even. reflexivity. }
    { kept_rw K1. kept_rw KB. exact R4. }
    { lia. }
    { lia. }
    { intros y Hy. apply DF2. lia. }
    2: { (* [comment removed for export] *)
      intros c' PF.
      destruct PF as (s3 & M3 & mdl3 & r3 & -> & W3 & RP3 & LG3 & Hh3 & Hlz3 & Hmat3 & Hfs3 & Hfds3 & Hlim3 & NJ3 & EL3 & Hcan3 &
                      LM3 & MU3 & F10 & F2 & K3 & FRM3 & DEF3).
      rewrite E1. replace (Z_to_bv 64 423568) with (0x67690%bv : word) by (apply bv_eq; reflexivity).
      apply (kf_of_kat F HL).
      apply (L_FM st L M mdl regs rom sp sc req (Kf F) d Hsc Hreq Hlimbo R2 Rra Hsp HQF s3 M3 mdl3 r3 m (0x67690%bv : word)).
      - constructor; try assumption.
        + rewrite Hfs3. exact Hfs2.
        + rewrite Hfds3. exact Hfds2.
        + rewrite Hlim3. exact Hlim2.
        + rewrite Hcan3. exact Hcan2.
        + intros x Hx. rewrite (LM3 x ltac:(rewrite EL2; right; exact Hx)). exact (LM2 x Hx).
        + intros x Ux. exact (MU3 x (MU2 x Ux)).
        + intros a Ha NE. destruct (decide (M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a))) as [E|NE2].
          * apply FR2; [exact Ha | congruence].
          * destruct (FRM3 a Ha NE2) as [A|[A|[A|A]]]; [left; lia | right; left; exact A | right; right; left; exact A | right; right; right; exact A].
        + intros a Ha. destruct (decide (M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a))) as [E|NE]; [rewrite E; exact (DF2 a Ha)|].
          destruct (FRM3 a ltac:(ceil; lia) NE) as [A|[A|[A|A]]].
          * apply DEF3. exact A.
          * exfalso. ceil. lia.
          * exfalso. ceil; unfold CTX_END, CTX in *. lia.
          * exfalso. ceil; unfold A_ERRNO, TPV in *. lia.
        + apply (stk_transfer st regs sp sc req d Hsc Hreq Hsp M2 M3); [|exact SK2]. intros y Hy.
          destruct (decide (M3 (Z_to_bv 64 y) = M2 (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso.
          destruct (FRM3 y ltac:(ceil; lia) NE) as [A|[A|[A|A]]]; ceil; unfold A_ERRNO, TPV, CTX_END, CTX, HEAPLO in *; lia.
        + rewrite F2, Er2. reflexivity.
        + kept_rw K3. kept_rw K1. exact Q20.
        + eapply keeps_big; [eapply keeps_big; [exact KB | exact K1 | reflexivity] | exact K3 | reflexivity].
      - exact NJ3.
      - rewrite EL3. exact EL2.
      - exact NLm.
      - kept_rw K3. kept_rw K1. exact G9.
      - kept_rw K3. kept_rw K1. exact Q22.
      - exact F10.
      - left. reflexivity. }
    intros c' POST. apply (kfx_of_kat F HL bi).
    destruct POST as (s3 & M3 & mdl3 & r3 & g' & idx' & -> & W3 & RP3 & LG3 & Hh3 & Hlz3 & Hmat3 & Hfs3 & Hfds3 & Hlim3 & EL3 & Hcan3 & Herr3 &
                      Hhd3 & Hg3 & Hgsc3 & Hidx3 & Hsl3 & OJ3 & Hstr3 & Hbig3 & BL3 & LM3 & MU3 & F10 & F2 & K3 & FRM3 & DEF3).
    rewrite E1. replace (Z_to_bv 64 423568) with (0x67690%bv : word) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    assert (P3 : pt st L M mdl regs sp sc d s3 M3 mdl3 r3).
    { apply (pt_step2 st L M mdl regs sp sc req d Hsc Hreq Hsp s2 M2 mdl2 r s3 M3 mdl3 r3 P2 W3 RP3 LG3 Hh3 Hlz3 Hmat3); try assumption.
      - intros k Hk. apply BL3. lia.
      - intros x Hx. apply LM3. rewrite EL2. right. exact Hx.
      - intros a Ha. destruct (decide (M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a))) as [E|NE]; [rewrite E; exact (DF2 a Ha)|].
        destruct (FRM3 a ltac:(ceil; lia) NE) as [A|[A|[A|A]]].
        + apply DEF3. exact A.
        + exfalso. ceil. lia.
        + exfalso. ceil; unfold CTX_END, CTX in *. lia.
        + exfalso. ceil; unfold A_ERRNO, TPV in *. lia.
      - intros a Ha NE. destruct (FRM3 a Ha NE) as [A|[A|[A|A]]]; [left; lia | right; left; exact A | right; right; left; exact A | right; right; right; exact A].
      - rewrite F2, Er2, Q2. reflexivity.
      - kept_rw K3. kept_rw K1. reflexivity.
      - kept_rw K3. kept_rw K1. reflexivity.
      - kept_rw K3. kept_rw K1. reflexivity.
      - kept_rw K3. kept_rw K1. reflexivity.
      - kept_rw K3. kept_rw K1. reflexivity.
      - eapply keeps_big; [eapply keeps_big; [exact KB | exact K1 | reflexivity] | exact K3 | reflexivity]. }
    pose proof P3 as [_ _ _ _ _ _ _ _ _ _ _ BL3' LM3' MU3' FR3' DF3' SK3 T2' T8 T20 T21 T22 T23 KB3].
    assert (Hnil3 : s_alist s3 sc = []) by (rewrite (BL3 sc ltac:(lia)); exact Hnil).
    assert (EL3' : s_limbo s3 = m :: s_limbo st) by (rewrite EL3; exact EL2).
    assert (LIM3 : In m (s_limbo s3)) by (rewrite EL3'; left; reflexivity).
    destruct (wG_limbo s3 L (WF_groups s3 L W3) m LIM3) as (Um3 & NG3 & NL3 & NF3).
    assert (Zm3 : s_meta s3 m = meta_zero) by (rewrite (LM3 m ltac:(rewrite EL2; left; reflexivity)); exact Zm).
    destruct (metaU_rng s3 L W3 m Um3) as (MR1 & MR2 & MR8).
    pose proof (wG_each s3 L (WF_groups s3 L W3) g' Hg3) as WG'.
    pose proof (glast_rng s3 g') as GL'. pose proof (wg_stride s3 L g' WG') as [S16' Smod']. pose proof (wg_mem s3 L g' WG') as (GM1 & GM2 & GM3).
    pose proof (size_class_pos j J48) as [SJ1 SJ2].
    (* [comment removed for export] *)
    assert (J24 : j <= 24).
    { apply (size_to_class_min nreq 24 Hnreq ltac:(lia)). rewrite size_class_24. lia. }
    assert (SCJ24 : size_class j <= 146) by (rewrite <- size_class_24; apply size_class_mono; lia).
    assert (STR : 16 * size_class j <= g_stride s3 g') by (destruct Hbig3 as [B|B]; lia).
    (* [comment removed for export] *)
    set (ctr := c_mmap_ctr (s_ctx s3)). pose proof (wc_ctr s3 (WF_ctx s3 L W3)) as CTR. fold ctr in CTR.
    pose proof (rc_active s3 M3 (rp_ctx s3 M3 RP3) j J48) as Ract. rewrite (wc_active s3 (WF_ctx s3 L W3) j J48), Hhd3 in Ract.
    pose proof (rc_ctr s3 M3 (rp_ctx s3 M3 RP3)) as Rctr. fold ctr in Rctr.
    destruct (aNenf M3 j idx' g' ctr J48 ltac:(lia) CTR Ract Rctr (sz_img_of_REP s3 M3 RP3) r3 rom F10
                ltac:(kept_rw K3; exact E18) T22 ltac:(kept_rw K3; kept_rw K1; exact G25)) as (r4 & RUN4 & I10 & I11 & I12 & I13 & I1 & K4).
    eapply kat_msteps; [exact Hh3 | exact Hlz3 | exact RUN4 |].
    (* [comment removed for export] *)
    set (n_e := 16 * size_class j - 4) in *.
    set (cT := getr r4 13).
    destruct (efH_junk s3 L M3 W3 RP3 g' idx' n_e cT Hg3 Hidx3 ltac:(rewrite Hgsc3; lia) ltac:(subst n_e; lia) ltac:(subst n_e; lia)) as (h3 & o16 & EFH).
    set (strideH := g_stride s3 g') in *. set (start := g_slot_start s3 g' idx') in *.
    set (off := enframe_off (slack_of strideH n_e) ((if h3 =? 0 then bv_unsigned cT else o16 + 1) mod 256)) in *.
    destruct (ref_enframe r4 M3 rom (Z_to_bv 64 423616) cT g' (g_mem s3 g') (g_W s3 g') idx' n_e h3 o16 strideH start off EFH I1
                ltac:(apply ret_ok_even; reflexivity) I10 I11 I12 eq_refl) as (r5 & M5 & RUN5 & KCS & J10 & FRM & POST).
    eapply kat_msteps; [exact Hh3 | exact Hlz3 | exact RUN5 |].
    replace (Z_to_bv 64 423616) with (0x676c0%bv : word) by (apply bv_eq; reflexivity).
    destruct FRM as [FR5 G5].
    pose proof (Pr _ _ _ _ _ _ POST) as (PR1 & PR2 & PR3). unfold P_r in PR1. unfold P_q in PR3.
    set (p := start + 16 * off) in *.
    pose proof (slot_in_span s3 L W3 g' idx' Hg3 Hidx3) as [SP1 SP2]. fold start in SP1.
    assert (Ese : g_slot_end s3 g' idx' = start + strideH - 4) by (unfold g_slot_end, IB; reflexivity).
    rewrite Ese in SP2.
    destruct (group_range s3 L W3 g' Hg3) as [GR1 GR2].
    assert (M5eq : forall a, 0 <= a < 2 ^ 64 -> ~ (start - 3 <= a < start + strideH - 4) -> M5 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
    { intros a Ha OUT. apply FR5. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite !u64_lit by (ceil; (first [ (clear H0 PR3 GM2 Smod' MR8 Hbig3 Herr3 Herr2 SIDE HL_E; lia) | lia ])). lia. }
    (* [comment removed for export] *)
    assert (OFF16 : 16 * off <= strideH - 16 * size_class j) by (subst n_e; lia).
    assert (PEND : p + 12 + 16 * size_class sc * cnt <= start + strideH - 4) by (first [clear - OFF16 Enreq FIT | clear - OFF16 FIT]; subst p; zlia).
    assert (Pst : start <= p) by (subst p; lia).
    pose proof (metaU_apart_span s3 L M3 m g' W3 RP3 Um3 Hg3) as APART.
    destruct (meta_cells s3 L M3 W3 RP3 m Um3) as (arm & km & _ & _ & _ & _ & _ & _ & RMm & DEFar & Alo & Ahi).
    rewrite Zm3 in RMm. destruct RMm as [Cm0 Cm8 Cm16 Cm24 Cm28 Cm32]. cbn [mr_prev mr_next mr_mem mr_avail mr_freed mr_W meta_zero] in Cm0, Cm8, Cm16, Cm24, Cm28, Cm32.
    pose proof (group_bytes_defined s3 L M3 8 g' W3 RP3 (wg_depth s3 L g' WG') Hg3) as DEFg.
    assert (DEFg5 : defined M5 (g_mem s3 g') (gspan s3 g')) by (eapply defined_grows; [exact G5 | exact DEFg]).
    assert (DEFar5 : defined M5 arm (arm + 4096)) by (eapply defined_grows; [exact G5 | exact DEFar]).
    assert (AGm : forall a k, m <= a -> a + Z.of_nat k <= m + 40 -> rdn RSEGS M5 (Z_to_bv 64 a) k = rdn RSEGS M3 (Z_to_bv 64 a) k).
    { intros a k Ha Hk. apply rdn_agreeZ; [unfold HEAPLO in *; (first [ (clear APART PR3 GM2 Smod' MR8 Hbig3 Herr3 Herr2 SIDE HL_E; lia) | lia ]) | ceil; (first [ (clear H0 APART PR3 GM2 Smod' MR8 Hbig3 Herr3 Herr2 SIDE HL_E; lia) | lia ]) |]. intros y Hy. apply M5eq; [ceil; unfold HEAPLO in *; (first [ (clear H0 APART PR3 GM2 Smod' MR8 FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ])|]. (first [ (clear APART GM2 MR8 FR3' Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ]). }
    set (b3 := idx' + 32 * res_code (strideH - 4 - n_e - 16 * off)).
    assert (Hb3 : 0 <= b3 < 256 /\ b3 mod 32 = idx').
    { subst b3. unfold res_code. destruct (Z.ltb_spec (strideH - 4 - n_e - 16 * off) 5).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      all: split; (first [ (clear APART GM2 MR8 FR3' Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ]). }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    (* [comment removed for export] *)
    assert (ZOK : forall k, 0 <= k <= cnt -> store_ok RSEGS M5 (Z_to_bv 64 (p + 12 + k * (16 * size_class sc))) 1%nat = true).
    { intros k Hk. assert (KM : 0 <= k * (16 * size_class sc) <= cnt * (16 * size_class sc)) by (split; [apply Z.mul_nonneg_nonneg; (first [ (clear Hb3 APART PR3 GM2 Smod' MR8 FR3' Herr3 FR2 Herr2 SIDE; lia) | lia ]) | apply Z.mul_le_mono_nonneg_r; (first [ (clear Hb3 APART PR3 GM2 Smod' MR8 FR3' Herr3 FR2 Herr2 SIDE; lia) | lia ])]).
      eapply (store_ok_defined M5 (g_mem s3 g') (gspan s3 g')); [exact DEFg5 | (first [ (clear Hb3 PR3 Smod' MR8 FR3' FR2 Herr2 SIDE; lia) | lia ]) | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; (first [ (clear Hb3 PR3 Smod' MR8 FR3' FR2 Herr2 SIDE; lia) | lia ]) | unfold HEAPLO in *; (first [ (clear Hb3 PR3 Smod' MR8 FR3' Hbig3 FR2 Herr2 SIDE HL_E; lia) | lia ]) | ceil; (first [ (clear H0 Hb3 PR3 Smod' MR8 FR3' Hbig3 FR2 Herr2 SIDE HL_E; lia) | lia ])]. }
    destruct (aNzero M5 m p 0 b3 (size_class sc) cnt ltac:((first [ (clear Hb3 APART PR3 GM2 Smod' MR8 FR3' Herr3 FR2 Herr2 SIDE; lia) | lia ])) ltac:((first [ (clear Hb3 APART PR3 GM2 Smod' MR8 FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ])) ltac:((first [ (clear Hb3 APART PR3 GM2 Smod' MR8 FR3' Herr3 FR2 Herr2 SIDE; lia) | lia ])) ltac:(unfold HEAPLO in *; (first [ (clear Hb3 PR3 GM2 Smod' Hbig3 Herr3 Herr2 SIDE HL_E; lia) | lia ])) ltac:((first [ (clear Hb3 APART PR3 GM2 Smod' MR8 Herr3 Herr2 SIDE; lia) | lia ]))
                ltac:(destruct APART; [left | right]; (first [ (clear Hb3 PR3 GM2 Smod' FR3' Herr3 FR2 Herr2 SIDE; lia) | lia ])) ltac:((first [ (clear Hb3 APART PR3 GM2 Smod' MR8 FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ])) (proj1 Hb3)
                ltac:(rewrite (AGm (m + 32) 8%nat) by (cbn; (first [ (clear Hb3 PR3 GM2 Smod' FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ])); exact Cm32)
                ltac:(eapply (store_ok_defined M5 arm (arm + 4096)); [exact DEFar5 | (first [ (clear Hb3 PR3 GM2 Smod' FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ]) | cbn; (first [ (clear Hb3 PR3 GM2 Smod' FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ]) | unfold HEAPLO in *; (first [ (clear Hb3 APART PR3 GM2 Smod' MR8 FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ]) | ceil; (first [ (clear H0 Hb3 APART PR3 GM2 Smod' MR8 FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ])])
                ltac:(apply rdn1_of_byte; exact (Pm3 _ _ _ _ _ _ POST))
                ltac:(eapply (store_ok_defined M5 (g_mem s3 g') (gspan s3 g')); [exact DEFg5 | (first [ (clear Hb3 PR3 Smod' MR8 FR3' Hbig3 FR2 Herr2 SIDE HL_E; lia) | lia ]) | cbn; (first [ (clear Hb3 PR3 Smod' MR8 FR3' Hbig3 FR2 Herr2 SIDE HL_E; lia) | lia ]) | unfold HEAPLO in *; (first [ (clear Hb3 PR3 Smod' MR8 FR3' Hbig3 FR2 Herr2 SIDE HL_E; lia) | lia ]) | ceil; (first [ (clear H0 Hb3 PR3 Smod' MR8 FR3' Hbig3 FR2 Herr2 SIDE HL_E; lia) | lia ])])
                ZOK
                r5 rom J10
                ltac:(rewrite (KCS 9%bv ltac:(inCS)); kept_rw K4; kept_rw K3; kept_rw K1; exact G9)
                ltac:(rewrite (KCS 19%bv ltac:(inCS)); kept_rw K4; kept_rw K3; kept_rw K1; exact G19)
                ltac:(rewrite (KCS 24%bv ltac:(inCS)); kept_rw K4; kept_rw K3; kept_rw K1; exact G24))
      as (r6 & RUN6 & H11 & H12 & H25 & H10 & K6).
    eapply kat_msteps; [exact Hh3 | exact Hlz3 | exact RUN6 |].
    set (M6 := m_nz M5 m p 0 b3 (size_class sc) cnt) in *.
    assert (G6 : mem_grows M5 M6) by (unfold M6, m_nz, m_nz1; eapply mem_grows_trans; [|apply zero_run_grows]; eapply mem_grows_trans; apply wbytes_grows).
    assert (SZr : Z.of_nat (Z.to_nat (cnt + 1)) = cnt + 1) by (first [ (clear Hb3 APART PR3 GM2 Smod' MR8 FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ]).
    assert (SC16 : 16 <= 16 * size_class sc) by (first [ (clear Hb3 APART PR3 GM2 Smod' MR8 FR3' Herr3 FR2 Herr2 SIDE; lia) | lia ]).
    (* [comment removed for export] *)
    assert (AG5 : forall a k, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 -> (a + Z.of_nat k <= start - 3 \/ start + strideH - 4 <= a) ->
                  rdn RSEGS M5 (Z_to_bv 64 a) k = rdn RSEGS M3 (Z_to_bv 64 a) k).
    { intros a k Ha Hk D. apply rdn_agreeZ; [lia | lia |]. intros y Hy. apply M5eq; clear - Ha Hk D Hy; zlia. }
    (* [comment removed for export] *)
    assert (ZR : forall a n v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (a + Z.of_nat n <= p + 12 \/ p + 12 + cnt * (16 * size_class sc) < a) ->
                 cell (m_nz1 M5 m p 0 b3) a n v -> cell M6 a n v).
    { intros a n v Ha Hn D C. unfold M6, m_nz.
      assert (X1 : (cnt + 1) * (16 * size_class sc) = cnt * (16 * size_class sc) + 16 * size_class sc) by lia.
      assert (X2 : cnt * (16 * size_class sc) = 16 * size_class sc * cnt) by lia.
      apply cell_zero_run; rewrite ?SZr; [unfold HEAPLO in *; (first [ (clear AG5 Hb3 APART PR3 GM2 Smod' MR8 FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ]) | ceil; (first [ (clear H0 AG5 Hb3 APART PR3 GM2 Smod' MR8 FR3' Herr3 FR2 Herr2 SIDE; lia) | lia ]) | (first [ (clear AG5 Hb3 APART PR3 GM2 Smod' MR8 FR3' Herr3 FR2 Herr2 SIDE; lia) | lia ]) | (first [ (clear Hb3 APART PR3 GM2 Smod' MR8 Hbig3 Herr3 Herr2 SIDE HL_E; lia) | lia ]) | (first [ (clear Hb3 APART PR3 GM2 Smod' MR8 Hbig3 Herr3 Herr2 SIDE HL_E; lia) | lia ]) | | exact C].
      replace (cnt + 1 - 1) with cnt by lia. exact D. }
    assert (C6u : cell M6 (ctx_usage sc) 8 (c_usage (s_ctx s3) sc)).
    { apply ZR; [unfold ctx_usage, CTX; (first [ (clear AG5 Hb3 APART PR3 GM2 Smod' MR8 FR3' Hbig3 Herr3 FR2 Herr2 SIDE; lia) | lia ]) | unfold ctx_usage, CTX; cbn; (first [ (clear AG5 Hb3 APART PR3 GM2 Smod' MR8 FR3' Hbig3 Herr3 FR2 Herr2 SIDE; lia) | lia ]) | unfold ctx_usage, CTX, HEAPLO in *; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; (first [ (clear AG5 Hb3 APART PR3 GM2 Smod' MR8 FR3' Herr3 FR2 Herr2 SIDE; lia) | lia ]) |].
      unfold m_nz1. ceil; unfold ctx_usage, CTX, HEAPLO in *. peel. peel. unfold cell. rewrite AG5 by (cbn; (first [ (clear H0 Hb3 APART GM2 MR8 FR3' Herr3 FR2 Herr2 SIDE; lia) | lia ])). exact (rc_usage s3 M3 (rp_ctx s3 M3 RP3) sc Hsc). }
    assert (C6a : cell M6 (ctx_active sc) 8 0).
    { apply ZR; [unfold ctx_active, CTX; (first [ (clear AG5 Hb3 APART PR3 GM2 Smod' MR8 FR3' Hbig3 Herr3 FR2 Herr2 SIDE; lia) | lia ]) | unfold ctx_active, CTX; cbn; (first [ (clear AG5 Hb3 APART PR3 GM2 Smod' MR8 FR3' Hbig3 Herr3 FR2 Herr2 SIDE; lia) | lia ]) | unfold ctx_active, CTX, HEAPLO in *; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; (first [ (clear AG5 Hb3 APART PR3 GM2 Smod' MR8 FR3' Herr3 FR2 Herr2 SIDE; lia) | lia ]) |].
      unfold m_nz1. ceil; unfold ctx_active, CTX, HEAPLO in *. peel. peel. unfold cell. rewrite AG5 by (cbn; (first [ (clear H0 Hb3 APART GM2 MR8 FR3' Herr3 FR2 Herr2 SIDE; lia) | lia ])).
      pose proof (rc_active s3 M3 (rp_ctx s3 M3 RP3) sc Hsc) as C. rewrite (wc_active s3 (WF_ctx s3 L W3) sc Hsc), Hnil3 in C. exact C. }
    assert (APd : forall a n, m <= a -> a + n <= m + 40 -> 0 <= n -> a + n <= p + 12 \/ p + 12 + cnt * (16 * size_class sc) < a).
    { intros a n Ha Hn Hn0. destruct APART as [A|A]; [left | right]; clear - A Ha Hn Hn0 SP1 SP2 Pst PEND; zlia. }
    assert (C6W : cell M6 (m + 32) 8 0).
    { apply ZR; [unfold HEAPLO in *; (first [ (clear AG5 Hb3 PR3 GM2 Smod' FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ]) | ceil; cbn; (first [ (clear H0 AG5 Hb3 PR3 GM2 Smod' FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ]) | apply APd; cbn; (first [ (clear AG5 Hb3 PR3 GM2 Smod' FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ]) |].
      unfold m_nz1. ceil; unfold HEAPLO in *. peel. change (0 mod 4096) with 0. hit. }
    assert (C6m8 : cell M6 (m + 8) 8 0).
    { apply ZR; [unfold HEAPLO in *; lia | ceil; cbn; lia | apply APd; cbn; lia |].
      unfold m_nz1. ceil; unfold HEAPLO in *. peel. peel. unfold cell. rewrite AG5 by (cbn; (first [ (clear H0 Hb3 GM2 FR3' Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ])). exact Cm8. }
    assert (C6m0 : cell M6 m 8 0).
    { apply ZR; [unfold HEAPLO in *; (first [ (clear AG5 Hb3 PR3 GM2 Smod' FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ]) | ceil; cbn; (first [ (clear H0 AG5 Hb3 PR3 GM2 Smod' FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ]) | apply APd; cbn; (first [ (clear AG5 Hb3 PR3 GM2 Smod' FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ]) |].
      unfold m_nz1. ceil; unfold HEAPLO in *. peel. peel. unfold cell. rewrite AG5 by (cbn; (first [ (clear H0 Hb3 GM2 FR3' Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ])). exact Cm0. }
    destruct (byte_of_def M6 (p + 8) ltac:(apply G6; apply DEFg5; (first [ (clear AG5 Hb3 PR3 Smod' MR8 FR3' Hbig3 FR2 Herr2 SIDE HL_E; lia) | lia ]))) as (b8 & Hb8 & B8).
    assert (SOKc6 : store_ok RSEGS M6 (Z_to_bv 64 CTX) 928%nat = true) by (apply store_ok_wseg; vm_compute; reflexivity).
    assert (SOKm6 : store_ok RSEGS M6 (Z_to_bv 64 m) 40%nat = true).
    { eapply (store_ok_defined M6 arm (arm + 4096)); [eapply defined_grows; [exact G6 | exact DEFar5] | (first [ (clear AG5 Hb3 PR3 GM2 Smod' FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ]) | cbn; (first [ (clear AG5 Hb3 PR3 GM2 Smod' FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ]) | unfold HEAPLO in *; (first [ (clear APd ZR AG5 Hb3 APART PR3 GM2 Smod' MR8 FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ]) | ceil; (first [ (clear H0 APd ZR AG5 Hb3 APART PR3 GM2 Smod' MR8 FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ])]. }
    assert (SOKp6 : store_ok RSEGS M6 (Z_to_bv 64 p) 9%nat = true).
    { eapply (store_ok_defined M6 (g_mem s3 g') (gspan s3 g')); [eapply defined_grows; [exact G6 | exact DEFg5] | (first [ (clear AG5 Hb3 PR3 Smod' MR8 FR3' Hbig3 FR2 Herr2 SIDE HL_E; lia) | lia ]) | cbn; (first [ (clear AG5 Hb3 PR3 Smod' MR8 FR3' Hbig3 FR2 Herr2 SIDE HL_E; lia) | lia ]) | unfold HEAPLO in *; (first [ (clear APd ZR AG5 Hb3 PR3 Smod' MR8 FR3' Hbig3 FR2 Herr2 SIDE HL_E; lia) | lia ]) | ceil; (first [ (clear H0 APd ZR AG5 Hb3 PR3 Smod' MR8 FR3' Hbig3 FR2 Herr2 SIDE HL_E; lia) | lia ])]. }
    pose proof (wc_usage s3 (WF_ctx s3 L W3) sc) as UR.
    (* [comment removed for export] *)
    destruct (aCommon M6 m p sc cnt (cnt - 1) (c_usage (s_ctx s3) sc) 0 b8 Hsc ltac:((first [ (clear AG5 Hb3 APART PR3 GM2 Smod' MR8 FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ])) ltac:((first [ (clear AG5 Hb3 APART PR3 GM2 Smod' MR8 FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ])) UR ltac:(unfold HEAPLO in *; (first [ (clear AG5 Hb3 PR3 GM2 Smod' Hbig3 Herr3 Herr2 SIDE HL_E; lia) | lia ])) ltac:((first [ (clear AG5 Hb3 APART PR3 GM2 Smod' MR8 Hbig3 Herr3 Herr2 SIDE HL_E; lia) | lia ]))
                ltac:(destruct APART; [left | right]; (first [ (clear AG5 Hb3 PR3 GM2 Smod' FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ])) ltac:((first [ (clear APd ZR AG5 Hb3 APART PR3 GM2 Smod' MR8 FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ])) Hb8 C6u C6a C6W C6m8 C6m0 (rdn1_of_byte _ _ _ B8) SOKc6 SOKm6 SOKp6 r6 rom
                ltac:(kept_rw K6; rewrite (KCS 23%bv ltac:(inCS)); kept_rw K4; exact T23)
                ltac:(kept_rw K6; rewrite (KCS 21%bv ltac:(inCS)); kept_rw K4; exact T21)
                ltac:(kept_rw K6; rewrite (KCS 8%bv ltac:(inCS)); kept_rw K4; exact T8)
                H25
                ltac:(kept_rw K6; rewrite (KCS 9%bv ltac:(inCS)); kept_rw K4; kept_rw K3; kept_rw K1; exact G9)
                H10 H11 H12) as (r7 & RUN7 & O10 & O9 & K7).
    eapply kat_msteps; [exact Hh3 | exact Hlz3 | exact RUN7 |].
    apply (nest_tail s3 M3 mdl3 r3 r4 r5 r6 r7 M5 g' idx' j m cnt off b3 b8 arm W3 RP3 Hg3 Hidx3 Hsl3 Hgsc3 J48 SCJ OJ3 Hnil3 EL3' Um3 NG3 NL3 NF3 Zm3 NLm P3
             ltac:((first [ (clear AG5 Hb3 APART PR3 GM2 Smod' MR8 FR3' Hbig3 Herr3 FR2 Herr2 SIDE HL_E; lia) | lia ])) Hle ltac:((first [ (clear AG5 Hb3 APART PR3 GM2 Smod' MR8 FR3' Herr3 FR2 Herr2 SIDE; lia) | lia ])) STR POST M5eq G5 Hb3 (Pm3 _ _ _ _ _ _ POST) Hb8 B8 Alo Ahi DEFar Cm0 Cm8 Cm32 K4 KCS K6 K7 O10).
  Qed.
End ASN.
