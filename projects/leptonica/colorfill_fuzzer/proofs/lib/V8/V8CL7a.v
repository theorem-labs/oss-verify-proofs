(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From OSSVerify.leptonica.colorfill_fuzzer.images Require Ubsan.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require PropExec.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require CatExec.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require CatSim.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require StepTac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Hoare.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require AllocIface.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require PureModel.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require VmLedger.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require StoreOk.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require MemSplit.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require StartupTac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require WalkTac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require AllocBase.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require AllocSure.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8LeptStderr.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8LeptBase.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8_code_13734_14000.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LeptRoom.
Module V8LeptErr.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.colorfill_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8LeptStderr.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8LeptBase.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8_code_13734_14000.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptRoom.
(* [comment removed for export] *)
(* [comment removed for export] *)









Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Err.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU8} {PU8 : V8Pins}.

#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section RetErr.
  Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma rep_A : forall regs m (s msg proc : Z) (ret val : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 16)) 16 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 msg ->
    getr regs 11 = Z_to_bv 64 proc -> getr regs 12 = val ->
    exists regs',
      msteps SEGS (mkst regs (0x13ef4 : word) m rom)
                  (mkst regs' (0x13e58 : word)
                        (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                                (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 1 = Z_to_bv 64 0x13f14
      /\ getr regs' 10 = Z_to_bv 64 0x10cbd /\ getr regs' 11 = Z_to_bv 64 proc /\ getr regs' 12 = Z_to_bv 64 msg
      /\ getr regs' 8 = val
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 12]%list) regs regs'.
  Proof.
    intros regs m s msg proc ret val Hs Hs64 SOK H2 H1 H10 H11 H12.
    eexists. split.
    - zv F_13df0 D_13df0 (Z_to_bv 64 (s - 16)).                              (* [comment removed for export] *)
      stepST F_13df4 D_13df4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).     (* [comment removed for export] *)
      stepST F_13df8 D_13df8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).  (* [comment removed for export] *)
      sn F_13dfc D_13dfc.                                                     (* [comment removed for export] *)
      sn F_13e00 D_13e00.                                                     (* [comment removed for export] *)
      sn F_13e04 D_13e04.                                                     (* [comment removed for export] *)
      sn F_13e08 D_13e08.                                                     (* [comment removed for export] *)
      sn F_13e0c D_13e0c.                                                     (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rep_B : forall regs m (s : Z) (ret s0v : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    getr regs 2 = Z_to_bv 64 (s - 16) ->
    exists regs',
      msteps SEGS (mkst regs (0x13f14 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = getr regs 8 /\ getr regs' 8 = s0v
      /\ regs_agree (fun r => In r [1; 2; 8; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v Hs Hs64 Hret R8 R16 H2.
    eexists. split.
    - sn F_13e10 D_13e10.                                                     (* [comment removed for export] *)
      stepLD8 F_13e14 D_13e14 ret.                                            (* [comment removed for export] *)
      stepLD8 F_13e18 D_13e18 s0v.                                            (* [comment removed for export] *)
      zv F_13e1c D_13e1c (Z_to_bv 64 s).                                      (* [comment removed for export] *)
      stepret F_13e20 D_13e20 ret ltac:(bveq).                                (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End RetErr.

(* [comment removed for export] *)
Lemma rdn_after : forall (m m' : word -> option byte) (lo hi a : Z) (n : nat) bs,
  (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) ->
  (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z -> (hi <= a \/ a + Z.of_nat n <= lo)%Z ->
  rdn SEGS m (Z_to_bv 64 a) n = Some bs -> rdn SEGS m' (Z_to_bv 64 a) n = Some bs.
Proof.
  intros m m' lo hi a n bs OUT Ha Hn Hd R. rewrite <- R. destruct n as [|n']; [reflexivity|].
  apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply OUT. lia.
Qed.

(* [comment removed for export] *)
Lemma returnErrorPtr_W : forall C A m md regs (s msg proc : Z) kmsg kproc (ret val : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + (16 + LSF) <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 msg -> getr regs 11 = Z_to_bv 64 proc -> getr regs 12 = val ->
  str16 msg kmsg -> str16 proc kproc ->
  (forall m' regs', W C A m' md ->
      (forall a : word, ~ (s - (16 + LSF) <= u a < s)%Z -> m' a = m a) -> mem_grows m m' ->
      cs_kept regs regs' -> getr regs' 10 = val ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x13ef4 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s msg proc kmsg kproc ret val S CK HW H2 Hu16 Hlo Hhi H1 Hret H10 H11 H12 Smsg Sproc HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU8] in *. unfold LSF in *.
  pose proof Smsg as (_ & _ & Bm & _). pose proof Sproc as (_ & _ & Bp & _).
  destruct (rep_A al_rom regs m s msg proc ret val ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes m _ _) _ _).
  assert (HW1 : W C A M1 md).
  { subst M1. apply (W_store_win C A); [exact CK | | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
    apply (W_store_win C A); [exact CK | exact HW | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
  apply (lept_stderr2_W C A M1 md r1 (s - 16) proc msg kproc kmsg (Z_to_bv 64 0x13f14) S CK HW1 Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hu16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity)
           Q10 Q11 Q12 Sproc Smsg).
  intros m2 r2 HW2 OUT2 GR2 CS2. unfold LSF in OUT2.
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 16)) by (csr; reflexivity).
  destruct (rep_B al_rom r2 m2 s ret (getr regs 8) ltac:(lia) ltac:(lia) Hret) as (r3 & RUN3 & P2 & P1 & P10 & P8 & AG3).
  { apply (rdn_after M1 m2 (s - 16 - 3376) (s - 16)); [exact OUT2 | lia | cbn; lia | cbn; lia |]. subst M1. rdn_solve. }
  { apply (rdn_after M1 m2 (s - 16 - 3376) (s - 16)); [exact OUT2 | lia | cbn; lia | cbn; lia |]. subst M1. rdn_solve. }
  { exact E2. }
  replace (Z_to_bv 64 0x13f14) with (0x13f14 : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  apply HK.
  - exact HW2.
  - intros a Ha. rewrite OUT2 by lia. subst M1. rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity.
  - eapply mem_grows_trans; [|exact GR2]. subst M1. eapply mem_grows_trans; apply wbytes_grows.
  - apply cs_kept_intro; csr; try reflexivity.
  - csr. reflexivity.
Qed.

Section RetErrI.
  Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma rei_A : forall regs m (s msg proc : Z) (ret val : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 16)) 16 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 msg ->
    getr regs 11 = Z_to_bv 64 proc -> getr regs 12 = val ->
    exists regs',
      msteps SEGS (mkst regs (0x13e24 : word) m rom)
                  (mkst regs' (0x13e58 : word)
                        (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                                (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 1 = Z_to_bv 64 0x13e44
      /\ getr regs' 10 = Z_to_bv 64 0x10cbd /\ getr regs' 11 = Z_to_bv 64 proc /\ getr regs' 12 = Z_to_bv 64 msg
      /\ getr regs' 8 = val
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 12]%list) regs regs'.
  Proof.
    intros regs m s msg proc ret val Hs Hs64 SOK H2 H1 H10 H11 H12.
    eexists. split.
    - zv F_13d20 D_13d20 (Z_to_bv 64 (s - 16)).                              (* [comment removed for export] *)
      stepST F_13d24 D_13d24 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).     (* [comment removed for export] *)
      stepST F_13d28 D_13d28 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).  (* [comment removed for export] *)
      sn F_13d2c D_13d2c.                                                     (* [comment removed for export] *)
      sn F_13d30 D_13d30.                                                     (* [comment removed for export] *)
      sn F_13d34 D_13d34.                                                     (* [comment removed for export] *)
      sn F_13d38 D_13d38.                                                     (* [comment removed for export] *)
      sn F_13d3c D_13d3c.                                                     (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rei_B : forall regs m (s : Z) (ret s0v : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    getr regs 2 = Z_to_bv 64 (s - 16) ->
    exists regs',
      msteps SEGS (mkst regs (0x13e44 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = getr regs 8 /\ getr regs' 8 = s0v
      /\ regs_agree (fun r => In r [1; 2; 8; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v Hs Hs64 Hret R8 R16 H2.
    eexists. split.
    - sn F_13d40 D_13d40.                                                     (* [comment removed for export] *)
      stepLD8 F_13d44 D_13d44 ret.                                            (* [comment removed for export] *)
      stepLD8 F_13d48 D_13d48 s0v.                                            (* [comment removed for export] *)
      zv F_13d4c D_13d4c (Z_to_bv 64 s).                                      (* [comment removed for export] *)
      stepret F_13d50 D_13d50 ret ltac:(bveq).                                (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End RetErrI.

(* [comment removed for export] *)
Lemma returnErrorInt_W : forall C A m md regs (s msg proc : Z) kmsg kproc (ret val : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + (16 + LSF) <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 msg -> getr regs 11 = Z_to_bv 64 proc -> getr regs 12 = val ->
  str16 msg kmsg -> str16 proc kproc ->
  (forall m' regs', W C A m' md ->
      (forall a : word, ~ (s - (16 + LSF) <= u a < s)%Z -> m' a = m a) -> mem_grows m m' ->
      cs_kept regs regs' -> getr regs' 10 = val ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x13e24 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s msg proc kmsg kproc ret val S CK HW H2 Hu16 Hlo Hhi H1 Hret H10 H11 H12 Smsg Sproc HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU8] in *. unfold LSF in *.
  pose proof Smsg as (_ & _ & Bm & _). pose proof Sproc as (_ & _ & Bp & _).
  destruct (rei_A al_rom regs m s msg proc ret val ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes m _ _) _ _).
  assert (HW1 : W C A M1 md).
  { subst M1. apply (W_store_win C A); [exact CK | | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
    apply (W_store_win C A); [exact CK | exact HW | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
  apply (lept_stderr2_W C A M1 md r1 (s - 16) proc msg kproc kmsg (Z_to_bv 64 0x13e44) S CK HW1 Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hu16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity)
           Q10 Q11 Q12 Sproc Smsg).
  intros m2 r2 HW2 OUT2 GR2 CS2. unfold LSF in OUT2.
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 16)) by (csr; reflexivity).
  destruct (rei_B al_rom r2 m2 s ret (getr regs 8) ltac:(lia) ltac:(lia) Hret) as (r3 & RUN3 & P2 & P1 & P10 & P8 & AG3).
  { apply (rdn_after M1 m2 (s - 16 - 3376) (s - 16)); [exact OUT2 | lia | cbn; lia | cbn; lia |]. subst M1. rdn_solve. }
  { apply (rdn_after M1 m2 (s - 16 - 3376) (s - 16)); [exact OUT2 | lia | cbn; lia | cbn; lia |]. subst M1. rdn_solve. }
  { exact E2. }
  replace (Z_to_bv 64 0x13e44) with (0x13e44 : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  apply HK.
  - exact HW2.
  - intros a Ha. rewrite OUT2 by lia. subst M1. rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity.
  - eapply mem_grows_trans; [|exact GR2]. subst M1. eapply mem_grows_trans; apply wbytes_grows.
  - apply cs_kept_intro; csr; try reflexivity.
  - csr. reflexivity.
Qed.

End Err.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V8LeptErr.

From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Reloc Require Reloc.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.VL Require LeptBase.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8Kit.
Module V8LeptG.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Reloc.Reloc.
Import V8Kit.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8LeptBase.
(* [comment removed for export] *)








Import V8Kit.V8Reloc. Import V8Kit.V8RelocVL.


Lemma v8_LL : LLU8 = @LeptBase.LLG v8_reloc v8_lept.
Proof. reflexivity. Qed.

Definition v8_pinsG {AL : AllocLayout} {CL : CallocLayout} (PP : @V8Pins AL CL) : @LeptBase.PinsG v8_reloc AL CL :=
  @LeptBase.Build_PinsG v8_reloc AL CL (@pu8_segs AL CL PP) (@pu8_malloc AL CL PP) (@pu8_free AL CL PP) (@pu8_calloc AL CL PP) (@pu8_tp AL CL PP).
End V8LeptG.

From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require W2Lib.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LeptArith.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LeptRecs.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LeptSlots.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8_code_15000_16000.
Module V8LeptPixMisc.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.colorfill_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptRecs.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptSlots.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8LeptStderr.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8LeptBase.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8_code_15000_16000.
(* [comment removed for export] *)








Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section PixMisc.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU8} {PU8 : V8Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM; unorm; rewrite EQ; reflexivity).

  Definition pxF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)).

  (* [comment removed for export] *)
  Lemma px_null : forall regs m (s pp : Z) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> ret_ok ret -> (pp mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) -> (pp + 8 <= s - 32 \/ s <= pp)%Z ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x154fc : word) m rom) (mkst regs' ret (pxF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 11]%list) regs regs'.
  Proof.
    intros regs m s pp ret Hs Hs64 Hpp Hpp64 Hret ALpp SOK Rpp DJ H2 H1 H10.
    eexists. split.
    - zv F_153f8 D_153f8 (Z_to_bv 64 (s - 32)).
      stepST F_153fc D_153fc (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_15400 D_15400 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_15404 D_15404 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_15408 D_15408 ltac:(condZ).
      zand F_1540c D_1540c andi_7 ALpp. stepb_ft F_15410 D_15410 ltac:(condZ).
      stepLD F_15414 D_15414 (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply lez8; lia).
      stepb_tk F_15418 D_15418 ltac:(condZ).
      unfold pxF.
      stepLD8 F_154c0 D_154c0 ret. stepLD8 F_154c4 D_154c4 (getr regs 8). stepLD8 F_154c8 D_154c8 (getr regs 9).
      zv F_154cc D_154cc (Z_to_bv 64 s).
      stepret F_154d0 D_154d0 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma px_dec : forall regs m (s pp pix : Z) (v : pixv) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> ret_ok ret -> (pix mod 16 = 0)%Z -> (1 <= pix)%Z -> (pp mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true -> store_ok SEGS m (Z_to_bv 64 pix) 64 = true -> store_ok SEGS m (Z_to_bv 64 pp) 8 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) -> (pp + 8 <= s - 32 \/ s <= pp)%Z ->
    PIXat m pix v -> p_rc v = 2%Z -> (pix + 64 <= s - 32)%Z -> (pp + 8 <= pix \/ pix + 64 <= pp)%Z ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x154fc : word) m rom)
                  (mkst regs' ret (wbytes (wbytes (pxF m s ret regs) (Z_to_bv 64 (pix + 20)) (word_to_le_bytes 4 (Z_to_bv 64 1)))
                                          (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s pp pix v ret Hs Hs64 Hpp Hpp64 Hret Hal Hpix1 ALpp SOK SOKx SOKp Rpp DJ PX RC Hpix DJ2 H2 H1 H10.
    pose proof PX as (Hp0 & Hp64 & WF & _).
    assert (AL8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact Hal | reflexivity]).
    assert (PX' : PIXat (pxF m s ret regs) pix v).
    { unfold pxF. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
    eexists. split.
    - zv F_153f8 D_153f8 (Z_to_bv 64 (s - 32)).
      stepST F_153fc D_153fc (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_15400 D_15400 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_15404 D_15404 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_15408 D_15408 ltac:(condZ).
      zand F_1540c D_1540c andi_7 ALpp. stepb_ft F_15410 D_15410 ltac:(condZ).
      stepLD F_15414 D_15414 (Z_to_le_bytes 8 pix) (Z_to_bv 64 pix) ltac:(addr_norm; rdn_solve) ltac:(apply lez8; lia).
      stepb_ft F_15418 D_15418 ltac:(condZ).
      zand F_1541c D_1541c andi_7 AL8. stepb_ft F_15420 D_15420 ltac:(condZ).
      zv F_15424 D_15424 (Z_to_bv 64 (pix + 20)).
      sn F_15428 D_15428.
      change (wbytes (wbytes (wbytes m _ _) _ _) _ _) with (pxF m s ret regs).
      chain_step;
        [ reflexivity
        | eapply (step_amoadd_w SEGS _ _ _ rom _ _ _ _ _ _ (Z_to_le_bytes 4 2) (Z_to_bv 64 2) F_1542c eq_refl D_1542c);
          [ gres; rewrite u_Z2bv by lia; apply mod16_plus_mod4; [exact Hal | reflexivity]
          | gres; rewrite <- RC; exact (PIX_rd_rc SEGS _ _ _ PX')
          | apply lez4; lia
          | gres; unfold pxF; sok_in SOKx ]
        | step_simpl ].
      gres. rewrite zbv_add. replace (Z_to_bv 64 (2 + 18446744073709551615)%Z) with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity).
      rewrite (v_lw_small 2) by lia.
      sn F_15430 D_15430.
      stepb_tk F_15434 D_15434 ltac:(condZ).
      stepST F_15480 D_15480 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(unfold pxF; sok_in SOKp).
      sn F_15484 D_15484.
      unfold pxF.
      stepLD8 F_154c0 D_154c0 ret. stepLD8 F_154c4 D_154c4 (getr regs 8). stepLD8 F_154c8 D_154c8 (getr regs 9).
      zv F_154cc D_154cc (Z_to_bv 64 s).
      stepret F_154d0 D_154d0 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

Lemma pxF_out : forall m s ret regs (x : word), (32 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (u x < s - 32 \/ s <= u x)%Z -> pxF m s ret regs x = m x.
Proof.
  intros m s ret regs x Hs Hs64 Hx. unfold pxF.
  repeat (rewrite wbytes_outside; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]).
  reflexivity.
Qed.

Theorem pixDestroy_null_W : forall C A m md regs (s pp : Z) (sb : option (word * Z)) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pp -> slotok C A s pp sb -> (pp mod 8 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' ->
     (forall x : word, (u x < s - 32 \/ s <= u x)%Z -> m' x = m x) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x154fc : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp sb ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 SL ALpp Rpp HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU8] in *.
  pose proof (slot_range C A m md s pp sb CK HW SL ltac:(lia)) as [Ppp Ppp2].
  pose proof (slot_where C A m md s pp sb CK HW SL ltac:(lia)) as SW.
  assert (DJ : (pp + 8 <= s - 32 \/ s <= pp)%Z) by lia.
  destruct (px_null al_rom regs m s pp ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret ALpp
              (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) Rpp DJ H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (pxF m s ret regs) md /\ POSTM C A s m (pxF m s ret regs)) by (unfold pxF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  apply (HK _ r1 HW1); [| exact PM1 | intros x Hx; apply pxF_out; lia].
  apply cs_kept_intro; rewrite ?Q2, ?Q8, ?Q9, ?H2; try reflexivity.
  all: rewrite (AG1 _) by notin_lit; reflexivity.
Qed.

Lemma set_rc_rc : forall v z z', set_rc (set_rc v z) z' = set_rc v z'.
Proof. intros v z z'. destruct v; reflexivity. Qed.
Lemma set_rc_id : forall v, set_rc v (p_rc v) = v.
Proof. intros v. destruct v; reflexivity. Qed.

(* [comment removed for export] *)
Theorem pixDestroy_dec_W : forall C A m md regs (s pp pix : Z) (v : pixv) (sb : option (word * Z)) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pp -> slotok C A s pp sb -> (pp mod 8 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) ->
  PIXat m pix v -> p_rc v = 2%Z -> live A (Z_to_bv 64 pix) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  (forall p k, sb = Some (p, k) -> p <> Z_to_bv 64 pix) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' ->
     PIXat m' pix (set_rc v 1) -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     (forall x : word, (u x < s - 32 \/ s <= u x)%Z -> ~ (pix + 20 <= u x < pix + 24)%Z -> ~ inslot pp x -> m' x = m x) ->
     mem_grows m m' ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x154fc : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp pix v sb ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 SL ALpp Rpp PX RC Lpix L0pix DISJ HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU8] in *.
  pose proof PX as (Hp0 & Hp64 & WF & _).
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lpix ltac:(lia)) as [Gpix TOPpix]. rewrite u_Z2bv in Gpix, TOPpix by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lpix) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  pose proof (slot_range C A m md s pp sb CK HW SL ltac:(lia)) as [Ppp Ppp2].
  pose proof (slot_where C A m md s pp sb CK HW SL ltac:(lia)) as SW.
  assert (DJ : (pp + 8 <= s - 32 \/ s <= pp)%Z) by lia.
  (* [comment removed for export] *)
  assert (DJ2 : (pp + 8 <= pix \/ pix + 64 <= pp)%Z).
  { destruct sb as [[p n]|]; cbn in SL; [| lia].
    destruct SL as (Lp & _ & R1 & R2).
    pose proof (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lp Lpix (DISJ p n eq_refl)) as D.
    pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (Hn0 & _). pose proof (round16_ge n Hn0).
    rewrite u_Z2bv in D by lia. change (round16 64) with 64%Z in D. lia. }
  assert (SOKx : store_ok SEGS m (Z_to_bv 64 pix) 64 = true).
  { rewrite <- pu8_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m pix v x PX ltac:(lia) E). }
  pose proof (slot_sok C A m md s pp sb CK HW SL ltac:(lia)) as SOKp. rewrite pu8_segs in SOKp.
  destruct (px_dec al_rom regs m s pp pix v ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret ALp ltac:(lia) ALpp
              (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) SOKx SOKp Rpp DJ PX RC ltac:(lia) DJ2 H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (HW1 : W C A (pxF m s ret regs) md) by (unfold pxF; pose proof (POSTM_refl C A s m) as PM0; assert (WP : W C A (pxF m s ret regs) md /\ POSTM C A s m (pxF m s ret regs)) by (unfold pxF; wp_win CK); exact (proj1 WP)).
  set (M2 := wbytes (pxF m s ret regs) (Z_to_bv 64 (pix + 20)) (word_to_le_bytes 4 (Z_to_bv 64 1))).
  assert (HW2 : W C A M2 md).
  { subst M2. apply (W_store_blk C A _ md (Z_to_bv 64 pix) _ 64 _ CK HW1 Lpix L0pix); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia]. }
  set (M3 := wbytes M2 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  assert (HW3 : W C A M3 md).
  { subst M3. apply (slot_W C A M2 md s pp sb _ CK HW2 SL ltac:(lia)). rewrite length_N_to_le_bytes. reflexivity. }
  apply (HK M3 r1 HW3).
  - apply cs_kept_intro; rewrite ?Q2, ?Q8, ?Q9, ?H2; try reflexivity. all: rewrite (AG1 _) by notin_lit; reflexivity.
  - subst M3 M2. apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
    rewrite <- (set_rc_rc v 2 1). apply PIX_wr_rc; [|lia].
    rewrite <- RC, set_rc_id. unfold pxF. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX.
  - subst M3. rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia.
  - intros x Hx N1 N2. unfold inslot in N2. subst M3 M2.
    rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
    rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
    apply pxF_out; lia.
  - subst M3 M2. unfold pxF. intros x Hx. repeat apply wbytes_grows. exact Hx.
Qed.
End PixMisc.
End V8LeptPixMisc.
