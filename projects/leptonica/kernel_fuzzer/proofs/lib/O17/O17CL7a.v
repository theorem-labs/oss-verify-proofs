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
From OSSVerify.leptonica.kernel_fuzzer.images Require Plain.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require PropExec.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require CatExec.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require CatSim.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require StepTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Hoare.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require AllocIface.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require PureModel.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require VmLedger.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require StoreOk.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require MemSplit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require StartupTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require WalkTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require AllocBase.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require AllocSure.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require AllocCredit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17LeptStderr.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17LeptBase.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17_code_132e8_14000.
Module O17LeptErr.
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
Import OSSVerify.leptonica.kernel_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocCredit.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17LeptStderr.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17LeptBase.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17_code_132e8_14000.
(* [comment removed for export] *)
(* [comment removed for export] *)








Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Err.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit}.
Context {PINS : @LeptPins AL LL17} {P16 : O17Pins}.

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
      msteps SEGS (mkst regs (0x13aa0 : word) m rom)
                  (mkst regs' (0x13a04 : word)
                        (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                                (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 1 = Z_to_bv 64 0x13ac0
      /\ getr regs' 10 = Z_to_bv 64 0x10b2b /\ getr regs' 11 = Z_to_bv 64 proc /\ getr regs' 12 = Z_to_bv 64 msg
      /\ getr regs' 8 = val
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 12]%list) regs regs'.
  Proof.
    intros regs m s msg proc ret val Hs Hs64 SOK H2 H1 H10 H11 H12.
    eexists. split.
    - zv F_139a4 D_139a4 (Z_to_bv 64 (s - 16)).                              (* [comment removed for export] *)
      stepST F_139a8 D_139a8 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).     (* [comment removed for export] *)
      stepST F_139ac D_139ac (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).  (* [comment removed for export] *)
      sn F_139b0 D_139b0.                                                     (* [comment removed for export] *)
      sn F_139b4 D_139b4.                                                     (* [comment removed for export] *)
      sn F_139b8 D_139b8.                                                     (* [comment removed for export] *)
      sn F_139bc D_139bc.                                                     (* [comment removed for export] *)
      sn F_139c0 D_139c0.                                                     (* [comment removed for export] *)
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
      msteps SEGS (mkst regs (0x13ac0 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = getr regs 8 /\ getr regs' 8 = s0v
      /\ regs_agree (fun r => In r [1; 2; 8; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v Hs Hs64 Hret R8 R16 H2.
    eexists. split.
    - sn F_139c4 D_139c4.                                                     (* [comment removed for export] *)
      stepLD8 F_139c8 D_139c8 ret.                                            (* [comment removed for export] *)
      stepLD8 F_139cc D_139cc s0v.                                            (* [comment removed for export] *)
      zv F_139d0 D_139d0 (Z_to_bv 64 s).                                      (* [comment removed for export] *)
      stepret F_139d4 D_139d4 ret ltac:(bveq).                                (* [comment removed for export] *)
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
  realizes SEGS (mkCfg (mkst regs (0x13aa0 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s msg proc kmsg kproc ret val S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 Smsg Sproc HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL17] in *. unfold LSF in *.
  pose proof Smsg as (_ & _ & Bm & _). pose proof Sproc as (_ & _ & Bp & _).
  destruct (rep_A al_rom regs m s msg proc ret val ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes m _ _) _ _).
  assert (HW1 : W C A M1 md).
  { subst M1. apply (W_store_win C A); [exact CK | | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
    apply (W_store_win C A); [exact CK | exact HW | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
  apply (lept_stderr2_W C A M1 md r1 (s - 16) proc msg kproc kmsg (Z_to_bv 64 0x13ac0) S CK HW1 Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity)
           Q10 Q11 Q12 Sproc Smsg).
  intros m2 r2 HW2 OUT2 GR2 CS2. unfold LSF in OUT2.
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 16)) by (csr; reflexivity).
  destruct (rep_B al_rom r2 m2 s ret (getr regs 8) ltac:(lia) ltac:(lia) Hret) as (r3 & RUN3 & P2 & P1 & P10 & P8 & AG3).
  { apply (rdn_after M1 m2 (s - 16 - 3376) (s - 16)); [exact OUT2 | lia | cbn; lia | cbn; lia |]. subst M1. rdn_solve. }
  { apply (rdn_after M1 m2 (s - 16 - 3376) (s - 16)); [exact OUT2 | lia | cbn; lia | cbn; lia |]. subst M1. rdn_solve. }
  { exact E2. }
  replace (Z_to_bv 64 0x13ac0) with (0x13ac0 : word) by (apply bv_eq; reflexivity).
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
      msteps SEGS (mkst regs (0x139d0 : word) m rom)
                  (mkst regs' (0x13a04 : word)
                        (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                                (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 1 = Z_to_bv 64 0x139f0
      /\ getr regs' 10 = Z_to_bv 64 0x10b2b /\ getr regs' 11 = Z_to_bv 64 proc /\ getr regs' 12 = Z_to_bv 64 msg
      /\ getr regs' 8 = val
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 12]%list) regs regs'.
  Proof.
    intros regs m s msg proc ret val Hs Hs64 SOK H2 H1 H10 H11 H12.
    eexists. split.
    - zv F_138d4 D_138d4 (Z_to_bv 64 (s - 16)).                              (* [comment removed for export] *)
      stepST F_138d8 D_138d8 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).     (* [comment removed for export] *)
      stepST F_138dc D_138dc (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).  (* [comment removed for export] *)
      sn F_138e0 D_138e0.                                                     (* [comment removed for export] *)
      sn F_138e4 D_138e4.                                                     (* [comment removed for export] *)
      sn F_138e8 D_138e8.                                                     (* [comment removed for export] *)
      sn F_138ec D_138ec.                                                     (* [comment removed for export] *)
      sn F_138f0 D_138f0.                                                     (* [comment removed for export] *)
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
      msteps SEGS (mkst regs (0x139f0 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = getr regs 8 /\ getr regs' 8 = s0v
      /\ regs_agree (fun r => In r [1; 2; 8; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v Hs Hs64 Hret R8 R16 H2.
    eexists. split.
    - sn F_138f4 D_138f4.                                                     (* [comment removed for export] *)
      stepLD8 F_138f8 D_138f8 ret.                                            (* [comment removed for export] *)
      stepLD8 F_138fc D_138fc s0v.                                            (* [comment removed for export] *)
      zv F_13900 D_13900 (Z_to_bv 64 s).                                      (* [comment removed for export] *)
      stepret F_13904 D_13904 ret ltac:(bveq).                                (* [comment removed for export] *)
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
  realizes SEGS (mkCfg (mkst regs (0x139d0 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s msg proc kmsg kproc ret val S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 Smsg Sproc HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL17] in *. unfold LSF in *.
  pose proof Smsg as (_ & _ & Bm & _). pose proof Sproc as (_ & _ & Bp & _).
  destruct (rei_A al_rom regs m s msg proc ret val ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes m _ _) _ _).
  assert (HW1 : W C A M1 md).
  { subst M1. apply (W_store_win C A); [exact CK | | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
    apply (W_store_win C A); [exact CK | exact HW | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
  apply (lept_stderr2_W C A M1 md r1 (s - 16) proc msg kproc kmsg (Z_to_bv 64 0x139f0) S CK HW1 Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity)
           Q10 Q11 Q12 Sproc Smsg).
  intros m2 r2 HW2 OUT2 GR2 CS2. unfold LSF in OUT2.
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 16)) by (csr; reflexivity).
  destruct (rei_B al_rom r2 m2 s ret (getr regs 8) ltac:(lia) ltac:(lia) Hret) as (r3 & RUN3 & P2 & P1 & P10 & P8 & AG3).
  { apply (rdn_after M1 m2 (s - 16 - 3376) (s - 16)); [exact OUT2 | lia | cbn; lia | cbn; lia |]. subst M1. rdn_solve. }
  { apply (rdn_after M1 m2 (s - 16 - 3376) (s - 16)); [exact OUT2 | lia | cbn; lia | cbn; lia |]. subst M1. rdn_solve. }
  { exact E2. }
  replace (Z_to_bv 64 0x139f0) with (0x139f0 : word) by (apply bv_eq; reflexivity).
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
End O17LeptErr.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require W2Lib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require LeptArith.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require LeptArith2.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17_code_15000_16000.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17_code_16000_17000.
Module O17LeptKernSegs2.
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
Import OSSVerify.leptonica.kernel_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocCredit.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptArith2.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17LeptStderr.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17LeptBase.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17_code_132e8_14000.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17_code_15000_16000.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17_code_16000_17000.
(* [comment removed for export] *)








Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Lemma lui_m100001 : v_addiw (Z_to_bv 64 4294868992) (-1697) = Z_to_bv 64 (2 ^ 64 - 100001).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma addw_m100001 : forall n, (1 <= n <= 100000)%Z ->
  v_addw (Z_to_bv 64 n) (Z_to_bv 64 (2 ^ 64 - 100001)) = Z_to_bv 64 (2 ^ 64 + (n - 100001)).
Proof.
  intros n Hn. rewrite v_addw_Z. apply bv_eq. rewrite !u_Z2bv_mod. unfold sw32.
  replace ((n + (2 ^ 64 - 100001) + 2 ^ 31) mod 2 ^ 32)%Z with (n - 100001 + 2 ^ 31)%Z.
  2:{ replace (n + (2 ^ 64 - 100001) + 2 ^ 31)%Z with ((n - 100001 + 2 ^ 31) + 2 ^ 32 * 2 ^ 32)%Z by lia.
      rewrite Z_mod_plus_full. rewrite Z.mod_small; lia. }
  replace (n - 100001 + 2 ^ 31 - 2 ^ 31)%Z with ((2 ^ 64 + (n - 100001)) + (-1) * 2 ^ 64)%Z by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma srli29_small : forall z, (0 <= z < 2 ^ 29)%Z -> v_srli (Z_to_bv 64 z) 29 = Z_to_bv 64 0.
Proof. intros z Hz. rewrite zbv_srli by lia. f_equal. apply Z.div_small. lia. Qed.

Section KernSegs2.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit}.
Context {PINS : @LeptPins AL LL17} {P16 : O17Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition C2F (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)).

  Definition c2cells (M : word -> option byte) (s : Z) (ret s0v s1v s2v s3v s4v : word) : Prop :=
    rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
    rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
    rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
    rdn SEGS M (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) /\
    rdn SEGS M (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) /\
    rdn SEGS M (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 s4v).

  Lemma c2cells_C2F : forall m s ret regs, (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
    c2cells (C2F m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20).
  Proof. intros m s ret regs Hs Hs64. unfold c2cells, C2F. repeat split; rdn_chain. Qed.

  Lemma c2cells_frame : forall M M' s ret s0v s1v s2v s3v s4v, (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
    c2cells M s ret s0v s1v s2v s3v s4v -> (forall x : word, (s - 48 <= u x < s)%Z -> M' x = M x) -> c2cells M' s ret s0v s1v s2v s3v s4v.
  Proof.
    intros M M' s ret s0v s1v s2v s3v s4v Hs Hs64 (C1 & C2 & C3 & C4 & C5 & C6) E.
    unfold c2cells. repeat split;
      [rewrite <- C1 | rewrite <- C2 | rewrite <- C3 | rewrite <- C4 | rewrite <- C5 | rewrite <- C6];
      (apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]; intros x Hx; cbn in Hx; apply E; lia).
  Qed.

  (* [comment removed for export] *)
  Local Ltac c2_epi CE :=
    let C1 := fresh in let C2 := fresh in let C3 := fresh in let C4 := fresh in let C5 := fresh in let C6 := fresh in
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6).

  (* [comment removed for export] *)
  Lemma kc_A : forall regs m (s w h : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= w < 2 ^ 31)%Z -> (1 <= h < 2 ^ 31)%Z -> (w * h < 2 ^ 29)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 h -> getr regs 11 = Z_to_bv 64 w ->
    exists regs',
      msteps SEGS (mkst regs (0x15528 : word) m rom) (mkst regs' (0x164cc : word) (C2F m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x15614 /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 24
      /\ getr regs' 8 = Z_to_bv 64 w /\ getr regs' 9 = Z_to_bv 64 (2 ^ 64 - 100001) /\ getr regs' 18 = Z_to_bv 64 h
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18]%list) regs regs'.
  Proof.
    intros regs m s w h ret Hs Hs64 Hw Hh Hwh SOK H2 H1 H10 H11.
    assert (Hwh0 : (0 <= w * h)%Z) by (apply Z.mul_nonneg_nonneg; lia).
    eexists. split.
    - zv F_1542c D_1542c (Z_to_bv 64 (s - 48)).
      stepST F_15430 D_15430 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_15434 D_15434 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_15438 D_15438 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_1543c D_1543c (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_15440 D_15440 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_15444 D_15444 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepb_ft F_15448 D_15448 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_1544c D_1544c ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_15450 D_15450.
      zv F_15454 D_15454 (Z_to_bv 64 (w * h)).
      stepiv F_15458 D_15458 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply srli29_small; lia).
      stepb_tk F_1545c D_1545c ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_15500 D_15500.
      stepiv F_15504 D_15504 (Z_to_bv 64 (2 ^ 64 - 100001)) ltac:(gres; pin; imm_norm; exact lui_m100001).
      sn F_15508 D_15508. sn F_1550c D_1550c. sn F_15510 D_15510. sn F_15514 D_15514.
      unfold C2F. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kc_B : forall regs m (w h kel : Z),
    (1 <= kel)%Z -> (kel + 24 < 2 ^ 64)%Z -> (1 <= w <= 100000)%Z -> (1 <= h <= 100000)%Z -> store_ok SEGS m (Z_to_bv 64 kel) 8 = true ->
    getr regs 10 = Z_to_bv 64 kel -> getr regs 8 = Z_to_bv 64 w -> getr regs 9 = Z_to_bv 64 (2 ^ 64 - 100001) -> getr regs 18 = Z_to_bv 64 h ->
    exists regs',
      msteps SEGS (mkst regs (0x15614 : word) m rom)
                  (mkst regs' (0x164cc : word) (wbytes (wbytes m (Z_to_bv 64 kel) (word_to_le_bytes 4 (Z_to_bv 64 h)))
                                                      (Z_to_bv 64 (kel + 4)) (word_to_le_bytes 4 (Z_to_bv 64 w))) rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x15718 /\ getr regs' 10 = Z_to_bv 64 h /\ getr regs' 11 = Z_to_bv 64 8
      /\ getr regs' 8 = Z_to_bv 64 w /\ getr regs' 18 = Z_to_bv 64 h /\ getr regs' 19 = Z_to_bv 64 kel
      /\ regs_agree (fun r => In r [1; 10; 11; 19]%list) regs regs'.
  Proof.
    intros regs m w h kel Hk Hk64 Hw Hh SOK H10 H8 H9 H18. eexists. split.
    - sn F_15518 D_15518. fixv (Z_to_bv 64 (2 ^ 64 + (w - 100001))) ltac:(rewrite addw_m100001 by lia; reflexivity).
      stepST F_1551c D_1551c (Z_to_bv 64 kel) (Z_to_bv 64 h) ltac:(sok_in SOK).
      stepST F_15520 D_15520 (Z_to_bv 64 (kel + 4)) (Z_to_bv 64 w) ltac:(sok_in SOK).
      stepb_tk F_15524 D_15524 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_1554c D_1554c. fixv (Z_to_bv 64 (2 ^ 64 + (h - 100001))) ltac:(rewrite addw_m100001 by lia; reflexivity).
      stepb_tk F_15550 D_15550 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_1560c D_1560c. sn F_15610 D_15610. sn F_15614 D_15614. sn F_15618 D_15618.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kc_C : forall regs m (h arr : Z),
    (1 <= arr)%Z -> (arr + 8 * h < 2 ^ 64)%Z -> (1 <= h < 2 ^ 31)%Z ->
    getr regs 10 = Z_to_bv 64 arr -> getr regs 18 = Z_to_bv 64 h ->
    exists regs',
      msteps SEGS (mkst regs (0x15718 : word) m rom) (mkst regs' (0x15728 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 9 = Z_to_bv 64 arr /\ getr regs' 18 = Z_to_bv 64 (arr + 8 * h) /\ getr regs' 20 = Z_to_bv 64 arr
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 19 = getr regs 19
      /\ regs_agree (fun r => In r [9; 18; 20]%list) regs regs'.
  Proof.
    intros regs m h arr Ha Ha64 Hh H10 H18. eexists. split.
    - sn F_1561c D_1561c.
      stepiv F_15620 D_15620 (Z_to_bv 64 (8 * h)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; lia).
      zv F_15624 D_15624 (Z_to_bv 64 (arr + 8 * h)).
      sn F_15628 D_15628.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kc_H : forall regs m (w : Z),
    getr regs 8 = Z_to_bv 64 w ->
    exists regs',
      msteps SEGS (mkst regs (0x15728 : word) m rom) (mkst regs' (0x164cc : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x15734 /\ getr regs' 10 = Z_to_bv 64 w /\ getr regs' 11 = Z_to_bv 64 4
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m w H8. eexists. split.
    - sn F_1562c D_1562c. sn F_15630 D_15630. sn F_15634 D_15634. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kc_I1 : forall regs m (arr h i row : Z),
    (1 <= arr)%Z -> (arr + 8 * h < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 < h)%Z -> (h < 2 ^ 31)%Z -> (1 <= row < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (arr + 8 * i)) 8 = true ->
    getr regs 10 = Z_to_bv 64 row -> getr regs 18 = Z_to_bv 64 (arr + 8 * h) -> getr regs 20 = Z_to_bv 64 (arr + 8 * i) ->
    exists regs',
      msteps SEGS (mkst regs (0x15734 : word) m rom)
                  (mkst regs' (0x15728 : word) (wbytes m (Z_to_bv 64 (arr + 8 * i)) (word_to_le_bytes 8 (Z_to_bv 64 row))) rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 20 = Z_to_bv 64 (arr + 8 * (i + 1))
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
      /\ regs_agree (fun r => In r [20]%list) regs regs'.
  Proof.
    intros regs m arr h i row Ha Ha64 Hi Hi1 Hh Hrow SOK H10 H18 H20. eexists. split.
    - stepST F_15638 D_15638 (Z_to_bv 64 (arr + 8 * i)) (Z_to_bv 64 row) ltac:(store_ok_peel; exact SOK).
      zv F_1563c D_1563c (Z_to_bv 64 (arr + 8 * (i + 1))).
      stepb_tk F_15640 D_15640 ltac:(condZ).                                          (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kc_I2 : forall regs m (s arr h i row kel : Z) (ret s0v s1v s2v s3v s4v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= arr)%Z -> (arr + 8 * h < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 = h)%Z -> (h < 2 ^ 31)%Z -> (1 <= row < 2 ^ 64)%Z ->
    (1 <= kel)%Z -> (kel + 24 < 2 ^ 64)%Z ->
    ret_ok ret -> store_ok SEGS m (Z_to_bv 64 (arr + 8 * i)) 8 = true -> store_ok SEGS m (Z_to_bv 64 (kel + 16)) 8 = true ->
    (arr + 8 * h <= s - 48 \/ s <= arr)%Z -> (kel + 24 <= s - 48 \/ s <= kel)%Z ->
    c2cells m s ret s0v s1v s2v s3v s4v ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 row -> getr regs 9 = Z_to_bv 64 arr -> getr regs 18 = Z_to_bv 64 (arr + 8 * h) ->
    getr regs 19 = Z_to_bv 64 kel -> getr regs 20 = Z_to_bv 64 (arr + 8 * i) ->
    exists regs',
      msteps SEGS (mkst regs (0x15734 : word) m rom)
                  (mkst regs' ret (wbytes (wbytes m (Z_to_bv 64 (arr + 8 * i)) (word_to_le_bytes 8 (Z_to_bv 64 row)))
                                          (Z_to_bv 64 (kel + 16)) (word_to_le_bytes 8 (Z_to_bv 64 arr))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 kel
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s arr h i row kel ret s0v s1v s2v s3v s4v Hs Hs64 Ha Ha64 Hi Hi1 Hh Hrow Hk Hk64 Hret SOK SOKk DJ DJk CE H2 H10 H9 H18 H19 H20. c2_epi CE.
    eexists. split.
    - stepST F_15638 D_15638 (Z_to_bv 64 (arr + 8 * i)) (Z_to_bv 64 row) ltac:(store_ok_peel; exact SOK).
      zv F_1563c D_1563c (Z_to_bv 64 (arr + 8 * (i + 1))).
      stepb_ft F_15640 D_15640 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_15644 D_15644.
      stepST F_15648 D_15648 (Z_to_bv 64 (kel + 16)) (Z_to_bv 64 arr) ltac:(sok_in SOKk).
      sn F_1564c D_1564c.
      stepLD8 F_155ec D_155ec ret. stepLD8 F_155f0 D_155f0 s0v. stepLD8 F_155f4 D_155f4 s1v.
      stepLD8 F_155f8 D_155f8 s2v. stepLD8 F_155fc D_155fc s3v. stepLD8 F_15600 D_15600 s4v.
      zv F_15604 D_15604 (Z_to_bv 64 s).
      stepret F_15608 D_15608 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition KDF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)).

  Definition kdcells (M : word -> option byte) (s : Z) (ret s0v s1v s2v s3v : word) : Prop :=
    rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
    rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
    rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
    rdn SEGS M (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) /\
    rdn SEGS M (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v).

  Lemma kdcells_KDF : forall m s ret regs, (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
    kdcells (KDF m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19).
  Proof. intros m s ret regs Hs Hs64. unfold kdcells, KDF. repeat split; rdn_chain. Qed.

  Lemma kdcells_frame : forall M M' s ret s0v s1v s2v s3v, (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
    kdcells M s ret s0v s1v s2v s3v -> (forall x : word, (s - 40 <= u x < s)%Z -> M' x = M x) -> kdcells M' s ret s0v s1v s2v s3v.
  Proof.
    intros M M' s ret s0v s1v s2v s3v Hs Hs64 (C1 & C2 & C3 & C4 & C5) E.
    unfold kdcells. repeat split;
      [rewrite <- C1 | rewrite <- C2 | rewrite <- C3 | rewrite <- C4 | rewrite <- C5];
      (apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]; intros x Hx; cbn in Hx; apply E; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma kd_A0 : forall regs m (s pp : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (s <= pp \/ pp + 8 <= s - 48)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x1574c : word) m rom) (mkst regs' ret (KDF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pp ret Hs Hs64 Hpp Hpp8 DJ Hret SOK Rpp H2 H1 H10. eexists. split.
    - zv F_15650 D_15650 (Z_to_bv 64 (s - 48)).
      stepST F_15654 D_15654 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_15658 D_15658 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_1565c D_1565c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_15660 D_15660 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_15664 D_15664 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepb_ft F_15668 D_15668 ltac:(condZ).
      sn F_1566c D_1566c.
      stepLD F_15670 D_15670 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; repeat rdn_peel1; exact Rpp) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_15674 D_15674 ltac:(condZ).
      stepLD8 F_15700 D_15700 ret. stepLD8 F_15704 D_15704 (getr regs 8). stepLD8 F_15708 D_15708 (getr regs 9).
      stepLD8 F_1570c D_1570c (getr regs 18). stepLD8 F_15710 D_15710 (getr regs 19).
      zv F_15714 D_15714 (Z_to_bv 64 s).
      stepret F_15718 D_15718 ret ltac:(bveq).
      unfold KDF. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kd_A1 : forall regs m (s pp kel sy : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (s <= pp \/ pp + 8 <= s - 48)%Z ->
    (1 <= kel)%Z -> (kel + 24 <= s - 48)%Z -> (1 <= sy < 2 ^ 31)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 kel)) ->
    rdn SEGS m (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 sy)) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x1574c : word) m rom) (mkst regs' (0x15784 : word) (KDF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 8 = Z_to_bv 64 pp /\ getr regs' 9 = Z_to_bv 64 kel
      /\ getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [2; 8; 9; 10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pp kel sy ret Hs Hs64 Hpp Hpp8 DJ Hk Hk24 Hsy SOK Rpp Rsy H2 H1 H10. eexists. split.
    - zv F_15650 D_15650 (Z_to_bv 64 (s - 48)).
      stepST F_15654 D_15654 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_15658 D_15658 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_1565c D_1565c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_15660 D_15660 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_15664 D_15664 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepb_ft F_15668 D_15668 ltac:(condZ).
      sn F_1566c D_1566c.
      stepLD F_15670 D_15670 (word_to_le_bytes 8 (Z_to_bv 64 kel)) (Z_to_bv 64 kel) ltac:(addr_norm; repeat rdn_peel1; exact Rpp) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_15674 D_15674 ltac:(condZ).
      stepLD F_15678 D_15678 (word_to_le_bytes 4 (Z_to_bv 64 sy)) (Z_to_bv 64 sy) ltac:(addr_norm; repeat rdn_peel1; exact Rsy) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small sy) by lia.
      stepb_ft F_1567c D_1567c ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_15680 D_15680. sn F_15684 D_15684.
      unfold KDF. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kd_H : forall regs m (kel arr sy i r : Z),
    (1 <= kel)%Z -> (kel + 24 < 2 ^ 64)%Z -> (1 <= arr)%Z -> (arr + 8 * sy < 2 ^ 64)%Z -> (0 <= i < sy)%Z -> (0 <= r < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (kel + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arr)) ->
    rdn SEGS m (Z_to_bv 64 (arr + 8 * i)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 r)) ->
    getr regs 9 = Z_to_bv 64 kel -> getr regs 18 = Z_to_bv 64 (8 * i) -> getr regs 19 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (mkst regs (0x15784 : word) m rom) (mkst regs' (0x16604 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x15794 /\ getr regs' 10 = Z_to_bv 64 r
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m kel arr sy i r Hk Hk64 Ha Ha64 Hi Hr Rarr Rr H9 H18 H19. eexists. split.
    - stepLD F_15688 D_15688 (word_to_le_bytes 8 (Z_to_bv 64 arr)) (Z_to_bv 64 arr) ltac:(addr_norm; exact Rarr) ltac:(apply bytes_le_to_Z_8).
      zv F_1568c D_1568c (Z_to_bv 64 (arr + 8 * i)).
      stepLD F_15690 D_15690 (word_to_le_bytes 8 (Z_to_bv 64 r)) (Z_to_bv 64 r) ltac:(addr_norm; exact Rr) ltac:(apply bytes_le_to_Z_8).
      sn F_15694 D_15694.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kd_Nn : forall regs m (kel sy i : Z),
    (1 <= kel)%Z -> (kel + 24 < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 < sy)%Z -> (sy < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 sy)) ->
    getr regs 9 = Z_to_bv 64 kel -> getr regs 18 = Z_to_bv 64 (8 * i) -> getr regs 19 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (mkst regs (0x15794 : word) m rom) (mkst regs' (0x15784 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 18 = Z_to_bv 64 (8 * (i + 1)) /\ getr regs' 19 = Z_to_bv 64 (i + 1)
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m kel sy i Hk Hk64 Hi Hi1 Hsy Rsy H9 H18 H19. eexists. split.
    - stepLD F_15698 D_15698 (word_to_le_bytes 4 (Z_to_bv 64 sy)) (Z_to_bv 64 sy) ltac:(addr_norm; exact Rsy) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small sy) by lia.
      zv F_1569c D_1569c (Z_to_bv 64 (i + 1)).
      zv F_156a0 D_156a0 (Z_to_bv 64 (8 * (i + 1))).
      stepb_tk F_156a4 D_156a4 ltac:(condZ).                                          (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kd_Nl : forall regs m (kel arr sy i : Z),
    (1 <= kel)%Z -> (kel + 24 < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 = sy)%Z -> (sy < 2 ^ 31)%Z -> (0 <= arr < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 sy)) ->
    rdn SEGS m (Z_to_bv 64 (kel + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arr)) ->
    getr regs 9 = Z_to_bv 64 kel -> getr regs 18 = Z_to_bv 64 (8 * i) -> getr regs 19 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (mkst regs (0x15794 : word) m rom) (mkst regs' (0x16604 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x157ac /\ getr regs' 10 = Z_to_bv 64 arr
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m kel arr sy i Hk Hk64 Hi Hi1 Hsy Ha Rsy Rarr H9 H18 H19. eexists. split.
    - stepLD F_15698 D_15698 (word_to_le_bytes 4 (Z_to_bv 64 sy)) (Z_to_bv 64 sy) ltac:(addr_norm; exact Rsy) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small sy) by lia.
      zv F_1569c D_1569c (Z_to_bv 64 (i + 1)).
      zv F_156a0 D_156a0 (Z_to_bv 64 (8 * (i + 1))).
      stepb_ft F_156a4 D_156a4 ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD F_156a8 D_156a8 (word_to_le_bytes 8 (Z_to_bv 64 arr)) (Z_to_bv 64 arr) ltac:(addr_norm; exact Rarr) ltac:(apply bytes_le_to_Z_8).
      sn F_156ac D_156ac.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kd_P : forall regs m (kel : word),
    getr regs 9 = kel ->
    exists regs',
      msteps SEGS (mkst regs (0x157ac : word) m rom) (mkst regs' (0x16604 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x157b4 /\ getr regs' 10 = kel
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m kel H9. eexists. split.
    - sn F_156b0 D_156b0. sn F_156b4 D_156b4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kd_Q : forall regs m (s pp : Z) (ret s0v s1v s2v s3v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (s <= pp \/ pp + 8 <= s - 48)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 pp) 8 = true -> kdcells m s ret s0v s1v s2v s3v ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x157b4 : word) m rom) (mkst regs' ret (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pp ret s0v s1v s2v s3v Hs Hs64 Hpp Hpp8 DJ Hret SOK (C1 & C2 & C3 & C4 & C5) H2 H8. eexists. split.
    - stepST F_156b8 D_156b8 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOK).
      sn F_156bc D_156bc.
      stepLD8 F_15700 D_15700 ret. stepLD8 F_15704 D_15704 s0v. stepLD8 F_15708 D_15708 s1v.
      stepLD8 F_1570c D_1570c s2v. stepLD8 F_15710 D_15710 s3v.
      zv F_15714 D_15714 (Z_to_bv 64 s).
      stepret F_15718 D_15718 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End Segs.
End KernSegs2.
End O17LeptKernSegs2.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17CL3a.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17_code_14000_15000.
Module O17LeptPadBitsW.
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
Import OSSVerify.leptonica.kernel_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocCredit.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17LeptStderr.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17LeptBase.
Import O17CL3a.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17_code_132e8_14000.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17_code_14000_15000.
(* [comment removed for export] *)
(* [comment removed for export] *)









Import O17CL3a.O17PadBits.

Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section PadBitsW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit}.
Context {PINS : @LeptPins AL LL17} {P16 : O17Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma pb32_run : forall regs m (s pix : Z) (v : pixv) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> PIXat m pix v -> p_d v = 32%Z -> (4096 <= pix)%Z -> (pix + 64 <= s - 48 \/ s <= pix)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 0 ->
    exists regs' m',
      msteps SEGS (mkst regs (0x14550 : word) m rom) (mkst regs' ret m' rom)
      /\ (forall x : word, ~ (s - 48 <= u x < s)%Z -> m' x = m x) /\ mem_grows m m'
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 18]%list) regs regs'.
  Proof.
    intros regs m s pix v ret Hs Hs64 Hret PX Hd Hpix DJ SOK H2 H1 H10 H11.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_w _ WF) as Rw. pose proof (wf_h _ WF) as Rh.
    eexists. eexists. split; [|split; [|split]].
    - zv F_14454 D_14454 (Z_to_bv 64 (s - 48)).
      stepST F_14458 D_14458 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_1445c D_1445c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_14460 D_14460 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_14464 D_14464 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepb_ft F_14468 D_14468 ltac:(condZ).
      zv F_1446c D_1446c (Z_to_bv 64 pix).
      zv F_14470 D_14470 (Z_to_bv 64 0).
      zv F_14474 D_14474 (Z_to_bv 64 (s - 36)).
      zv F_14478 D_14478 (Z_to_bv 64 (s - 40)).
      zv F_1447c D_1447c (Z_to_bv 64 (s - 44)).
      sn F_14480 D_14480.
      stepb_ft F_13fd8 D_13fd8 ltac:(condZ).
      stepST F_13fdc D_13fdc (Z_to_bv 64 (s - 36)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_13fe0 D_13fe0 ltac:(condZ).
      stepST F_13fe4 D_13fe4 (Z_to_bv 64 (s - 40)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_13fe8 D_13fe8 ltac:(condZ).
      stepST F_13fec D_13fec (Z_to_bv 64 (s - 44)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_13ff0 D_13ff0 ltac:(condZ).
      stepb_ft F_13ff4 D_13ff4 ltac:(condZ).
      stepLD F_13ff8 D_13ff8 (Z_to_le_bytes 4 (p_w v)) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_w SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w v)) by lia.
      stepST F_13ffc D_13ffc (Z_to_bv 64 (s - 36)) (Z_to_bv 64 (p_w v)) ltac:(sok_in SOK).
      stepb_ft F_14000 D_14000 ltac:(condZ).
      stepLD F_14004 D_14004 (Z_to_le_bytes 4 (p_h v)) (Z_to_bv 64 (p_h v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_h SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h v)) by lia.
      stepST F_14008 D_14008 (Z_to_bv 64 (s - 40)) (Z_to_bv 64 (p_h v)) ltac:(sok_in SOK).
      sn F_1400c D_1400c.
      stepb_ft F_14010 D_14010 ltac:(condZ).
      stepLD F_14014 D_14014 (Z_to_le_bytes 4 (p_d v)) (Z_to_bv 64 (p_d v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_d SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite Hd. change (v_lw (Z_to_bv 64 32)) with (Z_to_bv 64 32).
      stepST F_14018 D_14018 (Z_to_bv 64 (s - 44)) (Z_to_bv 64 32) ltac:(sok_in SOK).
      sn F_1401c D_1401c.
      stepret F_14020 D_14020 (0x14580 : word) ltac:(bveq).
      stepLD F_14484 D_14484 (word_to_le_bytes 4 (Z_to_bv 64 32)) (Z_to_bv 64 32)
        ltac:(addr_norm; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 32))); zlen; unorm; lia)
        ltac:(apply bytes_le_to_Z_4; unorm; lia).
      change (v_lw (Z_to_bv 64 32)) with (Z_to_bv 64 32).
      sn F_14488 D_14488.
      stepb_tk F_1448c D_1448c ltac:(condZ).
      sn F_145b4 D_145b4.
      stepLD8 F_145b8 D_145b8 ret.
      stepLD8 F_145bc D_145bc (getr regs 8).
      stepLD8 F_145c0 D_145c0 (getr regs 9).
      stepLD8 F_145c4 D_145c4 (getr regs 18).
      zv F_145c8 D_145c8 (Z_to_bv 64 s).
      stepret F_145cc D_145cc ret ltac:(bveq).
      apply mst_refl.
    - intros x Hx. rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity.
    - repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

Lemma str_pixSetPadBits : str16 0x1072b 13. Proof. str16_tac. Qed.
Lemma str_msg_24bpp : str16 0x10636 26. Proof. str16_tac. Qed.

(* [comment removed for export] *)
Theorem padbits_W : forall C Ar A m md regs (s pix : Z) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 0 ->
  PIXat m pix v -> dval (p_d v) -> (1 <= p_w v <= 20000)%Z -> (1 <= p_h v <= 20000)%Z -> p_wpl v = wpl_of (p_w v) (p_d v) ->
  live A (Z_to_bv 64 pix) = Some 64%Z ->
  live A (Z_to_bv 64 (p_data v)) = Some (4 * (p_wpl v * p_h v))%Z -> live Ar (Z_to_bv 64 (p_data v)) = None ->
  live (c_A0 C) (Z_to_bv 64 (p_data v)) = None -> Z_to_bv 64 pix <> Z_to_bv 64 (p_data v) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' ->
      PIXat m' pix v -> (getr regs' 10 = Z_to_bv 64 0 \/ getr regs' 10 = Z_to_bv 64 1) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x14550 : word) m al_rom) md) S.
Proof.
  intros C Ar A m md regs s pix v ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 PX DV Hw Hh Hwpl Lp Ld Ld0 Ld00 NEpd HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL17] in *. unfold LSF in *.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rdat.
  pose proof (dval_range _ DV) as Hd32. pose proof (wpl_of_range (p_w v) (p_d v) ltac:(lia) DV) as Hwr. rewrite <- Hwpl in Hwr.
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  pose proof (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (Z.eq_dec (p_d v) 32) as [D32|ND32].
  { (* [comment removed for export] *)
    destruct (pb32_run al_rom regs m s pix v ret ltac:(lia) ltac:(lia) Hret PX D32 Gp ltac:(lia) SOK H2 H1 H10 H11)
      as (r1 & m1 & RUN1 & OUT1 & GR1 & Q2 & Q1 & Q10 & Q8 & Q9 & Q18 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    apply HK.
    - apply (W_local C A m md m1 s CK HW Hhi); [|exact GR1]. intros a NE. left. unfold scratch.
      destruct (Z_lt_ge_dec (u a) (s - 48)); [exfalso; apply NE; apply OUT1; lia|]. destruct (Z_lt_ge_dec (u a) s); [lia|]. exfalso; apply NE; apply OUT1; lia.
    - apply cs_kept_intro; csr; try reflexivity.
    - apply (POSTM_local C Ar A m md m1 s CK HW SUB). intros a NE. left. unfold scratch.
      destruct (Z_lt_ge_dec (u a) (s - 48)); [exfalso; apply NE; apply OUT1; lia|]. destruct (Z_lt_ge_dec (u a) s); [lia|]. exfalso; apply NE; apply OUT1; lia.
    - apply (PIXat_frame m); [exact PX|]. intros x Hx. apply OUT1. lia.
    - left. exact Q10. }
  destruct (blk_range C A m md (Z_to_bv 64 (p_data v)) _ CK HW Ld ltac:(lia)) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  pose proof (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lp Ld NEpd) as DJpd. rewrite !u_Z2bv in DJpd by lia.
  pose proof (round16_ge (4 * (p_wpl v * p_h v)) ltac:(lia)) as R16d. unfold round16 in DJpd at 1. change ((64 + 15) / 16)%Z with 4%Z in DJpd.
  assert (SOKd : store_ok SEGS m (Z_to_bv 64 (p_data v)) (Z.to_nat (4 * (p_wpl v * p_h v))) = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|]. intros x Hx.
    unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso.
    destruct (blk_byte C A m md (Z_to_bv 64 (p_data v)) _ x CK HW Ld ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact (D E). }
  destruct (Z.eq_dec (p_d v) 24) as [D24|ND24].
  { (* [comment removed for export] *)
    destruct (canary_any m) as (cv & Hcv & Ccan).
    pose proof (W_sev_got C A m md HW) as Rsg. pose proof (W_sev C A m md HW) as Rsv.
    pose proof (W_hdl16 C A m md HW) as Rh. pose proof (W_can_got C A m md HW) as Rcg.
    assert (PRE : SSP.spec_pre SEGS (SSP.spec_padbits24 0x14550 (48 + 3376) L17)
                    [pix; 0; p_w v; p_h v; 24; 0x139cc; 0x50788; cv; 0x201c0; 3]%Z regs m).
    { unfold SSP.spec_padbits24. SSP.spec_unfold.
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ length SSP.ls_handler_cell SSP.ls_devnull SSP.ls_canary_got SSP.ls_canary SSP.ls_img_lo
           SSP.ls_img_hi SSP.ls_sp_lo SSP.ls_sp_hi SSP.ls_frame SSP.ls_sev_got SSP.ls_sev L17].
      rewrite H1, H2, H10, H11. rewrite !u_Z2bv by lia. pose proof (wf_w _ WF). pose proof (wf_h _ WF).
      split; [|split; [|split; [|exact Hret]]].
      - split; [split; [reflexivity | lia]|]. split; [lia|]. split; [split; [lia | ]|].
        { pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALGN & _). rewrite u_Z2bv in ALGN by lia.
          rewrite <- (Z.add_0_r pix). apply mod16_plus_mod8; [exact ALGN | reflexivity]. }
        split; [split; [reflexivity | lia]|]. split; [reflexivity|].
        split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | rewrite Z.add_0_r; exact (PIX_rd_w SEGS _ _ _ PX)]]]|].
        split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | exact (PIX_rd_h SEGS _ _ _ PX)]]]|].
        split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | rewrite <- D24; exact (PIX_rd_d SEGS _ _ _ PX)]]]|].
        split; [reflexivity|].
        split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | exact Rh]]]|]. split; [reflexivity|].
        split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | exact Rcg]]]|]. split; [reflexivity|].
        split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | exact Ccan]]]|].
        split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | exact Rsg]]]|]. split; [reflexivity|].
        split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | exact Rsv]]]|].
        split; [intros i Hi; exact (W_img16 C A m md i HW Hi)|].
        split; [split; [lia | exact Hs16]|]. split; [lia | exact I].
      - split; [lia|]. split; [unfold SSP.flatZ; lia|]. split; [|exact I].
        apply (W_sok_win C A m md); [exact CK | exact HW | lia | cbn; lia].
      - cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. repeat split; try lia. all: exact I. }
    pose proof (padbits24_contract L17 ltac:(unfold padbits24_L_ok; cbn; repeat split; try lia; do 5 right; left; reflexivity) lept_stderr_s1) as CT.
    unfold SSP.sum_contract in CT.
    destruct (CT [pix; 0; p_w v; p_h v; 24; 0x139cc; 0x50788; cv; 0x201c0; 3]%Z regs m al_rom eq_refl PRE) as (outs & R' & M' & _ & RUN & POST).
    unfold SSP.spec_padbits24 in POST. SSP.spec_unfold_in POST. cbn [SSP.ls_frame L17] in POST.
    destruct POST as (KEPT & A10 & FRMx & GR & _).
    cbn [SSP.su_entry SSP.exit_target SSP.su_exit SSP.spec_padbits24] in RUN. rewrite H1 in RUN. rewrite H2, u_Z2bv in FRMx by lia.
    assert (OUT : forall a : word, ~ (s - 3424 <= u a < s)%Z -> M' a = m a) by (intros a Ha; apply FRMx; split; [lia | exact I]).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | |].
    { lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ => replace pc with (Z_to_bv 64 0x14550) by (apply bv_eq; reflexivity) end. exact RUN. }
    apply HK.
    - apply (W_local C A m md M' s CK HW Hhi); [|exact GR]. intros a NE. left. unfold scratch.
      destruct (Z_lt_ge_dec (u a) (s - 3424)); [exfalso; apply NE; apply OUT; lia|]. destruct (Z_lt_ge_dec (u a) s); [lia|]. exfalso; apply NE; apply OUT; lia.
    - exact (cs_kept_of_list regs R' KEPT).
    - apply (POSTM_local C Ar A m md M' s CK HW SUB). intros a NE. left. unfold scratch.
      destruct (Z_lt_ge_dec (u a) (s - 3424)); [exfalso; apply NE; apply OUT; lia|]. destruct (Z_lt_ge_dec (u a) s); [lia|]. exfalso; apply NE; apply OUT; lia.
    - apply (PIXat_frame m); [exact PX|]. intros x Hx. apply OUT. lia.
    - right. exact A10. }
  (* [comment removed for export] *)
  destruct (padbits_run m al_rom pix (p_w v) (p_h v) (p_d v) (p_wpl v) (p_data v) s ret (getr regs 8) (getr regs 9) (getr regs 18)
              ltac:(lia) ltac:(lia) ltac:(pose proof (wf_w _ WF); lia) ltac:(pose proof (wf_h _ WF); lia) Hw Hh
              ltac:(unfold dval in DV; lia) ltac:(lia) Hret
              (PIX_rd_w SEGS _ _ _ PX) (PIX_rd_h SEGS _ _ _ PX) (PIX_rd_d SEGS _ _ _ PX) (PIX_rd_wpl SEGS _ _ _ PX) (PIX_rd_data SEGS _ _ _ PX)
              ltac:(lia) ltac:(lia) ltac:(lia) SOKd ltac:(unfold disj_apart; lia) SOK ltac:(unfold disj_apart; lia) ltac:(unfold disj_apart; lia)
              regs ND24 ltac:(rewrite Hwpl; reflexivity) H1 H2 eq_refl eq_refl eq_refl H10 H11)
    as (r1 & m1 & RUN1 & INV1 & Q10 & Q2 & Q8 & Q9 & Q18 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  destruct INV1 as [OUT1 GR1].
  assert (CH : forall a, m1 a <> m a -> scratch C s a \/ (u a = u a /\ (p_data v <= u a < p_data v + 4 * (p_wpl v * p_h v))%Z)).
  { intros a NE. destruct (Z_lt_ge_dec (u a) (p_data v)) as [B1|B1];
      [| destruct (Z_lt_ge_dec (u a) (p_data v + 4 * (p_wpl v * p_h v))) as [B2|B2]; [right; split; [reflexivity | lia] |]];
      (left; unfold scratch; rewrite OUT1 in NE by lia;
       destruct (Z_lt_ge_dec (u a) (s - 48)); [exfalso; apply NE; apply M2g_outside; lia|];
       destruct (Z_lt_ge_dec (u a) s); [lia|]; exfalso; apply NE; apply M2g_outside; lia). }
  apply HK.
  - apply (W_local C A m md m1 s CK HW Hhi).
    + intros a NE. destruct (CH a NE) as [X|[_ R]]; [left; exact X | right].
      exists (Z_to_bv 64 (p_data v)), (4 * (p_wpl v * p_h v))%Z. rewrite u_Z2bv by lia. split; [exact Ld | split; [exact Ld00 | lia]].
    + eapply mem_grows_trans; [apply M2_grows | exact GR1].
  - apply cs_kept_intro; csr; try reflexivity.
  - apply (POSTM_local C Ar A m md m1 s CK HW SUB). intros a NE. destruct (CH a NE) as [X|[_ R]]; [left; exact X | right].
    exists (Z_to_bv 64 (p_data v)), (4 * (p_wpl v * p_h v))%Z. rewrite u_Z2bv by lia. split; [exact Ld | split; [exact Ld0 | lia]].
  - apply (PIXat_frame m); [exact PX|]. intros x Hx. rewrite OUT1 by lia. apply M2g_outside; lia.
  - left. exact Q10.
Qed.

End PadBitsW.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End O17LeptPadBitsW.
