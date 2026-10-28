(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
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
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require PropExec.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require CatExec.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require CatSim.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require StepTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Hoare.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require ShapeAlg.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require AllocIface.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require PureModel.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require VmLedger.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require StoreOk.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require MemSplit.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require StartupTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require WalkTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require AllocBase.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require AllocSure.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require WalksLib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10LeptStderr.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10LeptBase.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10_code_15040_16000.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptRoom.
Module V10LeptErr.
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
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.WalkTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptStderr.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10_code_15040_16000.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptRoom.
(* [comment removed for export] *)
(* [comment removed for export] *)









Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Err.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V10Pins}.

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
      msteps SEGS (mkst regs (0x1586c : word) m rom)
                  (mkst regs' (0x157d0 : word)
                        (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                                (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 1 = Z_to_bv 64 0x1588c
      /\ getr regs' 10 = Z_to_bv 64 0x115cf /\ getr regs' 11 = Z_to_bv 64 proc /\ getr regs' 12 = Z_to_bv 64 msg
      /\ getr regs' 8 = val
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 12]%list) regs regs'.
  Proof.
    intros regs m s msg proc ret val Hs Hs64 SOK H2 H1 H10 H11 H12.
    eexists. split.
    - zv F_15770 D_15770 (Z_to_bv 64 (s - 16)).                              (* [comment removed for export] *)
      stepST F_15774 D_15774 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).     (* [comment removed for export] *)
      stepST F_15778 D_15778 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).  (* [comment removed for export] *)
      sn F_1577c D_1577c.                                                     (* [comment removed for export] *)
      sn F_15780 D_15780.                                                     (* [comment removed for export] *)
      sn F_15784 D_15784.                                                     (* [comment removed for export] *)
      sn F_15788 D_15788.                                                     (* [comment removed for export] *)
      sn F_1578c D_1578c.                                                     (* [comment removed for export] *)
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
      msteps SEGS (mkst regs (0x1588c : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = getr regs 8 /\ getr regs' 8 = s0v
      /\ regs_agree (fun r => In r [1; 2; 8; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v Hs Hs64 Hret R8 R16 H2.
    eexists. split.
    - sn F_15790 D_15790.                                                     (* [comment removed for export] *)
      stepLD8 F_15794 D_15794 ret.                                            (* [comment removed for export] *)
      stepLD8 F_15798 D_15798 s0v.                                            (* [comment removed for export] *)
      zv F_1579c D_1579c (Z_to_bv 64 s).                                      (* [comment removed for export] *)
      stepret F_157a0 D_157a0 ret ltac:(bveq).                                (* [comment removed for export] *)
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
  realizes SEGS (mkCfg (mkst regs (0x1586c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s msg proc kmsg kproc ret val S CK HW H2 Hu16 Hlo Hhi H1 Hret H10 H11 H12 Smsg Sproc HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof Smsg as (_ & _ & Bm & _). pose proof Sproc as (_ & _ & Bp & _).
  destruct (rep_A al_rom regs m s msg proc ret val ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes m _ _) _ _).
  assert (HW1 : W C A M1 md).
  { subst M1. apply (W_store_win C A); [exact CK | | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
    apply (W_store_win C A); [exact CK | exact HW | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
  apply (lept_stderr2_W C A M1 md r1 (s - 16) proc msg kproc kmsg (Z_to_bv 64 0x1588c) S CK HW1 Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hu16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity)
           Q10 Q11 Q12 Sproc Smsg).
  intros m2 r2 HW2 OUT2 GR2 CS2. unfold LSF in OUT2.
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 16)) by (csr; reflexivity).
  destruct (rep_B al_rom r2 m2 s ret (getr regs 8) ltac:(lia) ltac:(lia) Hret) as (r3 & RUN3 & P2 & P1 & P10 & P8 & AG3).
  { apply (rdn_after M1 m2 (s - 16 - 3376) (s - 16)); [exact OUT2 | lia | cbn; lia | cbn; lia |]. subst M1. rdn_solve. }
  { apply (rdn_after M1 m2 (s - 16 - 3376) (s - 16)); [exact OUT2 | lia | cbn; lia | cbn; lia |]. subst M1. rdn_solve. }
  { exact E2. }
  replace (Z_to_bv 64 0x1588c) with (0x1588c : word) by (apply bv_eq; reflexivity).
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
      msteps SEGS (mkst regs (0x1579c : word) m rom)
                  (mkst regs' (0x157d0 : word)
                        (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                                (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 1 = Z_to_bv 64 0x157bc
      /\ getr regs' 10 = Z_to_bv 64 0x115cf /\ getr regs' 11 = Z_to_bv 64 proc /\ getr regs' 12 = Z_to_bv 64 msg
      /\ getr regs' 8 = val
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 12]%list) regs regs'.
  Proof.
    intros regs m s msg proc ret val Hs Hs64 SOK H2 H1 H10 H11 H12.
    eexists. split.
    - zv F_156a0 D_156a0 (Z_to_bv 64 (s - 16)).                              (* [comment removed for export] *)
      stepST F_156a4 D_156a4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).     (* [comment removed for export] *)
      stepST F_156a8 D_156a8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).  (* [comment removed for export] *)
      sn F_156ac D_156ac.                                                     (* [comment removed for export] *)
      sn F_156b0 D_156b0.                                                     (* [comment removed for export] *)
      sn F_156b4 D_156b4.                                                     (* [comment removed for export] *)
      sn F_156b8 D_156b8.                                                     (* [comment removed for export] *)
      sn F_156bc D_156bc.                                                     (* [comment removed for export] *)
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
      msteps SEGS (mkst regs (0x157bc : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = getr regs 8 /\ getr regs' 8 = s0v
      /\ regs_agree (fun r => In r [1; 2; 8; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v Hs Hs64 Hret R8 R16 H2.
    eexists. split.
    - sn F_156c0 D_156c0.                                                     (* [comment removed for export] *)
      stepLD8 F_156c4 D_156c4 ret.                                            (* [comment removed for export] *)
      stepLD8 F_156c8 D_156c8 s0v.                                            (* [comment removed for export] *)
      zv F_156cc D_156cc (Z_to_bv 64 s).                                      (* [comment removed for export] *)
      stepret F_156d0 D_156d0 ret ltac:(bveq).                                (* [comment removed for export] *)
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
  realizes SEGS (mkCfg (mkst regs (0x1579c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s msg proc kmsg kproc ret val S CK HW H2 Hu16 Hlo Hhi H1 Hret H10 H11 H12 Smsg Sproc HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof Smsg as (_ & _ & Bm & _). pose proof Sproc as (_ & _ & Bp & _).
  destruct (rei_A al_rom regs m s msg proc ret val ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes m _ _) _ _).
  assert (HW1 : W C A M1 md).
  { subst M1. apply (W_store_win C A); [exact CK | | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
    apply (W_store_win C A); [exact CK | exact HW | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
  apply (lept_stderr2_W C A M1 md r1 (s - 16) proc msg kproc kmsg (Z_to_bv 64 0x157bc) S CK HW1 Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hu16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity)
           Q10 Q11 Q12 Sproc Smsg).
  intros m2 r2 HW2 OUT2 GR2 CS2. unfold LSF in OUT2.
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 16)) by (csr; reflexivity).
  destruct (rei_B al_rom r2 m2 s ret (getr regs 8) ltac:(lia) ltac:(lia) Hret) as (r3 & RUN3 & P2 & P1 & P10 & P8 & AG3).
  { apply (rdn_after M1 m2 (s - 16 - 3376) (s - 16)); [exact OUT2 | lia | cbn; lia | cbn; lia |]. subst M1. rdn_solve. }
  { apply (rdn_after M1 m2 (s - 16 - 3376) (s - 16)); [exact OUT2 | lia | cbn; lia | cbn; lia |]. subst M1. rdn_solve. }
  { exact E2. }
  replace (Z_to_bv 64 0x157bc) with (0x157bc : word) by (apply bv_eq; reflexivity).
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
End V10LeptErr.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require Reloc.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.VL Require LeptBase.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10Kit.
Module V10LeptG.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import V10Kit.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptBase.
(* [comment removed for export] *)








Import V10Kit.V10Reloc. Import V10Kit.V10RelocVL.


Lemma v10_LL : LLU16 = @LeptBase.LLG v10_reloc v10_lept.
Proof. reflexivity. Qed.

Definition v10_pinsG {AL : AllocLayout} {CL : CallocLayout} (PP : @V10Pins AL CL) : @LeptBase.PinsG v10_reloc AL CL :=
  @LeptBase.Build_PinsG v10_reloc AL CL (@p16_segs AL CL PP) (@p16_malloc AL CL PP) (@p16_free AL CL PP) (@p16_calloc AL CL PP) (@p16_tp AL CL PP).
End V10LeptG.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require W2Lib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptArith.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10CL3a.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10_code_16000_17000.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10_code_17000_18000.
Module V10LeptPadBitsW.
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
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.WalkTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.W2Lib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptArith.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptStderr.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptBase.
Import V10CL3a.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10_code_15040_16000.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10_code_16000_17000.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10_code_17000_18000.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptRoom.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)









Import V10CL3a.V10PadBits.


Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section PadBitsW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V10Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma pb32_run : forall regs m (s pix : Z) (v : pixv) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> PIXat m pix v -> p_d v = 32%Z -> (4096 <= pix)%Z -> (pix + 64 <= s - 48 \/ s <= pix)%Z ->
    (s mod 16 = 0)%Z -> (pix mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 0 ->
    exists regs' m',
      msteps SEGS (mkst regs (0x17d74 : word) m rom) (mkst regs' ret m' rom)
      /\ (forall x : word, ~ (s - 48 <= u x < s)%Z -> m' x = m x) /\ mem_grows m m'
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]%list) regs regs'.
  Proof.
    intros regs m s pix v ret Hs Hs64 Hret PX Hd Hpix DJ Hs16 ALp SOK H2 H1 H10 H11.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_w _ WF) as Rw. pose proof (wf_h _ WF) as Rh.
    assert (A36 : ((s - 36) mod 4 = 0)%Z) by (replace (s - 36)%Z with (s + (-36))%Z by lia; apply mod16_plus_mod4; [exact Hs16 | reflexivity]).
    assert (A40 : ((s - 40) mod 4 = 0)%Z) by (replace (s - 40)%Z with (s + (-40))%Z by lia; apply mod16_plus_mod4; [exact Hs16 | reflexivity]).
    assert (A44 : ((s - 44) mod 4 = 0)%Z) by (replace (s - 44)%Z with (s + (-44))%Z by lia; apply mod16_plus_mod4; [exact Hs16 | reflexivity]).
    Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM; unorm; rewrite EQ; reflexivity).
    eexists. eexists. split; [|split; [|split]].
    - zv F_17c78 D_17c78 (Z_to_bv 64 (s - 48)).
      stepST F_17c7c D_17c7c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_17c80 D_17c80 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_17c84 D_17c84 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_17c88 D_17c88 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepb_ft F_17c8c D_17c8c ltac:(condZ).
      zv F_17c90 D_17c90 (Z_to_bv 64 0).
      zv F_17c94 D_17c94 (Z_to_bv 64 pix).
      zv F_17c98 D_17c98 (Z_to_bv 64 (s - 36)).
      zv F_17c9c D_17c9c (Z_to_bv 64 (s - 40)).
      zv F_17ca0 D_17ca0 (Z_to_bv 64 (s - 44)).
      sn F_17ca4 D_17ca4.
      (* [comment removed for export] *)
      zand F_1636c D_1636c andi_3 A36.
      stepb_ft F_16370 D_16370 ltac:(condZ). stepb_ft F_16374 D_16374 ltac:(condZ).
      stepST F_16378 D_16378 (Z_to_bv 64 (s - 36)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_1637c D_1637c andi_3 A40.
      stepb_ft F_16380 D_16380 ltac:(condZ). stepb_ft F_16384 D_16384 ltac:(condZ).
      stepST F_16388 D_16388 (Z_to_bv 64 (s - 40)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_1638c D_1638c andi_3 A44.
      stepb_ft F_16390 D_16390 ltac:(condZ). stepb_ft F_16394 D_16394 ltac:(condZ).
      stepST F_16398 D_16398 (Z_to_bv 64 (s - 44)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_1639c D_1639c ltac:(condZ).
      zand F_163a0 D_163a0 andi_7 ALp.
      stepb_ft F_163a4 D_163a4 ltac:(condZ).
      sn F_163a8 D_163a8. stepb_ft F_163ac D_163ac ltac:(pin; vm_compute; reflexivity).
      stepLD F_163b0 D_163b0 (Z_to_le_bytes 4 (p_w v)) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_w SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w v)) by lia.
      stepST F_163b4 D_163b4 (Z_to_bv 64 (s - 36)) (Z_to_bv 64 (p_w v)) ltac:(sok_in SOK).
      stepb_ft F_163b8 D_163b8 ltac:(condZ).
      sn F_163bc D_163bc. stepb_ft F_163c0 D_163c0 ltac:(pin; vm_compute; reflexivity).
      stepLD F_163c4 D_163c4 (Z_to_le_bytes 4 (p_h v)) (Z_to_bv 64 (p_h v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_h SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h v)) by lia.
      stepST F_163c8 D_163c8 (Z_to_bv 64 (s - 40)) (Z_to_bv 64 (p_h v)) ltac:(sok_in SOK).
      stepb_ft F_163cc D_163cc ltac:(condZ).
      sn F_163d0 D_163d0. stepb_ft F_163d4 D_163d4 ltac:(pin; vm_compute; reflexivity).
      stepLD F_163d8 D_163d8 (Z_to_le_bytes 4 (p_d v)) (Z_to_bv 64 (p_d v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_d SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite Hd. change (v_lw (Z_to_bv 64 32)) with (Z_to_bv 64 32).
      stepST F_163dc D_163dc (Z_to_bv 64 (s - 44)) (Z_to_bv 64 32) ltac:(sok_in SOK).
      sn F_163e0 D_163e0.
      stepret F_163e4 D_163e4 (0x17da4 : word) ltac:(bveq).
      stepLD F_17ca8 D_17ca8 (word_to_le_bytes 4 (Z_to_bv 64 32)) (Z_to_bv 64 32)
        ltac:(addr_norm; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 32))); zlen; unorm; lia)
        ltac:(apply bytes_le_to_Z_4; unorm; lia).
      change (v_lw (Z_to_bv 64 32)) with (Z_to_bv 64 32).
      sn F_17cac D_17cac.
      stepb_tk F_17cb0 D_17cb0 ltac:(condZ).
      sn F_17e48 D_17e48.
      stepLD8 F_17e4c D_17e4c ret.
      stepLD8 F_17e50 D_17e50 (getr regs 8).
      stepLD8 F_17e54 D_17e54 (getr regs 9).
      stepLD8 F_17e58 D_17e58 (getr regs 18).
      zv F_17e5c D_17e5c (Z_to_bv 64 s).
      stepret F_17e60 D_17e60 ret ltac:(bveq).
      apply mst_refl.
    - intros x Hx. rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity.
    - repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

Lemma str_pixSetPadBits : str16 0x10d3c 13. Proof. str16_tac. Qed.
Lemma str_msg_24bpp : str16 0x10b50 26. Proof. str16_tac. Qed.

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
      PIXat m' pix v ->
      (forall a : word, ~ (s - (48 + LSF) <= u a < s)%Z -> ~ (p_data v <= u a < p_data v + 4 * (p_wpl v * p_h v))%Z -> m' a = m a) ->
      (getr regs' 10 = Z_to_bv 64 0 \/ getr regs' 10 = Z_to_bv 64 1) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x17d74 : word) m al_rom) md) S.
Proof.
  intros C Ar A m md regs s pix v ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 PX DV Hw Hh Hwpl Lp Ld Ld0 Ld00 NEpd HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rdat.
  pose proof (dval_range _ DV) as Hd32. pose proof (wpl_of_range (p_w v) (p_d v) ltac:(lia) DV) as Hwr. rewrite <- Hwpl in Hwr.
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  pose proof (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp16 & _). rewrite u_Z2bv in ALp16 by lia.
  assert (ALp8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact ALp16 | reflexivity]).
  destruct (Z.eq_dec (p_d v) 32) as [D32|ND32].
  { (* [comment removed for export] *)
    destruct (pb32_run al_rom regs m s pix v ret ltac:(lia) ltac:(lia) Hret PX D32 Gp ltac:(lia) Hs16 ALp8 SOK H2 H1 H10 H11)
      as (r1 & m1 & RUN1 & OUT1 & GR1 & Q2 & Q1 & Q10 & Q8 & Q9 & Q18 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    apply HK.
    - apply (W_local C A m md m1 s CK HW Hhi); [|exact GR1]. intros a NE. left. unfold scratch.
      destruct (Z_lt_ge_dec (u a) (s - 48)); [exfalso; apply NE; apply OUT1; lia|]. destruct (Z_lt_ge_dec (u a) s); [lia|]. exfalso; apply NE; apply OUT1; lia.
    - apply cs_kept_intro; csr; try reflexivity.
    - apply (POSTM_local C Ar A m md m1 s CK HW SUB). intros a NE. left. unfold scratch.
      destruct (Z_lt_ge_dec (u a) (s - 48)); [exfalso; apply NE; apply OUT1; lia|]. destruct (Z_lt_ge_dec (u a) s); [lia|]. exfalso; apply NE; apply OUT1; lia.
    - apply (PIXat_frame m); [exact PX|]. intros x Hx. apply OUT1. lia.
    - intros a Ha Hb. apply OUT1. lia.
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
    assert (PRE : SSP.spec_pre SEGS (SSP.spec_padbits24 0x17d74 (48 + 3376) LU16)
                    [pix; 0; p_w v; p_h v; 24; 0x15798; 0x656e8; cv; 0x34e00; 3]%Z regs m).
    { unfold SSP.spec_padbits24. SSP.spec_unfold.
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ length SSP.ls_handler_cell SSP.ls_devnull SSP.ls_canary_got SSP.ls_canary SSP.ls_img_lo
           SSP.ls_img_hi SSP.ls_sp_lo SSP.ls_sp_hi SSP.ls_frame SSP.ls_sev_got SSP.ls_sev LU16].
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
    pose proof (padbits24_contract LU16 ltac:(unfold padbits24_L_ok; cbn; repeat split; try lia; repeat (first [left; reflexivity | right])) lept_stderr_s1) as CT.
    unfold SSP.sum_contract in CT.
    destruct (CT [pix; 0; p_w v; p_h v; 24; 0x15798; 0x656e8; cv; 0x34e00; 3]%Z regs m al_rom eq_refl PRE) as (outs & R' & M' & _ & RUN & POST).
    unfold SSP.spec_padbits24 in POST. SSP.spec_unfold_in POST. cbn [SSP.ls_frame LU16] in POST.
    destruct POST as (KEPT & A10 & FRMx & GR & _).
    cbn [SSP.su_entry SSP.exit_target SSP.su_exit SSP.spec_padbits24] in RUN. rewrite H1 in RUN. rewrite H2, u_Z2bv in FRMx by lia.
    assert (OUT : forall a : word, ~ (s - 3424 <= u a < s)%Z -> M' a = m a) by (intros a Ha; apply FRMx; split; [lia | exact I]).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | |].
    { lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ => replace pc with (Z_to_bv 64 0x17d74) by (apply bv_eq; reflexivity) end. exact RUN. }
    apply HK.
    - apply (W_local C A m md M' s CK HW Hhi); [|exact GR]. intros a NE. left. unfold scratch.
      destruct (Z_lt_ge_dec (u a) (s - 3424)); [exfalso; apply NE; apply OUT; lia|]. destruct (Z_lt_ge_dec (u a) s); [lia|]. exfalso; apply NE; apply OUT; lia.
    - exact (cs_kept_of_list regs R' KEPT).
    - apply (POSTM_local C Ar A m md M' s CK HW SUB). intros a NE. left. unfold scratch.
      destruct (Z_lt_ge_dec (u a) (s - 3424)); [exfalso; apply NE; apply OUT; lia|]. destruct (Z_lt_ge_dec (u a) s); [lia|]. exfalso; apply NE; apply OUT; lia.
    - apply (PIXat_frame m); [exact PX|]. intros x Hx. apply OUT. lia.
    - intros a Ha Hb. apply OUT. lia.
    - right. exact A10. }
  (* [comment removed for export] *)
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & ALd16 & _). rewrite u_Z2bv in ALd16 by lia.
  assert (ALd4 : is_aligned (p_data v) 4) by (unfold is_aligned; rewrite <- (Z.add_0_r (p_data v)); apply mod16_plus_mod4; [exact ALd16 | reflexivity]).
  destruct (padbits_run m al_rom pix (p_w v) (p_h v) (p_d v) (p_wpl v) (p_data v) s ret (getr regs 8) (getr regs 9) (getr regs 18)
              ltac:(lia) ltac:(lia) ALp8 ltac:(pose proof (wf_w _ WF); lia) ltac:(pose proof (wf_h _ WF); lia) Hw Hh
              ltac:(unfold dval in DV; lia) ltac:(lia) Hs16 Hret
              (PIX_rd_w SEGS _ _ _ PX) (PIX_rd_h SEGS _ _ _ PX) (PIX_rd_d SEGS _ _ _ PX) (PIX_rd_wpl SEGS _ _ _ PX) (PIX_rd_data SEGS _ _ _ PX)
              ltac:(lia) ltac:(lia) ALd4 ltac:(lia) SOKd ltac:(unfold disj_apart; lia) SOK ltac:(unfold disj_apart; lia) ltac:(unfold disj_apart; lia)
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
  - intros a Ha Hb. rewrite OUT1 by lia. apply M2g_outside; lia.
  - left. exact Q10.
Qed.

End PadBitsW.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V10LeptPadBitsW.

Module V10LeptRop_iface.
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
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptArith.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptBase.
(* [comment removed for export] *)







Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition ROPUNI_STACK : Z := 128.   (* [comment removed for export] *)
Definition ROPLOW_STACK : Z := 240.   (* [comment removed for export] *)
Definition ROP_STACK : Z := 480.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition PC_rasteropUniLow : Z := 0x1e724.
Definition PC_rasteropLow : Z := 0x1efe8.
Definition PC_pixRasterop : Z := 0x1e488.

Section RopIface.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V10Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition rop_shape (w h d wpl : Z) : Prop :=
  (d = 1 \/ d = 8)%Z /\ (1 <= w <= 20000)%Z /\ (1 <= h <= 20000)%Z /\ wpl = wpl_of w d /\ (4 * (wpl * h) <= 67108864)%Z.

(* [comment removed for export] *)
Definition rop_rect (w h x y rw rh : Z) : Prop :=
  (0 <= x)%Z /\ (0 <= y)%Z /\ (1 <= rw)%Z /\ (1 <= rh)%Z /\ (x + rw <= w)%Z /\ (y + rh <= h)%Z.

(* [comment removed for export] *)
Definition rasteropUniLow_contract : Prop :=
  forall C Ar A m md regs (s datad dpixw dpixh d dwpl dx dy dw dh op : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ROPUNI_STACK <= s)%Z -> (s + 16 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 dpixw -> getr regs 12 = Z_to_bv 64 dpixh -> getr regs 13 = Z_to_bv 64 d ->
  getr regs 14 = Z_to_bv 64 dwpl -> getr regs 15 = Z_to_bv 64 dx -> getr regs 16 = Z_to_bv 64 dy -> getr regs 17 = Z_to_bv 64 dw ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 op)) ->
  (0 <= datad < 2 ^ 64)%Z ->
  rop_shape dpixw dpixh d dwpl -> rop_rect dpixw dpixh dx dy dw dh -> (op = 0 \/ op = 15)%Z ->
  live A (Z_to_bv 64 datad) = Some (4 * (dwpl * dpixh))%Z -> live Ar (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' ->
      (forall a : word, ~ scratch C s a -> ~ (datad <= bv_unsigned a < datad + 4 * (dwpl * dpixh))%Z -> m' a = m a) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_rasteropUniLow) m al_rom) md) S.

(* [comment removed for export] *)
Definition rasteropLow_contract : Prop :=
  forall C Ar A m md regs (s datad dpixw dpixh d dwpl dx dy dw dh datas spixw spixh swpl sx sy : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ROPLOW_STACK <= s)%Z -> (s + 64 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 dpixw -> getr regs 12 = Z_to_bv 64 dpixh -> getr regs 13 = Z_to_bv 64 d ->
  getr regs 14 = Z_to_bv 64 dwpl -> getr regs 15 = Z_to_bv 64 dx -> getr regs 16 = Z_to_bv 64 dy -> getr regs 17 = Z_to_bv 64 dw ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 12)) ->
  rdn SEGS m (Z_to_bv 64 (s + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas)) ->
  rdn SEGS m (Z_to_bv 64 (s + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixw)) ->
  rdn SEGS m (Z_to_bv 64 (s + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) ->
  rdn SEGS m (Z_to_bv 64 (s + 48)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sx)) ->
  rdn SEGS m (Z_to_bv 64 (s + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sy)) ->
  (0 <= datad < 2 ^ 64)%Z -> (0 <= datas < 2 ^ 64)%Z ->
  rop_shape dpixw dpixh d dwpl -> rop_shape spixw spixh d swpl ->
  rop_rect dpixw dpixh dx dy dw dh -> rop_rect spixw spixh sx sy dw dh ->
  ((dx * d) mod 32 = 0)%Z -> ((sx * d) mod 32 = 0)%Z ->
  live A (Z_to_bv 64 datad) = Some (4 * (dwpl * dpixh))%Z -> live Ar (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  live A (Z_to_bv 64 datas) = Some (4 * (swpl * spixh))%Z -> Z_to_bv 64 datas <> Z_to_bv 64 datad ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' ->
      (forall a : word, ~ scratch C s a -> ~ (datad <= bv_unsigned a < datad + 4 * (dwpl * dpixh))%Z -> m' a = m a) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_rasteropLow) m al_rom) md) S.

(* [comment removed for export] *)
Definition pixRasterop_uni_contract : Prop :=
  forall C Ar A m md regs (s pixd dx dy dw dh op : Z) (v : pixv) (syw : word) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ROP_STACK <= s)%Z -> (s + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 dx -> getr regs 12 = Z_to_bv 64 dy -> getr regs 13 = Z_to_bv 64 dw ->
  getr regs 14 = Z_to_bv 64 dh -> getr regs 15 = Z_to_bv 64 op ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 syw) ->
  PIXat m pixd v -> rop_shape (p_w v) (p_h v) (p_d v) (p_wpl v) -> rop_rect (p_w v) (p_h v) dx dy dw dh -> (op = 0 \/ op = 15)%Z ->
  live A (Z_to_bv 64 pixd) = Some 64%Z -> Z_to_bv 64 pixd <> Z_to_bv 64 (p_data v) ->
  live A (Z_to_bv 64 (p_data v)) = Some (4 * (p_wpl v * p_h v))%Z -> live Ar (Z_to_bv 64 (p_data v)) = None ->
  live (c_A0 C) (Z_to_bv 64 (p_data v)) = None ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' -> PIXat m' pixd v ->
      (forall a : word, ~ scratch C s a -> ~ (p_data v <= bv_unsigned a < p_data v + 4 * (p_wpl v * p_h v))%Z -> m' a = m a) ->
      getr regs' 10 = Z_to_bv 64 0 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixRasterop) m al_rom) md) S.

(* [comment removed for export] *)
Definition pixRasterop_src_contract : Prop :=
  forall C Ar A m md regs (s pixd dx dy dw dh pixs sx sy : Z) (vd vs : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ROP_STACK <= s)%Z -> (s + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 dx -> getr regs 12 = Z_to_bv 64 dy -> getr regs 13 = Z_to_bv 64 dw ->
  getr regs 14 = Z_to_bv 64 dh -> getr regs 15 = Z_to_bv 64 12 -> getr regs 16 = Z_to_bv 64 pixs -> getr regs 17 = Z_to_bv 64 sx ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sy)) ->
  PIXat m pixd vd -> PIXat m pixs vs -> p_d vs = p_d vd ->
  rop_shape (p_w vd) (p_h vd) (p_d vd) (p_wpl vd) -> rop_shape (p_w vs) (p_h vs) (p_d vs) (p_wpl vs) ->
  rop_rect (p_w vd) (p_h vd) dx dy dw dh -> rop_rect (p_w vs) (p_h vs) sx sy dw dh ->
  ((dx * p_d vd) mod 32 = 0)%Z -> ((sx * p_d vd) mod 32 = 0)%Z ->
  live A (Z_to_bv 64 pixd) = Some 64%Z -> live A (Z_to_bv 64 pixs) = Some 64%Z ->
  Z_to_bv 64 pixd <> Z_to_bv 64 (p_data vd) -> Z_to_bv 64 pixs <> Z_to_bv 64 (p_data vd) ->
  live A (Z_to_bv 64 (p_data vd)) = Some (4 * (p_wpl vd * p_h vd))%Z -> live Ar (Z_to_bv 64 (p_data vd)) = None ->
  live (c_A0 C) (Z_to_bv 64 (p_data vd)) = None ->
  live A (Z_to_bv 64 (p_data vs)) = Some (4 * (p_wpl vs * p_h vs))%Z -> Z_to_bv 64 (p_data vs) <> Z_to_bv 64 (p_data vd) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' -> PIXat m' pixd vd -> PIXat m' pixs vs ->
      (forall a : word, ~ scratch C s a -> ~ (p_data vd <= bv_unsigned a < p_data vd + 4 * (p_wpl vd * p_h vd))%Z -> m' a = m a) ->
      getr regs' 10 = Z_to_bv 64 0 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixRasterop) m al_rom) md) S.

End RopIface.
End V10LeptRop_iface.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptRecs.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptSel.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptRoom10.
Module V10LeptSel_iface.
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
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptRecs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptSel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptRoom10.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptBase.
(* [comment removed for export] *)







Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition SELAHM_STACK : Z := 32 + 48 + 48 + 64 + CALLOC_STACK.   (* [comment removed for export] *)
Definition SELADESTROY_STACK : Z := 48 + 48 + ALLOC_STACK.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition PC_selaAddHitMiss : Z := 0x27be8.
Definition PC_selaGetCount : Z := 0x27aa0.
Definition PC_selaGetSel : Z := 0x27aec.
Definition PC_selGetName : Z := 0x27b9c.
Definition PC_selaDestroy : Z := 0x26eac.
Definition PC_strcmp : Z := 0x32838.

Section SelIface.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V10Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition selaAddHitMiss_contract : Prop :=
  forall C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x45480 ->
  getr regs 10 = Z_to_bv 64 0 ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK10_sela <= kR)%Z -> (RB10_sela <= bR)%Z ->
  (forall A' m' vm' regs' (sela arr : Z) (sels : Z -> Z) (vs : Z -> selv),
     W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 sela ->
     sela_hm (alloc_top (c_vm C)) A' m' sela arr sels vs ->
     sela_off A sela arr 10 sels vs -> sela_off (c_A0 C) sela arr 10 sels vs -> sela_only A A' sela arr 10 sels vs ->
     aroom A' vm' (kR - RK10_sela) (bR - RB10_sela) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_selaAddHitMiss) m al_rom) md) S.

(* [comment removed for export] *)
Definition selaDestroy_contract : Prop :=
  forall C A m md regs (s pp sela arr : Z) (sels : Z -> Z) (vs : Z -> selv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELADESTROY_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  (pp mod 8 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x45480 ->
  getr regs 10 = Z_to_bv 64 pp -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 sela) ->
  sela_hm (alloc_top (c_vm C)) A m sela arr sels vs -> sela_off (c_A0 C) sela arr 10 sels vs ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     sela_off A' sela arr 10 sels vs -> sela_only A A' sela arr 10 sels vs ->
     POSTM C A' (pp + 8) m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     (forall a : word, (s <= u a < pp)%Z -> m' a = m a) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_selaDestroy) m al_rom) md) S.

(* [comment removed for export] *)
Definition selaGetCount_run : Prop :=
  forall (rom : word -> option byte) regs m (sela n na arr : Z) (ret : word),
  RECat m sela (sela_flds n na arr) -> (1 <= sela)%Z -> (sela mod 8 = 0)%Z -> (0 <= n < 2 ^ 31)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 sela ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 PC_selaGetCount) m rom) (mkst regs' ret m rom)
    /\ getr regs' 10 = Z_to_bv 64 n
    /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.

Definition selaGetSel_run : Prop :=
  forall (rom : word -> option byte) regs m (sela n na arr i seli : Z) (ret : word),
  RECat m sela (sela_flds n na arr) -> (1 <= sela)%Z -> (sela mod 8 = 0)%Z -> (0 <= i < n)%Z -> (n <= 50)%Z ->
  (1 <= arr)%Z -> (arr + 400 < 2 ^ 64)%Z -> (arr mod 8 = 0)%Z ->
  bytes_at m (arr + 8 * i) (Z_to_le_bytes 8 seli) -> (0 <= seli < 2 ^ 64)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 sela -> getr regs 11 = Z_to_bv 64 i ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 PC_selaGetSel) m rom) (mkst regs' ret m rom)
    /\ getr regs' 10 = Z_to_bv 64 seli
    /\ regs_agree (fun r => In r [10; 11; 12; 13]%list) regs regs'.

Definition selGetName_run : Prop :=
  forall (rom : word -> option byte) regs m (sel sy sx cy cx data name : Z) (ret : word),
  RECat m sel (sel_flds sy sx cy cx data name) -> (1 <= sel)%Z -> (sel mod 8 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 sel ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 PC_selGetName) m rom) (mkst regs' ret m rom)
    /\ getr regs' 10 = Z_to_bv 64 name
    /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.

(* [comment removed for export] *)
Definition strcmp_run : Prop :=
  forall (rom : word -> option byte) regs m (l r : Z) (la lb : list byte) (ret : word),
  rd_str SEGS m l la -> rd_str SEGS m r lb -> cstr la -> cstr lb ->
  (1 <= l)%Z -> (l + Z.of_nat (length la) < 2 ^ 64)%Z -> (1 <= r)%Z -> (r + Z.of_nat (length lb) < 2 ^ 64)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 l -> getr regs 11 = Z_to_bv 64 r ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 PC_strcmp) m rom) (mkst regs' ret m rom)
    /\ getr regs' 10 = Z_to_bv 64 (strcmp_Z la lb)
    /\ regs_agree (fun x => In x [10; 11; 12; 13]%list) regs regs'.

End SelIface.
End V10LeptSel_iface.
