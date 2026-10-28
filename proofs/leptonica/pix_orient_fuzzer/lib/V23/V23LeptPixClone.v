(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit FPSteps FPStepsV.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptRoom LeptExec LeptExecW LeptExecFP LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptUb V23ExecUb.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptExecT.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Ltac exB_sc_hook ::= v23_sc_hook.

Definition STOPS : list Z := []%Z.
Definition FDEF : list (nat * nat) := [(8%nat, 33%nat)].
Definition PC_pixClone : Z := 453384.

Section Seg.
Variable rom : word -> option byte.

Lemma pc_seg : forall (fx : FPState) regs m (pix : Z) (ret : word),
  (1 <= pix)%Z -> (pix + 64 < 2 ^ 64)%Z -> (pix mod 8 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 (pix + 20)) 4 = Some (Z_to_le_bytes 4 1) ->
  store_ok SEGS m (Z_to_bv 64 (pix + 20)) 4 = true ->
  getr regs 10 = Z_to_bv 64 pix -> getr regs 1 = ret -> ret_ok ret ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x6eb08) m rom)
                (@mkst fx regs' ret (wbytes m (Z_to_bv 64 (pix + 20)) (Z_to_le_bytes 4 2)) rom)
    /\ getr regs' 10 = Z_to_bv 64 pix
    /\ regs_agree (fun r => In r [11; 12]%list) regs regs'.
Proof.
  intros fx regs m pix ret Hp1 Hp64 AL8 RD SOK H10 H1 Hret.
  destruct fx as [fr cs].
  ex_entry regs [pix] HR.
  assert (HK : know_ok SEGS (ex_env regs [pix]) m
                 [KRange (EVar 32) 1 (2 ^ 64 - 65); KAlign (EVar 32) 8; KWr (SA (EVar 32) 20) 4;
                  KWord (SA (EVar 32) 20) 4 (ELit 1)]%Z) by (ex_know regs).
  exb_open HR HK ST.
  exb_adriveS 3%nat 40%nat (@nil Z) (SCR [false] [] []) FDEF HK ST HR.
  exb_ret ST ret H1 Hret R HR' Hlf Hms.
  exists R. split; [| split].
  - ex_mem regs Hms.
  - ex_reg regs HR'.
  - ex_agree HR HR'.
Qed.
End Seg.

Section Chain.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
(* [comment removed for export] *)
#[local] Existing Instance exf_fxd | 100.

Lemma pixClone_W : forall (fx : FPState) C A m md regs (s pix : Z) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (c_top C - LSTK + 16 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pix ->
  PIXat m pix v -> p_rc v = 1%Z -> live A (Z_to_bv 64 pix) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  (forall (m' : word -> option byte) regs', m' = wbytes m (Z_to_bv 64 (pix + 20)) (Z_to_le_bytes 4 2) -> W C A m' md -> cs_kept regs regs' ->
     getr regs' 10 = Z_to_bv 64 pix ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 PC_pixClone) m al_rom) md) S.
Proof.
  intros fx C A m md regs s pix v ret S CK HW H2 Hs1 Hs2 H1 Hret H10 PX RC LA LA0 K.
  pose proof PX as (Hp0 & Hp64 & _).
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW LA ltac:(lia)) as [G TOP]. rewrite u_Z2bv in G, TOP by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) LA) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  assert (SOK : store_ok SEGS m (Z_to_bv 64 (pix + 20)) 4 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]. intros x Hx.
    unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso.
    destruct (blk_byte C A m _ (Z_to_bv 64 pix) _ x CK HW LA ltac:(rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; lia)) as (_ & D & _).
    exact (D E). }
  assert (RD : rdn SEGS m (Z_to_bv 64 (pix + 20)) 4 = Some (Z_to_le_bytes 4 1)).
  { rewrite <- RC. exact (PIX_rd_rc SEGS m pix v PX). }
  destruct (pc_seg al_rom fx regs m pix ret ltac:(lia) Hp64 (al16_mod8 _ ALp) RD SOK H10 H1 Hret) as (regs' & RUN & R10 & AG).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
  assert (LEN : length (Z_to_le_bytes 4 2) = 4%nat) by reflexivity.
  apply (K (wbytes m (Z_to_bv 64 (pix + 20)) (Z_to_le_bytes 4 2)) regs').
  - reflexivity.
  - apply (W_store_blk C A m md (Z_to_bv 64 pix) _ 64 _ CK HW LA LA0);
      rewrite ?LEN, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
  - intros r Hr. apply AG. intro HIn. cbv [In] in HIn.
    destruct (cs_cases r Hr) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      repeat destruct HIn as [HIn|HIn]; try contradiction; apply (f_equal bv_unsigned) in HIn; vm_compute in HIn; discriminate.
  - exact R10.
Qed.
End Chain.
