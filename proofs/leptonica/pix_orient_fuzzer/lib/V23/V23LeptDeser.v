(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptErr V23LeptCmap V23LeptCmapDeser V23LeptCmapValid.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptDeser.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica.VL Require LeptDeser.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23Reloc V23RelocCode V23RelocSites V23RelocImg V23RelocVL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23RelocMusl V23LeptEnv V23LeptG.
Import ListNotations.
Open Scope bv_scope.

Section Deser.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Definition DK (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s : Z) (ret : word) (S : TSet) (kR bR : Z) : Prop :=
  forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C (c_A0 C) s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix v cv, getr regs' 10 = Z_to_bv 64 pix /\ O23LeptDeser.pixobj C A A' m' pix v cv /\ O23LeptDeser.pixfacts v cv)) ->
     aroom A' vm' (kR - RK_deser) (bR - RB_deser) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S.
Lemma live_apart : forall C A m md (p q : word) (n k : Z), Cok C -> W C A m md ->
  live A p = Some n -> live A q = Some k -> p <> q -> (0 <= n)%Z -> (0 <= k)%Z ->
  (u p + n <= u q \/ u q + k <= u p)%Z.
Proof. rl_tail (@VL.LeptDeser.live_apart v23_reloc v23_lept AL CL ASR). Qed.

Theorem pixDeserialize_W : forall C A m md regs (s dp : Z) (pl : list byte) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 256 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length pl)) ->
  O23LeptDeser.payload C dp pl -> (3 <= Z.of_nat (length pl) < 2 ^ 26)%Z -> (dp mod 4 = 0)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_deser <= kR)%Z -> (RB_deser <= bR)%Z ->
  DK C A m md regs s ret S kR bR ->
  realizes SEGS (mkCfg (mkst regs (0xa04bc : word) m al_rom) md) S.
Proof.
  intros C A m md regs s dp pl ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 PLD Hnb Hal4 kR bR Hrm Hrk Hrb HK.
  pose proof (@VL.LeptDeser.pixDeserialize_W fx v23_reloc v23_code v23_sites v23_code_vl v23_sites_vl v23_lept v23_img_vl v23_data v23_img v23_rw v23_pf v23_lenv_vl AL CL ASR PINS (v23_pinsG P16) C A m md regs s dp pl ret S CK HW H2 Hs16 Hlo Hhi H1 Hret) as RLT.
  rl_to_Z_in RLT; bvlit64_to_Z_in RLT; bvlit64_to_Z.
  assert (HDP : O23LeptDeser.payload C dp pl -> (1 <= dp < 2 ^ 64)%Z).
  { intros (_ & _ & Hd1 & Hd2). pose proof (Zle_0_nat (length pl)). lia. }
  apply (RLT H4 H10 H11 (HDP PLD) ltac:(lia) (fun _ => PLD) Hal4 kR bR Hrm Hrk Hrb).
  exact HK.
Qed.

End Deser.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).      (* [comment removed for export] *)
