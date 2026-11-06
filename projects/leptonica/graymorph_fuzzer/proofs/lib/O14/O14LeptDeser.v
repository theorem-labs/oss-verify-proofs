(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14LeptStderr O14LeptBase.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14CL7a.
Import O14CL7a.O14LeptErr. Import O14CL7a.O14LeptPadBitsW.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14CL8a.
Import O14CL8a.O14LeptCmap.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14LeptPixDestroy O14LeptPixHdr O14LeptPixCreate O14LeptCmapDeser O14LeptCmapValid.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14Kit.
Import O14Kit.O14MemcpyBase. Import O14Kit.O14Memcpy.
Import O14CL8a.O14LeptDeserA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.OL Require LeptDeser.
Import O14Kit.O14Reloc. Import O14Kit.O14RelocCode. Import O14Kit.O14RelocSites. Import O14Kit.O14RelocImg. Import O14Kit.O14RelocOL.
Import O14Kit.O14RelocMusl. Import O14Kit.O14LeptEnv.
Import O14CL7a.O14LeptG.
Import ListNotations.
Open Scope bv_scope.

Section Deser.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O14Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Definition payload (C : lctx) (dp : Z) (pl : list byte) : Prop :=
  live (c_A0 C) (Z_to_bv 64 dp) = Some (Z.of_nat (length pl)) /\ bytes_at (c_m0 C) dp pl /\ (1 <= dp)%Z /\ (dp + Z.of_nat (length pl) < 2 ^ 64)%Z.
Definition pixobj (C : lctx) (A A' : AS) (m' : word -> option byte) (pix : Z) (v : pixv) (cv : cmapv) : Prop :=
  PIXat m' pix v /\ p_rc v = 1%Z /\ p_text v = 0%Z /\ (0 < 4 * (p_wpl v * p_h v))%Z /\
  live A' (Z_to_bv 64 pix) = Some 64%Z /\ live A (Z_to_bv 64 pix) = None /\ live (c_A0 C) (Z_to_bv 64 pix) = None /\
  live A' (Z_to_bv 64 (p_data v)) = Some (4 * (p_wpl v * p_h v))%Z /\ live A (Z_to_bv 64 (p_data v)) = None /\
  live (c_A0 C) (Z_to_bv 64 (p_data v)) = None /\ p_data v <> pix /\
  (p_cmap v = 0%Z \/
   ((1 <= p_cmap v)%Z /\ CMAPat m' (p_cmap v) cv /\ live A' (Z_to_bv 64 (p_cmap v)) = Some 24%Z /\ live A' (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z /\
    (0 < 4 * c_nalloc cv)%Z /\ live A (Z_to_bv 64 (p_cmap v)) = None /\ live A (Z_to_bv 64 (c_arr cv)) = None /\
    live (c_A0 C) (Z_to_bv 64 (p_cmap v)) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None /\
    p_cmap v <> c_arr cv /\ p_cmap v <> pix /\ c_arr cv <> pix /\ p_data v <> p_cmap v /\ p_data v <> c_arr cv)) /\
  (forall q, q <> Z_to_bv 64 pix -> q <> Z_to_bv 64 (p_data v) -> (p_cmap v <> 0%Z -> q <> Z_to_bv 64 (p_cmap v) /\ q <> Z_to_bv 64 (c_arr cv)) ->
             live A' q = live A q).
Definition pixfacts (v : pixv) (cv : cmapv) : Prop :=
  v = PIXV (p_w v) (p_h v) (p_d v) (spp_of (p_d v)) (wpl_of (p_w v) (p_d v)) 1%Z 0%Z 0%Z 0%Z 0%Z 0%Z (p_cmap v) (p_data v) /\
  hdr_ok (p_w v) (p_h v) (p_d v) /\ (1 <= p_w v)%Z /\ (1 <= p_h v)%Z /\ (p_cmap v <> 0%Z -> cmap_ok cv).
Definition DK (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s : Z) (ret : word) (S : TSet) (kR bR : Z) : Prop :=
  forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C (c_A0 C) s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix v cv, getr regs' 10 = Z_to_bv 64 pix /\ pixobj C A A' m' pix v cv /\ pixfacts v cv)) ->
     aroom A' vm' (kR - RK_deser) (bR - RB_deser) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S.
Lemma live_apart : forall C A m md (p q : word) (n k : Z), Cok C -> W C A m md ->
  live A p = Some n -> live A q = Some k -> p <> q -> (0 <= n)%Z -> (0 <= k)%Z ->
  (u p + n <= u q \/ u q + k <= u p)%Z.
Proof. rl_tail (@LeptDeser.live_apart o14_reloc o14_lept AL CL ASR). Qed.

Lemma zbv_ne : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> a <> b -> Z_to_bv 64 a <> Z_to_bv 64 b.
Proof. rl_tail (@LeptDeser.zbv_ne). Qed.

Theorem pixDeserialize_W : forall C A m md regs (s dp : Z) (pl : list byte) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 256 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x3be10 ->
  getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length pl)) ->
  payload C dp pl -> (3 <= Z.of_nat (length pl) < 2 ^ 26)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_deser <= kR)%Z -> (RB_deser <= bR)%Z ->
  DK C A m md regs s ret S kR bR ->
  realizes SEGS (mkCfg (mkst regs (0x1f9c4 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s dp pl ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 PLD Hnb kR bR Hrm Hrk Hrb HK.
  pose proof (@LeptDeser.pixDeserialize_W fx o14_reloc o14_code o14_sites o14_code_ol o14_sites_ol o14_lept o14_img_ol o14_data o14_img o14_rw o14_pf o14_lenv_ol AL CL ASR PINS (o14_pinsG P16) C A m md regs s dp pl ret S CK HW H2 Hs16 Hlo Hhi H1 Hret) as RLT.
  rl_to_Z_in RLT; bvlit64_to_Z_in RLT; bvlit64_to_Z.
  assert (HDP : payload C dp pl -> (1 <= dp < 2 ^ 64)%Z).
  { intros (_ & _ & Hd1 & Hd2). pose proof (Zle_0_nat (length pl)). lia. }
  apply (RLT H4 H10 H11 (HDP PLD) ltac:(lia) (fun _ => PLD) kR bR Hrm Hrk Hrb).
  exact HK.
Qed.

End Deser.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).      (* [comment removed for export] *)
