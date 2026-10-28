(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptStderr V10LeptBase.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL7a.
Import V10CL7a.V10LeptErr. Import V10CL7a.V10LeptPadBitsW.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL8a.
Import V10CL8a.V10LeptCmap. Import V10CL8a.V10LeptPixHdr.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL9a.
Import V10CL9a.V10LeptPixDestroy. Import V10CL9a.V10LeptCmapDeser.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptPixCreate V10LeptCmapValid.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10Kit.
Import V10Kit.V10MemcpyBase. Import V10Kit.V10Memcpy.
Import V10CL8a.V10LeptDeserA. Import V10CL8a.V10LeptDeserB.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.VL Require LeptDeser.
Import V10Kit.V10Reloc. Import V10Kit.V10RelocCode. Import V10Kit.V10RelocSites. Import V10Kit.V10RelocImg. Import V10Kit.V10RelocVL.
Import V10Kit.V10RelocMusl. Import V10Kit.V10LeptEnv.
Import V10CL7a.V10LeptG.
Import ListNotations.
Open Scope bv_scope.

Section Deser.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V10Pins}.
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
Proof. rl_tail (@LeptDeser.live_apart v10_reloc v10_lept AL CL ASR). Qed.

Lemma zbv_ne : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> a <> b -> Z_to_bv 64 a <> Z_to_bv 64 b.
Proof. rl_tail (@LeptDeser.zbv_ne). Qed.

Theorem pixDeserialize_W : forall C A m md regs (s dp : Z) (pl : list byte) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 256 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x45480 ->
  getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length pl)) ->
  payload C dp pl -> (3 <= Z.of_nat (length pl) < 2 ^ 26)%Z -> (dp mod 4 = 0)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_deser <= kR)%Z -> (RB_deser <= bR)%Z ->
  DK C A m md regs s ret S kR bR ->
  realizes SEGS (mkCfg (mkst regs (0x26944 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s dp pl ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 PLD Hnb Hal4 kR bR Hrm Hrk Hrb HK.
  pose proof (@LeptDeser.pixDeserialize_W fx v10_reloc v10_code v10_sites v10_code_vl v10_sites_vl v10_lept v10_img_vl v10_data v10_img v10_rw v10_pf v10_lenv_vl AL CL ASR PINS (v10_pinsG P16) C A m md regs s dp pl ret S CK HW H2 Hs16 Hlo Hhi H1 Hret) as RLT.
  rl_to_Z_in RLT; bvlit64_to_Z_in RLT; bvlit64_to_Z.
  assert (HDP : payload C dp pl -> (1 <= dp < 2 ^ 64)%Z).
  { intros (_ & _ & Hd1 & Hd2). pose proof (Zle_0_nat (length pl)). lia. }
  apply (RLT H4 H10 H11 (HDP PLD) ltac:(lia) (fun _ => PLD) Hal4 kR bR Hrm Hrk Hrb).
  exact HK.
Qed.

End Deser.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).      (* [comment removed for export] *)
