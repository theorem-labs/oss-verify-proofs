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
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require PropExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatSim.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StepTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Hoare.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require ShapeAlg.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require AllocIface.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require PureModel.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require VmLedger.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StoreOk.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require MemSplit.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StartupTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require WalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require AllocBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require AllocSure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require WalksLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require W2Lib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptArith.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptStderr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL7a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL8a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL9a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptPadBitsW.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptPixCreate.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL10a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15Kit.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc Require Reloc.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require RelocLept.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.VL Require LeptDeser.
Module V15LeptDeser.
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
Import OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.WalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptStderr.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
Import V15CL7a.
Import V15CL8a.
Import V15CL9a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPadBitsW.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCreate.
Import V15CL10a.
Import V15Kit.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc.Reloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.RelocLept.
(* [comment removed for export] *)










Import V15CL7a.V15LeptErr.

Import V15CL8a.V15LeptCmap. Import V15CL8a.V15LeptPixHdr.

Import V15CL9a.V15LeptPixDestroy. Import V15CL9a.V15LeptCmapDeser.


Import V15CL10a.V15LeptCmapValid.

Import V15Kit.V15MemcpyBase. Import V15Kit.V15Memcpy.
Import V15CL8a.V15LeptDeserA. Import V15CL8a.V15LeptDeserB.


Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].



Import V15Kit.V15Reloc. Import V15Kit.V15RelocCode. Import V15Kit.V15RelocSites. Import V15Kit.V15RelocImg. Import V15Kit.V15RelocVL.
Import V15Kit.V15RelocMusl. Import V15Kit.V15LeptEnv.
Import V15CL7a.V15LeptG.
Import ListNotations.
Open Scope bv_scope.

Section Deser.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
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
Proof. rl_tail (@LeptDeser.live_apart v15_reloc v15_lept AL CL ASR). Qed.

Lemma zbv_ne : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> a <> b -> Z_to_bv 64 a <> Z_to_bv 64 b.
Proof. rl_tail (@LeptDeser.zbv_ne). Qed.

Theorem pixDeserialize_W : forall C A m md regs (s dp : Z) (pl : list byte) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 256 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x455c0 ->
  getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length pl)) ->
  payload C dp pl -> (3 <= Z.of_nat (length pl) < 2 ^ 26)%Z -> (dp mod 4 = 0)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_deser <= kR)%Z -> (RB_deser <= bR)%Z ->
  DK C A m md regs s ret S kR bR ->
  realizes SEGS (mkCfg (mkst regs (0x27928 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s dp pl ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 PLD Hnb Hal4 kR bR Hrm Hrk Hrb HK.
  pose proof (@LeptDeser.pixDeserialize_W fx v15_reloc v15_code v15_sites v15_code_vl v15_sites_vl v15_lept v15_img_vl v15_data v15_img v15_rw v15_pf v15_lenv_vl AL CL ASR PINS (v15_pinsG P16) C A m md regs s dp pl ret S CK HW H2 Hs16 Hlo Hhi H1 Hret) as RLT.
  rl_to_Z_in RLT; bvlit64_to_Z_in RLT; bvlit64_to_Z.
  assert (HDP : payload C dp pl -> (1 <= dp < 2 ^ 64)%Z).
  { intros (_ & _ & Hd1 & Hd2). pose proof (Zle_0_nat (length pl)). lia. }
  apply (RLT H4 H10 H11 (HDP PLD) ltac:(lia) (fun _ => PLD) Hal4 kR bR Hrm Hrk Hrb).
  exact HK.
Qed.

End Deser.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).      (* [comment removed for export] *)
End V15LeptDeser.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15_code_gqD_sc.
Module V15LeptSetCmapS.
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
Import OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.WalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptStderr.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
Import V15CL7a.
Import V15CL8a.
Import V15CL10a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15_code_gqD_sc.
(* [comment removed for export] *)









Import V15CL7a.V15LeptErr.

Import V15CL8a.V15LeptCmap.

Import V15CL10a.V15LeptCmapValid.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section Segs.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

  (* [comment removed for export] *)
  Lemma sc_A : forall regs m (s pix cm : Z) (v : pixv) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> PIXat m pix v -> p_cmap v = 0%Z -> (1 <= pix)%Z -> (pix + 64 <= s - 48)%Z -> (1 <= cm < 2 ^ 64)%Z -> (pix mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true -> store_ok SEGS m (Z_to_bv 64 pix) 64 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 cm ->
    exists regs',
      msteps SEGS (mkst regs (0x176bc : word) m rom)
                  (mkst regs' (0x18888 : word)
                     (wbytes (wbytes (wbytes (wbytes (wbytes m
                        (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                        (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                        (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
                        (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
                        (Z_to_bv 64 (pix + 48)) (word_to_le_bytes 8 (Z_to_bv 64 cm))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x17714 /\ getr regs' 10 = Z_to_bv 64 cm
      /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (s - 36)
      /\ regs_agree (fun r => In r [1; 2; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s pix cm v ret Hs Hs64 PX Hcm0 Hpix Hpixhi Hcm AL8 SOK SOKx H2 H1 H10 H11.
    pose proof PX as (Hp0 & Hp64 & WF & _).
    eexists. split.
    - zv F_175b8 D_175b8 (Z_to_bv 64 (s - 48)).
      stepST F_175bc D_175bc (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_175c0 D_175c0 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_175c4 D_175c4 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_175c8 D_175c8 ltac:(condZ).
      stepb_ft F_175cc D_175cc ltac:(condZ).
      stepiv F_175d0 D_175d0 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite AL8; reflexivity). stepb_ft F_175d4 D_175d4 ltac:(condZ).
      stepLD F_175d8 D_175d8 (Z_to_le_bytes 8 (p_cmap v)) (Z_to_bv 64 (p_cmap v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_cmap SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      rewrite Hcm0.
      stepST F_175dc D_175dc (Z_to_bv 64 (s - 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_175e0 D_175e0 ltac:(condZ).
      stepST F_175fc D_175fc (Z_to_bv 64 (pix + 48)) (Z_to_bv 64 cm) ltac:(sok_in SOKx).
      zv F_17600 D_17600 (Z_to_bv 64 (s - 36)).
      sn F_17604 D_17604. sn F_17608 D_17608.
      sn F_1760c D_1760c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sc_B : forall regs m (s : Z) (ret s0v s1v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 36)) 4 = Some (Z_to_le_bytes 4 1) ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs',
      msteps SEGS (mkst regs (0x17714 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v Hs Hs64 Hret Rv R1 R2 R3 H2. eexists. split.
    - stepLD F_17610 D_17610 (Z_to_le_bytes 4 1) (Z_to_bv 64 1) ltac:(addr_norm; exact Rv) ltac:(apply lez4; lia).
      stepb_ft F_17614 D_17614 ltac:(condZ).
      sn F_17618 D_17618. sn F_1761c D_1761c.
      stepLD8 F_17690 D_17690 ret. stepLD8 F_17694 D_17694 s0v. stepLD8 F_17698 D_17698 s1v.
      zv F_1769c D_1769c (Z_to_bv 64 s). stepret F_176a0 D_176a0 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

Section SetCmapS.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Theorem pixSetColormap_S_W : forall C Ar A m md regs (s pix cm : Z) (v : pixv) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 cm ->
  PIXat m pix v -> p_cmap v = 0%Z ->
  live A (Z_to_bv 64 pix) = Some 64%Z -> live Ar (Z_to_bv 64 pix) = None -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  CMAPat m cm cv -> cmap_ok cv -> live A (Z_to_bv 64 cm) = Some 24%Z -> Z_to_bv 64 pix <> Z_to_bv 64 cm ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' ->
      PIXat m' pix (set_cmap v cm) -> CMAPat m' cm cv -> getr regs' 10 = Z_to_bv 64 0 ->
      (forall (q : word) k, live A q = Some k -> q <> Z_to_bv 64 pix -> forall i, (0 <= i < k)%Z -> m' (at_ q i) = m (at_ q i)) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x176bc : word) m al_rom) md) S.
Proof.
  intros C Ar A m md regs s pix cm v cv ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 PX Hpc Lp LpR Lp0 CM CMOK Lcm NE HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof CM as (Hc0 & Hc64 & CWF & _).
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gc TOPc]. rewrite u_Z2bv in Gc, TOPc by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  assert (AL8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact ALp | reflexivity]).
  assert (DISJ : (pix + 64 <= cm \/ cm + 24 <= pix)%Z).
  { destruct (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lp Lcm NE) as [X|X]; rewrite !u_Z2bv in X by lia;
      [left; pose proof (round16_ge 64 ltac:(lia)); lia | right; pose proof (round16_ge 24 ltac:(lia)); lia]. }
  pose proof (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  assert (SOKx : store_ok SEGS m (Z_to_bv 64 pix) 64 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m pix _ x PX ltac:(lia) E). }
  destruct (sc_A al_rom regs m s pix cm v ret ltac:(lia) ltac:(lia) PX Hpc ltac:(lia) ltac:(lia) ltac:(lia) AL8 SOK SOKx H2 H1 H10 H11)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M0 := wbytes (wbytes (wbytes (wbytes m _ _) _ _) _ _) (Z_to_bv 64 (s - 32)) _).
  set (M1 := wbytes M0 _ _).
  assert (WP0 : W C A M0 md /\ POSTM C Ar s m M0).
  { subst M0. wp_win CK. }
  destruct (WP_blk C Ar A m M0 md (Z_to_bv 64 pix) (Z_to_bv 64 (pix + 48)) 64 (word_to_le_bytes 8 (Z_to_bv 64 cm)) s CK WP0 Lp LpR Lp0 SUB
              ltac:(rewrite !u_Z2bv by lia; lia) ltac:(rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia)) as [HW1 PM1].
  fold M1 in HW1, PM1. destruct WP0 as [HW0 PM0].
  assert (PX1 : PIXat M1 pix (set_cmap v cm)).
  { subst M1. apply PIX_wr_cmap; [|lia]. subst M0. repeat (apply PIXat_out; [|rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  assert (CM1 : CMAPat M1 cm cv).
  { subst M1 M0. repeat (apply CMAPat_out; [|rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact CM. }
  replace (0x18888 : word) with (0x18888 : word) by reflexivity.
  apply (pixcmapIsValid_null_W C A M1 md r1 (s - 48) cm (s - 36) cv (Z_to_bv 64 0x17714) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(replace (s - 36)%Z with (s + (-36))%Z by lia; apply mod16_plus_mod4; [exact Hs16 | reflexivity]) Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 CM1 CMOK Lcm).
  intros m2 r2 HW2 CS2 PV2 A10.
  pose proof PV2 as [F2 L2].
  assert (Rv : rdn SEGS m2 (Z_to_bv 64 (s - 36)) 4 = Some (Z_to_le_bytes 4 1)).
  { rewrite (FRM_rdn16 C (s - 48) _ m2 (s - 36) 4 CK F2) by (cbn; lia). rewrite <- (w2l_Z4 1) by lia. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  assert (CE : cellsZ m2 [((s - 8)%Z, ret); ((s - 16)%Z, getr regs 8); ((s - 24)%Z, getr regs 9)]).
  { apply (cellsZ_frm C (s - 48) _ m2 _ CK F2 ltac:(lia)); [repeat (apply Forall_cons; [cbn [fst snd]; lia |]); apply Forall_nil|].
    eapply (cellsZ_out M1 _ (s - 36) (s - 32)); [intros x Hx; apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia
      | repeat (apply Forall_cons; [cbn [fst snd]; lia |]); apply Forall_nil |].
    subst M1 M0. cbn [cellsZ]. repeat split; rdn_solve. }
  cbn [cellsZ] in CE. destruct CE as (C1 & C2 & C3 & _).
  replace (Z_to_bv 64 0x17714) with (0x17714 : word) by (apply bv_eq; reflexivity).
  destruct (sc_B al_rom r2 m2 s ret _ _ ltac:(lia) ltac:(lia) Hret Rv C1 C2 C3 ltac:(csr; reflexivity))
    as (r3 & RUN3 & V2 & V1 & V10 & V8 & V9 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  assert (EQb : forall (p n : Z) (x : word), live A (Z_to_bv 64 p) = Some n -> (0 <= p)%Z -> (p + n <= alloc_top (c_vm C))%Z ->
            (p <= u x < p + n)%Z -> m2 x = M1 x).
  { intros p n x L G0 TP Hx. pose proof (L2 (Z_to_bv 64 p) n (u x - p)%Z L ltac:(lia)) as E.
    replace (at_ (Z_to_bv 64 p) (u x - p)) with x in E by (unfold at_; apply bv_eq; rewrite !u_Z2bv; rewrite ?u_Z2bv; pose proof (u64_range x); lia).
    rewrite E. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
  apply (HK m2 r3 HW2).
  - apply cs_kept_intro; csr; reflexivity.
  - eapply POSTM_trans; [exact PM1|].
    unshelve (eapply (POSTM_absorb C Ar A M1 md m2 s (s - 48) _ _ CK HW1 SUB ltac:(lia) _ _ Hhi PV2)); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
  - apply (PIXat_frame M1 m2 pix _ PX1). intros x Hx. exact (EQb pix 64%Z x Lp ltac:(lia) TOPp Hx).
  - apply (CMAPat_frame M1 m2 cm _ CM1). intros x Hx. exact (EQb cm 24%Z x Lcm ltac:(lia) TOPc Hx).
  - exact V10.
  - (* [comment removed for export] *)
    intros q k Lq NEq i Hi.
    destruct (blk_range C A m md q k CK HW Lq ltac:(lia)) as [Gq TOPq].
    assert (Ea : u (at_ q i) = (u q + i)%Z) by (unfold at_; rewrite u_Z2bv by lia; reflexivity).
    pose proof (L2 q k i Lq Hi) as E2. rewrite E2.
    destruct (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lq Lp NEq) as [X|X]; rewrite ?u_Z2bv in X by lia;
      pose proof (round16_ge 64 ltac:(lia)); pose proof (round16_ge k ltac:(lia));
      (rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, ?Ea, ?u_Z2bv by lia; cbn; lia));
      subst M1 M0; repeat (rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, ?Ea, ?u_Z2bv by lia; cbn; lia)); reflexivity.
Qed.
End SetCmapS.
End V15LeptSetCmapS.
