(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/libreac/fuzz_pcap/lib/B/PcapDriver.v (origin/ossv/recipes
   198234fa4d3) for libdiginet/fuzz_transport's ASan+UBSan image, reduced to its G content: the driver obligation
   drv_mainX_stmt (lib/B/YD1q.v, which lib/B/YD1q.v tfib_srealizesX_of_main closes with the start-up part) holds from
   lib/B/YD1p.v tfib_drv_main with the program contract at the harness's globals, LIBX := tfib_lib_contract_x_all
   G_HARNESS_B ... (lib/B/YCfn.v, lib/B/TransportGB.v), as pcap's DRV_MAINX takes its LIBX at G_HARNESS_U. The slot keeps
   the float state, so tfib_drv_main is used at P = (fun fx => fx = YK11.fx0), as lib/B/YD1q.v tfib_srealizesX does.
   The parts stay Section hypotheses, over this core's names; MT, XM_LIB, XN_LIB, RLO and RHI stay abstract (MT_FREE,
   RO_IN), as in lib/B/YD1q.v. pcap's stdio / fopen parts (its sink head, source record, output shape and the
   start-up tables it names) are not ported. YK09, YA0c, YA0e, YA01 and YA02 are Required from lib/Reusable, where the
   run's placement table puts them (SHARED). rule 24: proves no function. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libdiginet.fuzz_transport.images Require Import AsanUbsan.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YG0f YG00 YG01 YG0n YG0d YK04 YA0i YA0n YI16.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK09 YA0c YA0e YA01 YA02.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB12 YB1h YB01 YB1n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YCbq YC5d YCbp.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import TransportShape.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YF0m YCeg YD1v YD1w YD1x YD1i YCfn YD1p YD1q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import TransportGB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance transport_shape.
Section b. Context {rc : YM05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis HB : TransportSyms B.
Hypothesis AMALLOC : amalloc_realizes tfibsegs B.
Hypothesis AFREE : afree_realizes tfibsegs B.
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : aread_check_stmt B.
Variables (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z).
Hypothesis MT_FREE : forall S m, mo_ok MT S m.
Hypothesis RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a.
(* pcap PcapDriver.v:64 LIBX, at this core's program contract with G := G_HARNESS_B. *)
Hypothesis LIBX : tfib_lib_contract_x_all G_HARNESS_B B MT XM_LIB XN_LIB RLO RHI.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis PF1 : printf_first_tfa B xst.
Hypothesis PFN : printf_next_tfa B xst.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis ESTI : est_img_tfa est.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis FWS : fwrite_site_tfa B est.
Hypothesis RFS : refused_site_tfa B est.
Hypothesis FPO : fprintf_s_site_tfa B est 0x1d83f (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est 0x1d854 (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est 0x15860 (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS : exit_site_tfa B est xst.
(* pcap PcapDriver.v:93-97 DRV_MAINX. *)
Lemma DRV_MAINX : drv_mainX_stmt.
Proof.
refine (tfib_drv_main (fun fx : YK11.FPState => fx = YK11.fx0) eq_refl B HB AMALLOC _ AICPY ARDCHK MT XM_LIB XN_LIB RLO RHI
MT_FREE RO_IN _ xst XFR _ _ est ESTI ESTF FWS RFS FPO FPR FPU _);
intros fx Hfx; cbv beta in Hfx; subst fx;
first [exact AFREE | exact PF1 | exact PFN | exact EXS
| exact (tfib_lib_contract_xP_pinned (fx := YK11.fx0) G_HARNESS_B B MT XM_LIB XN_LIB RLO RHI (fun fx : YK11.FPState => fx = YK11.fx0) eq_refl
(LIBX YK11.fx0))].
Qed.
End d.
End b.
