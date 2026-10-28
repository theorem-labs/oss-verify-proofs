(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptRop2Arith.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptPixHdr O23LeptCmapValid O23LeptRop_iface O23LeptRop2_iface O23LeptGrayA O23LeptBord_iface O23LeptBordCW O23LeptPixCopyT O23LeptBordC32.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptErr V23LeptPixHdr V23LeptCmapValid V23LeptRop_iface V23LeptRop2_iface V23LeptGrayA V23LeptBord_iface V23LeptBordCW V23LeptPixCopyT V23_code_port_bordc32.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Segs.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
Lemma pab_run : forall regs m (pixs npix val : Z),
  (1 <= pixs < 2 ^ 64)%Z -> (1 <= npix < 2 ^ 31)%Z ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 npix -> getr regs 12 = Z_to_bv 64 val ->
  exists regs',
    msteps SEGS (mkst regs (0x70e84 : word) m rom) (mkst regs' (0x70ed8 : word) m rom)
    /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 npix /\ getr regs' 12 = Z_to_bv 64 npix
    /\ getr regs' 13 = Z_to_bv 64 npix /\ getr regs' 14 = Z_to_bv 64 npix /\ getr regs' 15 = Z_to_bv 64 val
    /\ regs_agree (fun r => In r [12; 13; 14; 15]%list) regs regs'.
Proof.
  intros regs m pixs npix val Hp Hn H10 H11 H12. eexists. split.
  - stepb_ft F_70e84 D_70e84 ltac:(condZ).
    stepb_ft F_70e88 D_70e88 ltac:(condZ).
    sn F_70e8c D_70e8c. sn F_70e90 D_70e90. sn F_70e94 D_70e94. sn F_70e98 D_70e98. sn F_70e9c D_70e9c.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.
End Segs.

Section BordC32.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Ltac rzs HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].

Theorem pixAddBorder32C_W : forall C A m md regs (s pixs w h cm datas : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ABG_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 32 -> getr regs 12 = Z_to_bv 64 0 ->
  PIXat m pixs (hdv w h 1 cm datas) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z -> ((w + 64) * (h + 64) <= 400000000)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z ->
  (RB_pixT (4 * (wpl_of (w + 64) 1 * (h + 64))) + RB_cmapT cm <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ hdr_ok (w + 64) (h + 64) 1 /\
                             pixt_new C A A' m' pixd (w + 64) (h + 64) 1 cd data cv) ) ->
     aroom A' vm' (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of (w + 64) 1 * (h + 64))) + RB_cmapT cm)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x70e84 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixs w h cm datas cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 PXs HOK Hw Hh Hprod Lps Lds HCM kR bR Hrm Hrk Hrb HK.
  pose proof PXs as (Hs0 & Hs64' & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct (pab_run al_rom regs m pixs 32 0 ltac:(lia) ltac:(lia) H10 H11 H12) as (r1 & RUN1 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & AG0).
  rzs HW RUN1. clear RUN1.
  replace (0x70ed8 : word) with (Z_to_bv 64 PC_pixAddBorderGeneral) by (apply bv_eq; reflexivity).
  assert (EW : (w + 64 = w + 32 + 32)%Z) by lia. assert (EH : (h + 64 = h + 32 + 32)%Z) by lia.
  rewrite EW, EH in Hprod, Hrb, HK.
  apply (pixAddBorderGeneralC_W C A m md r1 s pixs w h 1%Z cm datas (spp_of 1) 1%Z 0%Z 0%Z 0%Z 32%Z 32%Z 32%Z 32%Z 0%Z cv ret S CK HW
           ltac:(csr; reflexivity) Hs16 Hlo Hhi ltac:(csr; reflexivity) Hret ltac:(csr; reflexivity)
           Q10 Q11 Q12 Q13 Q14 Q15 PXs HOK Hw Hh ltac:(left; reflexivity) eq_refl eq_refl Lps Lds HCM
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(red; left; split; reflexivity) ltac:(left; reflexivity) Hprod
           kR bR Hrm Hrk Hrb).
  intros A' m' vm' regs' HW' CS' PM' EX' RM'.
  apply (HK A' m' vm' regs' HW'); [| exact PM' | exact EX' | exact RM'].
  apply cs_kept_intro; csr; reflexivity.
Qed.

End BordC32.
