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
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptPixHdr O23LeptCmapValid O23LeptPixCopyTR.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptRotHip_iface V23LeptRot90W V23LeptRot180W.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptRotOrth V23LeptRot180C.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section RotOrthW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.

(* [comment removed for export] *)
Lemma ro_cs : forall regs r1, regs_agree (fun r => In r [10; 11; 12]%list) regs r1 -> cs_kept regs r1.
Proof. intros regs r1 AG. apply cs_kept_intro; csr; reflexivity. Qed.

(* [comment removed for export] *)
Theorem pixRotateOrth_q1_W : forall C A m md regs (s pixs rc w h cm datas : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + R90_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 1 ->
  PIXat m pixs (hdvr rc w h 1 cm datas) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pix + RK_cmapcopy <= kR)%Z ->
  (RB_pixT (4 * (wpl_of h 1 * w)) + RB_cmapcopy <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C A A' m' pixd h w 1 cd data cv) ) ->
     aroom A' vm' (kR - RK_pix - RK_cmapcopy) (bR - RB_pixT (4 * (wpl_of h 1 * w)) - RB_cmapcopy) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x97094 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixs rc w h cm datas cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 PXs HOK Hw Hh Lps Lds HCM kR bR Hrm Hrk Hrb HK.
  pose proof PXs as (Hp0 & Hp64 & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  destruct (ro_q1 al_rom regs m pixs ltac:(lia) H10 H11) as (r1 & RUN1 & Q10 & Q11 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  apply (pixRotate90_W C A m md r1 s pixs rc w h cm datas 1 cv ret S CK HW ltac:(csr; reflexivity) Hs16 Hlo Hhi
           ltac:(csr; reflexivity) Hret ltac:(csr; reflexivity) Q10 Q11 ltac:(lia) PXs HOK Hw Hh Lps Lds HCM kR bR Hrm Hrk Hrb).
  intros A' m' vm' regs' HW' CS' PM' OUT' Hrm'.
  exact (HK A' m' vm' regs' HW' (cs_kept_trans _ _ _ (ro_cs regs r1 AG1) CS') PM' OUT' Hrm').
Qed.

(* [comment removed for export] *)
Theorem pixRotateOrth_q3_W : forall C A m md regs (s pixs rc w h cm datas : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + R90_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 3 ->
  PIXat m pixs (hdvr rc w h 1 cm datas) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pix + RK_cmapcopy <= kR)%Z ->
  (RB_pixT (4 * (wpl_of h 1 * w)) + RB_cmapcopy <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C A A' m' pixd h w 1 cd data cv) ) ->
     aroom A' vm' (kR - RK_pix - RK_cmapcopy) (bR - RB_pixT (4 * (wpl_of h 1 * w)) - RB_cmapcopy) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x97094 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixs rc w h cm datas cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 PXs HOK Hw Hh Lps Lds HCM kR bR Hrm Hrk Hrb HK.
  pose proof PXs as (Hp0 & Hp64 & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  destruct (ro_q3 al_rom regs m pixs ltac:(lia) H10 H11) as (r1 & RUN1 & Q10 & Q11 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  apply (pixRotate90_W C A m md r1 s pixs rc w h cm datas (-1) cv ret S CK HW ltac:(csr; reflexivity) Hs16 Hlo Hhi
           ltac:(csr; reflexivity) Hret ltac:(csr; reflexivity) Q10 Q11 ltac:(lia) PXs HOK Hw Hh Lps Lds HCM kR bR Hrm Hrk Hrb).
  intros A' m' vm' regs' HW' CS' PM' OUT' Hrm'.
  exact (HK A' m' vm' regs' HW' (cs_kept_trans _ _ _ (ro_cs regs r1 AG1) CS') PM' OUT' Hrm').
Qed.

(* [comment removed for export] *)
Theorem pixRotateOrth_q2_W : forall C A m md regs (s pixs rc w h cm datas : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + R180_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 2 ->
  PIXat m pixs (hdvr rc w h 1 cm datas) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy + 3 <= kR)%Z ->
  (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm + alloc_margin 256 + 2 * alloc_margin (4 * wpl_of w 1) <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C A A' m' pixd w h 1 cd data cv) ) ->
     aroom A' vm' (kR - RK_pixcopy - 3) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm) - alloc_margin 256 - 2 * alloc_margin (4 * wpl_of w 1)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x97094 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixs rc w h cm datas cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 PXs HOK Hw Hh Lps Lds HCM kR bR Hrm Hrk Hrb HK.
  pose proof PXs as (Hp0 & Hp64 & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  destruct (ro_q2 al_rom regs m pixs ltac:(lia) H10 H11) as (r1 & RUN1 & Q10 & Q11 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  apply (pixRotate180_Wc C A m md r1 s pixs rc w h cm datas cv ret S CK HW
           ltac:(csr; reflexivity) Hs16 Hlo Hhi ltac:(csr; reflexivity) Hret ltac:(csr; reflexivity) Q10 Q11
           PXs HOK Hw Hh Lps Lds HCM kR bR Hrm Hrk Hrb).
  intros A' m' vm' regs' HW' CS' PM' OUT' Hrm'.
  exact (HK A' m' vm' regs' HW' (cs_kept_trans _ _ _ (ro_cs regs r1 AG1) CS') PM' OUT' Hrm').
Qed.

End RotOrthW.
