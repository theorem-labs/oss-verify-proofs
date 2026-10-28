(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptPixHdr O23LeptPixCreate O23LeptCmapValid O23LeptCmap2 O23LeptPixCopyA O23LeptPixCopy O23LeptPixCopyAT O23LeptPixCreateT2 O23LeptRop_iface O23LeptRop O23LeptGrayA O23LeptRop2_iface O23LeptRop2 O23LeptRopClip O23LeptRop2C O23LeptRopUC O23LeptBord_iface O23LeptBordSegs O23LeptBordW O23LeptBordCW O23LeptBordC32 O23LeptPixCreateBig O23LeptPixCopyT O23LeptBordC32B.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptErr V23LeptPixHdr V23LeptPixCreate V23LeptCmapValid V23LeptCmap2 V23LeptPixCopyA V23LeptPixCopy V23LeptPixCopyAT V23LeptPixCreateT2 V23LeptRop_iface V23LeptRop V23LeptGrayA V23LeptRop2_iface V23LeptRop2 V23LeptRop2C V23LeptRopUC V23LeptBord_iface V23LeptBordSegs V23LeptBordW V23LeptBordCW V23LeptBordC32 V23LeptPixCreateBig V23LeptPixCopyT.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL LeptRop2Arith.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require V23LeptPixCopyT.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require LiaFast.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section BordC32B.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Ltac rzs HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].

Theorem pixAddBorder32C_big_W : forall C A m md regs (s pixs w h cm datas : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ABG_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 32 -> getr regs 12 = Z_to_bv 64 0 ->
  PIXat m pixs (hdv w h 1 cm datas) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z -> (20000 < w + 64 \/ 20000 < h + 64)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x70e84 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixs w h cm datas ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 PXs HOK Hw Hh Hbig Lps HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ABG_STACK, O23LeptBase.LSF, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz).
  pose proof PXs as (Hs0 & Hs64' & WFs & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  assert (ALps8 : (pixs mod 8 = 0)%Z) by (pose proof (ai_live_hull A m _ _ _ (w_inv _ _ _ _ HW) Lps) as (_ & X16 & _); rewrite u_Z2bv in X16 by lia; apply mod16_mod8; exact X16).
  destruct (pab_run al_rom regs m pixs 32 0 ltac:(lia) ltac:(lia) H10 H11 H12) as (r0 & RUN0 & P10 & P11 & P12 & P13 & P14 & P15 & AG0).
  rzs HW RUN0. clear RUN0.
  destruct (ab_A al_rom r0 m s pixs 32 32 32 32 0 (hdv w h 1 cm datas) ret ltac:(lia) ltac:(lia) Hs16 ltac:(lia) ALps8 PXs ltac:(lia)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)
              (W_sok_win C A m md (s - 112) 112 CK HW ltac:(lia) ltac:(cbn; lia)) ltac:(csr; reflexivity) ltac:(csr; reflexivity) P10 P11 P12 P13 P14 P15)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & Q18 & Q22 & Q9 & Q19 & Q24 & Q21 & Q23 & AG1).
  cbn [p_w p_h p_d hdv] in RUN1, Q10, Q11, Q12, Q21, Q23.
  rzs HW RUN1. clear RUN1.
  set (M1 := DIMS (FRA m s ret r0) (s - 84) w h 1) in *.
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold DIMS, FRA; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (abfr_init m s ret r0 w h 1 ltac:(lia) ltac:(lia)) as FR1. fold M1 in FR1.
  apply (pixCreate_big_W C A M1 md r1 (s - 112) (w + 32 + 32) (h + 32 + 32) 1 (Z_to_bv 64 0x70f94) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 ltac:(lia) ltac:(lia) ltac:(clear - Hw Hh Hw2 Hh2; nia) DV ltac:(lia)).
  intros m1 r2 HWa CSa PMa Hres0.
  replace (Z_to_bv 64 0x70f94) with (0x70f94 : word) by (apply bv_eq; reflexivity).
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  pose proof (abfr_frm C (s - 112) M1 m1 s ret r0 w h 1 CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FR1) as FR2.
  destruct (ab_F al_rom r2 m1 (W_sev_got C A m1 _ HWa) (W_sev C A m1 _ HWa) Hres0) as (r3 & RUN3 & V1 & V10 & V11 & V12 & AG3).
  rzs HWa RUN3. clear RUN3.
  apply (returnErrorPtr_W C A m1 _ r3 (s - 112) _ _ _ _ (Z_to_bv 64 0x71084) (Z_to_bv 64 0) S CK HWa ltac:(csr; reflexivity)
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) V1 ltac:(red; apply bv_eq; reflexivity)
           V10 V11 V12 str_msg_pixd str_pixAddBorderGeneral).
  intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
  replace (Z_to_bv 64 0x71084) with (0x71084 : word) by (apply bv_eq; reflexivity).
  destruct (ab_F2 al_rom r5 m4 0 A10) as (r6 & RUN6 & X19 & AG6).
  rzs HW4 RUN6. clear RUN6.
  pose proof (abfr_out m1 m4 _ _ s ret r0 w h 1 OUT4 ltac:(lia) ltac:(lia) ltac:(lia) FR2) as (CE4 & _).
  destruct (ab_E al_rom r6 r0 m4 s 0 ret ltac:(lia) ltac:(lia) Hret CE4 ltac:(csr; reflexivity) X19) as (r7 & RUN7 & Z2 & Z1 & Z10 & ZR & AG7).
  rzs HW4 RUN7. clear RUN7.
  apply (HK m4 r7 HW4).
  - apply cs_kept_intro; csr; reflexivity.
  - eapply POSTM_trans; [exact PMa'|]. eapply (POSTM_range C A m1 _ m4); [exact CK | exact HWa | exact OUT4 | lia | lia | lia].
  - exact Z10.
Qed.

(* [comment removed for export] *)
Theorem pixAddBorder32C_any_W : forall C A m md regs (s pixs w h cm datas : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ABG_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 32 -> getr regs 12 = Z_to_bv 64 0 ->
  PIXat m pixs (hdv w h 1 cm datas) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
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
  intros C A m md regs s pixs w h cm datas cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 PXs HOK Hw Hh Lps Lds HCM kR bR Hrm Hrk Hrb HK.
  assert (BIGC : (20000 < w + 64 \/ 20000 < h + 64)%Z \/ (w + 64 <= 20000 /\ h + 64 <= 20000)%Z) by lia.
  destruct BIGC as [BG | [Bw Bh]].
  - apply (pixAddBorder32C_big_W C A m md regs s pixs w h cm datas ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 PXs HOK Hw Hh BG Lps).
    intros m' regs' HW' CS' PM' R10.
    rewrite <- (with_vmmaps_same md).
    apply (HK A m' (m_vmmaps md) regs'); [rewrite with_vmmaps_same; exact HW' | exact CS' | exact PM' | left; split; [exact R10 | intros q; reflexivity] |].
    eapply aroom_mono; [exact Hrm | unfold RK_pixcopy, RK_pix, RK_cmapcopy in *; lia |].
    pose proof (RB_pixT_nonneg (4 * (wpl_of (w + 64) 1 * (h + 64)))). pose proof (RB_cmapT_le cm). lia.
  - apply (pixAddBorder32C_W C A m md regs s pixs w h cm datas cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 PXs HOK Hw Hh
             ltac:(clear - Hw Hh Bw Bh; nia) Lps Lds HCM kR bR Hrm Hrk Hrb HK).
Qed.

End BordC32B.
