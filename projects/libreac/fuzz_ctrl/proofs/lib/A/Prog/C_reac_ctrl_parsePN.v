(* lib/A/Prog/C_reac_ctrl_parsePN.v -- fuzz_ctrl image A (asan, libreac v1.9.0): the re-based post stretch for the
   cgif-form glue pb_reac_ctrl_parse (lib/A/Prog/C_reac_ctrl_parseP.v), route (C).
   rcpPN_post runs reac_ctrl_parseF_rpost.RPostFOn.post_all_F2 (the return of __asan_stack_malloc_1 at 0x835ec, the
   release store, the post-release stretch, to RPostFOn.QF) at the NORMALIZED return memory mc0 = MemNorm.normalize
   mem2, with the Section base mB = mc0 with flag jj written back to 0.  Every premise of that Section comes from facts
   at the REAL return memory mem2: memory and footprint facts only, no world (AR) fact.  The three callee contracts
   asan_memset_contract_F_on / asan_memcpy_contract_F_on / bcmp_wrap_contract_F_on are premises (a Theorem Labs lane 2026-10-29:
   C_reac_ctrl_parseP.v discharges them); kind_of_link1's is discharged here by kind_of_link1F.kind_of_link1_F_holds.
   Steps: (1) mem2 -> mc0 by MemNorm.mem_rel_normalize / mrd_rel / bytes_at_normalize / mem_inv_normalize,
   MemNormTr.stk_normalize_ro / rw_cells_normalize / ro_addr_above_img / asan_cells_normalize /
   addressable_normalize / asan_tls_cells_normalize, C_reac_ctrl_parsePP.rcpPP_fpx_normalize, and rcpPN_srw_norm (the
   proof of A.ShadowRwOnT.shadow_rw_on_rel, copied: ShadowRwOnT is not built in this workspace);
   (2) mc0 -> mB by C_reac_ctrl_parseVT.rcpVT_base (every Section premise at mB, and munch / wmono / rd_mono mB mc0);
   (3) RPostFOn.post_all_F2 at m := mB, its return memory mc0, the class-1 flag array of fpx mc0 (RcAsanFP.fp_cls).
   Route (C): no ctlrt_of_AR / shadow_rw_of_AR / rt_of_core / RT_used_of_AR / AR_states_* / VIS0 / OWNED_RO.
   Twin rule: every project module is Required without Import and named through a full-path Module alias.
   rule 24: no function proved. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame Cells Step PropExec MState ExecF RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Img0 AsanRT MemNorm MemNormTr ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ImgBounds asan_stack_malloc_c RcAsanFP
  reac_ctrl_parse_c reac_ctrl_parseF bcmp_wrap_c memcmp_c asan_memset_cF_on asan_memcpy_cF_on bcmp_wrap_c_on
  kind_of_link1F reac_ctrl_parseF_rpost C_reac_ctrl_parseVT C_reac_ctrl_parsePP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11.
Import ListNotations.
Local Open Scope Z_scope.

Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LX := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LRB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.RngBytes.
Module AI0 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module MN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.
Module MNT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormTr.
Module SRO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Module IB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c.
Module FP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.RcAsanFP.
Module PC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parse_c.
Module PF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parseF.
Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c.
Module MC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.memcmp_c.
Module MSO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memset_cF_on.
Module MCO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy_cF_on.
Module BWO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c_on.
Module KLF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.kind_of_link1F.
Module RP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parseF_rpost.
Module VT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_parseVT.
Module PP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_parsePP.
Module RcP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.
Module RK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Local Notation rsegs := AI0.rsegs (only parsing).

(* shadow_rw_on across normalize: the proof of A.ShadowRwOnT.shadow_rw_on_rel / shadow_rw_on_normalize, copied (a
   shadow byte is above the image, so normalize keeps it). *)
Lemma rcpPN_srw_norm : forall (P : Z -> Prop) (m : word -> option byte), MN.ro_agree rsegs m ->
  SRO.shadow_rw_on P m -> SRO.shadow_rw_on P (MN.normalize rsegs m).
Proof.
  intros P m RO H a Hp Ha. pose proof (MN.mem_rel_normalize rsegs m RO) as REL.
  destruct (H a Hp Ha) as [Hv [b Hb]].
  assert (E : LM.ro_addr rsegs (LM.wa a) = false).
  { apply MNT.ro_addr_above_img.
    unfold ART.in_shadow, ART.LOWMEM_END, ART.LOWSHADOW_END, ART.HIGHSHADOW_BEG, ART.HIGHMEM_BEG in Ha.
    unfold IB.IMG_HI. lia. }
  split; [rewrite (MN.wview_rel_rw rsegs m _ _ REL E); exact Hv|].
  exists b. rewrite <- (MN.mrd_rel rsegs m _ _ REL). exact Hb.
Qed.

Section PN.
Context {fx : RK11.FPState}.

Lemma rcpPN_post : MSO.asan_memset_contract_F_on -> MCO.asan_memcpy_contract_F_on -> BWO.bcmp_wrap_contract_F_on ->
  forall (mem2 : word -> option byte) (RNG : LX.footprint)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (f n o S FS jj : Z) (fr junk : list byte) (X : list (nat * Z))
    (xra u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 : word),
  let fl := SMC.fs_flag FS 1 jj in
  let mB := write_to_mem (MN.normalize rsegs mem2) (LM.wa fl) [Z_to_bv 8 0] in
  0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= o < 2^64 -> 8800 <= S < 2^64 -> S mod 16 = 0 -> length fr = 50%nat ->
  (50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ (f + 50 <= S - 8800 \/ S <= f)) ->
  ART.HIGHMEM_BEG <= S - 8800 -> S <= ART.APPMEM_END ->
  0 <= jj < SMC.fs_M 1 -> SMC.ASAN_GT <= FS -> FS + SMC.FS_SIZE <= S - 8800 ->
  (forall a, FS <= a < FS + SMC.FS_SIZE -> ART.app_mem a) ->
  (50 <= n -> f + 50 <= FS \/ FS + SMC.FS_SIZE <= f) ->
  (o <> 0 -> o mod 4 = 0 /\ o + 36 <= 2^64 /\ (o + 36 <= S - 8800 \/ S <= o) /\
     (50 <= n -> o + 36 <= f \/ f + 50 <= o) /\ ART.app_mem (o + 36) /\ (o + 36 <= BW.GOT_CF \/ BW.CF + 256 <= o) /\
     SMC.fs_frame FS 0 0 <= o) ->
  MN.ro_agree rsegs mem2 ->
  LM.bytes_at rsegs mem2 fl [Z_to_bv 8 1] ->
  LF.stk rsegs mem2 (S - 8800) S ->
  (forall i, In i (RcP.cp_rd n fr) -> LM.mrd rsegs mem2 (LM.wa (f + Z.of_nat i)) = nth_error fr i) ->
  (o <> 0 -> LS.rw_cells rsegs mem2 o [LC.CB 36 junk]) ->
  ART.asan_cells mem2 -> SRO.shadow_rw_on (PC.reac_ctrl_parse_shadow_R f n o S FS) mem2 ->
  ART.addressable mem2 (S - 8800) 8800 -> (50 <= n -> ART.addressable mem2 f 50) ->
  (o <> 0 -> ART.addressable mem2 o 36) -> ART.addressable mem2 PC.REAC_CTRL_PARSE_BC 6 ->
  LM.bytes_at rsegs mem2 BW.REAL_BCMP (LM.le8 (LM.wa BW.BCMP)) ->
  LM.bytes_at rsegs mem2 BW.REAL_MEMCMP (LM.le8 (LM.wa MC.MEMCMP)) ->
  LM.bytes_at rsegs mem2 BW.GOT_CF (LM.le8 (LM.wa BW.CF)) -> LM.bytes_at rsegs mem2 (BW.CF + 254) [Z_to_bv 8 1] ->
  LM.bytes_at rsegs mem2 (BW.CF + 255) [Z_to_bv 8 1] ->
  Forall (fun ci => fst ci = 1%nat /\ LM.bytes_at rsegs mem2 (SMC.fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) X ->
  Forall (fun ci => 0 <= snd ci < SMC.fs_M 1 /\ snd ci <> jj) X ->
  FP.fpx [1%nat] mem2 (bv_unsigned tp) FS (S - 8800) S (PC.reac_ctrl_parse_W o S) (PC.reac_ctrl_parse_D f n o) X ->
  PC.reac_ctrl_parse_tls mem2 (bv_unsigned tp) FS (S - 8800) S ->
  LS.rw_cells rsegs mem2 (S - 96) (PF.ParseFOn.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) ->
  LM.bytes_at rsegs mem2 (SMC.fs_frame FS 1 jj + 120) (LM.le8 (Z_to_bv 64 fl)) ->
  LRB.rng_bytes RNG -> LX.rng RNG 0x10000 0x5ee000 -> LX.rng RNG (S - 8800) 8800 -> PF.shcov RNG (S - 8800) 8800 ->
  PF.shkov RNG (S - 288) 160 ->
  (50 <= n -> LX.rng RNG f 50) -> (50 <= n -> PF.shcov RNG f 50) -> (50 <= n -> PF.shkov RNG f 50) ->
  (o <> 0 -> LX.rng RNG o 36) -> (o <> 0 -> PF.shcov RNG o 36) -> (o <> 0 -> PF.shkov RNG o 36) ->
  LX.rng RNG PC.REAC_CTRL_PARSE_BC 6 -> PF.shkov RNG PC.REAC_CTRL_PARSE_BC 6 ->
  LX.rng RNG FS (SMC.fs_frame FS 0 0 - FS) -> LX.rng RNG (SMC.fs_flag FS 1 0) (SMC.fs_M 1) ->
  LX.rng RNG (SMC.fs_frame FS 1 0) (SMC.fs_frame FS 1 (SMC.fs_M 1) - SMC.fs_frame FS 1 0) ->
  PF.shcov RNG (SMC.fs_frame FS 1 0) (SMC.fs_frame FS 1 (SMC.fs_M 1) - SMC.fs_frame FS 1 0) ->
  PF.shkov RNG (SMC.fs_frame FS 1 0) (SMC.fs_frame FS 1 (SMC.fs_M 1) - SMC.fs_frame FS 1 0) ->
  Forall (fun iv => LX.rng RNG (fst iv) (snd iv - fst iv)) (FP.fp_w [1%nat] FS) ->
  (forall DT TS C T DB k, SMC.asan_tls_cells mem2 (bv_unsigned tp) DT TS C T DB k ->
     Forall (fun iv => LX.rng RNG (fst iv) (snd iv - fst iv)) (FP.fp_tls (bv_unsigned tp) DT TS C T DB k)) ->
  LX.evtF rsegs RNG (RP.RPostFOn.QF ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mB f n o S FS fr X jj)
    (LMS.MS (LF.mkR xra (Z_to_bv 64 ((S - 128) / 32 * 32)) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 ((S - 128) / 32 * 32))
               (Z_to_bv 64 (SMC.fs_frame FS 1 jj)) x1 x2 x3 x4 x5 x6 x7 s2 s3 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 n)
               s7 s8 (LM.wa 0x7fff8000) s10 s11 u3 u4 u5 u6)
       F (Z_to_bv 64 0x835ec) fc None (MN.normalize rsegs mem2) (LP.seg_rom rsegs)).
Proof.
  intros HMSET HMCPY HBCMPW mem2 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f n o S FS jj fr junk X
    xra u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 fl mB
    Rf Rn Ro RS S16 Lfr HF SHM SAE Hjj GT FSS FApp Hf HOo RO HFLg STK Hrd HOrw AC SR AW AF AO ABC
    HBCMP HMEMCMP HGCF HCF254 HCF255 XF XB FPX TLS HSV H120 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO
    RBC SKBC RFSS RFLG RFRM SCFR SKFR RFW1 RTLS.
  pose proof KLF.kind_of_link1_F_holds as HKOL.
  assert (HIMG : IB.IMG_HI <= S - 8800) by (unfold IB.IMG_HI; unfold ART.HIGHMEM_BEG in SHM; lia).
  pose (mc0 := MN.normalize rsegs mem2).
  (* ---- (1) the facts at mc0, from those at mem2 ---- *)
  pose proof (MN.mem_rel_normalize rsegs mem2 RO) as REL.
  assert (BN : forall a bs, LM.bytes_at rsegs mem2 a bs -> LM.bytes_at rsegs mc0 a bs)
    by (intros a bs H; exact (MN.bytes_at_normalize rsegs mem2 a bs RO H)).
  assert (EF00 : SMC.fs_frame FS 0 0 = FS + 36864) by (unfold SMC.fs_frame; cbn [Z.of_nat]; ring).
  assert (HO0 : o <> 0 -> LS.rw_cells rsegs mc0 o [LC.CB 36 junk] /\ SMC.fs_frame FS 0 0 <= o).
  { intros Eo. destruct (HOo Eo) as (_ & Ho36 & _ & _ & _ & _ & Hlo). split; [|exact Hlo].
    apply (MNT.rw_cells_normalize mem2 o _ RO); [|exact (HOrw Eo)].
    intros i Hi.
    assert (E36 : Z.of_nat (LC.cells_size [LC.CB 36 junk]) = 36) by reflexivity.
    rewrite E36 in Hi. apply MNT.ro_addr_above_img.
    unfold IB.IMG_HI. unfold SMC.ASAN_GT in GT. lia. }
  pose proof (MNT.stk_normalize_ro mem2 (S - 8800) S RO HIMG STK) as STK0.
  assert (Hrd0 : forall i, In i (RcP.cp_rd n fr) -> LM.mrd rsegs mc0 (LM.wa (f + Z.of_nat i)) = nth_error fr i).
  { intros i Hi. rewrite <- (MN.mrd_rel rsegs mem2 mc0 _ REL). exact (Hrd i Hi). }
  pose proof (MNT.asan_cells_normalize mem2 RO AC) as AC0.
  pose proof (rcpPN_srw_norm _ mem2 RO SR) as SR0.
  pose proof (MNT.addressable_normalize mem2 _ _ RO AW) as AW0.
  assert (AF0 : 50 <= n -> ART.addressable mc0 f 50)
    by (intros Hn; exact (MNT.addressable_normalize mem2 _ _ RO (AF Hn))).
  assert (AO0 : o <> 0 -> ART.addressable mc0 o 36)
    by (intros Eo; exact (MNT.addressable_normalize mem2 _ _ RO (AO Eo))).
  pose proof (MNT.addressable_normalize mem2 _ _ RO ABC) as ABC0.
  assert (XF0 : Forall (fun ci => fst ci = 1%nat /\ LM.bytes_at rsegs mc0 (SMC.fs_flag FS (fst ci) (snd ci))
                                                     [Z_to_bv 8 1]) X).
  { eapply Forall_impl; [|exact XF]. intros ci [H1 Hb]. split; [exact H1 | exact (BN _ _ Hb)]. }
  pose proof (PP.rcpPP_fpx_normalize _ _ _ _ _ _ _ _ _ RO FPX) as FPX0.
  assert (TLS0 : PC.reac_ctrl_parse_tls mc0 (bv_unsigned tp) FS (S - 8800) S).
  { unfold PC.reac_ctrl_parse_tls in TLS |- *. intros DT TS C T DB k H. apply TLS.
    exact (proj1 (MNT.asan_tls_cells_normalize mem2 _ DT TS C T DB k RO) H). }
  pose proof (MN.mem_inv_normalize rsegs mem2) as MI2.
  assert (FR2 : LS.rw_cells rsegs mc0 (S - 96) (PF.ParseFOn.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10)).
  { apply (MNT.rw_cells_normalize mem2 _ _ RO); [|exact HSV].
    intros i Hi.
    assert (E96 : Z.of_nat (LC.cells_size (PF.ParseFOn.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10)) = 96)
      by reflexivity.
    rewrite E96 in Hi. apply MNT.ro_addr_above_img. lia. }
  (* the class-1 flag array at mc0 (fpx mc0's fp_cls) *)
  pose proof FPX0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & _ & _ & _ & HCL0 & _).
  pose proof (Forall_inv HCL0) as (_ & h & flags & _ & HFl & HFln & HFb).
  (* ---- (2) mc0 -> mB: every Section premise at mB, and mB's links to mc0 ---- *)
  destruct (VT.rcpVT_base mc0 (bv_unsigned tp) FS jj f n o S fr junk X Hjj GT FSS SHM SAE FApp (BN _ _ HFLg) STK0
              Hrd0 Hf HO0 AC0 SR0 AW0 AF0 AO0 ABC0 (BN _ _ HBCMP) (BN _ _ HMEMCMP) (BN _ _ HGCF) (BN _ _ HCF254)
              (BN _ _ HCF255) XF0 XB FPX0 TLS0)
    as (MU0 & WM0 & RM0 & HFjB & STB & HrdB & HOB & ACB & SRB & AWB & AFB & AOB & ABCB & HBCMPB & HMEMCMPB & HGCFB
        & HCF254B & HCF255B & XFB & FPB & TLSB).
  assert (HOKB : o <> 0 -> o mod 4 = 0 /\ o + 36 <= 2^64 /\ LS.rw_cells rsegs mB o [LC.CB 36 junk] /\
                 (o + 36 <= S - 8800 \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o)).
  { intros Eo. destruct (HOo Eo) as (H4 & H36 & HoS & Hof & _).
    exact (conj H4 (conj H36 (conj (HOB Eo) (conj HoS Hof)))). }
  assert (AOB2 : o <> 0 -> ART.addressable mB o 36 /\ ART.app_mem (o + 36) /\
                 (o + 36 <= BW.GOT_CF \/ BW.CF + 256 <= o)).
  { intros Eo. destruct (HOo Eo) as (_ & _ & _ & _ & Happ & Hcf & _). exact (conj (AOB Eo) (conj Happ Hcf)). }
  assert (XB0 : Forall (fun ci => 0 <= snd ci < SMC.fs_M 1) X).
  { eapply Forall_impl; [|exact XB]. intros ci [Hc _]. exact Hc. }
  (* ---- (3) the re-based stretch at the base mB, from its return memory mc0 ---- *)
  exact (RP.RPostFOn.post_all_F2 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mB f n o S FS fr junk RNG
           HMSET HMCPY HBCMPW HKOL Rf Rn Ro RS S16 STB Lfr HF HrdB HOKB ACB SRB SHM SAE AWB AFB AOB2 ABCB
           HBCMPB HMEMCMPB HGCFB HCF254B HCF255B X XFB XB0 FPB TLSB RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO
           RBC SKBC RFLG RFRM SCFR SKFR xra u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 mc0 flags jj
           Hjj MU0 WM0 RM0 MI2 FR2 HFjB HFl HFln HFb (BN _ _ H120)).
Qed.

End PN.
