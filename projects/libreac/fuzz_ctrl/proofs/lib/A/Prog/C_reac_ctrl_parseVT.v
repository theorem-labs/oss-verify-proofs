(* lib/A/Prog/C_reac_ctrl_parseVT.v -- fuzz_ctrl image A (asan, libreac v1.9.0): memory facts for the cgif-form glue
   pb_reac_ctrl_parse (lib/A/Prog/C_reac_ctrl_parseP.v).  rcpVT_base moves the premises of the re-based stretch
   (reac_ctrl_parseF_rpost.RPostFOn.post_all_F2, whose Section memory is the base mB) from the normalized return memory
   mc0 of __asan_stack_malloc_1 (flag jj reads 1) to mB = write_to_mem mc0 (wa (fs_flag FS 1 jj)) [0] (flag jj reads
   0), and gives mB's links to mc0 (munch / wmono / rd_mono).  No world (AR) fact: memory facts only.  The moves are
   those of reac_ctrl_parseF_rpost.v Module RCutFOn, parse_run_rcut (the same mB); there the facts come from the entry
   memory by munch, here from mc0 by the one-byte write.
   Sources: Lib.Mem write_to_mem_spec / bytes_at_write_same / upd_bytes_length; Lib.Frame stk_write / wmono_write /
   wmono_refl / rw_cells_transport; Lib.Step wa_of_var; A.Prog.reac_ctrl_parseF rd_mono_list / rd_of_bytes / stk_wv /
   munch_mrd_out / bytes_at_munch_upd / upd_bytes_01 / fpx_fp_nil / fpx_dj / fpx_of_fp_nil; A.Prog.RcAsanFPLib
   fl_bytes / fl_addressable / fl_asan_cells / fl_fp_free / fl_tls_same / fl_dj_out_r / outside_app_iff;
   A.ShadowRwOnK fl_shadow_rw_on; Prog.RcParse cp_rd_lt39.
   Twin rule: every project module is Required without Import and named through a full-path Module alias.
   rule 24: no function proved. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Img0 AsanRT ShadowRwOn ShadowRwOnK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_stack_malloc_c RcAsanFP RcAsanFPLib
  reac_ctrl_parse_c reac_ctrl_parseF bcmp_wrap_c memcmp_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse.
Import ListNotations.
Local Open Scope Z_scope.

Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module AI0 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module SRO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Module SRK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnK.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c.
Module FP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.RcAsanFP.
Module FPL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.RcAsanFPLib.
Module PC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parse_c.
Module PF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parseF.
Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c.
Module MC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.memcmp_c.
Module RcP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.
Local Notation rsegs := AI0.rsegs (only parsing).

(* A byte below the flag fl (an image / runtime cell) is outside [(fl, fl + 1)]. *)
Local Ltac vt_below :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; rewrite ?LM.length_le8 in Hx; cbn [length Z.of_nat Pos.of_succ_nat] in Hx;
  cbn [LF.outside]; split; [|exact I];
  unfold BW.REAL_BCMP, BW.REAL_MEMCMP, BW.GOT_CF, BW.CF in Hx; lia.

Lemma rcpVT_base : forall (mc0 : word -> option byte) (TP FS jj f n o S : Z) (fr junk : list byte) (X : list (nat * Z)),
  let fl := SMC.fs_flag FS 1 jj in
  let mB := write_to_mem mc0 (LM.wa fl) [Z_to_bv 8 0] in
  0 <= jj < SMC.fs_M 1 ->
  SMC.ASAN_GT <= FS -> FS + SMC.FS_SIZE <= S - 8800 -> ART.HIGHMEM_BEG <= S - 8800 -> S <= ART.APPMEM_END ->
  (forall a, FS <= a < FS + SMC.FS_SIZE -> ART.app_mem a) ->
  LM.bytes_at rsegs mc0 fl [Z_to_bv 8 1] ->
  (* the facts at mc0 *)
  LF.stk rsegs mc0 (S - 8800) S ->
  (forall i, In i (RcP.cp_rd n fr) -> LM.mrd rsegs mc0 (LM.wa (f + Z.of_nat i)) = nth_error fr i) ->
  (50 <= n -> f + 50 <= FS \/ FS + SMC.FS_SIZE <= f) ->
  (o <> 0 -> LS.rw_cells rsegs mc0 o [LC.CB 36 junk] /\ SMC.fs_frame FS 0 0 <= o) ->
  ART.asan_cells mc0 ->
  SRO.shadow_rw_on (PC.reac_ctrl_parse_shadow_R f n o S FS) mc0 ->
  ART.addressable mc0 (S - 8800) 8800 -> (50 <= n -> ART.addressable mc0 f 50) ->
  (o <> 0 -> ART.addressable mc0 o 36) -> ART.addressable mc0 PC.REAC_CTRL_PARSE_BC 6 ->
  LM.bytes_at rsegs mc0 BW.REAL_BCMP (LM.le8 (LM.wa BW.BCMP)) ->
  LM.bytes_at rsegs mc0 BW.REAL_MEMCMP (LM.le8 (LM.wa MC.MEMCMP)) ->
  LM.bytes_at rsegs mc0 BW.GOT_CF (LM.le8 (LM.wa BW.CF)) -> LM.bytes_at rsegs mc0 (BW.CF + 254) [Z_to_bv 8 1] ->
  LM.bytes_at rsegs mc0 (BW.CF + 255) [Z_to_bv 8 1] ->
  Forall (fun ci => fst ci = 1%nat /\ LM.bytes_at rsegs mc0 (SMC.fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) X ->
  Forall (fun ci => 0 <= snd ci < SMC.fs_M 1 /\ snd ci <> jj) X ->
  FP.fpx [1%nat] mc0 TP FS (S - 8800) S (PC.reac_ctrl_parse_W o S) (PC.reac_ctrl_parse_D f n o) X ->
  PC.reac_ctrl_parse_tls mc0 TP FS (S - 8800) S ->
  (* the facts at mB, and mB's link to mc0 *)
  LF.munch [(fl, fl + 1)] mB mc0 /\ LF.wmono rsegs mB mc0 /\ PF.rd_mono mB mc0 /\
  LM.bytes_at rsegs mB fl [Z_to_bv 8 0] /\
  LF.stk rsegs mB (S - 8800) S /\
  (forall i, In i (RcP.cp_rd n fr) -> LM.mrd rsegs mB (LM.wa (f + Z.of_nat i)) = nth_error fr i) /\
  (o <> 0 -> LS.rw_cells rsegs mB o [LC.CB 36 junk]) /\
  ART.asan_cells mB /\ SRO.shadow_rw_on (PC.reac_ctrl_parse_shadow_R f n o S FS) mB /\
  ART.addressable mB (S - 8800) 8800 /\ (50 <= n -> ART.addressable mB f 50) /\
  (o <> 0 -> ART.addressable mB o 36) /\ ART.addressable mB PC.REAC_CTRL_PARSE_BC 6 /\
  LM.bytes_at rsegs mB BW.REAL_BCMP (LM.le8 (LM.wa BW.BCMP)) /\
  LM.bytes_at rsegs mB BW.REAL_MEMCMP (LM.le8 (LM.wa MC.MEMCMP)) /\
  LM.bytes_at rsegs mB BW.GOT_CF (LM.le8 (LM.wa BW.CF)) /\ LM.bytes_at rsegs mB (BW.CF + 254) [Z_to_bv 8 1] /\
  LM.bytes_at rsegs mB (BW.CF + 255) [Z_to_bv 8 1] /\
  Forall (fun ci => fst ci = 1%nat /\ LM.bytes_at rsegs mB (SMC.fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) X /\
  FP.fpx [1%nat] mB TP FS (S - 8800) S (PC.reac_ctrl_parse_W o S) (PC.reac_ctrl_parse_D f n o) X /\
  PC.reac_ctrl_parse_tls mB TP FS (S - 8800) S.
Proof.
  intros mc0 TP FS jj f n o S fr junk X fl mB Hjj GT FSS SHM SAE FApp HFLg STK Hrd Hf HO AC SR AW AF AO ABC
    HBCMP HMEMCMP HGCF HCF254 HCF255 XF XB FPX TLS.
  assert (Efs : forall j, SMC.fs_flag FS 1 j = FS + 20480 + j)
    by (intros j; unfold SMC.fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
        change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
  assert (EFl : fl = FS + 20480 + jj) by (unfold fl; apply Efs).
  assert (EmB : mB = write_to_mem mc0 (LM.wa fl) [Z_to_bv 8 0]) by reflexivity.
  clearbody mB fl.
  assert (EM1 : SMC.fs_M 1 = 8192) by reflexivity.
  rewrite EM1 in Hjj.
  unfold SMC.ASAN_GT in GT. unfold SMC.FS_SIZE in FSS, FApp, Hf. unfold ART.HIGHMEM_BEG in SHM.
  unfold ART.APPMEM_END in SAE.
  assert (Hflin : FS <= fl < FS + 11571200) by lia.
  assert (Rfl : 0 <= fl /\ fl + 1 <= 2 ^ 64) by lia.
  pose proof (FApp fl Hflin) as Happ.
  (* mB's links to mc0: mc0 is mB with flag jj set back to 1 *)
  assert (MU0 : LF.munch [(fl, fl + 1)] mB mc0).
  { intros x Hx. rewrite EmB. rewrite LM.write_to_mem_spec by (cbn [length Z.of_nat Pos.of_succ_nat]; lia).
    cbn [LF.outside length Z.of_nat Pos.of_succ_nat] in Hx |- *. destruct Hx as [Hx _].
    destruct (Z.leb_spec0 fl (bv_unsigned x)); cbn [andb]; [|reflexivity].
    destruct (Z.ltb_spec0 (bv_unsigned x) (fl + Z.of_nat 1)); [exfalso; lia | reflexivity]. }
  assert (MU1 : LF.munch [(fl, fl + 1)] mc0 mB) by (intros x Hx; symmetry; exact (MU0 x Hx)).
  assert (WM1 : LF.wmono rsegs mc0 mB) by (rewrite EmB; apply LF.wmono_write, LF.wmono_refl).
  pose proof FPX as (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & HTP0 & HP0 & H880 & H960 & HCL0 & HFS0 & HA0 & HWd0
                     & HDd0).
  pose proof HP0 as (_ & _ & _ & _ & STfs).
  unfold SMC.FS_SIZE in STfs.
  assert (WM0 : LF.wmono rsegs mB mc0).
  { intros x Hx. destruct (Z.eq_dec (bv_unsigned x) fl) as [Ex|Ex].
    - rewrite <- (LS.wa_of_var x _ Ex).
      apply (PF.stk_wv mc0 FS (FS + 11571200)); [exact STfs | lia].
    - unfold wview in *. rewrite (MU0 x ltac:(cbn [LF.outside]; split; [lia | exact I])). exact Hx. }
  assert (RM0 : PF.rd_mono mB mc0).
  { apply (PF.rd_mono_list _ _ _ MU0). constructor; [|constructor]. cbn [fst snd]. intros y Hy.
    apply (PF.rd_of_bytes _ _ _ HFLg). cbn [length Z.of_nat Pos.of_succ_nat]. lia. }
  assert (HFjB : LM.bytes_at rsegs mB fl [Z_to_bv 8 0])
    by (rewrite EmB; apply LM.bytes_at_write_same; cbn [length Z.of_nat Pos.of_succ_nat]; lia).
  (* fl is app memory, so no shadow byte is fl *)
  assert (NOSH : forall x, ART.in_shadow x -> LF.outside [(fl, fl + 1)] x).
  { intros x Hx. cbn [LF.outside]. split; [|exact I]. intros Hr. assert (Ex : x = fl) by lia. subst x.
    unfold ART.app_mem, ART.in_shadow, ART.LOWMEM_END, ART.LOWSHADOW_END, ART.HIGHSHADOW_BEG, ART.HIGHMEM_BEG,
      ART.APPMEM_END in *. lia. }
  (* fl is one of the class-1 flag bytes of fp_w [1] FS *)
  assert (HSUB : forall R, LF.sub_fp [(fl, fl + 1)] (FP.fp_w [1%nat] FS ++ R)).
  { intros R x Hx. apply FPL.outside_app_iff in Hx as [Hx _].
    cbn [FP.fp_w flat_map FP.fp_w1 app LF.outside] in Hx. destruct Hx as (_ & Hfl & _).
    cbn [LF.outside]. split; [|exact I]. intros Hr. apply Hfl. rewrite Efs, EM1. lia. }
  split; [exact MU0|]. split; [exact WM0|]. split; [exact RM0|]. split; [exact HFjB|].
  split; [rewrite EmB; apply LF.stk_write; [exact STK | lia | cbn [length Z.of_nat Pos.of_succ_nat]; lia]|].
  split.
  { intros i Hi. rewrite <- (Hrd i Hi).
    assert (Hn50 : 50 <= n)
      by (unfold RcP.cp_rd in Hi; destruct (50 <=? n) eqn:E50; cbn [negb] in Hi;
          [apply Z.leb_le; exact E50 | destruct Hi]).
    pose proof (RcP.cp_rd_lt39 n fr i Hi) as Hi39.
    pose proof (AF Hn50) as (Af0 & _ & Af1 & _). unfold ART.APPMEM_END in Af1.
    apply (PF.munch_mrd_out _ mc0 mB _ MU1); [lia|].
    cbn [LF.outside]. split; [|exact I]. destruct (Hf Hn50); lia. }
  split.
  { intros Eo. destruct (HO Eo) as [HOrw HOlo].
    unfold SMC.fs_frame in HOlo. cbn [Z.of_nat] in HOlo.
    apply (LF.rw_cells_transport rsegs [(fl, fl + 1)] mc0 mB o _ HOrw MU1 WM1).
    cbn [LF.disjoint_from LC.cells_size LC.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. split; [|exact I].
    right. lia. }
  split.
  { apply (FPL.fl_asan_cells [(fl, fl + 1)] mc0 mB AC MU1).
    intros x Hx. cbn [LF.outside]. split; [|exact I]. unfold ART.RT_LO, ART.RT_HI in Hx. lia. }
  split; [exact (SRK.fl_shadow_rw_on _ [(fl, fl + 1)] mc0 mB SR MU1 WM1 NOSH)|].
  split; [exact (FPL.fl_addressable _ mc0 mB _ _ AW MU1 NOSH)|].
  split; [intros Hn50; exact (FPL.fl_addressable _ mc0 mB _ _ (AF Hn50) MU1 NOSH)|].
  split; [intros Eo; exact (FPL.fl_addressable _ mc0 mB _ _ (AO Eo) MU1 NOSH)|].
  split; [exact (FPL.fl_addressable _ mc0 mB _ _ ABC MU1 NOSH)|].
  split; [apply (FPL.fl_bytes _ mc0 mB _ _ HBCMP MU1); vt_below|].
  split; [apply (FPL.fl_bytes _ mc0 mB _ _ HMEMCMP MU1); vt_below|].
  split; [apply (FPL.fl_bytes _ mc0 mB _ _ HGCF MU1); vt_below|].
  split; [apply (FPL.fl_bytes _ mc0 mB _ _ HCF254 MU1); vt_below|].
  split; [apply (FPL.fl_bytes _ mc0 mB _ _ HCF255 MU1); vt_below|].
  split.
  { rewrite Forall_forall in XF, XB |- *. intros ci Hci.
    destruct (XF ci Hci) as [H1 Hb]. destruct (XB ci Hci) as [_ Hne]. split; [exact H1|].
    apply (FPL.fl_bytes _ mc0 mB _ _ Hb MU1).
    intros x Hx. rewrite H1, Efs in Hx. cbn [length Z.of_nat Pos.of_succ_nat] in Hx.
    cbn [LF.outside]. split; [|exact I]. lia. }
  split.
  { (* fpx at mB: fp from mc0's by the one-byte write (fl_fp_free), and mc0's data-range fact *)
    apply PF.fpx_of_fp_nil; [|exact (PF.fpx_dj _ _ _ _ _ _ _ _ _ FPX)].
    pose proof (Forall_inv HCL0) as (_ & h & flags & HH & HF & HFl & HFb).
    rewrite EM1 in HFl.
    apply (FPL.fl_fp_free [1%nat] mc0 mB TP FS (S - 8800) S (PC.reac_ctrl_parse_W o S) [] [(fl, fl + 1)]
             (PF.fpx_fp_nil _ _ _ _ _ _ _ _ _ FPX) TLS MU1 WM1).
    - intros x Hx. apply FPL.outside_app_iff in Hx as [_ Hx]. exact (HSUB _ x Hx).
    - intros x Hx. cbn [LF.outside]. split; [lia | exact I].
    - intros x Hx. destruct (Z.eq_dec x fl) as [Ex|Ex].
      + right. rewrite Ex. pose proof HFjB as (_ & _ & Hb).
        specialize (Hb 0%nat ltac:(cbn [length]; lia)). cbn [Z.of_nat nth_error] in Hb.
        rewrite Z.add_0_r in Hb. exists (Z_to_bv 8 0). exact Hb.
      + left. cbn [LF.outside]. split; [lia | exact I].
    - intros c Hc. destruct Hc as [Hc|[]]. subst c. split.
      + exists h. apply (FPL.fl_bytes _ mc0 mB _ _ HH MU1).
        intros x Hx. rewrite LM.length_le8 in Hx. unfold SMC.fs_hint in Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx.
        cbn [LF.outside]. split; [lia | exact I].
      + exists (LM.upd_bytes flags (Z.to_nat jj) [Z_to_bv 8 0]).
        split; [|split].
        * apply (PF.bytes_at_munch_upd _ mc0 mB _ flags (Z.to_nat jj) (Z_to_bv 8 0) HF MU1); [lia| |].
          -- replace (SMC.fs_flag FS 1 0 + Z.of_nat (Z.to_nat jj)) with fl
               by (rewrite Z2Nat.id by lia; rewrite Efs; lia).
             exact HFjB.
          -- intros x Hx Hne. rewrite Z2Nat.id in Hne by lia. rewrite Efs in Hne.
             cbn [LF.outside]. split; [lia | exact I].
        * rewrite LM.upd_bytes_length; [rewrite EM1; exact HFl | cbn [length]; lia].
        * apply PF.upd_bytes_01; [exact HFb | left; reflexivity]. }
  (* the tls premise at mB: the thread cells are apart from fl (mc0's tls premise), so they name the same cells *)
  unfold PC.reac_ctrl_parse_tls in TLS |- *.
  intros DT TS C T DB k HTB.
  pose proof (TLS DT0 TS0 C0 T0 DB0 k0 HT0) as TLSdj.
  assert (Hc : Forall (fun d => forall x, fst d <= x < snd d -> LF.outside [(fl, fl + 1)] x)
                 (FP.fp_tls TP DT0 TS0 C0 T0 DB0 k0)).
  { apply Forall_forall. intros [a b] Hin x Hx.
    exact (HSUB _ x (FPL.fl_dj_out_r _ _ a b x TLSdj Hin Hx)). }
  destruct (FPL.fl_tls_same mc0 mB [(fl, fl + 1)] TP DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HTB MU1 Hc)
    as (E1 & E2 & E3 & E4 & E5 & E6).
  subst DT TS C T DB k. exact TLSdj.
Qed.
