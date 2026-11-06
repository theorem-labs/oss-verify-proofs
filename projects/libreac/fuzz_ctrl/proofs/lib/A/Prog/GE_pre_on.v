(* fuzz_ctrl image A, ctrl_emit_as (0x849d8): the FIRST lifted stretch of a Theorem Labs lane's cgif-form glue in its
   route (C) form. NEW file (additive form ruling, auditor a Theorem Labs lane): GE_pre.v is not changed.

   `ge_pre_on` is GE_pre.ge_pre re-pointed at A/Prog/ctrl_emit_asF2_on.v `ctrl_emit_as_pre_lay_F_on` (post
   `aMid_on`), at GE_pre's instantiation, with exactly these changes:
     - HMSF / HMCF are a Theorem Labs lane's asan_memset_cF_on.asan_memset_contract_F_on /
       asan_memcpy_cF_on.asan_memcpy_contract_F_on;
     - the premise `shadow_rw memc` is the REGIONAL `A.ShadowRwOn.shadow_rw_on Rsh memc` for a region Rsh (a new
       binder) that holds the shadow-word spans the stretch's helper calls read: the output [p, p + LEN) when
       EE = true, the source d and the box (ctrl_emit_asF2_on.v HRsh at o := p, s := VAL (A_OBJ A_BOX)); it
       moves to normalize rsegs memc by A.ShadowRwOnT.shadow_rw_on_normalize.
   GE_pre's helper lemmas (ge_img_in, ge_ro_not_img, ge_dj_out) are reused from GE_pre.v.

   Memory-checking runtime: before each load or store the code loads a shadow byte at (a >> 3) + 0x7fff8000 and
   compares it; with the range addressable the check passes and the error path is not reached.

   Glue closure rule (two Theorem Labs lanes, 2026-10-28 23:38Z): ctrl_emit_asF2_on and the _cF_on / _on files are
   Required qualified only. rule 24: At ossv/recipes c5e779efe8c (2026-10-31), no released proof of ctrl_emit_as outside this unit. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import GEbase GE_row GE_img GE_buf GE_pre.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import MemNorm MemNormTr.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLay RcFin RcEmit RcEmitLib RcSynth RcBox.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ImgBounds asan_memset_cF_on asan_memcpy_cF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require sh_word_on ctrl_emit_asF2_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn ShadowRwOnT.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope Z_scope.

(* The six modules the core and lib/A/Reusable both carry (YI04, YI16, YK11, YK1b, YM05, YO09) are always named
   with their path here (a Theorem Labs lane, 04:03Z): A/MemNorm.v loads lib/A/Reusable's copies after the core's, and a
   partial module name then denotes the later copy. *)
Section b. Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
  {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}.
Context {SK : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := AB1v.tfibsegs.
#[local] Notation VAL := (@pa_val _ ctrl_listing PI_ctrl).
#[local] Notation BASE := (@pa_val _ ctrl_listing PI_ctrl A_TEXT).

(* ---------------------------------------------------------------------------------------------------------
   The first lifted stretch at the call. *)
Section e.
Variable B : asyms.
Variable GLOBS : list (Z * Z).
Variables RLO RHI : Z.

Lemma ge_pre_on :
  forall (HMSF : asan_memset_cF_on.asan_memset_contract_F_on)
    (HMCF : asan_memcpy_cF_on.asan_memcpy_contract_F_on)
    (LAWS : AR_laws SEGS B)
    (HIMGSH : img_shadow_vis SEGS B)
    (HGM : globs_marked SEGS B GLOBS)
    (HFR_glob : In (VAL (A_OBJ A_FRAMES), 11 * ROW_BYTES) GLOBS)
    (HFR_al : VAL (A_OBJ A_FRAMES) mod 8 = 0)
    (HCAT_glob : In (VAL (A_OBJ A_CAT), 11 * CAT_BYTES) GLOBS)
    (HCAT_al : VAL (A_OBJ A_CAT) mod 8 = 0)
    (HBOX_glob : In (VAL (A_OBJ A_BOX), 6) GLOBS)
    (HROWS : forall r, 3 <= r <= 9 -> forall (H : word -> bool) mem,
       arodata_okS SEGS B RLO RHI (aview SEGS H mem) ->
       garr8 SEGS (mrestrict H mem) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) (map bv_unsigned (CROW r)))
    (HFR_rng : IMG_LO + 64 <= VAL (A_OBJ A_FRAMES) /\ VAL (A_OBJ A_FRAMES) + 11 * ROW_BYTES + 64 <= IMG_HI)
    (HCAT_rng : IMG_LO + 64 <= VAL (A_OBJ A_CAT) /\ VAL (A_OBJ A_CAT) + 11 * CAT_BYTES + 64 <= IMG_HI)
    (HBOX_rng : IMG_LO + 64 <= VAL (A_OBJ A_BOX) /\ VAL (A_OBJ A_BOX) + 6 + 64 <= IMG_HI)
    (RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k (regs : bvmap 5 word)
    (p md d n r i ns FS : Z) (mb nb db sb : list byte) (Rsh : Z -> Prop),
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc) ->
  getr regs 10 = w64 p ->
  getr regs 11 = w64 (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) -> 3 <= r <= 9 ->
  getr regs 12 = w64 md -> md = VAL (A_OBJ A_CAT) + CAT_BYTES * i -> 0 <= i < 11 ->
  getr regs 13 = w64 d ->
  getr regs 14 = w64 (VAL (A_OBJ A_BOX)) ->
  getr regs 16 = w64 n -> - 2 ^ 31 <= n < 2 ^ 31 ->
  getr regs 17 = w64 0 ->
  getr regs 29 = w64 ns ->
  sp0 - STK <= spZ regs - TEMIT_STK -> spZ regs <= sp0 ->
  0 < p -> p + 1492 <= 2 ^ 47 - 8 -> amem_range p 1492 ->
  (forall x, p <= x < p + 1492 -> ~ in_img SEGS x) ->
  twr_ok (PI := PI_ctrl) B STK sp0 FP ly S lyc Sc own W memc (spZ regs) p 1492 ->
  afobj SEGS B lyc Sc W memc p 1492 ->
  tfr_hull lyc Sc p 1492 ->
  length db = 6%nat -> garr8 SEGS (mrestrict (w_H W) memc) d (map bv_unsigned db) ->
  tsrc_ok (PI := PI_ctrl) W memc (spZ regs) d 6 ->
  (p + 1492 <= d \/ d + 6 <= p) ->
  (d + 6 <= spZ regs - TEMIT_STK \/ spZ regs <= d) ->
  d mod 8 = 0 ->
  length sb = 6%nat ->
  garr8 SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ A_BOX)) (map bv_unsigned sb) ->
  garr8 SEGS (mrestrict (w_H W) memc) md (map bv_unsigned mb) -> length mb = 296%nat ->
  ((RcLay.ly_bb r = 5 \/ RcLay.ly_bb r = 6) -> RcSynth.has mb <> 0 -> RcSynth.rname mb <> 0 ->
     RcBox.name_ok nb /\
     garr8 SEGS (mrestrict (w_H W) memc) (RcSynth.rname mb) (map bv_unsigned nb) /\
     (exists q sz, In (q, sz) GLOBS /\ q <= RcSynth.rname mb /\ RcSynth.rname mb + Z.of_nat (length nb) <= q + sz) /\
     (forall x, RcSynth.rname mb <= x < RcSynth.rname mb + Z.of_nat (length nb) -> in_roP SEGS RLO RHI x /\
        ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4))) ->
  (* the run state of the memory-checking runtime at the call, which no core law gives *)
  ro_agree rsegs memc ->
  asan_cells memc ->
  A.ShadowRwOn.shadow_rw_on Rsh memc ->
  (forall a, (RcEmit.em_E (RcFin.ubat (CROW r) 21) (RcFin.ubat (CROW r) 22) n (RcEmit.em_hid mb) = true /\
              sh_word_on.sh_word_on p (RcEmit.em_len (RcFin.ubat (CROW r) 21) n) a) \/
             sh_word_on.sh_word_on d 6 a \/ sh_word_on.sh_word_on (VAL (A_OBJ A_BOX)) 6 a -> Rsh a) ->
  addressable memc (spZ regs - 4640) 4640 ->
  fp [0%nat; 1%nat] memc (bv_unsigned (getr regs 4)) FS (spZ regs - 4640) (spZ regs)
    [(spZ regs - 4640, spZ regs);
     (p, p + (if RcEmit.em_E (RcFin.ubat (CROW r) 21) (RcFin.ubat (CROW r) 22) n (RcEmit.em_hid mb)
              then RcEmit.em_len (RcFin.ubat (CROW r) 21) n else 0))]
    [(VAL (A_OBJ A_FRAMES) + ROW_BYTES * r, VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + 24); (md, md + 296);
     (d, d + 6); (VAL (A_OBJ A_BOX), VAL (A_OBJ A_BOX) + 6);
     (p, p + (if RcEmit.em_E (RcFin.ubat (CROW r) 21) (RcFin.ubat (CROW r) 22) n (RcEmit.em_hid mb)
              then RcEmit.em_len (RcFin.ubat (CROW r) 21) n else 0))] ->
  ctrl_emit_as_c.ctrl_emit_as_tls memc (bv_unsigned (getr regs 4)) FS (spZ regs - 4640) (spZ regs) ->
  sh_cov_vis (w_H W) (spZ regs - 4640) (spZ regs - 1) ->
  ExecF.evtF rsegs (RNG_W (w_H W))
    (fun s => exists s0,
       ctrl_emit_asF2_on.aMid_on (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 8) (getr regs 9)
         (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
         (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 15)
         lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr (normalize rsegs memc)
         p (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) md d (VAL (A_OBJ A_BOX)) 0 n ns FS
         (CROW r) [] mb nb [] db sb Rsh s0 /\
       ms_rel rsegs s s0 /\ ro_same rsegs memc (ms_mem s))
    (MS (mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
             (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13)
             (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
             (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
             (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31))
        lib.Reusable.YK11.fp_regs (Z_to_bv 64 (BASE + AF_ctrl_emit_as)) lib.Reusable.YK11.fp_csr None memc
        (seg_rom SEGS)).
Proof.
  intros HMSF HMCF LAWS HIMGSH HGM HFR_glob HFR_al HCAT_glob HCAT_al HBOX_glob HROWS HFR_rng HCAT_rng HBOX_rng
    RELRO_IMG STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p md d n r i ns FS mb nb db sb Rsh
    HJ HRO Hr10 Hr11 Hr Hr12 Hmd Hi Hr13 Hr14 Hr16 Hn Hr17 Hr29 Hslo Hshi Hp Hpe Hpam Hpni Hptw Hpfo Hpfh
    Hdl HdG Hdsrc Hdp Hds Hd8 Hsl HsG HmG Hml HNB RO HAC HSW HRsh HAWIN HFP HFPT HWSH.
  (* ---- the start state is the run's ---- *)
  replace (BASE + AF_ctrl_emit_as) with 0x849d8 by (vm_compute; reflexivity).
  rewrite Hr10, Hr11, Hr12, Hr13, Hr14, Hr16, Hr17, Hr29. unfold w64.
  change (seg_rom SEGS) with (seg_rom rsegs).
  (* ---- facts of the caller's world, in lib.Lib form on memc ---- *)
  pose proof (ge_win B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs HJ Hslo Hshi) as [VWIN STK0].
  assert (Brow : bytes_at rsegs memc (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) (CROW r))
    by (eapply ge_row_bytes; eassumption).
  assert (Bmd : bytes_at rsegs memc md mb) by (eapply ge_md_bytes; eassumption).
  assert (Bsb : bytes_at rsegs memc (VAL (A_OBJ A_BOX)) sb) by (eapply ge_sb_bytes; eassumption).
  assert (Bdb : bytes_at rsegs memc d db) by (eapply ge_src_bytes; eassumption).
  assert (Arow : addressable memc (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) 24)
    by (eapply ge_row_addr; eassumption).
  assert (Amd0 : addressable memc md 296) by (eapply ge_md_addr; eassumption).
  assert (Asb : addressable memc (VAL (A_OBJ A_BOX)) 6) by (eapply ge_sb_addr; eassumption).
  assert (Adb : addressable memc d 6 /\ app_mem (d + 6)) by (eapply ge_src_addr; eassumption).
  assert (APD0 : app_mem (d + 6) /\ app_mem (d + 7)) by (eapply ge_src_app7; eassumption).
  assert (Vrow : range_visible (w_H W) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) 24)
    by (eapply ge_row_vis; eassumption).
  assert (Vmd : range_visible (w_H W) md 296) by (eapply ge_md_vis; eassumption).
  assert (Vsb : range_visible (w_H W) (VAL (A_OBJ A_BOX)) 6) by (eapply ge_sb_vis; eassumption).
  assert (Crow : sh_cov_vis (w_H W) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + 23))
    by (eapply ge_row_shcov; eassumption).
  assert (Cmd : sh_cov_vis (w_H W) md (md + 295)) by (eapply ge_md_shcov; eassumption).
  assert (Csb : sh_cov_vis (w_H W) (VAL (A_OBJ A_BOX)) (VAL (A_OBJ A_BOX) + 5))
    by (eapply ge_sb_shcov; eassumption).
  assert (VCdb : range_visible (w_H W) d 6 /\ sh_cov_vis (w_H W) d (d + 5)) by (eapply ge_src_vis; eassumption).
  (* ---- the stack window lies above alloc_ceiling, the image below it ---- *)
  pose proof asan_consts as (CV & _).
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HK & _).
  destruct HK as (_ & _ & HC & HL & HH & H47 & _).
  assert (HT : 4640 <= TEMIT_STK) by (unfold TEMIT_STK; lia).
  (* the buffer lies in a frame of the caller, below alloc_ceiling *)
  pose proof Hpfh as (cid & pos & Hin & Hflo & Hfhi).
  pose proof (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & FB & _).
  pose proof (Z.div_mod (p + 1492 - 1) 64 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (p + 1492 - 1) 64 ltac:(lia)) as D2.
  assert (PEND : p + 1492 <= lib.Reusable.YM05.alloc_ceiling) by lia.
  clear Hin Hflo Hfhi FB D1 D2.
  change (spZ regs) with (bv_unsigned (getr regs 2)) in *.
  assert (CEIL : lib.Reusable.YM05.alloc_ceiling <= bv_unsigned (getr regs 2) - 4640) by lia.
  (* ---- the junk bytes of the output buffer ---- *)
  assert (JK : exists junk : list byte,
     RcEmit.em_E (RcFin.ubat (CROW r) 21) (RcFin.ubat (CROW r) 22) n (RcEmit.em_hid mb) = true ->
     rw_cells rsegs memc p [CB (Z.to_nat (RcEmit.em_len (RcFin.ubat (CROW r) 21) n)) junk]).
  { destruct (RcEmit.em_E (RcFin.ubat (CROW r) 21) (RcFin.ubat (CROW r) 22) n (RcEmit.em_hid mb)) eqn:E.
    - pose proof (RcEmitLib.em_len_rng _ _ _ _ E) as RLN.
      destruct (ge_buf_rw B STK sp0 FP ly S lyc Sc own W memc regs p
                  (RcEmit.em_len (RcFin.ubat (CROW r) 21) n) Hp Hpe Hptw ltac:(lia)) as (_ & junk & Hc).
      exists junk. intros _. exact Hc.
    - exists []. intros H. discriminate H. }
  destruct JK as [junk HJK].
  (* ---- the run's hypotheses, on normalize rsegs memc ---- *)
  assert (Hg0 : 0 <= 0 < 2 ^ 64) by lia.
  assert (HST : stk rsegs (normalize rsegs memc) (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2))).
  { apply stk_normalize_ro; [exact RO | unfold ImgBounds.IMG_HI; lia | exact STK0]. }
  assert (Dsf : RcLay.ly_dj (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2))
                  (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + 24)).
  { unfold RcLay.ly_dj. right. unfold IMG_HI, ROW_BYTES in *. lia. }
  assert (Dsm : RcLay.ly_dj (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2)) md (md + 296)).
  { unfold RcLay.ly_dj. right. unfold IMG_HI, CAT_BYTES in *. lia. }
  assert (Dsd : RcLay.ly_dj (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2)) d (d + 6)).
  { unfold RcLay.ly_dj. lia. }
  assert (Dss : RcLay.ly_dj (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2))
                  (VAL (A_OBJ A_BOX)) (VAL (A_OBJ A_BOX) + 6)).
  { unfold RcLay.ly_dj. right. unfold IMG_HI in *. lia. }
  assert (Hf8 : (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) mod 8 = 0).
  { replace (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) with (VAL (A_OBJ A_FRAMES) + (3 * r) * 8)
      by (unfold ROW_BYTES; lia).
    rewrite Z.mod_add by lia. exact HFR_al. }
  assert (Hf24 : VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + 24 <= 2 ^ 64).
  { unfold IMG_HI, ROW_BYTES in *. lia. }
  pose proof (ge_row_len r) as Hrl.
  pose proof (bytes_at_normalize rsegs memc _ _ RO Brow) as HR.
  pose proof (ge_row_HL r) as HL0.
  assert (Hmd0 : md <> 0) by (unfold IMG_LO, CAT_BYTES in *; lia).
  assert (Hmd8 : md mod 8 = 0).
  { rewrite Hmd. replace (VAL (A_OBJ A_CAT) + CAT_BYTES * i) with (VAL (A_OBJ A_CAT) + (37 * i) * 8)
      by (unfold CAT_BYTES; lia).
    rewrite Z.mod_add by lia. exact HCAT_al. }
  assert (Hmd296 : md + 296 <= 2 ^ 64) by (unfold IMG_HI, CAT_BYTES in *; lia).
  pose proof (bytes_at_normalize rsegs memc _ _ RO Bmd) as HM.
  assert (Ho1492 : p + 1492 <= 2 ^ 64) by lia.
  assert (HEo : RcEmit.em_E (RcFin.ubat (CROW r) 21) (RcFin.ubat (CROW r) 22) n (RcEmit.em_hid mb) = true ->
     rw_cells rsegs (normalize rsegs memc) p [CB (Z.to_nat (RcEmit.em_len (RcFin.ubat (CROW r) 21) n)) junk] /\
     RcLay.ly_dj (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2)) p
       (p + RcEmit.em_len (RcFin.ubat (CROW r) 21) n) /\
     RcLay.ly_dj p (p + RcEmit.em_len (RcFin.ubat (CROW r) 21) n)
       (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + 24) /\
     (RcLay.ly_k (CROW r) = 2 ->
        RcLay.ly_dj p (p + RcEmit.em_len (RcFin.ubat (CROW r) 21) n)
          (RcLay.ly_tm (CROW r)) (RcLay.ly_tm (CROW r) + 32)) /\
     RcLay.ly_dj p (p + RcEmit.em_len (RcFin.ubat (CROW r) 21) n) md (md + 296) /\
     ((3 <= RcLay.ly_k (CROW r) <= 9 /\
       (RcLay.ly_bb (RcLay.ly_k (CROW r)) = 5 \/ RcLay.ly_bb (RcLay.ly_k (CROW r)) = 6)) /\
      RcSynth.has mb <> 0 /\ RcSynth.rname mb <> 0 ->
        RcLay.ly_dj p (p + RcEmit.em_len (RcFin.ubat (CROW r) 21) n)
          (RcSynth.rname mb) (RcSynth.rname mb + Z.of_nat (length nb))) /\
     RcLay.ly_dj p (p + RcEmit.em_len (RcFin.ubat (CROW r) 21) n) d (d + 6) /\
     RcLay.ly_dj p (p + RcEmit.em_len (RcFin.ubat (CROW r) 21) n) (VAL (A_OBJ A_BOX)) (VAL (A_OBJ A_BOX) + 6) /\
     (0 <> 0 -> RcLay.ly_al (CROW r) <> 0 ->
        RcLay.ly_dj p (p + RcEmit.em_len (RcFin.ubat (CROW r) 21) n) 0 (0 + RcLay.ly_al (CROW r)))).
  { intros HE. pose proof (RcEmitLib.em_len_rng _ _ _ _ HE) as RLN.
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
    - apply rw_cells_normalize; [exact RO | | exact (HJK HE)].
      intros j Hj. cbn [cells_size csize] in Hj.
      apply ge_ro_not_img; [lia | apply Hpni; lia].
    - unfold RcLay.ly_dj. right. lia.
    - apply ge_dj_out; [exact Hpni | lia | lia |].
      intros x Hx. apply ge_img_in. unfold IMG_LO, IMG_HI, ROW_BYTES in *. lia.
    - intros E2. exact (ge_row_kb2 r _ Hr E2).
    - apply ge_dj_out; [exact Hpni | lia | lia |].
      intros x Hx. apply ge_img_in. unfold IMG_LO, IMG_HI, CAT_BYTES in *. lia.
    - intros HNM. apply (ge_row_NM r mb Hr) in HNM. destruct HNM as (HB & Hh & Hn0).
      destruct (HNB HB Hh Hn0) as (Hok & _ & _ & Hro).
      destruct Hok as (Hlen & _).
      apply ge_dj_out; [exact Hpni | lia | lia |].
      intros x Hx. destruct (Hro x Hx) as ([(sg & Hs & _ & Hsr) | Hsr] & _).
      + exists sg. split; [exact Hs | exact Hsr].
      + exact (RELRO_IMG x Hsr).
    - unfold RcLay.ly_dj. lia.
    - apply ge_dj_out; [exact Hpni | lia | lia |].
      intros x Hx. apply ge_img_in. unfold IMG_LO, IMG_HI in *. lia.
    - intros H0. exfalso. exact (H0 eq_refl). }
  pose proof (bytes_at_normalize rsegs memc _ _ RO Bdb) as HD.
  pose proof (bytes_at_normalize rsegs memc _ _ RO Bsb) as HSb.
  pose proof (mem_inv_normalize rsegs memc) as MI0.
  pose proof (asan_cells_normalize memc RO HAC) as HAC'.
  pose proof (A.ShadowRwOnT.shadow_rw_on_normalize Rsh memc RO HSW) as HSW'.
  assert (HHM : HIGHMEM_BEG <= bv_unsigned (getr regs 2) - 4640) by (unfold HIGHMEM_BEG; lia).
  assert (HAE : bv_unsigned (getr regs 2) <= APPMEM_END) by (unfold APPMEM_END; lia).
  pose proof (addressable_normalize memc _ _ RO HAWIN) as AWIN.
  pose proof (addressable_normalize memc _ _ RO Arow) as Af.
  pose proof (addressable_normalize memc _ _ RO Amd0) as Amd.
  pose proof (addressable_normalize memc _ _ RO (proj1 Adb)) as Ad.
  pose proof (addressable_normalize memc _ _ RO Asb) as As.
  assert (APS : app_mem (VAL (A_OBJ A_BOX) + 6) /\ app_mem (VAL (A_OBJ A_BOX) + 7)).
  { unfold app_mem, LOWMEM_END, IMG_LO, IMG_HI in *. split; left; lia. }
  assert (AO : RcEmit.em_E (RcFin.ubat (CROW r) 21) (RcFin.ubat (CROW r) 22) n (RcEmit.em_hid mb) = true ->
     addressable (normalize rsegs memc) p (RcEmit.em_len (RcFin.ubat (CROW r) 21) n) /\
     app_mem (p + RcEmit.em_len (RcFin.ubat (CROW r) 21) n) /\
     (p + RcEmit.em_len (RcFin.ubat (CROW r) 21) n <= RT_LO \/ RT_HI <= p)).
  { intros HE. pose proof (RcEmitLib.em_len_rng _ _ _ _ HE) as RLN.
    destruct (ge_buf_addr B lyc Sc W memc p (RcEmit.em_len (RcFin.ubat (CROW r) 21) n) Hp Hpam Hpni Hpfo
                ltac:(lia)) as (A1 & A2 & A3).
    split; [exact (addressable_normalize memc _ _ RO A1) | exact (conj A2 A3)]. }
  pose proof (fp_normalize _ memc _ _ _ _ _ _ RO HFP) as FP0.
  (* ctrl_emit_as_tls m TP FS lo hi IS MemNormTr.tls_dj m TP (fp_w [0;1] FS ++ [(shadow_addr lo, shadow_addr hi)])
     by conversion (a Theorem Labs lane proved it by eq_refl), so the frozen PA layer's transport serves directly. *)
  pose proof (tls_dj_normalize memc (bv_unsigned (getr regs 4))
                (fp_w [0%nat; 1%nat] FS ++ [(shadow_addr (bv_unsigned (getr regs 2) - 4640),
                                             shadow_addr (bv_unsigned (getr regs 2)))]) RO HFPT
              : ctrl_emit_as_c.ctrl_emit_as_tls (normalize rsegs memc) (bv_unsigned (getr regs 4)) FS
                  (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2))) as FPT.
  pose proof (rng_bytes_RNG_W (w_H W)) as RRB.
  assert (RIMG : ExecF.rng (RNG_W (w_H W)) 0x10000 0x5ee000) by exact (rng_of_visible _ _ _ (img_vis_W W)).
  pose proof (rng_of_visible _ _ _ VWIN) as RWIN.
  pose proof (sh_cov_rng _ _ _ HWSH) as RWSH.
  pose proof (rng_of_visible _ _ _ Vrow) as RROW.
  pose proof (sh_cov_rng _ _ _ Crow) as RROWS.
  pose proof (rng_of_visible _ _ _ Vmd) as RMD.
  pose proof (sh_cov_rng _ _ _ Cmd) as RMDS.
  pose proof (rng_of_visible _ _ _ (proj1 VCdb)) as RDB.
  pose proof (sh_cov_rng _ _ _ (proj2 VCdb)) as RDBS.
  pose proof (rng_of_visible _ _ _ Vsb) as RSB.
  pose proof (sh_cov_rng _ _ _ Csb) as RSBS.
  assert (ROB : RcEmit.em_E (RcFin.ubat (CROW r) 21) (RcFin.ubat (CROW r) 22) n (RcEmit.em_hid mb) = true ->
     ExecF.rng (RNG_W (w_H W)) p (RcEmit.em_len (RcFin.ubat (CROW r) 21) n)).
  { intros HE. pose proof (RcEmitLib.em_len_rng _ _ _ _ HE) as RLN.
    exact (rng_of_visible _ _ _ (proj1 (ge_buf_rw B STK sp0 FP ly S lyc Sc own W memc regs p
             (RcEmit.em_len (RcFin.ubat (CROW r) 21) n) Hp Hpe Hptw ltac:(lia)))). }
  assert (ROBS : RcEmit.em_E (RcFin.ubat (CROW r) 21) (RcFin.ubat (CROW r) 22) n (RcEmit.em_hid mb) = true ->
     forall x y, p <= x -> y <= p + RcEmit.em_len (RcFin.ubat (CROW r) 21) n - 1 ->
       ExecF.rng (RNG_W (w_H W)) (shadow_addr x / 8 * 8) (shadow_addr y / 8 * 8 + 8 - shadow_addr x / 8 * 8)).
  { intros HE. pose proof (RcEmitLib.em_len_rng _ _ _ _ HE) as RLN.
    apply sh_cov_rng. eapply ge_buf_shcov; [exact LAWS | exact HJ | exact Hp | exact Hpe | exact Hpfh | lia]. }
  (* ---- the run on normalize rsegs memc, moved to memc ---- *)
  refine (MemNormF.evtF_normalize_ro _ _ _ _ _ _ _ memc _ RO _).
  apply (ctrl_emit_asF2_on.ctrl_emit_as_pre_lay_F_on (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4)
           (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
           (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
           (getr regs 15) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr (normalize rsegs memc)
           p (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) md d (VAL (A_OBJ A_BOX)) 0 n ns FS
           (CROW r) [] mb nb [] db sb junk (RNG_W (w_H W))).
  all: assumption.
Qed.

End e.
End b.

Print Assumptions ge_pre_on.
