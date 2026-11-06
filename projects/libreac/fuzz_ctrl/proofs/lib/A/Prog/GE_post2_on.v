(* fuzz_ctrl image A, ctrl_emit_as (0x849d8): the second lifted stretch of a Theorem Labs lane's cgif-form glue in its
   route (C) form. NEW file (additive form ruling, auditor a Theorem Labs lane): GE_post2.v is not changed.

   `ge_post2_on` is GE_post2.ge_post2 re-pointed at A/Prog/ctrl_emit_asF2_on.v `ctrl_emit_as_post_lay_F_on`
   (premise aJ_on m5, post aQg_on m5 aWL), at GE_post2's instantiation, with exactly these changes:
     - HFNF is a Theorem Labs lane's ctrl_finish_c.ctrl_finish_contract_F_on (no shadow_rw premise);
     - the premise `shadow_rw m5` is the REGIONAL `A.ShadowRwOn.shadow_rw_on Rsh m5` for a region Rsh (a new
       binder); it moves to normalize rsegs m5 by A.ShadowRwOnT.shadow_rw_on_normalize and is carried, never
       read: the second stretch calls no memset / memcpy, so no shadow span of it is required here.
   GE_post2's helper lemmas (the gp2_ lemmas) are reused from GE_post2.v.

   Memory-checking runtime: before each load or store the code loads a shadow byte at (a >> 3) + 0x7fff8000 and
   compares it; with the range addressable the check passes and the error path is not reached.

   Glue closure rule (two Theorem Labs lanes, 2026-10-28 23:38Z): ctrl_emit_asF2_on and the _on files are Required
   QUALIFIED; ctrl's address-free model files are Required qualified; the six duplicated modules are written
   lib.Reusable.<X>. rule 24: At ossv/recipes c5e779efe8c (2026-10-31), no released proof of ctrl_emit_as outside this unit. *)
(* GEbase is Imported LAST, as in GE_post2.v. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import GE_row GE_img GE_buf GE_post2.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import MemNorm MemNormTr.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ctrl_emit_asF2_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcEmitLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import GEbase.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := AB1v.tfibsegs.
#[local] Notation VAL := (@pa_val _ ctrl_listing PI_ctrl).

(* ctrl_emit_asF2.v's Local Abbreviations at row := CROW r (as G_ctrl_emit_as.v writes them). *)
Local Abbreviation LENr r n := (RcEmit.em_len (RcFin.ubat (CROW r) 21) n).
Local Abbreviation EEr r n mb :=
  (RcEmit.em_E (RcFin.ubat (CROW r) 21) (RcFin.ubat (CROW r) 22) n (RcEmit.em_hid mb)).
Local Abbreviation NMr r mb :=
  ((3 <= RcLay.ly_k (CROW r) <= 9 /\
    (RcLay.ly_bb (RcLay.ly_k (CROW r)) = 5 \/ RcLay.ly_bb (RcLay.ly_k (CROW r)) = 6)) /\
   RcSynth.has mb <> 0 /\ RcSynth.rname mb <> 0).

(* ---- the second stretch on the real returned memory ------------------------------------------------------- *)
Section e.
Variable B : asyms.
Variable GLOBS : list (Z * Z).
Variables RLO RHI : Z.

Lemma ge_post2_on :
  forall (HBRF : reac_braid_encode_ns0_c.reac_braid_encode_ns0_contract_F)
    (HFNF : ctrl_finish_c.ctrl_finish_contract_F_on)
    (LAWS : AR_laws SEGS B)
    (HIMGSH : img_shadow_vis SEGS B)
    (HGM : globs_marked SEGS B GLOBS)
    (HFR_glob : In (VAL (A_OBJ A_FRAMES), 11 * ROW_BYTES) GLOBS)
    (HFR_al : VAL (A_OBJ A_FRAMES) mod 8 = 0)
    (HCAT_glob : In (VAL (A_OBJ A_CAT), 11 * CAT_BYTES) GLOBS)
    (HFR_rng : IMG_LO + 64 <= VAL (A_OBJ A_FRAMES) /\ VAL (A_OBJ A_FRAMES) + 11 * ROW_BYTES + 64 <= IMG_HI)
    (HCAT_rng : IMG_LO + 64 <= VAL (A_OBJ A_CAT) /\ VAL (A_OBJ A_CAT) + 11 * CAT_BYTES + 64 <= IMG_HI)
    (HBOX_rng : IMG_LO + 64 <= VAL (A_OBJ A_BOX) /\ VAL (A_OBJ A_BOX) + 6 + 64 <= IMG_HI)
    (RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (W2 : world SEGS) (m5 : word -> option byte) (regs : bvmap 5 word)
    (FS p md d n r i ns : Z) (mb nb db sb j0 : list byte) (P : word)
    (x1 c0 c1 c2 x8 x9 b0 b1 b2 b3 b4 b5 b6 b7 c3 c4 c5 c6 : word) (Rsh : Z -> Prop),
  (* ---- the run state at the returned memory: the conjuncts of G_ctrl_emit_as.v
          ge_ret W2 m5 regs FS p md d n r mb nb db sb j0 P ns, verbatim and in order, with the regional
          shadow_rw_on Rsh m5 in place of shadow_rw m5 ---- *)
  asan_cells m5 ->
  A.ShadowRwOn.shadow_rw_on Rsh m5 ->
  addressable m5 (bv_unsigned (getr regs 2) - 4640) 4640 ->
  addressable m5 p (LENr r n) ->
  fp [0%nat; 1%nat] m5 (bv_unsigned (getr regs 4)) FS (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2))
    [(bv_unsigned (getr regs 2) - 4640, bv_unsigned (getr regs 2)); (p, p + LENr r n)]
    [(VAL (A_OBJ A_FRAMES) + ROW_BYTES * r, VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + 24); (md, md + 296);
     (d, d + 6); (VAL (A_OBJ A_BOX), VAL (A_OBJ A_BOX) + 6); (p, p + LENr r n)] ->
  ctrl_emit_as_c.ctrl_emit_as_tls m5 (bv_unsigned (getr regs 4)) FS (bv_unsigned (getr regs 2) - 4640)
    (bv_unsigned (getr regs 2)) ->
  stk rsegs m5 (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2) + -128) ->
  ro_agree rsegs m5 ->
  length j0 = 8%nat ->
  rw_cells rsegs m5 (bv_unsigned (getr regs 2) + -128)
    (CB 8 j0 :: C8 P :: C8 (Z_to_bv 64 ns) ::
     [C8 (getr regs 27); C8 (getr regs 26); C8 (getr regs 25); C8 (getr regs 24); C8 (getr regs 23);
      C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
      C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]) ->
  bytes_at rsegs m5 (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) (CROW r) ->
  addressable m5 (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) 24 ->
  rw_cells rsegs m5 p [CB 6 db] ->
  rw_cells rsegs m5 (p + 6) [CB 6 sb] ->
  rw_cells rsegs m5 (p + 12)
    [CB 6 [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned (getr regs 15) mod 65536) mod 256);
           Z_to_bv 8 ((bv_unsigned (getr regs 15) mod 65536) / 256); nth 0 (CROW r) (Z_to_bv 8 0);
           nth 1 (CROW r) (Z_to_bv 8 0)]] ->
  rw_cells rsegs m5 (p + 18)
    [CB 32 (RcLay.ly_lay (RcLay.ly_k (CROW r)) [] (RcLay.ly_Z md mb nb (RcLay.ly_bb (RcLay.ly_k (CROW r)))) 0
              (RcLay.ly_ao (CROW r)) (RcLay.ly_al (CROW r)) [])] ->
  rw_cells rsegs m5 (p + 50) [CB (Z.to_nat (LENr r n - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LENr r n - 52)))] ->
  rw_cells rsegs m5 (p + LENr r n + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] ->
  range_visible (w_H W2) (bv_unsigned (getr regs 2) - 4640) 4640 ->
  sh_cov_vis (w_H W2) (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2) - 1) ->
  range_visible (w_H W2) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) 24 ->
  sh_cov_vis (w_H W2) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + 23) ->
  sh_cov_vis (w_H W2) md (md + 295) ->
  range_visible (w_H W2) p (LENr r n) ->
  sh_cov_vis (w_H W2) p (p + LENr r n - 1) ->
  (* ---- the gate, in the form aAtLay hands over ---- *)
  EEr r n mb = true ->
  (* ---- premises of GE_pre.ge_pre, verbatim (the call's premises and the entry memory's ro_agree) ---- *)
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  3 <= r <= 9 ->
  md = VAL (A_OBJ A_CAT) + CAT_BYTES * i -> 0 <= i < 11 ->
  - 2 ^ 31 <= n < 2 ^ 31 ->
  sp0 - STK <= spZ regs - TEMIT_STK -> spZ regs <= sp0 ->
  0 < p -> p + 1492 <= 2 ^ 47 - 8 -> amem_range p 1492 ->
  (forall x, p <= x < p + 1492 -> ~ in_img SEGS x) ->
  twr_ok (PI := PI_ctrl) B STK sp0 FP ly S lyc Sc own W memc (spZ regs) p 1492 ->
  afobj SEGS B lyc Sc W memc p 1492 ->
  tfr_hull lyc Sc p 1492 ->
  length db = 6%nat ->
  tsrc_ok (PI := PI_ctrl) W memc (spZ regs) d 6 ->
  (p + 1492 <= d \/ d + 6 <= p) ->
  d mod 8 = 0 ->
  length sb = 6%nat ->
  length mb = 296%nat ->
  ((RcLay.ly_bb r = 5 \/ RcLay.ly_bb r = 6) -> RcSynth.has mb <> 0 -> RcSynth.rname mb <> 0 ->
     RcBox.name_ok nb /\
     garr8 SEGS (mrestrict (w_H W) memc) (RcSynth.rname mb) (map bv_unsigned nb) /\
     (exists q sz, In (q, sz) GLOBS /\ q <= RcSynth.rname mb /\ RcSynth.rname mb + Z.of_nat (length nb) <= q + sz) /\
     (forall x, RcSynth.rname mb <= x < RcSynth.rname mb + Z.of_nat (length nb) -> in_roP SEGS RLO RHI x /\
        ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4))) ->
  ro_agree rsegs memc ->
  (* ---- a value fact in the call's premise form, and the world order across the call ---- *)
  - 2 ^ 31 <= ns <= 0 ->
  wle W W2 ->
  ExecF.evtF rsegs (RNG_W (w_H W2))
    (fun s => exists s0,
       ctrl_emit_asF2_on.aQg_on (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 8) (getr regs 9)
         (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
         (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 15)
         lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr
         p (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) md d (VAL (A_OBJ A_BOX)) 0 n FS
         (CROW r) [] mb nb [] db sb Rsh
         (normalize rsegs m5) [(bv_unsigned (getr regs 2) - 4640, bv_unsigned (getr regs 2)); (p, p + LENr r n)]
         s0 /\
       ms_rel rsegs s s0 /\ ro_same rsegs m5 (ms_mem s))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned (getr regs 2) + -128)) (getr regs 3) (getr regs 4) c0 c1 c2 x8 x9
             b0 b1 b2 b3 b4 b5 b6 b7
             (Z_to_bv 64 n) (Z_to_bv 64 (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r)) (Z_to_bv 64 p) (getr regs 15)
             (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 0) (Z_to_bv 64 (VAL (A_OBJ A_BOX)))
             (Z_to_bv 64 (LENr r n)) (Z_to_bv 64 ASAN_K) c3 c4 c5 c6)
        lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x84cf0) lib.Reusable.YK11.fp_csr None m5 (seg_rom SEGS)).
Proof.
  intros HBRF HFNF LAWS HIMGSH HGM HFR_glob HFR_al HCAT_glob HFR_rng HCAT_rng HBOX_rng RELRO_IMG
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k W2 m5 regs FS p md d n r i ns mb nb db sb j0 P
    x1 c0 c1 c2 x8 x9 b0 b1 b2 b3 b4 b5 b6 b7 c3 c4 c5 c6 Rsh
    AC5 SW5 AW5 AO5 FP5 TL5 ST5 RO5 Lj0 FR5 HR5 Af5 P1 P2 P3 P4 P5 P6 VWIN VWSH VROW VROWS VMDS VOB VOBS
    HE HJ Hr Hmd Hi Hn Hslo Hshi Hp Hpe Hpam Hpni Hptw Hpfo Hpfh Hdl Hdsrc Hdp Hd8 Hsl Hml HNB RO Hns Hle.
  pose proof (RcEmitLib.em_len_rng _ _ _ _ HE) as RLN.
  (* ---- the stack window lies above alloc_ceiling, the image below it (GE_pre) ---- *)
  pose proof (ge_win B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs HJ Hslo Hshi) as [_ STK0].
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HK & _).
  destruct HK as (_ & _ & HC & HL & HH & H47 & _).
  pose proof (proj1 (@lib.Reusable.YM05.alloc_ceiling_val rc)) as CV.
  assert (HT : 4640 <= TEMIT_STK) by (unfold TEMIT_STK; lia).
  change (spZ regs) with (bv_unsigned (getr regs 2)) in *.
  assert (CEIL : lib.Reusable.YM05.alloc_ceiling <= bv_unsigned (getr regs 2) - 4640) by lia.
  assert (IMGLO : ImgBounds.IMG_HI <= bv_unsigned (getr regs 2) - 4640) by (unfold ImgBounds.IMG_HI; lia).
  assert (HHM : HIGHMEM_BEG <= bv_unsigned (getr regs 2) - 4640) by (unfold HIGHMEM_BEG; lia).
  pose proof AW5 as (_ & _ & AWE & _).
  (* the buffer lies in a frame of the caller, below alloc_ceiling (GE_pre) *)
  pose proof Hpfh as (cid & pos & Hin & _ & Hflo & Hfhi).
  pose proof (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & FB & _).
  pose proof (Z.div_mod (p + 1492 - 1) 64 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (p + 1492 - 1) 64 ltac:(lia)) as D2.
  assert (PEND : p + 1492 <= lib.Reusable.YM05.alloc_ceiling) by lia.
  clear Hin Hflo Hfhi FB D1 D2.
  pose proof (fp_FS_above_img _ _ _ _ _ _ _ _ FP5) as FSI.
  (* ---- the junk bytes of the output buffer (GE_pre) ---- *)
  destruct (ge_buf_rw B STK sp0 FP ly S lyc Sc own W memc regs p (LENr r n) Hp Hpe Hptw ltac:(lia))
    as (_ & junk & HJK).
  (* ---- the name bytes: image memory ---- *)
  assert (NMI : NMr r mb ->
     RcBox.name_ok nb /\ bytes_at rsegs memc (RcSynth.rname mb) nb /\
     IMG_LO <= RcSynth.rname mb /\ 0 < Z.of_nat (length nb) /\
     RcSynth.rname mb + Z.of_nat (length nb) <= IMG_HI /\
     (forall x, RcSynth.rname mb <= x < RcSynth.rname mb + Z.of_nat (length nb) -> in_img SEGS x) /\
     addressable memc (RcSynth.rname mb) (Z.of_nat (length nb))).
  { intros HNM. apply (ge_row_NM r mb Hr) in HNM. destruct HNM as (HB & Hh & Hn0).
    destruct (HNB HB Hh Hn0) as (Hok & HG & (q & sz & Hq & Hq1 & Hq2) & Hro).
    pose proof Hok as (Hlen & _).
    assert (HI : forall x, RcSynth.rname mb <= x < RcSynth.rname mb + Z.of_nat (length nb) -> in_img SEGS x).
    { intros x Hx. destruct (Hro x Hx) as ([(sg & Hs & _ & Hsr) | Hsr] & _).
      - exists sg. split; [exact Hs | exact Hsr].
      - exact (RELRO_IMG x Hsr). }
    pose proof (ctrl_img_range _ (HI (RcSynth.rname mb) ltac:(lia))) as R1.
    pose proof (ctrl_img_range _ (HI (RcSynth.rname mb + Z.of_nat (length nb) - 1) ltac:(lia))) as R2.
    assert (BLO : IMG_LO <= RcSynth.rname mb) by (unfold IMG_LO; lia).
    assert (BHI : RcSynth.rname mb + Z.of_nat (length nb) <= IMG_HI) by (unfold IMG_HI; lia).
    split; [exact Hok|]. split; [exact (ge_bytes W memc _ _ BLO BHI HG)|].
    split; [exact BLO|]. split; [lia|]. split; [exact BHI|]. split; [exact HI|].
    apply (ge_addr W memc); [exact BLO | lia | exact BHI |].
    exact (ro_usable_glob SEGS B GLOBS lyc Sc W memc mdc q sz _ _ HGM Hq HAR Hq1 Hq2). }
  (* ---- the Section's hypotheses about m := normalize rsegs memc ---- *)
  assert (HST : stk rsegs (normalize rsegs memc) (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2)))
    by exact (stk_normalize_ro memc _ _ RO IMGLO STK0).
  assert (Dsf : RcLay.ly_dj (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2))
                  (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + 24)).
  { unfold RcLay.ly_dj. right. unfold IMG_HI, ROW_BYTES, ImgBounds.IMG_HI in *. lia. }
  assert (Dsn : NMr r mb -> RcLay.ly_dj (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2))
                  (RcSynth.rname mb) (RcSynth.rname mb + Z.of_nat (length nb))).
  { intros HNM. destruct (NMI HNM) as (_ & _ & _ & _ & BHI & _). unfold RcLay.ly_dj. right.
    unfold IMG_HI, ImgBounds.IMG_HI in *. lia. }
  assert (Hf8 : (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) mod 8 = 0).
  { replace (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) with (VAL (A_OBJ A_FRAMES) + (3 * r) * 8)
      by (unfold ROW_BYTES; lia).
    rewrite Z.mod_add by lia. exact HFR_al. }
  assert (Hf24 : VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + 24 <= 2 ^ 64) by (unfold IMG_HI, ROW_BYTES in *; lia).
  assert (Hnm : NMr r mb -> RcBox.name_ok nb /\ bytes_at rsegs (normalize rsegs memc) (RcSynth.rname mb) nb).
  { intros HNM. destruct (NMI HNM) as (Hok & HBn & _). split; [exact Hok|].
    exact (bytes_at_normalize rsegs memc _ _ RO HBn). }
  assert (Ho1492 : p + 1492 <= 2 ^ 64) by lia.
  assert (HEo : EEr r n mb = true ->
     rw_cells rsegs (normalize rsegs memc) p [CB (Z.to_nat (LENr r n)) junk] /\
     RcLay.ly_dj (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2)) p (p + LENr r n) /\
     RcLay.ly_dj p (p + LENr r n) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + 24) /\
     (RcLay.ly_k (CROW r) = 2 ->
        RcLay.ly_dj p (p + LENr r n) (RcLay.ly_tm (CROW r)) (RcLay.ly_tm (CROW r) + 32)) /\
     RcLay.ly_dj p (p + LENr r n) md (md + 296) /\
     (NMr r mb -> RcLay.ly_dj p (p + LENr r n) (RcSynth.rname mb) (RcSynth.rname mb + Z.of_nat (length nb))) /\
     RcLay.ly_dj p (p + LENr r n) d (d + 6) /\
     RcLay.ly_dj p (p + LENr r n) (VAL (A_OBJ A_BOX)) (VAL (A_OBJ A_BOX) + 6) /\
     (0 <> 0 -> RcLay.ly_al (CROW r) <> 0 -> RcLay.ly_dj p (p + LENr r n) 0 (0 + RcLay.ly_al (CROW r)))).
  { intros _.
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
    - apply (gp2_rw_out memc p p _ RO Hpni); [lia | lia | lia | | exact HJK].
      cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. lia.
    - unfold RcLay.ly_dj. right. lia.
    - apply gp2_dj_out; [exact Hpni | lia | lia |].
      intros x Hx. apply gp2_img_in. unfold IMG_LO, IMG_HI, ROW_BYTES in *. lia.
    - intros E2. exact (ge_row_kb2 r _ Hr E2).
    - apply gp2_dj_out; [exact Hpni | lia | lia |].
      intros x Hx. apply gp2_img_in. unfold IMG_LO, IMG_HI, CAT_BYTES in *. lia.
    - intros HNM. destruct (NMI HNM) as (_ & _ & _ & Hl0 & _ & HI & _).
      apply gp2_dj_out; [exact Hpni | lia | exact Hl0 | exact HI].
    - unfold RcLay.ly_dj. lia.
    - apply gp2_dj_out; [exact Hpni | lia | lia |].
      intros x Hx. apply gp2_img_in. unfold IMG_LO, IMG_HI in *. lia.
    - intros H0. exfalso. exact (H0 eq_refl). }
  assert (Af : addressable (normalize rsegs memc) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) 24).
  { apply (addressable_normalize memc _ _ RO). eapply ge_row_addr; eassumption. }
  assert (Amd : addressable (normalize rsegs memc) md 296).
  { apply (addressable_normalize memc _ _ RO). eapply ge_md_addr; eassumption. }
  assert (APD : app_mem (d + 6) /\ app_mem (d + 7)) by (eapply ge_src_app7; eassumption).
  assert (APS : app_mem (VAL (A_OBJ A_BOX) + 6) /\ app_mem (VAL (A_OBJ A_BOX) + 7)).
  { unfold app_mem, LOWMEM_END, IMG_LO, IMG_HI in *. split; left; lia. }
  assert (An : NMr r mb -> addressable (normalize rsegs memc) (RcSynth.rname mb) (Z.of_nat (length nb))).
  { intros HNM. destruct (NMI HNM) as (_ & _ & _ & _ & _ & _ & HAn).
    exact (addressable_normalize memc _ _ RO HAn). }
  assert (AO : EEr r n mb = true ->
     addressable (normalize rsegs memc) p (LENr r n) /\ app_mem (p + LENr r n) /\
     (p + LENr r n <= RT_LO \/ RT_HI <= p)).
  { intros _.
    destruct (ge_buf_addr B lyc Sc W memc p (LENr r n) Hp Hpam Hpni Hpfo ltac:(lia)) as (A1 & A2 & A3).
    split; [exact (addressable_normalize memc _ _ RO A1) | exact (conj A2 A3)]. }
  assert (FPn : NMr r mb ->
     fp_dj [(RcSynth.rname mb, RcSynth.rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS)).
  { intros HNM. destruct (NMI HNM) as (_ & _ & BLO & _ & BHI & _).
    apply gp2_fpw_dj; unfold IMG_LO, IMG_HI, ImgBounds.IMG_HI, ASAN_K in *; lia. }
  (* ---- the footprint at RNG_W (w_H W2) ---- *)
  assert (RNB : NMr r mb -> ExecF.rng (RNG_W (w_H W2)) (RcSynth.rname mb) (Z.of_nat (length nb))).
  { intros HNM. destruct (NMI HNM) as (_ & _ & BLO & _ & BHI & _).
    apply rng_of_visible. apply ge_vis; [exact BLO | lia | exact BHI]. }
  assert (RNBS : NMr r mb -> forall x y, RcSynth.rname mb <= x ->
       y <= RcSynth.rname mb + Z.of_nat (length nb) - 1 ->
       ExecF.rng (RNG_W (w_H W2)) (shadow_addr x / 8 * 8) (shadow_addr y / 8 * 8 + 8 - shadow_addr x / 8 * 8)).
  { intros HNM. destruct (NMI HNM) as (_ & _ & BLO & Hl0 & BHI & _).
    apply sh_cov_rng. apply (gp2_shcov_wle W W2 _ _ Hle).
    exact (gp2_img_shcov B lyc Sc W memc mdc _ _ HIMGSH HAR BLO Hl0 BHI). }
  (* ---- the stretch's premises at normalize rsegs m5 ---- *)
  assert (TLn : ctrl_emit_as_c.ctrl_emit_as_tls (normalize rsegs m5) (bv_unsigned (getr regs 4)) FS
                  (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2))).
  { exact (tls_dj_normalize m5 (bv_unsigned (getr regs 4))
             (fp_w [0%nat; 1%nat] FS ++ [(shadow_addr (bv_unsigned (getr regs 2) - 4640),
                                          shadow_addr (bv_unsigned (getr regs 2)))]) RO5 TL5). }
  assert (AJ : ctrl_emit_asF2_on.aJ_on (getr regs 2) (getr regs 4) p (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) md d
                 (VAL (A_OBJ A_BOX)) n FS (CROW r) Rsh (normalize rsegs m5)).
  { exact (conj (asan_cells_normalize m5 RO5 AC5) (conj (A.ShadowRwOnT.shadow_rw_on_normalize Rsh m5 RO5 SW5)
            (conj (addressable_normalize m5 _ _ RO5 AW5) (conj (addressable_normalize m5 _ _ RO5 AO5)
            (conj (fp_normalize _ m5 _ _ _ _ _ _ RO5 FP5) TLn))))). }
  assert (STn : stk rsegs (normalize rsegs m5) (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2) + -128))
    by exact (stk_normalize_ro m5 _ _ RO5 IMGLO ST5).
  assert (FRn : rw_cells rsegs (normalize rsegs m5) (bv_unsigned (getr regs 2) + -128)
    (CB 8 j0 :: C8 P :: C8 (Z_to_bv 64 ns) ::
     [C8 (getr regs 27); C8 (getr regs 26); C8 (getr regs 25); C8 (getr regs 24); C8 (getr regs 23);
      C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
      C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)])).
  { apply (rw_cells_normalize m5 _ _ RO5); [|exact FR5].
    intros j Hj. cbn [cells_size csize Nat.add] in Hj.
    apply ro_addr_above_img. unfold ImgBounds.IMG_HI, APPMEM_END in *. lia. }
  assert (P1n : rw_cells rsegs (normalize rsegs m5) p [CB 6 db]).
  { apply (gp2_rw_out m5 p p _ RO5 Hpni); [lia | lia | lia | cbn [cells_size csize]; lia | exact P1]. }
  assert (P2n : rw_cells rsegs (normalize rsegs m5) (p + 6) [CB 6 sb]).
  { apply (gp2_rw_out m5 p _ _ RO5 Hpni); [lia | lia | lia | cbn [cells_size csize]; lia | exact P2]. }
  match type of P3 with rw_cells _ _ ?q ?cs => assert (P3n : rw_cells rsegs (normalize rsegs m5) q cs) end.
  { apply (gp2_rw_out m5 p _ _ RO5 Hpni); [lia | lia | lia | cbn [cells_size csize]; lia | exact P3]. }
  match type of P4 with rw_cells _ _ ?q ?cs => assert (P4n : rw_cells rsegs (normalize rsegs m5) q cs) end.
  { apply (gp2_rw_out m5 p _ _ RO5 Hpni); [lia | lia | lia | cbn [cells_size csize]; lia | exact P4]. }
  match type of P5 with rw_cells _ _ ?q ?cs => assert (P5n : rw_cells rsegs (normalize rsegs m5) q cs) end.
  { apply (gp2_rw_out m5 p _ _ RO5 Hpni); [lia | lia | lia | | exact P5].
    cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. lia. }
  match type of P6 with rw_cells _ _ ?q ?cs => assert (P6n : rw_cells rsegs (normalize rsegs m5) q cs) end.
  { apply (gp2_rw_out m5 p _ _ RO5 Hpni); [lia | lia | lia | cbn [cells_size csize]; lia | exact P6]. }
  (* ---- the rest of the stretch's premises, as GE_post2 passes them ---- *)
  pose proof (ge_row_len r) as Hrl. pose proof (ge_row_Hc r) as Hc. pose proof (ge_row_HA r) as HA.
  pose proof (ge_row_Hc2 r) as Hc2.
  assert (Hns' : - 2 ^ 31 <= ns < 2 ^ 31) by lia.
  assert (Hg : 0 <= 0 < 2 ^ 64) by lia.
  assert (Hns0 : RcFin.ubat (CROW r) 23 = 1 -> ns <= 0) by (intros _; lia).
  pose proof (rng_of_visible _ _ _ (img_vis_W W2)) as RIMG.
  pose proof (rng_of_visible _ _ _ VWIN) as RWIN.
  pose proof (rng_of_visible _ _ _ VROW) as RROW.
  pose proof (sh_cov_rng _ _ _ VROWS) as RROWS.
  pose proof (sh_cov_rng _ _ _ VMDS) as RMDS.
  assert (ROB : EEr r n mb = true -> ExecF.rng (RNG_W (w_H W2)) p (LENr r n))
    by (intros _; exact (rng_of_visible _ _ _ VOB)).
  assert (ROBS : EEr r n mb = true -> forall x y, p <= x -> y <= p + LENr r n - 1 ->
     ExecF.rng (RNG_W (w_H W2)) (shadow_addr x / 8 * 8) (shadow_addr y / 8 * 8 + 8 - shadow_addr x / 8 * 8))
    by (intros _; exact (sh_cov_rng _ _ _ VOBS)).
  pose proof (mem_inv_normalize rsegs m5) as MI5.
  pose proof (bytes_at_normalize rsegs m5 _ _ RO5 HR5) as HR5n.
  pose proof (addressable_normalize m5 _ _ RO5 Af5) as Af5n.
  (* ---- the stretch's run on normalize rsegs m5, moved to m5 ---- *)
  refine (MemNormF.evtF_normalize_ro _ _ _ _ _ _ _ m5 _ RO5 _).
  eapply (ctrl_emit_asF2_on.ctrl_emit_as_post_lay_F_on (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4)
           (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
           (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
           (getr regs 15) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr (normalize rsegs memc)
           p (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) md d (VAL (A_OBJ A_BOX)) 0 n ns FS
           (CROW r) [] mb nb [] db sb junk (RNG_W (w_H W2))).
  all: first [eassumption | lia].
Qed.

End e.
End b.

Print Assumptions ge_post2_on.
