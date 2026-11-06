(* fuzz_ctrl image A (libreac v1.9.0), ctrl_emit_as (0x849d8): the top-level cgif-form glue of a Theorem Labs lane, ROUTE (C).
   NEW file (additive form ruling, auditor a Theorem Labs lane): G_ctrl_emit_as.v is not changed, and its lemmas that
   do not mention shadow_rw are reused from it (Required).

   `pb_ctrl_emit_as_on` proves `pb_ctrl_emit_as_stmt_on B GLOBS RLO RHI`, which is C_ctrl_emit_as.v's
   pb_ctrl_emit_as_stmt with exactly three binder types changed:
     HMSF : asan_memset_cF_on.asan_memset_contract_F_on    (a Theorem Labs lane; asan_memsetF_on.v)
     HMCF : asan_memcpy_cF_on.asan_memcpy_contract_F_on    (a Theorem Labs lane; asan_memcpyF_on.v)
     HFNF : ctrl_finish_c.ctrl_finish_contract_F_on        (a Theorem Labs lane; ctrl_finish_c.v:162)
   (HBRF, TLAY, every other binder and the spec tctrl_emit_as_spec unchanged).

   Hypotheses of pb_ctrl_emit_as_on beyond the statement's binders:
     HTS  : A.AF0m.CtrlTSyms B                   the bundle is ctrl's (AF0m.v:293); no binder of the statement gives it.
     HRLO : RLO = PA_RLO,  HRHI : RHI = PA_RHI    TLAY is stated at PI_ctrl's read-only bounds, the spec at RLO / RHI.
   NO visible-zero-shadow premise: G_ctrl_emit_as.pb_ctrl_emit_as takes ProgWorld's core fact of that name only for
   the UNIVERSAL shadow_rw (A.ProgWorldCtlRt's run-state lemma). Here the run state comes from GE_rtC.ge_rtC_jrnl
   (A.ProgWorldCtlRtC.ctl_rt_C_of_AR, no such premise): ro_agree, asan_cells and the REGIONAL shadow_rw_on (ge_Rsh B ly S) at the call memory and at the memory
   ctrl_lay_block returns, ge_Rsh B ly S := cut_shadow B ly S \/ img_shadow. The first stretch (GE_pre_on.ge_pre_on)
   needs the region to hold the shadow spans its helper calls read; GE_rtC.ge_rsh_cov proves it from the spec's two
   frame premises and HBOX_rng. The second stretch (GE_post2_on.ge_post2_on) only carries the region.

   The composition is G_ctrl_emit_as.v's Parts 4-6 with: the call's run state from ge_rtC_jrnl in place of
   ProgWorldCtlRt's run-state lemma; ge_pre / ge_post2 replaced by ge_pre_on / ge_post2_on; ge_ret / ge_stretch2 / gc_ret / gc_stretch2
   replaced by ge_ret_on / ge_stretch2_on / gc_ret_on / gc_stretch2_on (their shadow parts only); aMid by aMid_on.

   The PROVED ProgWorld statements are cited by name, never taken as binders: ctl_rt_C_of_AR (via GE_rtC),
   ProgWorldShadow.ctl_stack_shadow_of_AR, ProgWorld_Fs.ctl_fp_of_AR, ProgWorld.as_tp_RT_TP (and AF0m.ts_tsd).

   Memory-checking runtime: before each load or store the code loads a shadow byte at (a >> 3) + 0x7fff8000 and
   compares it; with the range addressable the check passes and the error path is not reached.

   Glue closure rule (two Theorem Labs lanes): the _F / _cF / _on files are Required qualified only; the six duplicated
   modules (YI04 YI16 YK11 YK1b YM05 YO09) are written lib.Reusable.<X>. rule 24: At ossv/recipes c5e779efe8c (2026-10-31), no released proof of ctrl_emit_as outside this unit. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import GEbase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import GE_row GE_img GE_buf GE_jrnl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorldVisWin ACtlK ProgWorld ProgWorld_Fs
ProgWorldShadow ProgWorldOwnedRo.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcEmitLib RcSynthLib RcFinLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import G_ctrl_emit_as GE_rtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ctrl_emit_asF2_on asan_memset_cF_on asan_memcpy_cF_on
sh_word_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope Z_scope.

(* ===================================================================================================== *)
(* Part A. The statement, and the statements of the run state at the returned memory (route (C)).       *)
(* ===================================================================================================== *)
Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := AB1v.tfibsegs.
#[local] Notation VAL := (@pa_val _ ctrl_listing PI_ctrl).
#[local] Notation BASE := (@pa_val _ ctrl_listing PI_ctrl A_TEXT).
#[local] Notation PA_RLO := (@pa_relro_lo _ ctrl_listing PI_ctrl).
#[local] Notation PA_RHI := (@pa_relro_hi _ ctrl_listing PI_ctrl).

(* ctrl_emit_asF2.v's Local Abbreviations at row := CROW r, g := 0 (as GE_post.v writes them). *)
Local Abbreviation EEr r n mb :=
  (RcEmit.em_E (RcFin.ubat (CROW r) 21) (RcFin.ubat (CROW r) 22) n (RcEmit.em_hid mb)).
Local Abbreviation LENr r n := (RcEmit.em_len (RcFin.ubat (CROW r) 21) n).
Local Abbreviation RRr r n mb := (if EEr r n mb then LENr r n else 0).
Local Abbreviation BLKr r md mb nb tb gb :=
  (RcFin.fin (RcFin.ubat (CROW r) 20) (RcFin.ubat (CROW r) 18) (RcFin.ubat (CROW r) 19)
     (RcLay.ly_lay (RcLay.ly_k (CROW r)) tb (RcLay.ly_Z md mb nb (RcLay.ly_bb (RcLay.ly_k (CROW r)))) 0
        (RcLay.ly_ao (CROW r)) (RcLay.ly_al (CROW r)) gb)).

Section e.
Variable B : asyms.
Variable GLOBS : list (Z * Z).
Variables RLO RHI : Z.

(* C_ctrl_emit_as.v pb_ctrl_emit_as_stmt with exactly the binder types of HMSF, HMCF and HFNF changed to their
   route (C) contracts; the spec is C_ctrl_emit_as.v's tctrl_emit_as_spec. *)
Definition pb_ctrl_emit_as_stmt_on : Prop :=
  forall (TL : PALib (PI := PI_ctrl) B) (LAWS : AR_laws SEGS B) (ML : model_laws (as_universe B))
    (HMSF : asan_memset_cF_on.asan_memset_contract_F_on)
    (HMCF : asan_memcpy_cF_on.asan_memcpy_contract_F_on)
    (HBRF : reac_braid_encode_ns0_c.reac_braid_encode_ns0_contract_F)
    (HFNF : ctrl_finish_c.ctrl_finish_contract_F_on)
    (TLAY : tctrl_lay_block_spec (SK := SK) B GLOBS (BASE + AF_ctrl_lay_block) PA_RLO PA_RHI)
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
    (RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a),
  tctrl_emit_as_spec (SK := SK) B GLOBS (BASE + AF_ctrl_emit_as) RLO RHI.

(* ---- G_ctrl_emit_as.v ge_ret with the REGIONAL shadow_rw_on R m5 in place of shadow_rw m5; every other conjunct
   verbatim and in order (the run state at the memory ctrl_lay_block returns). ---- *)
Definition ge_ret_on (R : Z -> Prop) (W2 : world SEGS) (m5 : word -> option byte) (regs : bvmap 5 word)
    (FS p md d n r : Z) (mb nb db sb j0 : list byte) (P : word) (ns : Z) : Prop :=
  asan_cells m5 /\ A.ShadowRwOn.shadow_rw_on R m5 /\
  addressable m5 (bv_unsigned (getr regs 2) - 4640) 4640 /\
  addressable m5 p (LENr r n) /\
  fp [0%nat; 1%nat] m5 (bv_unsigned (getr regs 4)) FS (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2))
    [(bv_unsigned (getr regs 2) - 4640, bv_unsigned (getr regs 2)); (p, p + LENr r n)]
    [(VAL (A_OBJ A_FRAMES) + ROW_BYTES * r, VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + 24); (md, md + 296);
     (d, d + 6); (VAL (A_OBJ A_BOX), VAL (A_OBJ A_BOX) + 6); (p, p + LENr r n)] /\
  ctrl_emit_as_c.ctrl_emit_as_tls m5 (bv_unsigned (getr regs 4)) FS (bv_unsigned (getr regs 2) - 4640)
    (bv_unsigned (getr regs 2)) /\
  stk rsegs m5 (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2) + -128) /\
  ro_agree rsegs m5 /\
  length j0 = 8%nat /\
  rw_cells rsegs m5 (bv_unsigned (getr regs 2) + -128)
    (CB 8 j0 :: C8 P :: C8 (Z_to_bv 64 ns) ::
     [C8 (getr regs 27); C8 (getr regs 26); C8 (getr regs 25); C8 (getr regs 24); C8 (getr regs 23);
      C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
      C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]) /\
  bytes_at rsegs m5 (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) (CROW r) /\
  addressable m5 (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) 24 /\
  rw_cells rsegs m5 p [CB 6 db] /\ rw_cells rsegs m5 (p + 6) [CB 6 sb] /\
  rw_cells rsegs m5 (p + 12)
    [CB 6 [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned (getr regs 15) mod 65536) mod 256);
           Z_to_bv 8 ((bv_unsigned (getr regs 15) mod 65536) / 256); nth 0 (CROW r) (Z_to_bv 8 0);
           nth 1 (CROW r) (Z_to_bv 8 0)]] /\
  rw_cells rsegs m5 (p + 18)
    [CB 32 (RcLay.ly_lay (RcLay.ly_k (CROW r)) [] (RcLay.ly_Z md mb nb (RcLay.ly_bb (RcLay.ly_k (CROW r)))) 0
              (RcLay.ly_ao (CROW r)) (RcLay.ly_al (CROW r)) [])] /\
  rw_cells rsegs m5 (p + 50) [CB (Z.to_nat (LENr r n - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LENr r n - 52)))] /\
  rw_cells rsegs m5 (p + LENr r n + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] /\
  range_visible (w_H W2) (bv_unsigned (getr regs 2) - 4640) 4640 /\
  sh_cov_vis (w_H W2) (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2) - 1) /\
  range_visible (w_H W2) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) 24 /\
  sh_cov_vis (w_H W2) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + 23) /\
  sh_cov_vis (w_H W2) md (md + 295) /\
  range_visible (w_H W2) p (LENr r n) /\ sh_cov_vis (w_H W2) p (p + LENr r n - 1).

(* ---- G_ctrl_emit_as.v ge_stretch2 with HFNF the route (C) ctrl_finish_c.ctrl_finish_contract_F_on, without the
   call memory's shadow_rw premise (gc_stretch2 never reads it), and with the run state ge_ret_on R (a region R, a
   new binder) at the returned memory. Part 6 proves it (gc_stretch2_on) from GE_post2_on.ge_post2_on. ---- *)
Definition ge_stretch2_on : Prop :=
  forall (HBRF : reac_braid_encode_ns0_c.reac_braid_encode_ns0_contract_F)
    (HFNF : ctrl_finish_c.ctrl_finish_contract_F_on)
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
    (p md d c16 n r i ns : Z) (mb nb db sb : list byte)
    (mc : word -> option byte) (W2 : world SEGS) ly2 S2 (regs2 : bvmap 5 word) (mem2 : word -> option byte)
    (md2 : Model) (j0 : list byte) (P : word) (R : Z -> Prop),
  (* the call's premises (tctrl_emit_as_spec, word for word) *)
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc) ->
  lib.Reusable.YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 p ->
  getr regs 11 = w64 (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) -> 3 <= r <= 9 ->
  getr regs 12 = w64 md -> md = VAL (A_OBJ A_CAT) + CAT_BYTES * i -> 0 <= i < 11 ->
  getr regs 13 = w64 d ->
  getr regs 14 = w64 (VAL (A_OBJ A_BOX)) ->
  getr regs 15 = w64 c16 -> 0 <= c16 < 2 ^ 64 ->
  getr regs 16 = w64 n -> - 2 ^ 31 <= n < 2 ^ 31 ->
  getr regs 17 = w64 0 ->
  getr regs 29 = w64 ns -> - 2 ^ 31 <= ns <= 0 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TEMIT_STK -> spZ regs <= sp0 ->
  count_cid 1 (frames Sc) < fs_frames 1 -> count_cid 0 (frames Sc) < fs_frames 0 ->
  0 < p -> p mod 8 = 0 -> p + 1492 <= 2 ^ 47 - 8 -> amem_range p 1492 ->
  (forall x, p <= x < p + 1492 -> ~ in_img SEGS x) ->
  twr_ok (PI := PI_ctrl) B STK sp0 FP ly S lyc Sc own W memc (spZ regs) p 1492 ->
  afobj SEGS B lyc Sc W memc p 1492 ->
  (exists cid pos, In (cid, pos) (frames Sc) /\ 2 <= cid /\ frame_addr lyc cid pos <= p /\
                   p + 1492 <= frame_addr lyc cid pos + fs_frame_bytes cid) ->
  (exists cid pos, In (cid, pos) (frames Sc) /\ 2 <= cid /\ frame_addr lyc cid pos <= d /\
                   d + 6 <= frame_addr lyc cid pos + fs_frame_bytes cid) ->
  tfr_hull lyc Sc p 1492 ->
  length db = 6%nat -> garr8 SEGS (mrestrict (w_H W) memc) d (map bv_unsigned db) ->
  tsrc_ok (PI := PI_ctrl) W memc (spZ regs) d 6 -> (forall x, d <= x < d + 6 -> ~ in_img SEGS x) ->
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
  (* the run state at the call memory, as ge_pre takes it (FS := the layout's side stack), less shadow_rw *)
  ro_agree rsegs memc -> asan_cells memc ->
  addressable memc (spZ regs - 4640) 4640 ->
  fp [0%nat; 1%nat] memc (bv_unsigned (getr regs 4)) (ly_F lyc) (spZ regs - 4640) (spZ regs)
    [(spZ regs - 4640, spZ regs); (p, p + RRr r n mb)]
    [(VAL (A_OBJ A_FRAMES) + ROW_BYTES * r, VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + 24); (md, md + 296);
     (d, d + 6); (VAL (A_OBJ A_BOX), VAL (A_OBJ A_BOX) + 6); (p, p + RRr r n mb)] ->
  ctrl_emit_as_c.ctrl_emit_as_tls memc (bv_unsigned (getr regs 4)) (ly_F lyc) (spZ regs - 4640) (spZ regs) ->
  sh_cov_vis (w_H W) (spZ regs - 4640) (spZ regs - 1) ->
  (* the first stretch reached the call site: the gate is open and the memory changed only in its writes *)
  EEr r n mb = true ->
  munch [(spZ regs - 4640, spZ regs); (p, p + LENr r n)] memc mc -> wmono rsegs memc mc ->
  (* ctrl_lay_block's post at the return *)
  wle W W2 ->
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_LAY) ->
  frames S2 = frames Sc -> ablocks B ly2 S2 = ablocks B lyc Sc ->
  tcj_kept (PI := PI_ctrl) B TLAY_STK lyc Sc W mc W2 mem2 (spZ regs + -128) (fun a => p + 18 <= a < p + 50) ->
  (* the register map at the return point: the callee-saved registers of the call site *)
  getr regs2 2 = Z_to_bv 64 (spZ regs + -128) -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 18 = Z_to_bv 64 n -> getr regs2 19 = Z_to_bv 64 (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) ->
  getr regs2 20 = Z_to_bv 64 p -> getr regs2 21 = getr regs 15 -> getr regs2 22 = Z_to_bv 64 md ->
  getr regs2 23 = Z_to_bv 64 d -> getr regs2 24 = Z_to_bv 64 0 -> getr regs2 25 = Z_to_bv 64 (VAL (A_OBJ A_BOX)) ->
  getr regs2 26 = Z_to_bv 64 (LENr r n) -> getr regs2 27 = Z_to_bv 64 ASAN_K ->
  (* the run state at the returned memory, with the region R *)
  ge_ret_on R W2 mem2 regs (ly_F lyc) p md d n r mb nb db sb j0 P ns ->
  SRr SEGS W2 (mkCfg (lib.Reusable.YK11.mkst regs2 (Z_to_bv 64 0x84cf0) mem2 (seg_rom SEGS)) md2)
    (tctrl_emit_as_post (SK := SK) B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p md c16 n r mb nb db sb).

End e.

End b.

(* ===================================================================================================== *)
(* Part 5. The run state at the memory ctrl_lay_block returns, from a Theorem Labs lane's post and ProgWorld.        *)
(* ===================================================================================================== *)
Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := AB1v.tfibsegs.
#[local] Notation VAL := (@pa_val _ ctrl_listing PI_ctrl).
Local Abbreviation LENr r n := (RcEmit.em_len (RcFin.ubat (CROW r) 21) n).
Local Abbreviation EEr r n mb :=
  (RcEmit.em_E (RcFin.ubat (CROW r) 21) (RcFin.ubat (CROW r) 22) n (RcEmit.em_hid mb)).
Section e.
Variable B : asyms.
Variable GLOBS : list (Z * Z).
Variables RLO RHI : Z.

(* rule 24: no function proved. A world / memory helper of the glue of ctrl_emit_as (image A): the run state
   `ge_ret` at the memory ctrl_lay_block returns, from the call's premises, the first stretch's writes and
   ctrl_lay_block's post. *)

(* G_ctrl_emit_as.v gc_ret without its three run-state binders (HRT and the two ProgWorld core facts): the run state at the returned memory comes from
   GE_rtC.ge_rtC_jrnl on TLAY's post journal (route (C)); its shadow conjunct is shadow_rw_on (ge_Rsh B ly2 S2). *)
Lemma gc_ret_on :
  forall (HTS : A.AF0m.CtrlTSyms B)
    (LAWS : AR_laws SEGS B)
    (HIMGSH : img_shadow_vis SEGS B)
    (HGM : globs_marked SEGS B GLOBS) (HFR_glob : In (VAL (A_OBJ A_FRAMES), 11 * ROW_BYTES) GLOBS)
    (HROWS : forall r, 3 <= r <= 9 -> forall (H : word -> bool) mem,
       arodata_okS SEGS B RLO RHI (aview SEGS H mem) ->
       garr8 SEGS (mrestrict H mem) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) (map bv_unsigned (CROW r)))
    (HFR_rng : IMG_LO + 64 <= VAL (A_OBJ A_FRAMES) /\ VAL (A_OBJ A_FRAMES) + 11 * ROW_BYTES + 64 <= IMG_HI)
    (HCAT_rng : IMG_LO + 64 <= VAL (A_OBJ A_CAT) /\ VAL (A_OBJ A_CAT) + 11 * CAT_BYTES + 64 <= IMG_HI)
    (HBOX_rng : IMG_LO + 64 <= VAL (A_OBJ A_BOX) /\ VAL (A_OBJ A_BOX) + 6 + 64 <= IMG_HI)
    (RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k (regs : bvmap 5 word)
    (p md d n r i ns : Z) (mb nb db sb : list byte)
    (mc : word -> option byte) (W2 : world SEGS) ly2 S2 (mem2 : word -> option byte) (md2 : Model)
    (j0 : list byte) (P : word),
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc) ->
  getr regs 4 = w64 (as_tp B) ->
  3 <= r <= 9 -> md = VAL (A_OBJ A_CAT) + CAT_BYTES * i -> 0 <= i < 11 ->
  sp0 - STK <= spZ regs - TEMIT_STK -> spZ regs <= sp0 -> spZ regs mod 16 = 0 ->
  0 < p -> p + 1492 <= 2 ^ 47 - 8 -> amem_range p 1492 ->
  (forall x, p <= x < p + 1492 -> ~ in_img SEGS x) ->
  twr_ok (PI := PI_ctrl) B STK sp0 FP ly S lyc Sc own W memc (spZ regs) p 1492 ->
  afobj SEGS B lyc Sc W memc p 1492 ->
  (exists cid pos, In (cid, pos) (frames Sc) /\ 2 <= cid /\ frame_addr lyc cid pos <= p /\
                   p + 1492 <= frame_addr lyc cid pos + fs_frame_bytes cid) ->
  (exists cid pos, In (cid, pos) (frames Sc) /\ 2 <= cid /\ frame_addr lyc cid pos <= d /\
                   d + 6 <= frame_addr lyc cid pos + fs_frame_bytes cid) ->
  tfr_hull lyc Sc p 1492 ->
  length mb = 296%nat ->
  EEr r n mb = true ->
  (* the call site 0x84cec, on the real memory mc *)
  munch [(spZ regs - 4640, spZ regs); (p, p + LENr r n)] memc mc -> wmono rsegs memc mc ->
  length j0 = 8%nat ->
  rw_cells rsegs mc (spZ regs + -128)
    (CB 8 j0 :: C8 P :: C8 (Z_to_bv 64 ns) ::
     [C8 (getr regs 27); C8 (getr regs 26); C8 (getr regs 25); C8 (getr regs 24); C8 (getr regs 23);
      C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
      C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]) ->
  rw_cells rsegs mc p [CB 6 db] -> rw_cells rsegs mc (p + 6) [CB 6 sb] ->
  rw_cells rsegs mc (p + 12)
    [CB 6 [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned (getr regs 15) mod 65536) mod 256);
           Z_to_bv 8 ((bv_unsigned (getr regs 15) mod 65536) / 256); nth 0 (CROW r) (Z_to_bv 8 0);
           nth 1 (CROW r) (Z_to_bv 8 0)]] ->
  rw_cells rsegs mc (p + 50) [CB (Z.to_nat (LENr r n - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LENr r n - 52)))] ->
  rw_cells rsegs mc (p + LENr r n + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] ->
  addressable mc p (LENr r n) ->
  (* ctrl_lay_block's post (a Theorem Labs lane's tctrl_lay_block_post conjuncts) *)
  wle W W2 ->
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_LAY) ->
  frames S2 = frames Sc ->
  garr8 SEGS (mrestrict (w_H W2) mem2) (p + 18) (C_reac_box_model_block.bmb_z (RcLay.ly_Z md mb nb (RcLay.ly_bb r))) ->
  tcj_kept (PI := PI_ctrl) B TLAY_STK lyc Sc W mc W2 mem2 (spZ regs + -128) (fun a => p + 18 <= a < p + 50) ->
  ge_ret_on (ge_Rsh B ly2 S2) W2 mem2 regs (ly_F lyc) p md d n r mb nb db sb j0 P ns.
Proof.
  intros HTS LAWS HIMGSH HGM HFR_glob HROWS HFR_rng HCAT_rng HBOX_rng RELRO_IMG
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p md d n r i ns mb nb db sb mc W2 ly2 S2 mem2 md2
    j0 P HJ HRO Htp Hr Hmd Hi Hslo Hshi Hsp16 Hp Hpe Hpam Hpni Hptw Hpfo HPC HDC Hpfh Hmbl HE
    MUc WMc Lj0 FRc P1 P2 P3 P5 P6 AOc Hle HJ2 FR2 GA KEPT.
  (* the PROVED ProgWorld statements, cited by name (L3 rule, a Theorem Labs lane 13:12Z), not taken as binders *)
  pose proof (A.ProgWorldShadow.ctl_stack_shadow_of_AR B : ge_stack_shadow_stmt B) as HSS.
  assert (HFP : ge_fp_stmt B) by (intros L; exact (A.ProgWorld_Fs.ctl_fp_of_AR B HTS L)).
  pose proof (A.ProgWorld.as_tp_RT_TP B HTS) as HTP.
  assert (HTSD : as_tsd B = 0x5fcbb8) by (rewrite (A.AF0m.ts_tsd B HTS); vm_compute; reflexivity).
  (* ---- the two journals: AR, the layout, the presence clause, the stack bounds ---- *)
  pose proof HJ as (HAR & HLE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & HSTK & _).
  destruct HSTK as (_ & _ & HCEIL & HSLO & HSHI & H47 & _).
  destruct HLE as (_ & _ & _ & _ & _ & ECF & _ & _ & _ & EClo & EChi & _).
  pose proof HJ2 as (HAR2 & HLE2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES2 & _).
  destruct HLE2 as (_ & _ & _ & _ & _ & E2F & _ & _ & _ & E2lo & E2hi & _).
  pose proof asan_consts as (CV & _ & _ & _ & _).
  assert (HT : TEMIT_STK = 4640) by reflexivity.
  pose proof (RcEmitLib.em_len_rng _ _ _ _ HE) as RLE.
  destruct KEPT as (K1 & K2 & K3 & K4 & K5 & K6).
  (* ---- the read-only data at (W, mc) and at (W2, mem2) ---- *)
  assert (IMGO : forall a, in_img SEGS a -> outside [(spZ regs - 4640, spZ regs); (p, p + LENr r n)] a).
  { intros a Hia. pose proof (ctrl_segs_low a Hia) as Hlow. cbn [outside].
    split; [unfold kLowMemEnd in Hlow; lia | split; [intros Ha; apply (Hpni a); [lia | exact Hia] | exact I]]. }
  assert (HROc : arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) mc))
    by exact (ge_ro_keep B (w_H W) RLO RHI memc mc _ RELRO_IMG HRO MUc IMGO).
  assert (HRO2 : arodata_okS SEGS B RLO RHI (aview SEGS (w_H W2) mem2))
    by exact (gc_ro_view B W W2 mc mem2 RLO RHI RELRO_IMG HROc K3).
  destruct (ge_rtC_jrnl (SK := SK) B HTS LAWS RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HRO2) as (RRO & RAC & RSW).
  (* ---- the frames ---- *)
  assert (Htp' : bv_unsigned (getr regs 4) = RT_TP).
  { rewrite Htp, HTP. unfold w64. apply gc_u64. unfold RT_TP. lia. }
  pose proof HPC as (cid & pos & HinP & Hc2 & HfaP & HfeP).
  pose proof HDC as (cid' & pos' & HinD & Hc2' & HfaD & HfeD).
  assert (EFA : forall c q, frame_addr ly2 c q = frame_addr lyc c q).
  { intros c q. unfold frame_addr. rewrite E2F, ECF. reflexivity. }
  pose proof Hpfh as (ch & ph & Hinh & _ & Hh1 & Hh2).
  destruct (al_frames _ _ LAWS lyc Sc W memc mdc ch ph HAR Hinh) as (Hal & _ & _ & Hshpres).
  (* ---- the output cells other than the laid block ---- *)
  assert (OUT : forall a cs, rw_cells rsegs mc a cs ->
     p <= a -> a + Z.of_nat (cells_size cs) <= p + LENr r n ->
     (a + Z.of_nat (cells_size cs) <= p + 18 \/ p + 50 <= a) ->
     rw_cells rsegs mem2 a cs).
  { intros a cs Hc Ha1 Ha2 Ha3. apply (gc_rw_view W W2 mc mem2 a cs Hc).
    intros j Hj.
    assert (Hx : p <= a + j < p + 1492) by lia.
    destruct (Hptw (a + j) Hx) as (_ & (Hh0 & _) & _ & _).
    assert (Hh : w_H W (Z_to_bv 64 (a + j)) = false) by exact Hh0.
    split; [apply Hpni; exact Hx|].
    split; [exact Hh|].
    split.
    - destruct (w_H W2 (Z_to_bv 64 (a + j))) eqn:E; [|reflexivity].
      rewrite (Hle _ E) in Hh. discriminate.
    - apply (K4 cid pos); [exact HinP | left; unfold in_zr, frame_rng; cbn [fst snd]; lia | cbv beta; lia]. }
  unfold ge_ret_on. change (bv_unsigned (getr regs 2)) with (spZ regs).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))))))))))))))).
  - (* asan_cells *) exact RAC.
  - (* shadow_rw *) exact RSW.
  - (* the window addressable *)
    apply (HSS LAWS ly2 S2 W2 mem2 md2); [exact HAR2 | lia | lia | lia].
  - (* the output addressable *)
    apply (gc_addr_view W W2 mc mem2 p (LENr r n) AOc).
    intros j Hj.
    pose proof (gcr_sh_in (frame_addr lyc ch ph) (fs_frame_bytes ch) p 1492 (p + j) Hal Hh1 Hh2 ltac:(lia))
      as Hs.
    destruct (Hshpres _ Hs) as ((Hh & _) & _).
    replace (YG0f.shadow_addr (frame_addr lyc ch ph) +
             (AsanRT.shadow_addr (p + j) - YG0f.shadow_addr (frame_addr lyc ch ph)))
      with (AsanRT.shadow_addr (p + j)) in Hh by lia.
    split; [exact Hh|]. split.
    + destruct (w_H W2 (Z_to_bv 64 (AsanRT.shadow_addr (p + j)))) eqn:E; [|reflexivity].
      rewrite (Hle _ E) in Hh. discriminate.
    + apply (K4 ch ph); [exact Hinh | right; unfold in_zr; cbn [fst snd]; lia | cbv beta].
      exact (gcr_sh_out p 1492 (p + j) ltac:(lia) ltac:(lia) Hpam ltac:(lia)).
  - (* fp *)
    rewrite Htp'. replace (ly_F lyc) with (ly_F ly2) by congruence.
    apply (gc_fp_emit B ly2 S2 W2 mem2 md2 (spZ regs - 4640) (spZ regs) _ md d _ p (LENr r n) cid pos cid' pos'
             LAWS (HFP LAWS) HAR2); rewrite ?FR2, ?EFA; try lia; try assumption.
    all: try (unfold ROW_BYTES, CAT_BYTES in *; lia).
    all: rewrite HTSD; unfold IMG_LO, IMG_HI; lia.
  - (* the thread cells *)
    rewrite Htp'. replace (ly_F lyc) with (ly_F ly2) by congruence.
    exact (gc_tls_AR' B ly2 S2 W2 mem2 md2 (spZ regs - 4640) (spZ regs) HTS LAWS HAR2
             ltac:(lia) ltac:(lia) ltac:(lia)).
  - (* the window below the call's frame present *)
    apply (ge_present_stk (w_H W2) mem2); [lia | lia | intros a Ha; apply HPRES2; lia].
  - (* ro_agree *) exact RRO.
  - (* length j0 *) exact Lj0.
  - (* the frame cells at spZ regs + -128 *)
    apply (gc_rw_view W W2 mc mem2 _ _ FRc).
    intros j Hj. cbn [cells_size csize] in Hj.
    split; [intros Hia; pose proof (ctrl_segs_low _ Hia); unfold kLowMemEnd in *; lia|].
    split; [exact (proj1 (HPRES (spZ regs + -128 + j) ltac:(lia)))|].
    split; [exact (proj1 (HPRES2 (spZ regs + -128 + j) ltac:(lia)))|].
    apply K1; [lia | lia |].
    cbv beta. intros Hin. destruct (Hptw (spZ regs + -128 + j) ltac:(lia)) as (_ & _ & _ & Hes).
    apply Hes. unfold ESTACK. lia.
  - (* the row's bytes *) exact (ge_row_bytes B RLO RHI HROWS HFR_rng W2 mem2 r HRO2 Hr).
  - (* the row addressable *)
    exact (ge_row_addr B GLOBS HGM HFR_glob HFR_rng _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r HJ2 Hr).
  - (* db *) apply OUT; [exact P1 | cbn [cells_size csize]; lia .. ].
  - (* sb *) apply OUT; [exact P2 | cbn [cells_size csize]; lia .. ].
  - (* the header *) apply OUT; [exact P3 | cbn [cells_size csize]; lia .. ].
  - (* the laid block *)
    rewrite (ge_row_LB r md mb nb [] [] Hr).
    assert (HZl : length (RcLay.ly_Z md mb nb (RcLay.ly_bb r)) = 32%nat).
    { unfold RcLay.ly_Z. destruct (md =? 0); [reflexivity|].
      destruct (RcSynth.rc mb (RcLay.ly_bb r) =? 1); [exact (RcSynthLib.rs_synth_len mb _ nb Hmbl) | reflexivity]. }
    assert (HB : bytes_at rsegs mem2 (p + 18) (RcLay.ly_Z md mb nb (RcLay.ly_bb r))).
    { apply (ge_bytes_of_garr8 W2 mem2); [lia | rewrite HZl; lia | exact GA]. }
    unfold rw_cells, cells_at, wr_at.
    split; [split; [cbn [cells_wf cell_wf]; split; [exact HZl | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB]|].
    cbn [cells_size csize].
    split; [lia|]. split; [lia|].
    intros j Hj.
    assert (Hx : 0 <= p + 18 + j < 2 ^ 64) by lia.
    assert (Hn : ~ in_img SEGS (p + 18 + j)) by (apply Hpni; lia).
    rewrite (gcv_wview_noimg mem2 _ Hx Hn), <- (gcv_mrd_noimg mem2 _ Hx Hn).
    destruct HB as (_ & _ & HBn).
    replace (p + 18 + j) with (p + 18 + Z.of_nat (Z.to_nat j)) by lia.
    rewrite (HBn (Z.to_nat j) ltac:(rewrite HZl; lia)).
    intros E. apply nth_error_None in E. rewrite HZl in E. lia.
  - (* the zeros *) apply OUT; [exact P5 | cbn [cells_size csize]; lia .. ].
  - (* the trailer *) apply OUT; [exact P6 | cbn [cells_size csize]; lia .. ].
  - (* the window visible *)
    exact (proj1 (ge_win B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_LAY) regs HJ2 Hslo Hshi)).
  - (* the window's shadow cover *)
    destruct (A.ProgWorldVisWin.win_sh_vis B LAWS ly2 S2 W2 mem2 md2 (spZ regs - 4640) 4640 HAR2
                ltac:(lia) ltac:(lia) ltac:(lia)) as [E0 | V]; [lia |].
    replace (spZ regs - 1) with (spZ regs - 4640 + 4640 - 1) by lia.
    exact (gc_shcov_of_al8 (w_H W2) (spZ regs - 4640) 4640 ltac:(lia) V).
  - (* the row visible *) exact (ge_row_vis HFR_rng W2 r Hr).
  - (* the row's shadow cover *)
    exact (ge_row_shcov B HIMGSH HFR_rng _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r HJ2 Hr).
  - (* md's shadow cover *)
    exact (ge_md_shcov B HIMGSH HCAT_rng _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ md i HJ2 Hmd Hi).
  - (* the output visible *)
    destruct (ge_buf_rw B STK sp0 FP ly S lyc Sc own W memc regs p (LENr r n) Hp Hpe Hptw ltac:(lia)) as [VB _].
    exact (gc_vis_wle W W2 _ _ Hle VB).
  - (* the output's shadow cover *)
    exact (gc_shcov_wle W W2 _ _ Hle
             (ge_buf_shcov B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k p (LENr r n) LAWS HJ Hp Hpe Hpfh
                ltac:(lia))).
Qed.

End e. End b.

From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import GE_lift GE_entry GE_cut GE_jal.
(* the glue's parts for the two stretches and the post, Required qualified (their names are written with the module) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require GE_post GE_pre_on GE_post2_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Regs6ss.
Import ListNotations.
Open Scope Z_scope.
(* The closure leaves zify's euclidean-division conversion switched off (A/AE2q.v and its siblings set the flag
   to false); the composition's arithmetic over shadow addresses (x / 8) needs it on. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ===================================================================================================== *)
(* Part 6. The composition.                                                                               *)
(* ===================================================================================================== *)
Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := AB1v.tfibsegs.
#[local] Notation VAL := (@pa_val _ ctrl_listing PI_ctrl).
#[local] Notation BASE := (@pa_val _ ctrl_listing PI_ctrl A_TEXT).
#[local] Notation PA_RLO := (@pa_relro_lo _ ctrl_listing PI_ctrl).
#[local] Notation PA_RHI := (@pa_relro_hi _ ctrl_listing PI_ctrl).

(* ctrl_emit_asF2.v's Local Abbreviations at row := CROW r, g := 0 (as GE_post.v writes them). *)
Local Abbreviation EEr r n mb :=
  (RcEmit.em_E (RcFin.ubat (CROW r) 21) (RcFin.ubat (CROW r) 22) n (RcEmit.em_hid mb)).
Local Abbreviation LENr r n := (RcEmit.em_len (RcFin.ubat (CROW r) 21) n).
Local Abbreviation RRr r n mb := (if EEr r n mb then LENr r n else 0).
Local Abbreviation BLKr r md mb nb tb gb :=
  (RcFin.fin (RcFin.ubat (CROW r) 20) (RcFin.ubat (CROW r) 18) (RcFin.ubat (CROW r) 19)
     (RcLay.ly_lay (RcLay.ly_k (CROW r)) tb (RcLay.ly_Z md mb nb (RcLay.ly_bb (RcLay.ly_k (CROW r)))) 0
        (RcLay.ly_ao (CROW r)) (RcLay.ly_al (CROW r)) gb)).

(* G_ctrl_emit_as.v's local tactic (Local, so not carried by the Require). *)
Local Ltac gc_ne1 := let E := fresh "E" in intro E; apply (f_equal bv_unsigned) in E; discriminate E.

Section m.
Variable B : asyms.
Variable GLOBS : list (Z * Z).
Variables RLO RHI : Z.

(* The second stretch and the post at the return point (route (C)). *)
Lemma gc_stretch2_on : ge_stretch2_on B GLOBS RLO RHI.
Proof.
  unfold ge_stretch2_on.
  intros HBRF HFNF LAWS HIMGSH HGM HFR_glob HFR_al HCAT_glob HCAT_al HBOX_glob HROWS HFR_rng HCAT_rng HBOX_rng
    RELRO_IMG STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p md d c16 n r i ns mb nb db sb
    mc W2 ly2 S2 regs2 mem2 md2 j0 P R
    HJ HRO Hret Hra4 Hgp Htp Hr10 Hr11 Hr Hr12 Hmd Hi Hr13 Hr14 Hr15 Hc16 Hr16 Hn Hr17 Hr29 Hns
    Hsp16 Hslo Hshi HC1 HC0 Hp Hp8 Hpe Hpam Hpni Hptw Hpfo HPC HDC Hpfh Hdl HdG Hdsrc Hdni Hdp Hds Hd8
    Hsl HsG HmG Hml HNB RO AC AWIN FP0 TLS0 SHW HE MUr WMr Hle J2 FR BL KEPT
    E2 E3 E4 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 RET.
  pose proof (RcEmitLib.em_len_rng _ _ _ _ HE) as RLE.
  pose proof RET as RET'.
  destruct RET' as (AC5 & SW5 & AW5 & AO5 & FP5 & TL5 & ST5r0 & RO5 & Lj0 & FR5 & HR5 & Af5 & P15 & P25 & P35 & P45 &
                    P55 & P65 & VWIN & VWSH & VROW & VROWS & VMDS & VOB & VOBS).
  (* the re-based second stretch, from the return point 0x84cf0 on the memory ctrl_lay_block returns *)
  refine (ge_entry W2 0x84cf0 regs2 mem2 md2 _ _ ctrl_wx _ _).
  { rewrite E2, E3, E4, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27.
    exact (GE_post2_on.ge_post2_on B GLOBS RLO RHI HBRF HFNF LAWS HIMGSH HGM HFR_glob HFR_al HCAT_glob HFR_rng HCAT_rng
             HBOX_rng RELRO_IMG STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k W2 mem2 regs (ly_F lyc)
             p md d n r i ns mb nb db sb j0 P
             (getr regs2 1) (getr regs2 5) (getr regs2 6) (getr regs2 7) (getr regs2 8) (getr regs2 9)
             (getr regs2 10) (getr regs2 11) (getr regs2 12) (getr regs2 13) (getr regs2 14) (getr regs2 15)
             (getr regs2 16) (getr regs2 17) (getr regs2 28) (getr regs2 29) (getr regs2 30) (getr regs2 31) R
             AC5 SW5 AW5 AO5 FP5 TL5 ST5r0 RO5 Lj0 FR5 HR5 Af5 P15 P25 P35 P45 P55 P65
             VWIN VWSH VROW VROWS VMDS VOB VOBS
             HE HJ Hr Hmd Hi Hn Hslo Hshi Hp Hpe Hpam Hpni Hptw Hpfo Hpfh Hdl Hdsrc Hdp Hd8 Hsl Hml HNB RO Hns Hle). }
  intros ms5 md5 (s5 & HQ5 & Hrel5 & Hros5) Hhid5 Hsame5.
  destruct HQ5 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                   Es5 & MU5 & WM5 & MI5 & ST5 & AC5' & SW5' & AW5' & FP5' & RES).
  rewrite Es5 in Hrel5.
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ Hrel5) as [Ems5 REL5].
  rewrite Ems5.
  pose proof (mem_rel_normalize rsegs mem2 RO5) as REL05.
  assert (MU5r : munch [(spZ regs - 4640, spZ regs); (p, p + LENr r n)] mem2 (ms_mem ms5))
    by exact (munch_rel rsegs _ _ _ _ _ REL05 REL5 Hros5 MU5).
  assert (WM5r : wmono rsegs mem2 (ms_mem ms5)) by exact (wmono_rel rsegs _ _ _ _ REL05 REL5 Hros5 WM5).
  assert (ST5r : stk rsegs (ms_mem ms5) (spZ regs - 4640) (spZ regs)) by exact (stk_of_rel _ _ _ _ REL5 ST5).
  (* the side stack's base is the same in the two layouts (layout_le of the two journals) *)
  assert (EF2 : ly_F ly2 = ly_F lyc).
  { pose proof HJ as (_ & HLE1 & _). pose proof J2 as (_ & HLE2 & _).
    destruct HLE1 as (_ & _ & _ & _ & _ & F1 & _). destruct HLE2 as (_ & _ & _ & _ & _ & F2 & _).
    rewrite F1, F2. reflexivity. }
  (* the caller's journal across the second stretch: it writes the window and the output only *)
  assert (HJ5 : ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 (ms_mem ms5) md5 (k + EV_LAY)).
  { apply (ge_jrnl B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_LAY) md5
             [(spZ regs - 4640, spZ regs); (p, p + LENr r n)] (ms_mem ms5) LAWS J2 MU5r WM5r Hhid5 Hsame5).
    intros a Ha Ho. destruct (gc_not_out2 _ _ _ _ _ Ho) as [Hw | Ho2].
    - unfold awr_byte. left. assert (HT : TEMIT_STK = 4640) by reflexivity. lia.
    - destruct (Hptw a ltac:(lia)) as (Haw & _).
      rewrite BL. exact (gc_awr_ly _ _ _ _ _ lyc ly2 own a EF2 Haw). }
  assert (HE' : RcEmit.em_E (EM_L r) (EM_G r) n (RcEmit.em_hid mb) = true)
    by (rewrite <- (ge_row_E r n mb); exact HE).
  pose proof (GE_post.ge_keep_lay B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n r mb mc W2 mem2
                (ms_mem ms5) LAWS HJ Hslo Hshi Hpni HE MUr WMr Hle KEPT MU5r WM5r ST5r) as KEEP.
  apply (SRr_ret SEGS).
  apply (GE_post.ge_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p md c16 n r mb nb db sb [] []
           W2 ly2 S2 (ms_mem ms5) md5 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
           Hret Hr15 Hc16 Hr Hptw Hml Hdl Hsl Hle).
  - intros HE0. destruct (RES HE0) as (RB & _). exact (proj2 (bytes_at_rel rsegs _ _ _ _ REL5) RB).
  - rewrite HE'. exact HJ5.
  - exact FR.
  - exact BL.
  - exact KEEP.
Qed.

Theorem pb_ctrl_emit_as_on :
  forall (HTS : A.AF0m.CtrlTSyms B)
    (HRLO : RLO = PA_RLO) (HRHI : RHI = PA_RHI),
  pb_ctrl_emit_as_stmt_on (SK := SK) B GLOBS RLO RHI.
Proof.
  intros HTS HRLO HRHI.
  (* a Theorem Labs lane's facts at CtrlTSyms B, in the forms the glue's parts state them; no visible-zero-shadow premise: the run state comes from
     GE_rtC.ge_rtC_jrnl (route (C)) *)
  assert (HSS' : ge_stack_shadow_stmt B) by exact (A.ProgWorldShadow.ctl_stack_shadow_of_AR B).
  assert (HFP : ge_fp_stmt B) by (intros L; exact (A.ProgWorld_Fs.ctl_fp_of_AR B HTS L)).
  pose proof (A.ProgWorld.as_tp_RT_TP B HTS) as HTP.
  assert (HTSD : as_tsd B = 0x5fcbb8) by (rewrite (A.AF0m.ts_tsd B HTS); vm_compute; reflexivity).
  unfold pb_ctrl_emit_as_stmt_on.
  intros TL LAWS ML HMSF HMCF HBRF HFNF TLAY HIMGSH HGM HFR_glob HFR_al HCAT_glob HCAT_al HBOX_glob HROWS
    HFR_rng HCAT_rng HBOX_rng RELRO_IMG.
  unfold tctrl_emit_as_spec.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p md d c16 n r i ns mb nb db sb
    HJ HRO Hret Hra4 Hgp Htp Hr10 Hr11 Hr Hr12 Hmd Hi Hr13 Hr14 Hr15 Hc16 Hr16 Hn Hr17 Hr29 Hns
    Hsp16 Hslo Hshi HC1 HC0 Hp Hp8 Hpe Hpam Hpni Hptw Hpfo HPC HDC Hpfh Hdl HdG Hdsrc Hdni Hdp Hds Hd8
    Hsl HsG HmG Hml HNB.
  (* ---- the run state at the call, from the caller's journal (its AR conjunct) and ProgWorld ---- *)
  pose proof HJ as HJ'.
  destruct HJ' as (HAR & HLE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & HSTK & _).
  destruct HSTK as (_ & _ & HCEIL & HSLO & HSHI & H47 & _).
  destruct HLE as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Eslo & Eshi & _).
  assert (HT : TEMIT_STK = 4640) by reflexivity.
  assert (Wlo : ly_stk_lo lyc <= spZ regs - 4640) by lia.
  assert (Whi : spZ regs <= ly_stk_hi lyc) by lia.
  (* route (C): ro_agree, asan_cells and the regional shadow_rw_on (ge_Rsh B lyc Sc) at the call memory *)
  destruct (ge_rtC_jrnl (SK := SK) B HTS LAWS RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HRO) as (RO & AC & SW).
  assert (AWIN : addressable memc (spZ regs - 4640) 4640).
  { apply (HSS' LAWS lyc Sc W memc mdc); [exact HAR | lia | lia | lia]. }
  assert (Htp' : bv_unsigned (getr regs 4) = RT_TP).
  { change (bv_unsigned (lib.Reusable.YK11.getr regs 4) = RT_TP).
    rewrite Htp, HTP. unfold w64. apply gc_u64. unfold RT_TP. lia. }
  pose proof HPC as (cid & pos & HinP & Hc2 & HfaP & HfeP).
  pose proof HDC as (cid' & pos' & HinD & Hc2' & HfaD & HfeD).
  assert (RLN : 0 <= RRr r n mb <= 1492).
  { destruct (EEr r n mb) eqn:E; [pose proof (RcEmitLib.em_len_rng _ _ _ _ E); lia | lia]. }
  assert (FP0 : fp [0%nat; 1%nat] memc (bv_unsigned (getr regs 4)) (ly_F lyc) (spZ regs - 4640) (spZ regs)
    [(spZ regs - 4640, spZ regs); (p, p + RRr r n mb)]
    [(VAL (A_OBJ A_FRAMES) + ROW_BYTES * r, VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + 24); (md, md + 296);
     (d, d + 6); (VAL (A_OBJ A_BOX), VAL (A_OBJ A_BOX) + 6); (p, p + RRr r n mb)]).
  { rewrite Htp'.
    apply (gc_fp_emit B lyc Sc W memc mdc (spZ regs - 4640) (spZ regs) _ md d _ p (RRr r n mb) cid pos cid' pos'
             LAWS (HFP LAWS) HAR); try lia.
    all: try (unfold ROW_BYTES, CAT_BYTES in *; lia).
    all: try assumption.
    all: rewrite HTSD; unfold IMG_LO, IMG_HI; lia. }
  assert (TLS0 : ctrl_emit_as_c.ctrl_emit_as_tls memc (bv_unsigned (getr regs 4)) (ly_F lyc)
                   (spZ regs - 4640) (spZ regs)).
  { rewrite Htp'. apply (gc_tls_AR' B lyc Sc W memc mdc); [exact HTS | exact LAWS | exact HAR | lia | lia | lia]. }
  assert (SHW : sh_cov_vis (w_H W) (spZ regs - 4640) (spZ regs - 1)).
  { destruct (A.ProgWorldVisWin.win_sh_vis B LAWS lyc Sc W memc mdc (spZ regs - 4640) 4640 HAR
               ltac:(lia) ltac:(lia) ltac:(lia)) as [E | V]; [lia |].
    replace (spZ regs - 1) with (spZ regs - 4640 + 4640 - 1) by lia.
    exact (gc_shcov_of_al8 _ (spZ regs - 4640) 4640 ltac:(lia) V). }
  (* the shadow spans the first stretch's helper calls read lie in ge_Rsh B lyc Sc (GE_rtC.ge_rsh_cov) *)
  assert (HRSH : forall a, (EEr r n mb = true /\ sh_word_on.sh_word_on p (LENr r n) a) \/
                   sh_word_on.sh_word_on d 6 a \/ sh_word_on.sh_word_on (VAL (A_OBJ A_BOX)) 6 a ->
                   ge_Rsh B lyc Sc a).
  { apply (ge_rsh_cov B lyc Sc W memc mdc p d (VAL (A_OBJ A_BOX)) (LENr r n) (EEr r n mb) HAR HPC HDC).
    - intros E. pose proof (RcEmitLib.em_len_rng _ _ _ _ E). lia.
    - exact HBOX_rng. }
  (* ---- the first lifted stretch ---- *)
  apply (ge_entry W (BASE + AF_ctrl_emit_as) regs memc mdc _ _ ctrl_wx
           (GE_pre_on.ge_pre_on B GLOBS RLO RHI HMSF HMCF LAWS HIMGSH HGM HFR_glob HFR_al HCAT_glob HCAT_al HBOX_glob
              HROWS
              HFR_rng HCAT_rng
              HBOX_rng RELRO_IMG STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p md d n r i ns
              (ly_F lyc) mb nb db sb (ge_Rsh B lyc Sc) HJ HRO Hr10 Hr11 Hr Hr12 Hmd Hi Hr13 Hr14 Hr16 Hn Hr17 Hr29
              Hslo Hshi Hp Hpe Hpam Hpni Hptw Hpfo Hpfh Hdl HdG Hdsrc Hdp Hds Hd8 Hsl HsG HmG Hml HNB RO AC SW HRSH
              AWIN FP0 TLS0 SHW)).
  intros ms' mdc' (s0 & Hmid & Hrel & Hros) Hhid Hsame.
  pose proof (mem_rel_normalize rsegs memc RO) as REL0.
  unfold ctrl_emit_asF2_on.aMid_on in Hmid.
  destruct Hmid as [HQ | HAT].
  - (* ---- the early return (EE = false): the run's own window is the stack window alone ---- *)
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    Es0 & MU & WM & MI & ST & ACq & SWq & AWq & FPq & RES).
    rewrite Es0 in Hrel.
    destruct (ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Ems REL].
    rewrite Ems.
    assert (MUs : munch [(spZ regs - 4640, spZ regs)] memc (ms_mem ms'))
      by exact (munch_rel rsegs _ _ _ _ _ REL0 REL Hros MU).
    assert (WMr : wmono rsegs memc (ms_mem ms')) by exact (wmono_rel rsegs _ _ _ _ REL0 REL Hros WM).
    assert (HJm : ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') mdc' k).
    { apply (ge_jrnl_win B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k mdc' (ms_mem ms') (spZ regs) 4640
               p 1492 W memc (spZ regs) LAWS HJ); [| exact WMr | exact Hhid | exact Hsame | lia | lia | exact Hptw].
      apply (gc_munch_sub _ _ _ _ MUs). intros x Hx. cbn [outside] in Hx |- *.
      destruct Hx as (H1 & _ & _). split; [exact H1 | exact I]. }
    pose proof (GE_post.ge_keep_ret B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
                  (fun a => p <= a < p + RRr r n mb) (ms_mem ms') LAWS HJ Hslo Hshi MUs WMr
                  (stk_of_rel _ _ _ _ REL ST)) as KEEP.
    apply (SRr_ret SEGS).
    apply (GE_post.ge_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p md c16 n r mb nb db sb [] []
             W lyc Sc (ms_mem ms') mdc' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
             Hret Hr15 Hc16 Hr Hptw Hml Hdl Hsl (wle_refl SEGS W)).
    + intros HE. destruct (RES HE) as (RB & _).
      exact (proj2 (bytes_at_rel rsegs _ _ _ _ REL) RB).
    + apply (ajournal_mono_k SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJm).
      assert (EV0 : EV_EMIT = 0) by reflexivity. rewrite EV0.
      destruct (RcEmit.em_E (EM_L r) (EM_G r) n (RcEmit.em_hid mb)); lia.
    + reflexivity.
    + reflexivity.
    + exact KEEP.
  - (* ---- the call site 0x84cec: the jal, a Theorem Labs lane's contract, then the second stretch ---- *)
    destruct HAT as (x1 & u0 & u1 & u2 & x8 & x9 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & mc0 & j0 & P &
                     Es0 & HE & Lj0 & AJ & STc & MUc & WMc & MIc & FRc & P1 & P2 & P3 & P4 & P5 & P6).
    rewrite Es0 in Hrel.
    destruct (ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Ems REL].
    rewrite Ems.
    pose proof (RcEmitLib.em_len_rng _ _ _ _ HE) as RLE.
    assert (MUr : munch [(spZ regs - 4640, spZ regs); (p, p + LENr r n)] memc (ms_mem ms'))
      by exact (munch_rel rsegs _ _ _ _ _ REL0 REL Hros MUc).
    assert (WMr : wmono rsegs memc (ms_mem ms')) by exact (wmono_rel rsegs _ _ _ _ REL0 REL Hros WMc).
    pose proof AJ as AJ'. destruct AJ' as (_ & _ & _ & AOc & _ & _).
    assert (AOr : addressable (ms_mem ms') p (LENr r n)) by exact (gc_addr_rel _ _ _ _ REL AOc).
    pose proof (rw_cells_of_rel _ _ _ _ REL FRc) as FRr.
    pose proof (rw_cells_of_rel _ _ _ _ REL P1) as P1r.
    pose proof (rw_cells_of_rel _ _ _ _ REL P2) as P2r.
    pose proof (rw_cells_of_rel _ _ _ _ REL P3) as P3r.
    pose proof (rw_cells_of_rel _ _ _ _ REL P5) as P5r.
    pose proof (rw_cells_of_rel _ _ _ _ REL P6) as P6r.
    (* the stack and the buffer: the window lies above alloc_ceiling, the buffer in a frame below it *)
    pose proof (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR HinP) as (_ & FBP & _).
    pose proof asan_consts as (CV & _).
    (* the journal at the call site *)
    assert (HJc : ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') mdc' k).
    { apply (ge_jrnl_win B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k mdc' (ms_mem ms') (spZ regs) 4640
               p 1492 W memc (spZ regs) LAWS HJ); [| exact WMr | exact Hhid | exact Hsame | lia | lia | exact Hptw].
      apply (gc_munch_sub _ _ _ _ MUr). intros x Hx. cbn [outside] in Hx |- *.
      destruct Hx as (H1 & H2 & _). split; [exact H1 | split; [lia | exact I]]. }
    (* the image is outside the first stretch's writes *)
    assert (IMGO : forall a, in_img SEGS a -> outside [(spZ regs - 4640, spZ regs); (p, p + LENr r n)] a).
    { intros a Hia. pose proof (ctrl_segs_low a Hia) as Hlow. cbn [outside].
      split; [unfold kLowMemEnd in Hlow; lia | split; [intros Ha; apply (Hpni a); [lia | exact Hia] | exact I]]. }
    (* the jal *)
    match goal with |- SRr _ _ (mkCfg (MS ?R0 _ _ _ _ _ _) _) _ => set (RR := R0) end.
    apply (ge_steps W _ (MS (lib.Reusable.YK11.regupd RR 1 (Z_to_bv 64 0x84cf0)) lib.Reusable.YK11.fp_regs
                           (Z_to_bv 64 0x855f4) lib.Reusable.YK11.fp_csr None (ms_mem ms') (seg_rom SEGS)) mdc' _
             ctrl_wx (ge_jal_lay (RNG_W (w_H W)) RR lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr (ms_mem ms'))).
    intros md' Hsame'.
    apply (ge_at_cfg W _ 0x855f4 (ms_mem ms') md' _).
    assert (Elay : BASE + AF_ctrl_lay_block = 0x855f4) by (vm_compute; reflexivity).
    rewrite <- Elay.
    set (RC := lib.Reusable.YK11.regupd RR 1 (Z_to_bv 64 0x84cf0)).
    assert (GRC : forall x : bv 5, x <> (1%bv : bv 5) -> lib.Reusable.YK11.getr RC x = lib.Reusable.YK11.getr RR x).
    { intros x Hx. apply lib.Reusable.YK11.getr_other. exact Hx. }
    assert (Esp : spZ RC = spZ regs + -128).
    { unfold spZ. rewrite (GRC 2%bv ltac:(gc_ne1)).
      change (lib.Reusable.YK11.getr RR 2%bv) with (Z_to_bv 64 (bv_unsigned (getr regs 2) + -128)).
      apply gc_u64. unfold spZ in *. lia. }
    apply (SRr_bind SEGS W _
             (tctrl_lay_block_post (SK := SK) B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') k RC p r md mb nb)).
    + apply (TLAY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k RC p r i md mb nb).
      * rewrite (same_but_materialized_wvb mdc' md' Hsame').
        exact (ajournal_materialize SEGS B LAWS ctrl_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc).
      * rewrite <- HRLO, <- HRHI.
        exact (ge_ro_keep B (w_H W) RLO RHI memc (ms_mem ms') _ RELRO_IMG HRO MUr IMGO).
      * unfold RC. rewrite lib.Reusable.YK11.getr_same by gc_ne1. vm_compute. reflexivity.
      * unfold raZ, RC. rewrite lib.Reusable.YK11.getr_same by gc_ne1. vm_compute. discriminate.
      * rewrite (GRC 3%bv ltac:(gc_ne1)). exact Hgp.
      * rewrite (GRC 4%bv ltac:(gc_ne1)). exact Htp.
      * rewrite (GRC 10%bv ltac:(gc_ne1)). reflexivity.
      * rewrite (GRC 11%bv ltac:(gc_ne1)). reflexivity.
      * exact Hr.
      * rewrite (GRC 12%bv ltac:(gc_ne1)). reflexivity.
      * exact Hmd.
      * exact Hi.
      * rewrite (GRC 13%bv ltac:(gc_ne1)). reflexivity.
      * rewrite Esp. replace (spZ regs + -128) with (spZ regs + (-8) * 16) by lia.
        rewrite Z.mod_add by lia. exact Hsp16.
      * rewrite Esp. change TLAY_STK with 4512. lia.
      * rewrite Esp. lia.
      * exact HC1.
      * exact HC0.
      * lia.
      * lia.
      * unfold amem_range in *. lia.
      * intros x Hx. apply Hpni. lia.
      * intros a Ha. destruct (Hptw a ltac:(lia)) as (Haw & Hpr & Hno & Hes).
        split; [exact Haw|]. split; [|split; [exact Hno|]].
        -- apply (gc_present_wmono _ memc); [exact WMr | lia | apply Hpni; lia | exact Hpr].
        -- rewrite Esp. unfold ESTACK. lia.
      * destruct Hpfo as ((cf & pf & Hinf & Hc0f & Hal & Hlo & Hhi) & H8 & HRA).
        split; [exists cf, pf; repeat split; (assumption || lia)|]. split; [exact H8|].
        intros x Hx. destruct (HRA x ltac:(lia)) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
        assert (Hxc : x < lib.Reusable.YM05.alloc_ceiling) by lia.
        assert (Hlw : lib.Reusable.YM05.alloc_ceiling <= spZ regs - 4640) by lia.
        destruct CV as [CV1 CV2].
        pose proof (gc_sh_out x p (LENr r n) (spZ regs - 4640) (spZ regs) lib.Reusable.YM05.alloc_ceiling
                      ltac:(lia) Hxc CV2 CV1 Hlw ltac:(lia) ltac:(lia) Hpam ltac:(lia)) as Hsh.
        unfold shadow_of_addr, SHADOW_OFF.
        rewrite (ge_view_of_munch (w_H W) memc (ms_mem ms') _ _ (proj1 Hsh) MUr (proj2 Hsh)). exact Hsv.
      * destruct Hpfh as (cf & pf & Hinf & Hcf & Hlo & Hhi). exists cf, pf. split; [exact Hinf|].
        split; [exact Hcf|].
        split; [pose proof (gc_div64 p (p + 18) ltac:(lia)); lia|].
        pose proof (gc_div64 (p + 18 + 32 - 1) (p + 1492 - 1) ltac:(lia)). lia.
      * apply (gc_garr8_munch _ _ memc (ms_mem ms') _ _ MUr); [| exact HmG].
        intros j Hj. unfold C_reac_box_model_block.bmb_z in Hj. rewrite length_map, Hml in Hj.
        unfold CAT_BYTES in Hmd. unfold IMG_LO, IMG_HI, CAT_BYTES in HCAT_rng.
        split; [unfold IMG_HI; lia|]. apply IMGO. apply gc_img_in. unfold IMG_LO, IMG_HI. lia.
      * exact Hml.
      * intros HB Hh Hn0. destruct (HNB HB Hh Hn0) as (Hok & HG & Hq & Hro).
        split; [exact Hok|]. split; [|split; [exact Hq|]].
        -- apply (gc_garr8_munch _ _ memc (ms_mem ms') _ _ MUr); [| exact HG].
           intros j Hj. unfold C_reac_box_model_block.bmb_z in Hj. rewrite length_map in Hj.
           assert (Hia : in_img SEGS (RcSynth.rname mb + Z.of_nat j)).
           { destruct (Hro (RcSynth.rname mb + Z.of_nat j) ltac:(lia)) as ([(sg & Hs & _ & Hsr) | Hsr] & _ & _).
             - exists sg. split; [exact Hs | exact Hsr].
             - exact (RELRO_IMG _ Hsr). }
           pose proof (ctrl_segs_low _ Hia) as Hlow. unfold kLowMemEnd in Hlow.
           split; [lia | exact (IMGO _ Hia)].
        -- intros x Hx. destruct (Hro x Hx) as (H1 & H2 & H3). rewrite <- HRLO, <- HRHI.
           exact (conj H1 (conj H2 H3)).
    + intros W2 c2 Hle (ly2 & S2 & regs2 & mem2 & md2 & Ec2 & J2 & PRE & FR & BL & GA & KEPT).
      subst c2.
      assert (Gra : lib.Reusable.YK11.getr RC 1 = Z_to_bv 64 0x84cf0).
      { unfold RC. apply lib.Reusable.YK11.getr_same. gc_ne1. }
      rewrite Gra. rewrite Esp in KEPT.
      apply (gc_stretch2_on HBRF HFNF LAWS HIMGSH HGM HFR_glob HFR_al HCAT_glob HCAT_al HBOX_glob HROWS HFR_rng HCAT_rng
               HBOX_rng RELRO_IMG STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p md d c16 n r i ns
               mb nb db sb (ms_mem ms') W2 ly2 S2 regs2 mem2 md2 j0 P (ge_Rsh B ly2 S2)
               HJ HRO Hret Hra4 Hgp Htp Hr10 Hr11 Hr Hr12 Hmd Hi Hr13 Hr14 Hr15 Hc16 Hr16 Hn Hr17 Hr29 Hns
               Hsp16 Hslo Hshi HC1 HC0 Hp Hp8 Hpe Hpam Hpni Hptw Hpfo HPC HDC Hpfh Hdl HdG Hdsrc Hdni Hdp Hds Hd8
               Hsl HsG HmG Hml HNB RO AC AWIN FP0 TLS0 SHW HE MUr WMr Hle J2 FR BL KEPT).
      1-13: lazymatch goal with
            | |- getr _ ?x = _ =>
                let rr := eval vm_compute in (bv_unsigned x) in
                refine (eq_trans (PRE rr _) _); [unfold acallee_saved; lia | unfold RC, RR; reflexivity]
            end.
      exact (gc_ret_on B GLOBS RLO RHI HTS LAWS HIMGSH HGM HFR_glob HROWS HFR_rng HCAT_rng HBOX_rng
               RELRO_IMG STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p md d n r i ns mb nb db sb
               (ms_mem ms') W2 ly2 S2 mem2 md2 j0 P HJ HRO Htp Hr Hmd Hi Hslo Hshi Hsp16 Hp Hpe Hpam Hpni Hptw
               Hpfo HPC HDC Hpfh Hml HE MUr WMr Lj0 FRr P1r P2r P3r P5r P6r AOr Hle J2 FR GA KEPT).
Qed.

End m.
End b.

(* Rests on Rocq's primitive int / string / array declarations and the library's own axioms only (the compile
   log shows the list); no axiom of this project, and no visible-zero-shadow premise. *)
Print Assumptions pb_ctrl_emit_as_on.
