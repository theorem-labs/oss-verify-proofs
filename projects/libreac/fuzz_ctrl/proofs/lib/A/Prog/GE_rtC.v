(* fuzz_ctrl image A, ctrl_emit_as (0x849d8): route (C) region facts of a Theorem Labs lane's cgif-form glue. NEW file
   (additive form ruling, auditor a Theorem Labs lane): G_ctrl_emit_as.v, GE_pre.v and GE_post2.v are not changed.

   G_ctrl_emit_as.pb_ctrl_emit_as takes the universal `shadow_rw m` from A.ProgWorldCtlRt's run-state lemma, which
   needs ProgWorld's visible-zero-shadow core fact (reported false). Route (C) takes the REGIONAL form instead:
   A.ProgWorldCtlRtC.ctl_rt_C_of_AR (no such premise) gives A.ACtlRtC.ctl_rt_C B ly S m, whose two shadow conjuncts are
   shadow_rw_on over cut_shadow B ly S and over img_shadow. This file proves:
     ge_rtC_AR / ge_rtC_jrnl : ro_agree, asan_cells and shadow_rw_on (ge_Rsh B ly S) at the memory of an AR (resp.
                               of a caller journal), ge_Rsh B ly S := cut_shadow B ly S \/ img_shadow
                               (shadow_rw_on_union); used at the call memory and at the memory ctrl_lay_block
                               returns;
     ge_rsh_cov              : the shadow spans the first stretch's callees read (the output [o, o + LEN) when
                               EE = true, the source d, the box s; ctrl_emit_asF2_on.v's HRsh) lie in ge_Rsh at the
                               call's values: o and d lie in live fake frames (the spec's two frame premises), whose
                               addresses are 64-aligned (ly_F is page-aligned, fs_frame_off is a multiple of 64:
                               YG0f.v:39, :313, :340, AR's Wf wfs_live YG01.v:313), so their aligned shadow words
                               lie in the frame's shadow (cut_shadow's (F) part); s is an image byte with a 64-byte
                               margin (HBOX_rng), so its shadow words are image shadow (img_shadow).
   rule 24: no function proved (region facts over the core's AR). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import GEbase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AF0m A.ACtlRtC A.ProgWorldCtlRtC A.ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require rng_asan sh_word_on.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope Z_scope.

Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := AB1v.tfibsegs.

(* The region of route (C) at a cut (ly, S): the cut's own shadow and the image's shadow. *)
Definition ge_Rsh (B : asyms) (ly : alayout) (S : astate) : Z -> Prop :=
  fun a => A.ACtlRtC.cut_shadow B ly S a \/ A.ACtlRtC.img_shadow a.

(* ---- (a) / (c): the run state of route (C) at the memory of an AR ---- *)
Lemma ge_rtC_AR : forall (B : asyms), A.AF0m.CtrlTSyms B -> AR_laws SEGS B ->
  forall (RLO RHI : Z) ly S (W : world SEGS) (m : word -> option byte) md,
  AR SEGS B ly S W m md -> arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) m) ->
  ro_agree rsegs m /\ asan_cells m /\ A.ShadowRwOn.shadow_rw_on (ge_Rsh B ly S) m.
Proof.
  intros B HTS LAWS RLO RHI ly S W m md HAR HRO.
  destruct (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B HTS LAWS RLO RHI ly S W m md HAR (fun a Ha => HRO a Ha))
    as (RAC & RCUT & RIMG & RRO).
  split; [exact RRO|]. split; [exact RAC|].
  exact (A.ShadowRwOn.shadow_rw_on_union _ _ m RCUT RIMG).
Qed.

(* The same at the memory of a caller journal (its AR conjunct): the call memory (the spec's journal) and the
   memory ctrl_lay_block returns (TLAY's post journal). *)
Lemma ge_rtC_jrnl : forall (B : asyms), A.AF0m.CtrlTSyms B -> AR_laws SEGS B ->
  forall (RLO RHI : Z) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k,
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc) ->
  ro_agree rsegs memc /\ asan_cells memc /\ A.ShadowRwOn.shadow_rw_on (ge_Rsh B lyc Sc) memc.
Proof.
  intros B HTS LAWS RLO RHI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ HRO.
  pose proof HJ as (HAR & _).
  exact (ge_rtC_AR B HTS LAWS RLO RHI lyc Sc W memc mdc HAR HRO).
Qed.

(* ---- (b): the coverage ---- *)

(* A live fake frame is 64-aligned and a whole number of 64-byte blocks long. *)
Lemma ge_frame_al64 : forall (B : asyms) ly S (W : world SEGS) (m : word -> option byte) md cid pos,
  AR SEGS B ly S W m md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0.
Proof.
  intros B ly S W m md cid pos HAR Hin.
  destruct HAR as (HARm & _).
  pose proof (lib.Reusable.YG0f.lo_F_al _ (lib.Reusable.YG0n.am_layout _ _ _ _ HARm)) as FAL.
  pose proof (lib.Reusable.YG01.wfs_live _
                (lib.Reusable.YG01.wf_fakestack _ _ _ _ _ (lib.Reusable.YG0n.am_wf _ _ _ _ HARm))) as LV.
  pose proof (proj1 (Forall_forall _ _) LV (cid, pos) Hin) as [Hc Hp]. cbn [fst snd] in Hc, Hp.
  unfold lib.Reusable.YG0f.page_aligned in FAL. apply Z.mod_divide in FAL as [q Hq]; [|lia].
  unfold frame_addr, lib.Reusable.YG0f.fs_frame_off, lib.Reusable.YG0f.kFakeFramesOff,
    lib.Reusable.YG00.fs_frame_bytes.
  rewrite Z.shiftl_1_l. rewrite (Z.shiftl_mul_pow2 64 cid) by lia.
  change lib.Reusable.YG00.kStackSizeLog with 20. change (2 ^ 20) with 1048576.
  split.
  - apply Z.mod_divide; [lia|]. exists (q * 64 + 576 + cid * 16384 + pos * 2 ^ cid). rewrite Hq. ring.
  - apply Z.mod_divide; [lia|]. exists (2 ^ cid). ring.
Qed.

(* The aligned shadow words of a span inside a live fake frame lie in the frame's shadow: cut_shadow (F). *)
Lemma ge_cov_frame : forall (B : asyms) ly S (W : world SEGS) (m : word -> option byte) md cid pos x n,
  AR SEGS B ly S W m md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= x -> x + n <= frame_addr ly cid pos + fs_frame_bytes cid -> 0 <= n ->
  forall a, sh_word_on.sh_word_on x n a -> A.ACtlRtC.cut_shadow B ly S a.
Proof.
  intros B ly S W m md cid pos x n HAR Hin H1 H2 Hn a (Hn0 & Ha1 & Ha2).
  destruct (ge_frame_al64 B ly S W m md cid pos HAR Hin) as (A1 & A2).
  left. exists cid, pos. split; [exact Hin|].
  unfold rng_asan.sh_al8_lo, rng_asan.sh_al8_hi, AsanRT.shadow_addr, AsanRT.ASAN_K in Ha1, Ha2.
  unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
  set (F := frame_addr ly cid pos) in *. set (FB := fs_frame_bytes cid) in *.
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. pose proof (Z.div_mod FB 64 ltac:(lia)) as DB.
  pose proof (Z.div_mod x 8 ltac:(lia)) as DX. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as BX.
  pose proof (Z.div_mod (x / 8 + 2147450880) 8 ltac:(lia)) as DX2.
  pose proof (Z.mod_pos_bound (x / 8 + 2147450880) 8 ltac:(lia)) as BX2.
  pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)) as DY. pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)) as BY.
  pose proof (Z.div_mod ((x + n - 1) / 8 + 2147450880) 8 ltac:(lia)) as DY2.
  pose proof (Z.mod_pos_bound ((x + n - 1) / 8 + 2147450880) 8 ltac:(lia)) as BY2.
  pose proof (Z.div_mod F 8 ltac:(lia)) as DF8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as BF8.
  pose proof (Z.div_mod FB 8 ltac:(lia)) as DB8. pose proof (Z.mod_pos_bound FB 8 ltac:(lia)) as BB8.
  lia.
Qed.

(* The aligned shadow words of an image span with a 64-byte margin are image shadow: img_shadow. *)
Lemma ge_cov_img : forall x n, IMG_LO + 64 <= x -> x + n + 64 <= IMG_HI -> 0 <= n ->
  forall a, sh_word_on.sh_word_on x n a -> A.ACtlRtC.img_shadow a.
Proof.
  intros x n H1 H2 Hn a (Hn0 & Ha1 & Ha2).
  unfold rng_asan.sh_al8_lo, rng_asan.sh_al8_hi, AsanRT.shadow_addr, AsanRT.ASAN_K in Ha1, Ha2.
  exists (8 * (a - 2147450880)). split.
  - unfold IMG_LO, IMG_HI, A.Prog.CtrlRo.IMG_LO, A.Prog.CtrlRo.IMG_HI in *.
    pose proof (Z.div_mod x 8 ltac:(lia)) as DX. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as BX.
    pose proof (Z.div_mod (x / 8 + 2147450880) 8 ltac:(lia)) as DX2.
    pose proof (Z.mod_pos_bound (x / 8 + 2147450880) 8 ltac:(lia)) as BX2.
    pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)) as DY.
    pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)) as BY.
    pose proof (Z.div_mod ((x + n - 1) / 8 + 2147450880) 8 ltac:(lia)) as DY2.
    pose proof (Z.mod_pos_bound ((x + n - 1) / 8 + 2147450880) 8 ltac:(lia)) as BY2.
    lia.
  - unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
    rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The coverage at the call's values (o := p, s := VAL (A_OBJ A_BOX), LEN / EE := the call's em_len / em_E):
   the premises are the spec's two frame premises (tctrl_emit_as_spec, C_ctrl_emit_as.v:173-176), the bound of
   LEN under EE (RcEmitLib.em_len_rng) and HBOX_rng. *)
Lemma ge_rsh_cov : forall (B : asyms) ly S (W : world SEGS) (m : word -> option byte) md
    (p d s LEN : Z) (EE : bool),
  AR SEGS B ly S W m md ->
  (exists cid pos, In (cid, pos) (frames S) /\ 2 <= cid /\ frame_addr ly cid pos <= p /\
                   p + 1492 <= frame_addr ly cid pos + fs_frame_bytes cid) ->
  (exists cid pos, In (cid, pos) (frames S) /\ 2 <= cid /\ frame_addr ly cid pos <= d /\
                   d + 6 <= frame_addr ly cid pos + fs_frame_bytes cid) ->
  (EE = true -> 0 <= LEN <= 1492) ->
  IMG_LO + 64 <= s /\ s + 6 + 64 <= IMG_HI ->
  forall a, (EE = true /\ sh_word_on.sh_word_on p LEN a) \/ sh_word_on.sh_word_on d 6 a \/
            sh_word_on.sh_word_on s 6 a -> ge_Rsh B ly S a.
Proof.
  intros B ly S W m md p d s LEN EE HAR (cid & pos & Hin & _ & Hp1 & Hp2) (cid' & pos' & Hin' & _ & Hd1 & Hd2)
    HLEN [Hs1 Hs2] a [(HE & Ha) | [Ha | Ha]].
  - left. pose proof (HLEN HE) as HL.
    exact (ge_cov_frame B ly S W m md cid pos p LEN HAR Hin Hp1 ltac:(lia) ltac:(lia) a Ha).
  - left. exact (ge_cov_frame B ly S W m md cid' pos' d 6 HAR Hin' Hd1 Hd2 ltac:(lia) a Ha).
  - right. exact (ge_cov_img s 6 Hs1 Hs2 ltac:(lia) a Ha).
Qed.

End b.

Print Assumptions ge_rtC_jrnl.
Print Assumptions ge_rsh_cov.
