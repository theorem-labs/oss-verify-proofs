(* lib/A/Prog/C_reac_ctrl_parseP.v -- fuzz_ctrl image A (asan, libreac v1.9.0): the cgif-form glue theorem
   pb_reac_ctrl_parse : treac_ctrl_parse_spec (lib/A/Prog/C_reac_ctrl_parse.v blob 7e1714c64e5 (the blob this tree had at release c5e779efe8c), FROZEN), route (C).
   rule 24: no function proved.  This lane writes the glue of ctrl's OWN proved v1.9 image-A run of reac_ctrl_parse
   (0x83578): it lifts the run's footprint stretches into the core's world and applies the core's rules at the two
   world events.  The walk, step by step (B's lib/B/Prog/C_reac_ctrl_parsePf.v @ 258208c7d59 is the template):
   1. the entry to the first slot of __asan_stack_malloc_1: reac_ctrl_parseF_pre.PreFOn.pre_call_F, lifted
      (C_reac_ctrl_parsePP.rcpPP_to_E1);
   2. the call `jal __asan_stack_malloc_1` (0x835e8): the core's astack_malloc_realizes at class 1, through
      YC85.aj_stack_malloc_atS (C_reac_ctrl_parsePM.rcpPM_E1);
   3. the re-based stretch after the call (reac_ctrl_parseF_rpost.RPostFOn.post_all_F2: the return, the release store
      `sb zero, 0(a1)`, the epilogue) run on the normalized return memory (C_reac_ctrl_parsePN.rcpPN_post), lifted
      (C_reac_ctrl_parseK.rcpK_lift_norm);
   4. the release of the class-1 frame: astack_free_law through ProgWorldAstack.ctl_release_of_free_law
      (C_reac_ctrl_parsePR.rcpPR_release);
   5. the post: ajournal, aregs_preserved, frames / ablocks / set_fs, a0, the 36 record bytes
      (C_reac_ctrl_parsePA.rcpPA_rec), acall_kept (C_reac_ctrl_parseK.rcpK_compose with
      C_reac_ctrl_parsePA.rcpPA_kept_wr).
   Route (C): every shadow premise is shadow_rw_on R m, from A.ProgWorldCtlRtC.ctl_rt_C_of_AR and
   A.ShadowRwOn.shadow_rw_on_mono per region (C_reac_ctrl_parseV.rcpV_rt / rcpV_srR); no ctlrt_of_AR /
   shadow_rw_of_AR / VIS0 / OWNED_RO.
   Section hypotheses: errno_low, ML, SMP, ASM1 (the core's open premises, carried by every ctrl glue) and TS (image A's
   symbol table).  The callees of the post stretch are cited as proved: asan_memsetF_on.asan_memset_holds_F_on with
   memset.memset_holds, asan_memcpyF_on.asan_memcpy_holds_F_on (a Theorem Labs lane's root-free set, 68c959385a88),
   bcmp_wrap_on.bcmp_wrap_holds_F_on (a Theorem Labs lane, f4423e558860).
   Twin rule: every project module is Required without Import and named through a full-path Module alias. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame Cells Step PropExec MState ExecF Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Img0 AB1v AsanRT MemNorm MemNormTr ProgBridge AF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorld ProgWorld_Fs ProgWorldShadow ProgWorldVisFrame
  ProgWorldVisHeap ProgWorldBlkApart.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require C_reac_ctrl_parse CtrlImg ImgBounds
  asan_stack_malloc_c reac_ctrl_parse_c reac_ctrl_parseF reac_ctrl_parseF_rbody reac_ctrl_parseF_rpost RcAsanFP
  bcmp_wrap_c memcmp_c asan_memsetF_on asan_memcpyF_on memset bcmp_wrap_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require C_reac_ctrl_parseK C_reac_ctrl_parseV
  C_reac_ctrl_parseVF C_reac_ctrl_parseVS C_reac_ctrl_parseVR C_reac_ctrl_parsePP C_reac_ctrl_parsePM
  C_reac_ctrl_parsePN C_reac_ctrl_parsePR C_reac_ctrl_parsePA.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK04 YK04R YK0s YK14 YA0n YA0nR YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0f YG0n YG0v YG0d YG0q YG0s YCbq YE01
  YP09 APostBase.
Import ListNotations.
Local Open Scope Z_scope.

Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LX := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module R6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module AI0 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.
Module AB1v := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AB1v.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module MN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.
Module MNT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormTr.
Module PB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AF0m.
Module PWF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorld_Fs.
Module PWS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldShadow.
Module PWVF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldVisFrame.
Module PWVH := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldVisHeap.
Module PWBA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldBlkApart.
Module SP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_parse.
Module CI := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlImg.
Module IB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c.
Module PC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parse_c.
Module PF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parseF.
Module RB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parseF_rbody.
Module RP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parseF_rpost.
Module FP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.RcAsanFP.
Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c.
Module MC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.memcmp_c.
Module MSF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memsetF_on.
Module MCF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpyF_on.
Module MSET := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.memset.
Module BWO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_on.
Module K := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_parseK.
Module V := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_parseV.
Module VF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_parseVF.
Module VS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_parseVS.
Module VR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_parseVR.
Module PP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_parsePP.
Module PM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_parsePM.
Module PN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_parsePN.
Module PR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_parsePR.
Module PA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_parsePA.
Module RcP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.
Module RK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module RK04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Module RK04R := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04R.
Module RK0s := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK0s.
Module RK14 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK14.
Module RA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module RA0nR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Module RM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module RI16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Module RG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Module RG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Module RG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Module RG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Module RG0v := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0v.
Module RG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module RG0q := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0q.
Module RG0s := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0s.
Module RCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Module RE01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YE01.
Module RP09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.
Module APB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.APostBase.
Local Notation rsegs := AI0.rsegs (only parsing).

(* ---------------------------------------------------------------------------------------------------------
   1. Generic helpers (B's lib/B/Prog/C_reac_ctrl_parsePf.v PBH section and lib/B/Prog/C_reac_ctrl_classify_box_frame.v
   cls_ret_pc_ok, image A). *)

Lemma rcpP_ret_pc_ok : forall k : word, RK0s.ret_ok k -> LMS.ret_pc k = k.
Proof.
  intros k H. unfold RK0s.ret_ok in H. rewrite <- H at 2.
  unfold LMS.ret_pc. apply bv_eq.
  unfold RK14.v_jalr, RK11.jalr_tgtZ.
  rewrite bv_and_unsigned, bv_not_unsigned, !Z_to_bv_unsigned.
  change (bv_wrap 64 1) with 1%Z. change (Z.lnot 1) with (-2)%Z.
  rewrite Z.add_0_r.
  rewrite <- (bv_wrap_small 64 (bv_unsigned k)) at 1 by apply bv_unsigned_in_range.
  apply RK11.Z_land_m2_wrap.
Qed.

Lemma rcpP_img_nonneg : forall a, RG0d.in_img rsegs a -> 0 <= a.
Proof. intros a (sg & _ & Ha). lia. Qed.

Section PH.
Context {fx : RK11.FPState} {rc : RM05.RunCeil}.

(* Equal views at a visible byte: equal mrd. *)
Lemma rcpP_mrd_of_view : forall (H : word -> bool) (m m' : word -> option byte) a,
  H (Z_to_bv 64 a) = false ->
  RG0n.aview rsegs H m' a = RG0n.aview rsegs H m a ->
  LM.mrd rsegs m' (LM.wa a) = LM.mrd rsegs m (LM.wa a).
Proof.
  intros H m m' a Hh E. rewrite (V.rcpV_aview_mrd H m' a Hh), (V.rcpV_aview_mrd H m a Hh) in E.
  destruct (LM.mrd rsegs m' (LM.wa a)) as [b'|], (LM.mrd rsegs m (LM.wa a)) as [b|]; cbn [option_map] in E;
    try discriminate E; [|reflexivity].
  injection E as Eb. f_equal. apply bv_eq. exact Eb.
Qed.

(* Bytes the view reads at visible addresses are a bytes_at. *)
Lemma rcpP_bytes_of_view : forall (H : word -> bool) (m : word -> option byte) a (bs : list byte) (d : byte),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, (i < length bs)%nat -> H (Z_to_bv 64 (a + Z.of_nat i)) = false) ->
  (forall i, (i < length bs)%nat ->
     RG0n.aview rsegs H m (a + Z.of_nat i) = Some (bv_unsigned (nth i bs d))) ->
  LM.bytes_at rsegs m a bs.
Proof.
  intros H m a bs d H0 H1 Hh Hv. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (Hv i Hi) as Vi. rewrite (V.rcpV_aview_mrd H m _ (Hh i Hi)) in Vi.
  rewrite (nth_error_nth' bs d Hi).
  destruct (LM.mrd rsegs m (LM.wa (a + Z.of_nat i))) as [b|]; cbn [option_map] in Vi; [|discriminate Vi].
  injection Vi as Vi. f_equal. apply bv_eq. exact Vi.
Qed.

(* A writable range above the image whose bytes are not hidden is present. *)
Lemma rcpP_pres_of_stk : forall (H : word -> bool) (m : word -> option byte) lo hi,
  IB.IMG_HI <= lo -> LF.stk rsegs m lo hi ->
  (forall a, lo <= a < hi -> H (Z_to_bv 64 a) = false) ->
  forall a, lo <= a < hi -> RG0n.apresent H m a.
Proof.
  intros H m lo hi Hlo (H0 & H1 & Hs) Hh a Ha.
  split; [exact (Hh a Ha)|].
  destruct (Hs a Ha) as [_ (b & Hb)]. unfold LM.mrd in Hb.
  assert (Hr : LP.seg_rom rsegs (LM.wa a) = None) by (apply K.rcpK_seg_rom_above; lia).
  unfold LM.wa in Hb, Hr.
  destruct (m (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|].
  assert (Hx : LP.seg_rom rsegs (Z_to_bv 64 a) = Some b) by exact Hb. rewrite Hr in Hx. discriminate Hx.
Qed.
End PH.

(* The real write set of the lifted post stretch: off WR the real end memory m' is the real start memory m, from the
   normalized run's munch over the flag-0 base mB (VT's mB = write (normalize m) fl 0) and fl inside WR. *)
Lemma rcpP_munch_base : forall (WR : list LF.ivl) (m mB m0 m' : word -> option byte) (fl : Z),
  LF.munch [(fl, fl + 1)] mB (MN.normalize rsegs m) ->
  (forall x : word, LF.outside WR (bv_unsigned x) -> LF.outside [(fl, fl + 1)] (bv_unsigned x)) ->
  LF.munch WR mB m0 -> MN.mem_rel rsegs m' m0 -> MN.ro_same rsegs m m' -> LF.munch WR m m'.
Proof.
  intros WR m mB m0 m' fl MUfl Hsub MUW REL ROS x Hx.
  destruct (LM.ro_addr rsegs x) eqn:R; [exact (ROS x R)|].
  rewrite <- (MN.mem_rel_rw rsegs m' m0 x REL R). rewrite (MUW x Hx). rewrite <- (MUfl x (Hsub x Hx)).
  unfold MN.normalize. rewrite R. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   2. The theorem. *)
Section P.
Context {fx : RK11.FPState} {rc : RM05.RunCeil} {SK : RI16.sink_head}.
Variable B : RG0f.asyms.
Variables RLO RHI : Z.
(* The core's open premises, carried by every ctrl glue (YCbq.v api_env; YG0d.v model_laws; YCbq.v
   stack_malloc_progressP; YG0d.v:285 astack_malloc_realizes at class 1). *)
Hypothesis errno_low : RCbq.api_env rsegs B.
Hypothesis ML : RG0d.model_laws (RG0f.as_universe B).
Hypothesis SMP : RCbq.stack_malloc_progressP B.
Hypothesis ASM1 : RG0d.astack_malloc_realizes rsegs B 1.
(* image A's symbol table (AF0m.v:2986). *)
Hypothesis TS : AF.CtrlTSyms B.
(* AR_laws of the bundle: the core's own proof (no premise). *)
Local Notation LAWS := (RG0q.AR_laws_ok rsegs B).

Theorem pb_reac_ctrl_parse : SP.treac_ctrl_parse_spec (SK := SK) B RLO RHI.
Proof.
  unfold SP.treac_ctrl_parse_spec.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs f n o fr
    HJ ARO HRA HRA4 Hgp Htp H10 H11 H12 Hn HS16 Hlo Hhi Hcnt HFB Hof Hawr Lfr Hfr.
  change AB1v.tfibsegs with rsegs in *.
  set (S := RG0d.spZ regs) in *.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _ & _).
  destruct Hastk as (H16sp0 & HSTK & Hceil & Hslo & Hshi & H47 & _).
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Eslo & Eshi & _).
  pose proof (@RM05.alloc_ceiling_value rc) as [[Hc0 Hc1] _].
  pose proof (@RM05.alloc_ceiling_lt rc) as Hclt.
  unfold SP.REAC_CTRL_PARSE_STK in Hlo.
  assert (B1 : RM05.alloc_ceiling <= S - 8800) by lia.
  assert (B3 : ART.HIGHMEM_BEG <= S - 8800) by (unfold ART.HIGHMEM_BEG; lia).
  assert (B4 : S <= ART.APPMEM_END) by (unfold ART.APPMEM_END; lia).
  assert (RS : 8800 <= S < 2 ^ 64) by lia.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (ESlo : RG0f.ly_stk_lo lyc <= S - 8800) by lia.
  assert (EShi : S <= RG0f.ly_stk_hi lyc) by lia.
  set (A := (S - 128) / 32 * 32) in *.
  assert (HA : A mod 32 = 0 /\ S - 160 < A <= S - 128) by (unfold A; Z.div_mod_to_equations; lia).
  (* tp = RT_TP *)
  assert (TPv : bv_unsigned (reg_get regs 4) = ART.RT_TP).
  { transitivity (bv_unsigned (RG0d.w64 (RG0f.as_tp B))); [exact (f_equal (@bv_unsigned 64) Htp)|].
    rewrite (AF.ts_tp B TS). unfold RG0d.w64. rewrite Z_to_bv_unsigned. vm_compute. reflexivity. }
  (* ---- the world at the entry memory memc ---- *)
  destruct (V.rcpV_rt B TS RLO RHI lyc Sc W memc mdc HAR ARO)
    as (ROc & ACc & _ & _ & _ & _ & _ & _ & _).
  destruct (V.rcpV_win B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k (S - 8800) S HJ
              ltac:(lia) ltac:(lia) ltac:(lia)) as (STc & _ & _).
  (* a0 / a2 as numbers *)
  set (fZ := bv_unsigned (RK11.getr regs 10)).
  assert (RfZ : 0 <= fZ < 2 ^ 64).
  { pose proof (bv_unsigned_in_range 64 (RK11.getr regs 10)) as R.
    change (bv_modulus 64) with (2 ^ 64) in R. exact R. }
  assert (EfZ : 50 <= n -> fZ = f /\ exists Lf, In (f, Lf) (RG0d.ablocks B lyc Sc) /\
                  50 <= RG00.req_size Lf /\ 4096 <= f /\ f + RG00.req_size Lf <= RM05.alloc_ceiling).
  { intros Hn50. destruct (HFB Hn50) as (Lf & InF & HLf).
    destruct (RG0d.al_blocks _ _ LAWS _ _ _ _ _ f Lf HAR InF) as (_ & Hf0 & Hf1 & _).
    split; [|exists Lf; repeat split; assumption].
    unfold fZ. rewrite H10. unfold RG0d.w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  assert (HFBz : 50 <= n -> exists Lf, In (fZ, Lf) (RG0d.ablocks B lyc Sc) /\ 50 <= RG00.req_size Lf).
  { intros Hn50. destruct (EfZ Hn50) as (E & Lf & InF & HLf & _). rewrite E. exists Lf. split; assumption. }
  assert (HoF : o <> 0 -> exists co po, In (co, po) (RG01.frames Sc) /\
            RG0f.frame_addr lyc co po <= o /\
            o + 36 <= RG0f.frame_addr lyc co po + RG00.fs_frame_bytes co).
  { intros Hne. destruct (Hof Hne) as ((co & po & Ino & _ & _ & Hf1 & Hf2) & _ & _).
    exists co, po. repeat split; assumption. }
  assert (Ro : 0 <= o < 2 ^ 64).
  { destruct (Z.eq_dec o 0) as [->|Hne]; [lia|]. destruct (HoF Hne) as (co & po & Ino & Hf1 & Hf2).
    destruct (RCbq.frames_bounds rsegs B LAWS lyc Sc W memc mdc co po HAR Ino) as (F1 & F2 & _).
    pose proof (RCbq.fs_frame_bytes_nonneg co). lia. }
  (* the window and the record are not owned (awr bytes) *)
  assert (WNO : forall a, S - 8800 <= a < S -> ~ RG0n.aowned B lyc Sc a).
  { intros a Ha. refine (proj1 (RCbq.awr_byte_cases rsegs B LAWS STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc
                                k a HJ _)). unfold RCbq.awr_byte. left. lia. }
  assert (ONO : o <> 0 -> forall a, o <= a < o + 36 -> ~ RG0n.aowned B lyc Sc a).
  { intros Hne a Ha. exact (proj1 (RCbq.awr_byte_cases rsegs B LAWS STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc
                                   mdc k a HJ (Hawr Hne a Ha))). }
  (* the free frames X: o's own class-1 frame, when o lies in one *)
  assert (HXok : exists X, VF.rcpVF_Xok lyc Sc o X).
  { destruct (Z.eq_dec o 0) as [E0|Hne]; [exists []; left; split; [exact E0 | reflexivity]|].
    destruct (HoF Hne) as (co & po & Ino & Hf1 & Hf2).
    exists (if co =? 1 then [(1%nat, po)] else []). right. split; [exact Hne|].
    exists co, po. split; [exact Ino|]. split; [exact Hf1|]. split; [exact Hf2 | reflexivity]. }
  destruct HXok as (X & HXok).
  pose proof (VF.rcpVF_fpx B TS lyc Sc W memc mdc fZ n o S X HAR B1 B3 B4 WNO ONO HFBz HXok) as FPXc.
  rewrite <- TPv in FPXc.
  (* ================= G0: the entry state in the form of rcpPP_to_E1 ================= *)
  rewrite PB.cfg_at_MS.
  assert (XR0 : R6.xregs_eqv
    (LF.mkR (reg_get regs 1) (Z_to_bv 64 S) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5) (reg_get regs 6)
       (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (Z_to_bv 64 fZ) (Z_to_bv 64 n) (Z_to_bv 64 o)
       (reg_get regs 13) (reg_get regs 14) (reg_get regs 15) (reg_get regs 16) (reg_get regs 17) (reg_get regs 18)
       (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24)
       (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29) (reg_get regs 30)
       (reg_get regs 31)) regs).
  { apply R6.xregs_eqv_sym. apply R6.mkR_eqv_of;
      first [ reflexivity | exact H11 | exact H12
            | (unfold fZ; rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned; reflexivity)
            | (unfold S, RG0d.spZ; rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned; reflexivity) ]. }
  refine (RA0nR.SRr_xregs_eqv rsegs W _ regs _ _ _ _ _ _ _ _ _ XR0).
  change (RK11.seg_rom rsegs) with (LP.seg_rom rsegs).
  replace (Z_to_bv 64 SP.A_reac_ctrl_parseP) with (Z_to_bv 64 PC.REAC_CTRL_PARSE) by (vm_compute; reflexivity).
  (* ================= S-A + J1: the entry stretch, lifted ================= *)
  apply (PP.rcpPP_to_E1 B CI.ctrl_wx STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k
           (reg_get regs 1) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5) (reg_get regs 6)
           (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15)
           (reg_get regs 16) (reg_get regs 17) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21)
           (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27)
           (reg_get regs 28) (reg_get regs 29) (reg_get regs 30) (reg_get regs 31) RK11.fp_regs RK11.fp_csr
           fZ n o S (RG0f.ly_F lyc) fr X _ HJ Hlo Hhi RfZ Hn Ro RS HS16 B3 B4 Lfr ROc STc ACc FPXc).
  { split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hpres a ltac:(lia))). }
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 m1n mdc1
    MU1 WM1 RM1 MI1 SV1 ST1 HMR1 HROS1 HHID1 HJ1.
  (* ================= E1: the call of __asan_stack_malloc_1 ================= *)
  apply (PM.rcpPM_E1 B errno_low ML SMP ASM1 TS STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W m1 mdc1 k
           (reg_get regs 3) (reg_get regs 4) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' (reg_get regs 18)
           (reg_get regs 19) (reg_get regs 23) (reg_get regs 24) (reg_get regs 26) (reg_get regs 27) t3' t4' t5' t6'
           fZ n o S _ HJ1 Hlo Hhi RS HS16 Hgp Htp Hcnt).
  intros S2 regs2 mem2 md2 pos f2 HJ2 HP C10 HAB HFR HNI ES2 HKEPT CFL C120.
  (* ================= the facts at the return memory mem2 of the class-1 request ================= *)
  pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _ & _ & _).
  assert (In1 : In (1, pos) (RG01.frames S2)) by (rewrite HFR; left; reflexivity).
  assert (InSc : forall c q, In (c, q) (RG01.frames Sc) -> In (c, q) (RG01.frames S2))
    by (intros c q Hcq; rewrite HFR; right; exact Hcq).
  assert (Ne1 : forall c q, In (c, q) (RG01.frames Sc) -> (c, q) <> (1, pos))
    by (intros c q Hcq E; rewrite E in Hcq; exact (HNI Hcq)).
  assert (InB2 : forall p m, In (p, m) (RG0d.ablocks B lyc Sc) -> In (p, m) (RG0d.ablocks B lyc S2))
    by (intros p m Hpm; rewrite HAB; exact Hpm).
  assert (EB1 : RG00.fs_frame_bytes 1 = 128) by reflexivity.
  pose proof (V.rcpV_frame B lyc S2 W mem2 md2 pos HAR2 In1) as WF. cbv zeta in WF.
  destruct WF as (FkLo & FkCeil & FLimg & FLceil & FlApp & FlSt & FLvis & SHimg & SHceil).
  destruct (V.rcpV_fgeo B lyc S2 W mem2 md2 1 pos HAR2 In1)
    as (_ & FGT & Ffr1 & Ffr2 & Ffr64 & _ & _ & Ffl1 & Ffl2 & Fapp).
  pose proof HAR2 as (M2 & _).
  destruct (RG0s.frame_facts B lyc S2 _ 1 pos M2 In1) as (_ & Hpos & _).
  set (FS := RG0f.ly_F lyc) in *.
  set (fra := RG0f.frame_addr lyc 1 pos) in *.
  set (fl := RG0f.flag_addr lyc 1 pos) in *.
  assert (Efra : fra = SMC.fs_frame FS 1 pos).
  { unfold fra, FS, RG0f.frame_addr, RG0f.fs_frame_off, SMC.fs_frame, SMC.fs_B, RG0f.kFakeFramesOff.
    rewrite EB1. cbn [Z.of_nat Pos.of_succ_nat]. change (Z.shiftl 1 RG00.kStackSizeLog) with (2 ^ 20). lia. }
  assert (Efl : SMC.fs_flag FS 1 pos = fl).
  { unfold fl, FS, RG0f.flag_addr, RG0f.fs_flag_off, SMC.fs_flag, RG0f.kFakeFlagsOff.
    change (RG0f.fs_flags_off 1) with 16384. cbn [Z.of_nat Pos.of_succ_nat].
    change (2 ^ 15) with 32768. change (2 ^ (15 - 1)) with 16384. lia. }
  assert (Hjj : 0 <= pos < SMC.fs_M 1) by (change (SMC.fs_M 1) with (RG00.fs_frames 1); exact Hpos).
  pose proof (PWF.pw_F_above B lyc S2 W mem2 md2 HAR2) as HGT.
  assert (HFSe : FS + SMC.FS_SIZE <= S - 8800).
  { unfold SMC.FS_SIZE. unfold RG0f.kFakeStackSize, RG0f.kLowShadowBeg, RG0f.kHighMemBeg in Fapp. lia. }
  assert (HFSapp : forall a, FS <= a < FS + SMC.FS_SIZE -> ART.app_mem a).
  { intros a Ha. unfold SMC.FS_SIZE in Ha. unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END.
    unfold SMC.ASAN_GT in HGT.
    unfold RG0f.kFakeStackSize, RG0f.kLowShadowBeg, RG0f.kHighMemBeg in Fapp. lia. }
  (* the views at mem2: the prologue kept every byte off [S - 8800, S), the call keeps (acall_kept) *)
  pose proof (K.rcpK_raw_SA memc m1 m1n (S - 8800) S HMR1 HROS1 MU1) as RA1.
  pose proof HKEPT as (KP1 & KP2 & KP3 & KP4 & KP5 & KP6).
  assert (VA : forall H a, 0 <= a < S - 8800 -> RG0n.aview rsegs H m1 a = RG0n.aview rsegs H memc a).
  { intros H a Ha. apply K.rcpK_aview_eq. apply RA1. rewrite K.rcpK_u64 by lia. lia. }
  assert (ARO2 : RE01.arodata_okS rsegs B RLO RLO (RG0n.aview rsegs (RA0n.w_H W) mem2)).
  { intros a Hro Hst Her. destruct Hro as [(sg & Hsg & Hwr & Hr) | Hg]; [|lia].
    assert (Hai : RG0d.in_img rsegs a) by (exists sg; split; [exact Hsg | exact Hr]).
    pose proof (V.rcpV_img_lt a Hai) as Hia. pose proof (rcpP_img_nonneg a Hai) as Hia0.
    rewrite (KP3 a Hai Hst Her). rewrite (VA _ a ltac:(unfold IB.IMG_HI in Hia; lia)).
    exact (ARO a (or_introl (ex_intro _ sg (conj Hsg (conj Hwr Hr)))) Hst Her). }
  destruct (V.rcpV_rt B TS RLO RLO lyc S2 W mem2 md2 HAR2 ARO2)
    as (RO2 & AC2 & SRcut2 & SRimg2 & HBC2 & HMC2 & HGC2 & H254 & H255).
  destruct (V.rcpV_win B STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) lyc S2 W mem2 md2 k (S - 8800) S HJ2
              ltac:(lia) ltac:(lia) ltac:(lia)) as (ST2 & AW2 & _).
  replace (S - (S - 8800)) with 8800 in AW2 by lia.
  destruct (V.rcpV_vis_win B STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) lyc S2 W mem2 md2 k (S - 8800) 8800
              HJ2 ltac:(lia) ltac:(lia) ltac:(lia)) as (RWIN & SCW & _).
  destruct (V.rcpV_vis_win B STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) lyc S2 W mem2 md2 k (S - 288) 160
              HJ2 ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & SKW).
  (* the caller's block f (n >= 50) *)
  assert (BLK : 50 <= n -> fZ = f /\ exists Lf, In (f, Lf) (RG0d.ablocks B lyc Sc) /\
                  In (f, Lf) (RG0d.ablocks B lyc S2) /\ 50 <= RG00.req_size Lf /\
                  4096 <= f /\ f + RG00.req_size Lf <= RM05.alloc_ceiling).
  { intros Hn50. destruct (EfZ Hn50) as (E & Lf & InF & HLf & H4 & Hc). split; [exact E|].
    exists Lf. split; [exact InF|]. split; [exact (InB2 _ _ InF)|]. split; [exact HLf|]. split; [exact H4 | exact Hc]. }
  (* the record buffer o's 36 bytes: some bytes, present (they lie in a caller's frame) *)
  assert (HJK : exists junk : list byte, o <> 0 -> LS.rw_cells rsegs mem2 o [LC.CB 36 junk]).
  { destruct (Z.eq_dec o 0) as [E0|Hne]; [exists []; intros H; exfalso; exact (H E0)|].
    destruct (HoF Hne) as (co & po & Ino & Hf1 & Hf2).
    destruct (V.rcpV_in_frame B lyc S2 W mem2 md2 co po o 36 HAR2 (InSc co po Ino) ltac:(lia) Hf1 Hf2)
      as (_ & _ & _ & _ & STo).
    destruct (LF.stk_carve rsegs mem2 o (o + 36) 36 STo ltac:(lia)) as [_ [junk Hj]].
    replace (o + 36 - Z.of_nat 36) with o in Hj by lia.
    exists junk. intros _. exact Hj. }
  destruct HJK as (junk & Hjunk).
  assert (HF : 50 <= n -> 0 < fZ /\ fZ + 50 <= 2 ^ 64 /\ (fZ + 50 <= S - 8800 \/ S <= fZ)).
  { intros Hn50. destruct (BLK Hn50) as (E & Lf & _ & _ & HLf & H4 & Hc). rewrite E. lia. }
  assert (BYf : 50 <= n -> LM.bytes_at rsegs mem2 fZ fr).
  { intros Hn50. destruct (BLK Hn50) as (E & Lf & InF & InF2 & HLf & H4 & Hc). rewrite E.
    pose proof (PWVH.heap_vis B LAWS lyc S2 W mem2 md2 f Lf f 50 HAR2 InF2 ltac:(lia) ltac:(lia)) as (_ & _ & VFh).
    apply (rcpP_bytes_of_view (RA0n.w_H W) mem2 f fr RcP.cp_z); [lia | rewrite Lfr; lia | |].
    - intros i Hi. rewrite Lfr in Hi. apply VFh. lia.
    - intros i Hi. rewrite Lfr in Hi.
      rewrite (KP2 f Lf (Z.of_nat i) InF ltac:(lia) ltac:(intros [])).
      rewrite VA by lia. exact (Hfr Hn50 i Hi). }
  assert (Hrd : forall i, In i (RcP.cp_rd n fr) -> LM.mrd rsegs mem2 (LM.wa (fZ + Z.of_nat i)) = nth_error fr i).
  { intros i Hi. destruct (Z_le_gt_dec 50 n) as [Hn50|Hn50].
    - destruct (BYf Hn50) as (_ & _ & Hb). apply Hb. rewrite Lfr.
      pose proof (RcP.cp_rd_lt39 n fr i Hi). lia.
    - exfalso. unfold RcP.cp_rd in Hi.
      replace (50 <=? n) with false in Hi by (symmetry; apply Z.leb_gt; lia). cbn in Hi. exact Hi. }
  assert (HOK : o <> 0 -> o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ (o + 36 <= S - 8800 \/ S <= o) /\
                  (50 <= n -> o + 36 <= fZ \/ fZ + 50 <= o) /\ ART.app_mem (o + 36) /\
                  (o + 36 <= BW.GOT_CF \/ BW.CF + 256 <= o) /\ SMC.fs_frame FS 0 0 <= o).
  { intros Hne. destruct (Hof Hne) as ((co & po & Ino & _ & Hf8 & Hf1 & Hf2) & Ho8 & _).
    destruct (RCbq.frames_bounds rsegs B LAWS lyc Sc W memc mdc co po HAR Ino) as (F1 & F2 & F3).
    destruct (V.rcpV_fgeo B lyc Sc W memc mdc co po HAR Ino) as (_ & FGc & Fc1 & _).
    destruct (V.rcpV_in_frame B lyc Sc W memc mdc co po o 36 HAR Ino ltac:(lia) Hf1 Hf2) as (_ & OH & _).
    split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [left; lia|].
    split.
    { intros Hn50. destruct (BLK Hn50) as (E & Lf & InF & _ & HLf & _). rewrite E.
      pose proof (RCbq.sep_block_frame rsegs B LAWS lyc Sc W memc mdc f Lf co po HAR InF Ino) as D.
      unfold RG0f.zdisjoint in D. cbn [fst snd] in D. lia. }
    split.
    { destruct F3 as [_ F3].
      unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END.
      unfold RG0f.kLowShadowBeg, RG0f.kHighMemBeg, RG0f.ASAN_CEIL in F3. lia. }
    split; [right; unfold BW.CF, IB.IMG_HI in *; lia|].
    unfold SMC.fs_frame, FS. cbn [Z.of_nat]. unfold RG0f.kFakeFramesOff in Fc1. lia. }
  assert (AF0 : 50 <= n -> ART.addressable mem2 fZ 50).
  { intros Hn50. destruct (BLK Hn50) as (E & Lf & _ & InF2 & HLf & _). rewrite E.
    exact (PWS.ctl_block_shadow_of_AR B LAWS lyc S2 W mem2 md2 f Lf f 50 HAR2 InF2
             (Z.le_refl _) ltac:(lia) ltac:(lia)). }
  assert (AO0 : o <> 0 -> ART.addressable mem2 o 36).
  { intros Hne. destruct (Hof Hne) as ((co & po & Ino & _ & Hf8 & Hf1 & Hf2) & Ho8 & RAo).
    destruct (RCbq.frames_bounds rsegs B LAWS lyc Sc W memc mdc co po HAR Ino) as (F1 & F2 & F3).
    destruct (V.rcpV_fgeo B lyc Sc W memc mdc co po HAR Ino) as (_ & _ & _ & _ & _ & Hb64 & Hbm & _).
    apply (V.rcpV_addressable_of_view W mem2 o 36); [lia | lia | unfold ART.APPMEM_END; lia | |].
    - intros i Hi. apply (V.rcpV_app_of_in_app _ _ (o + i) F3). lia.
    - apply (V.rcpV_ra_transfer (RG0n.aview rsegs (RA0n.w_H W) memc)); [|exact RAo].
      intros x Hx.
      assert (Hsx : RG0n.in_zr (RG0v.shadow_of_addr RG0f.SHADOW_OFF x)
                (RG0f.shadow_addr (RG0f.frame_addr lyc co po), RG00.fs_frame_bytes co / 8)).
      { apply V.rcpV_sh_in_frame; [exact Hf8 | Z.div_mod_to_equations; lia | lia]. }
      transitivity (RG0n.aview rsegs (RA0n.w_H W) m1 (RG0v.shadow_of_addr RG0f.SHADOW_OFF x)).
      + exact (KP4 co po _ Ino (or_intror Hsx) (fun H => H)).
      + apply VA. unfold RG0v.shadow_of_addr, RG0f.SHADOW_OFF. Z.div_mod_to_equations. lia. }
  destruct (VS.rcpVS_bc B TS lyc S2 W mem2 md2 HAR2) as (ABC & SKBC).
  destruct (VS.rcpVS_side B lyc S2 W mem2 md2 HAR2) as (RFLG & RFRM & SCFR & SKFR).
  pose proof (VR.rcpVR_fss B lyc S2 W mem2 md2 HAR2) as RFSS.
  pose proof (VR.rcpVR_fw1 B lyc S2 W mem2 md2 HAR2) as RFW1.
  (* the route (C) shadow premise: R inside ctl_rt_C's regions *)
  pose proof (V.rcpV_srR B lyc S2 W mem2 md2 fZ n o S HAR2 SRcut2 SRimg2 ltac:(lia) ltac:(lia)
                (fun Hne => match HoF Hne with ex_intro _ co (ex_intro _ po (conj Ino Hc)) =>
                              ex_intro _ co (ex_intro _ po (conj (InSc co po Ino) Hc)) end)
                (fun Hn50 => match HFBz Hn50 with ex_intro _ Lf (conj InF HLf) =>
                               ex_intro _ Lf (conj (InB2 _ _ InF) HLf) end)) as SR2.
  (* the free frames at S2, flag 1 *)
  assert (HXok2 : VF.rcpVF_Xok lyc S2 o X).
  { destruct HXok as [(E0 & EX) | (Hne & co & po & Ino & Hf1 & Hf2 & EX)]; [left; split; assumption|].
    right. split; [exact Hne|]. exists co, po. split; [exact (InSc co po Ino)|]. split; [exact Hf1|].
    split; [exact Hf2 | exact EX]. }
  destruct (VF.rcpVF_XF B lyc S2 W mem2 md2 o X HAR2 HXok2) as (XF2 & XB2).
  assert (XB2' : Forall (fun ci => 0 <= snd ci < SMC.fs_M 1 /\ snd ci <> pos) X).
  { destruct HXok as [(_ & ->) | (Hne & co & po & Ino & _ & _ & ->)]; [constructor|].
    destruct (Z.eqb_spec co 1) as [->|Hc]; [|constructor].
    inversion XB2 as [|ci l Hci _]; subst. constructor; [|constructor].
    split; [exact Hci|]. cbn [snd]. intros Ep. subst po. exact (HNI Ino). }
  (* the window and the record at S2: not owned *)
  assert (WNO2 : forall a, S - 8800 <= a < S -> ~ RG0n.aowned B lyc S2 a).
  { intros a Ha. refine (proj1 (RCbq.awr_byte_cases rsegs B LAWS STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own)
                                lyc S2 W mem2 md2 k a HJ2 _)). unfold RCbq.awr_byte. left. lia. }
  assert (ONO2 : o <> 0 -> forall a, o <= a < o + 36 -> ~ RG0n.aowned B lyc S2 a).
  { intros Hne a Ha. refine (proj1 (RCbq.awr_byte_cases rsegs B LAWS STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own)
                                     lyc S2 W mem2 md2 k a HJ2 _)).
    pose proof (Hawr Hne a Ha) as Haw. unfold RCbq.awr_byte in Haw |- *. rewrite HAB.
    destruct Haw as [Q|[Q|[Q|Q]]]; [left; exact Q | right; left; exact Q | right; right; left; exact Q|].
    right; right; right. destruct Q as (cid & pos' & Hown & Q). exists cid, pos'. split; [right; exact Hown | exact Q]. }
  pose proof (VF.rcpVF_fpx B TS lyc S2 W mem2 md2 fZ n o S X HAR2 B1 B3 B4 WNO2 ONO2
                (fun Hn50 => match HFBz Hn50 with ex_intro _ Lf (conj InF HLf) =>
                               ex_intro _ Lf (conj (InB2 _ _ InF) HLf) end) HXok2) as FPX2.
  rewrite <- TPv in FPX2.
  pose proof (VF.rcpVF_tls B TS lyc S2 W mem2 md2 S HAR2 ltac:(lia) ltac:(lia)) as TLS2.
  rewrite <- TPv in TLS2.
  assert (RTLS2 : forall DT TS' C T DB kk, SMC.asan_tls_cells mem2 (bv_unsigned (reg_get regs 4)) DT TS' C T DB kk ->
            Forall (fun iv => LX.rng (PB.RNG_W (RA0n.w_H W)) (fst iv) (snd iv - fst iv))
              (FP.fp_tls (bv_unsigned (reg_get regs 4)) DT TS' C T DB kk)).
  { rewrite TPv. exact (VR.rcpVR_rtls B TS lyc S2 W mem2 md2 HAR2). }
  (* the footprint premises at RNG := RNG_W (w_H W) *)
  assert (RIMG : LX.rng (PB.RNG_W (RA0n.w_H W)) 0x10000 0x5ee000).
  { pose proof (PB.rng_of_visible _ _ _ (PB.img_vis_W W)) as R.
    unfold IB.IMG_LO, IB.IMG_HI in R. exact R. }
  assert (RBC : LX.rng (PB.RNG_W (RA0n.w_H W)) PC.REAC_CTRL_PARSE_BC 6).
  { apply (LX.rng_sub _ 0x10000 0x5ee000 _ _ RIMG); unfold PC.REAC_CTRL_PARSE_BC; lia. }
  assert (VF2 : 50 <= n ->
    LX.rng (PB.RNG_W (RA0n.w_H W)) fZ 50 /\ V.rcpV_shc (PB.RNG_W (RA0n.w_H W)) fZ 50 /\
    V.rcpV_shk (PB.RNG_W (RA0n.w_H W)) fZ 50).
  { intros Hn50. destruct (BLK Hn50) as (E & Lf & _ & InF2 & HLf & _). rewrite E.
    exact (V.rcpV_vis_block B lyc S2 W mem2 md2 f Lf f 50 HAR2 InF2 (Z.le_refl _) ltac:(lia) ltac:(lia)). }
  assert (VO2 : o <> 0 ->
    LX.rng (PB.RNG_W (RA0n.w_H W)) o 36 /\ V.rcpV_shc (PB.RNG_W (RA0n.w_H W)) o 36 /\
    V.rcpV_shk (PB.RNG_W (RA0n.w_H W)) o 36).
  { intros Hne. destruct (HoF Hne) as (co & po & Ino & Hf1 & Hf2).
    exact (V.rcpV_vis_frame B lyc S2 W mem2 md2 co po o 36 HAR2 (InSc co po Ino) Hf1 Hf2 ltac:(lia)). }
  (* the 12 saved registers at [S - 96, S): the prologue's cells at m1n, read at m1, kept by the call *)
  assert (SVm : LS.rw_cells rsegs mem2 (S - 96)
      (PF.ParseFOn.SAVES (reg_get regs 1) (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19)
         (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
         (reg_get regs 26))).
  { pose proof (MNT.rw_cells_of_rel m1 m1n _ _ HMR1 SV1) as SV1r.
    unfold PF.ParseFOn.SAVES in SV1r |- *.
    apply (K.rcpK_rw_cells_tr m1 mem2 (S - 96) _ SV1r).
    - intros i Hi. cbn [LC.cells_size LC.csize Nat.add] in Hi.
      apply (rcpP_mrd_of_view (RA0n.w_H W)).
      + exact (proj1 (Hpres2 (S - 96 + i) ltac:(lia))).
      + apply KP1; [lia | unfold RG0d.ESTACK; lia].
    - cbn [LC.cells_size LC.csize Nat.add]. apply (V.rcpV_stk_of_pres (RA0n.w_H W)); [lia | lia |].
      intros a Ha. apply Hpres2. lia. }
  (* the back pointer and the flag byte in fs_ form *)
  assert (C120' : LM.bytes_at rsegs mem2 (SMC.fs_frame FS 1 pos + 120) (LM.le8 (Z_to_bv 64 (SMC.fs_flag FS 1 pos)))).
  { rewrite <- Efra, Efl. exact C120. }
  assert (CFL' : LM.bytes_at rsegs mem2 (SMC.fs_flag FS 1 pos) [Z_to_bv 8 1]) by (rewrite Efl; exact CFL).
  (* ================= (a) the state at 0x835ec in rcpPN_post's register form ================= *)
  assert (XR2 : R6.xregs_eqv
    (LF.mkR (reg_get regs2 1) (Z_to_bv 64 A) (reg_get regs 3) (reg_get regs 4) (reg_get regs2 5)
       (reg_get regs2 6) (reg_get regs2 7) (Z_to_bv 64 S) (Z_to_bv 64 A)
       (Z_to_bv 64 (SMC.fs_frame FS 1 pos)) (reg_get regs2 11) (reg_get regs2 12)
       (reg_get regs2 13) (reg_get regs2 14) (reg_get regs2 15) (reg_get regs2 16) (reg_get regs2 17)
       (reg_get regs 18) (reg_get regs 19) (Z_to_bv 64 o) (Z_to_bv 64 fZ) (Z_to_bv 64 n) (reg_get regs 23)
       (reg_get regs 24) (LM.wa 0x7fff8000) (reg_get regs 26) (reg_get regs 27) (reg_get regs2 28) (reg_get regs2 29)
       (reg_get regs2 30) (reg_get regs2 31)) regs2).
  { apply R6.xregs_eqv_sym. apply R6.mkR_eqv_of;
      first [ reflexivity | (rewrite <- Efra; exact C10)
            | exact (HP 2 ltac:(unfold RG0d.acallee_saved; lia))
            | exact (HP 3 ltac:(unfold RG0d.acallee_saved; lia))
            | exact (HP 4 ltac:(unfold RG0d.acallee_saved; lia))
            | exact (HP 8 ltac:(unfold RG0d.acallee_saved; lia))
            | exact (HP 9 ltac:(unfold RG0d.acallee_saved; lia))
            | exact (HP 18 ltac:(unfold RG0d.acallee_saved; lia))
            | exact (HP 19 ltac:(unfold RG0d.acallee_saved; lia))
            | exact (HP 20 ltac:(unfold RG0d.acallee_saved; lia))
            | exact (HP 21 ltac:(unfold RG0d.acallee_saved; lia))
            | exact (HP 22 ltac:(unfold RG0d.acallee_saved; lia))
            | exact (HP 23 ltac:(unfold RG0d.acallee_saved; lia))
            | exact (HP 24 ltac:(unfold RG0d.acallee_saved; lia))
            | exact (HP 25 ltac:(unfold RG0d.acallee_saved; lia))
            | exact (HP 26 ltac:(unfold RG0d.acallee_saved; lia))
            | exact (HP 27 ltac:(unfold RG0d.acallee_saved; lia)) ]. }
  change (RK11.mkst regs2 (Z_to_bv 64 0x835ec) mem2 (RK11.seg_rom rsegs))
    with (LMS.MS regs2 RK11.fp_regs (Z_to_bv 64 0x835ec) RK11.fp_csr None mem2 (LP.seg_rom rsegs)).
  refine (RA0nR.SRr_xregs_eqv rsegs W _ regs2 _ _ _ _ _ _ _ _ _ XR2).
  (* f's 50 bytes are apart from the side stack (ProgWorldBlkApart.ctl_block_apart_fs) *)
  assert (HFap : 50 <= n -> fZ + 50 <= FS \/ FS + SMC.FS_SIZE <= fZ).
  { intros Hn50. destruct (BLK Hn50) as (E & Lf & _ & InF2 & HLf & _). rewrite E.
    destruct (PWBA.ctl_block_apart_fs B LAWS lyc S2 W mem2 md2 f Lf HAR2 InF2) as [Q|Q]; [left | right];
      change (RG0f.ly_F lyc) with FS in Q; unfold RG0f.kFakeStackSize in Q; unfold SMC.FS_SIZE; lia. }
  (* ================= (b) + (c) the re-based stretch on normalize mem2, lifted ================= *)
  eapply (K.rcpK_lift_norm CI.ctrl_wx W md2); [exact RO2 | |].
  { eapply (PN.rcpPN_post (MSF.asan_memset_holds_F_on MSET.memset_holds) MCF.asan_memcpy_holds_F_on
             BWO.bcmp_wrap_holds_F_on mem2 (PB.RNG_W (RA0n.w_H W))
             (reg_get regs 1) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8) (reg_get regs 9)
             (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
             (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27)
             RK11.fp_regs RK11.fp_csr fZ n o S FS pos fr junk X).
    all: first [ assumption
               | exact (PB.rng_bytes_RNG_W _)
               | exact (proj1 (HOK ltac:(assumption)))
               | (intros Hn50; exact (proj1 (VF2 Hn50)))
               | (intros Hn50; exact (proj1 (proj2 (VF2 Hn50))))
               | (intros Hn50; exact (proj2 (proj2 (VF2 Hn50))))
               | (intros Hne; exact (proj1 (VO2 Hne)))
               | (intros Hne; exact (proj1 (proj2 (VO2 Hne))))
               | (intros Hne; exact (proj2 (proj2 (VO2 Hne))))
               | (unfold SMC.ASAN_GT in *; lia) ]. }
  intros ms' md' Hrun (s0 & HQF & HREL & HROS) Hhid Hs.
  destruct HQF as (HQp & (ob & HOB & MUb) & HFL0).
  destruct HQp as (t0q & t1q & t2q & a1q & a2q & a3q & a4q & a5q & a6q & a7q & t3q & t4q & t5q & t6q & m0' &
                   E0 & MUq & WMq & MIq & STq & HRECq & ACq & SWq & AWq & FPq & XFq & FLKq & TLq).
  subst s0.
  destruct (MNT.ms_rel_MS ms' _ _ _ _ _ _ _ HREL) as (Ems' & REL').
  (* the real write set *)
  set (WR := RB.RBodyFOn.Wf2 S FS fra pos 1 ++ [(ob, ob + 36)]).
  assert (Rfl : 0 <= fl /\ fl + 1 <= 2 ^ 64) by (unfold IB.IMG_HI in FLimg; lia).
  assert (MUfl : LF.munch [(fl, fl + 1)]
                   (write_to_mem (MN.normalize rsegs mem2) (LM.wa fl) [Z_to_bv 8 0]) (MN.normalize rsegs mem2)).
  { intros x Hx. rewrite LM.write_to_mem_spec by (cbn [length Z.of_nat Pos.of_succ_nat]; lia).
    cbn [LF.outside length Z.of_nat Pos.of_succ_nat] in Hx |- *. destruct Hx as [Hx _].
    destruct (Z.leb_spec0 fl (bv_unsigned x)); cbn [andb]; [|reflexivity].
    destruct (Z.ltb_spec0 (bv_unsigned x) (fl + Z.of_nat 1)); [exfalso; lia | reflexivity]. }
  assert (MUr : LF.munch WR mem2 (ms_mem ms')).
  { apply (rcpP_munch_base WR mem2 _ m0' (ms_mem ms') fl MUfl);
      [| unfold WR; rewrite Efra, <- Efl; exact MUb | exact REL' | exact HROS].
    intros x Hx. unfold WR, RB.RBodyFOn.Wf2 in Hx. cbn [app LF.outside] in Hx |- *.
    destruct Hx as (_ & _ & H3 & _). rewrite Efl in H3. split; [exact H3 | exact I]. }
  assert (HFL' : LM.bytes_at rsegs (ms_mem ms') fl [Z_to_bv 8 0]).
  { rewrite <- Efl. exact (proj2 (MN.bytes_at_rel rsegs (ms_mem ms') m0' _ _ REL') HFL0). }
  assert (HOB' : (o = 0 /\ ob = fra + 32) \/ (o <> 0 /\ ob = o)).
  { rewrite Efra. exact HOB. }
  (* ================= (d) the release: the journal at ms' with own and stack_free_state 1 pos S2 ================= *)
  assert (J3 : RCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc
                 (RG01.stack_free_state 1 pos S2) W (ms_mem ms') md' k).
  { lazymatch type of Hrun with
    | RK04R.fsteps _ _ ?ms0 ?ms1 =>
        apply (PR.rcpPR_release B STK sp0 FP ly S0 W0 mem0 md0 own lyc S2 W ms0 ms1 md2 md' k pos pos fra ob o S
                 (PB.RNG_W (RA0n.w_H W)) HJ2 Hrun (PB.fp_avoids_RNG_W _))
    end.
    - exact MUr.
    - exact Hs.
    - exact HFL'.
    - lia.
    - lia.
    - reflexivity.
    - exact Efra.
    - exact Efl.
    - exact HOB'.
    - intros Hne a Ha. rewrite HAB. exact (Hawr Hne a Ha). }
  (* ================= (e) the post ================= *)
  apply RA0n.SRr_ret. unfold SP.treac_ctrl_parse_post. cbv beta.
  exists lyc, (RG01.stack_free_state 1 pos S2).
  eexists _, (ms_mem ms'), md'.
  split.
  { rewrite Ems'. rewrite (rcpP_ret_pc_ok (reg_get regs 1) HRA). reflexivity. }
  split; [exact J3|].
  split.
  { intros r Hr. unfold RG0d.acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]; try reflexivity.
    change (RK11.getr regs (Z_to_bv 5 2)) with (reg_get regs 2).
    change (RK11.getr _ (Z_to_bv 5 2)) with (Z_to_bv 64 S).
    unfold S, RG0d.spZ. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned. reflexivity. }
  split.
  { change (RG01.frames (RG01.stack_free_state 1 pos S2)) with (RG00.del_pos (RG01.frames S2) 1 pos).
    rewrite HFR. cbn [RG00.del_pos]. rewrite !Z.eqb_refl. reflexivity. }
  split.
  { change (RG0d.ablocks B lyc (RG01.stack_free_state 1 pos S2)) with (RG0d.ablocks B lyc S2). exact HAB. }
  split.
  { exists (RG00.mkFS (RG00.fs_hint (RG00.st_fs S2)) (RG00.del_pos (RG00.fs_live (RG00.st_fs S2)) 1 pos)).
    rewrite ES2. reflexivity. }
  split; [reflexivity|].
  split.
  { intros Hne i Hi.
    destruct (HoF Hne) as (co & po & Ino & Hf1 & Hf2).
    apply (PA.rcpPA_rec B lyc Sc W memc mdc (ms_mem ms') co po o _ RcP.cp_z HAR Ino Hf1 Hf2
             (MNT.rw_cells_of_rel _ _ _ _ REL' (HRECq Hne)) (RcP.ctrlparse_length n fr) i Hi). }
  (* acall_kept from memc to ms' over [S - 8800, S), E = the record *)
  unfold SP.REAC_CTRL_PARSE_STK. fold S.
  apply (K.rcpK_compose B lyc Sc W memc m1 mem2 (ms_mem ms') S A o WR
           B1 ltac:(unfold RG0d.ESTACK; lia) ltac:(lia) ltac:(lia) RA1 HKEPT MUr).
  - intros b m i Hb Hi.
    destruct (RG0d.al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & Hb4 & Hbc & _). lia.
  - intros cid pos' a Hin Hr.
    destruct (RCbq.frames_bounds rsegs B LAWS lyc Sc W memc mdc cid pos' HAR Hin) as (F1 & F2 & _).
    pose proof (RCbq.fs_frame_bytes_nonneg cid).
    unfold RG0n.in_zr, RCbq.frame_rng in Hr. cbn [fst snd] in Hr.
    unfold RG0f.shadow_addr, RG0f.SHADOW_OFF in Hr.
    Z.div_mod_to_equations. lia.
  - intros a Hi. pose proof (V.rcpV_img_lt a Hi). pose proof (rcpP_img_nonneg a Hi). unfold IB.IMG_HI in *. lia.
  - exact (PA.rcpPA_kept_wr B lyc S2 W mem2 md2 Sc pos pos fra ob o S HAR2 HFR HNI HAB eq_refl Efra Efl HOB'
             HoF B1).
  - apply (rcpP_pres_of_stk _ (ms_mem ms') (S - 8800) S); [unfold IB.IMG_HI; lia | |].
    + exact (MNT.stk_of_rel _ _ _ _ REL' STq).
    + intros a Ha. exact (proj1 (Hpres2 a ltac:(lia))).
Qed.

End P.
