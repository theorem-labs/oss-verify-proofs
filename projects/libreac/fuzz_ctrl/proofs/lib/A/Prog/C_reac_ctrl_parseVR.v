(* lib/A/Prog/C_reac_ctrl_parseVR.v -- fuzz_ctrl image A (asan, libreac v1.9.0): three visibility facts for the
   cgif-form glue pb_reac_ctrl_parse (lib/A/Prog/C_reac_ctrl_parseP.v), at a state the core's AR describes, in the
   footprint RNG := PB.RNG_W (w_H W):
     rcpVR_rtls  every cell of RcAsanFP.fp_tls (the cells asan_tls_cells names) is a footprint range;
     rcpVR_fw1   every range of RcAsanFP.fp_w [1] ly_F (class 1's hint word, flag bytes, frames and their shadow);
     rcpVR_fss   the side stack's header [ly_F, fs_frame ly_F 0 0).
   rule 24: no function proved.  These are bridge lemmas over the core's world (AR / aview / cell_holds).
   Route (C): only AR's own fields (ARm, ALedger) and the lemmas cited below; no universal shadow or runtime lemma
   of the retired route, and no visibility or read-only premise.
   rcpVR_rtls: (1) the values DT = TP+32, TS = ly_tsd, k = 0, C = ly_C, T = ly_T, DB = ly_D, as lib/A/ProgWorldTlsApart.v
   step 1 (ProgWorldTlsApart.bytes_at_uniq / le8_inj against the const rows, ProgWorld_Fs.pw_row / pw_c8_bytes /
   pw_z4_bytes); (2) the image cells by ProgBridge.img_vis_W, the cells C+152 / T+48 (16 bytes) / DB+24 by the const
   rows c8 (AC 152) (AT 0), z8 (AT 48), z8 (AT 56), c8 (AD 24) (ATp 0) (AF0m.Tfib_const_sym): a byte the view reads is
   visible (ProgWorldVisFrame.vis_of_aview).  rcpVR_fw1 / rcpVR_fss: C_reac_ctrl_parseW.pz_side_vis for the side-stack
   ranges, C_reac_ctrl_parseW.pz_Fsh_present + pz_rv_of_present for the class-1 frames' shadow.
   Cited: ProgBridge.rng_of_visible / range_visible_sub / img_vis_W; ProgWorld_Fs.pw_row / pw_c8_bytes / pw_z4_bytes /
   pw_u64 / pw_ext_range / pw_F_in_owned; ProgWorldTlsApart.bytes_at_uniq / le8_inj; ProgWorldVisFrame.vis_of_aview;
   C_reac_ctrl_parseW.pz_side_vis / pz_rv_of_present / pz_Fsh_present; AF0m.ts_tp / ts_tsd; YG0n.am_layout / am_tsd.
   Twin rule: every project module is Required without Import and named through a full-path Module alias. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Img0 AsanRT ProgBridge AF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorld_Fs ProgWorldVisFrame ProgWorldTlsApart.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ImgBounds asan_stack_malloc_c RcAsanFP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require C_reac_ctrl_parseW.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YA0n YG0f YG0n YConstIn.
Import ListNotations.
Local Open Scope Z_scope.

Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LX := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module AI0 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module PB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AF0m.
Module PWF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorld_Fs.
Module PWVF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldVisFrame.
Module PWTA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldTlsApart.
Module IB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c.
Module FP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.RcAsanFP.
Module PZ := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_parseW.
Module RK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module RM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module RA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module RG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Module RG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Local Notation rsegs := AI0.rsegs (only parsing).

(* membership of a row in image A's const table (one closed vm_compute, YConstIn.in_const_tbl) *)
Local Ltac vr_in := unfold AF.Tfib_const; OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YConstIn.in_const_tbl.

(* numeric side goals over the image constants (the goal only) *)
Local Ltac vr_num :=
  cbn [RG0f.aeval];
  cbv beta delta [ART.RT_TP AF.TFIB_TP AF.TFIB_TSD IB.IMG_LO IB.IMG_HI
                  SMC.TLS_INDEX SMC.REAL_TLS_GET_ADDR SMC.TSD_KEY_INITED SMC.TSD_KEY SMC.GOT_CF SMC.CF
                  SMC.GOT_VERBOSITY SMC.VERBOSITY SMC.DTLS_TPOFF];
  try change (2 ^ 64) with 18446744073709551616;
  try change (2 ^ 32) with 4294967296;
  lia.

Section VR.
Context {fx : RK11.FPState} {rc : RM05.RunCeil}.
Variable B : RG0f.asyms.
Hypothesis TS : AF.CtrlTSyms B.

(* ---------------------------------------------------------------------------------------------------------
   1. Byte-wise footprint ranges. *)

(* A range all of whose bytes are visible is a footprint range of RNG_W. *)
Lemma vr_rng : forall (H : word -> bool) lo hi, 0 <= lo -> lo <= hi -> hi <= 2 ^ 64 ->
  (forall x, lo <= x < hi -> H (Z_to_bv 64 x) = false) -> LX.rng (PB.RNG_W H) lo (hi - lo).
Proof.
  intros H lo hi H0 H1 H2 HV. apply PB.rng_of_visible.
  split; [exact H0|]. split; [lia|]. intros x Hx. apply HV. lia.
Qed.

(* An image range [lo, hi) inside [IMG_LO, IMG_HI) is a footprint range (every world shows the whole image). *)
Lemma vr_img_rng : forall (W : RA0n.world rsegs) lo hi, IB.IMG_LO <= lo -> lo <= hi -> hi <= IB.IMG_HI ->
  LX.rng (PB.RNG_W (RA0n.w_H W)) lo (hi - lo).
Proof.
  intros W lo hi H0 H1 H2. apply PB.rng_of_visible.
  apply (PB.range_visible_sub _ _ _ _ _ (PB.img_vis_W W)); lia.
Qed.

(* Each byte of an 8-byte cell row the view reads is visible. *)
Lemma vr_c8_vis : forall ly (W : RA0n.world rsegs) m ea ev x,
  RG0f.cell_holds B ly (RG0n.aview rsegs (RA0n.w_H W) m) (RG0f.c8 ea ev) ->
  RG0f.aeval B ly ea <= x < RG0f.aeval B ly ea + 8 -> RA0n.w_H W (Z_to_bv 64 x) = false.
Proof.
  intros ly W m ea ev x Hc Hx. unfold RG0f.cell_holds in Hc.
  cbn [RG0f.c_at RG0f.c_val RG0f.c_w RG0f.c8] in Hc.
  apply (PWVF.vis_of_aview rsegs W m x).
  specialize (Hc (Z.to_nat (x - RG0f.aeval B ly ea)) ltac:(lia)).
  rewrite Z2Nat.id in Hc by lia.
  replace (RG0f.aeval B ly ea + (x - RG0f.aeval B ly ea)) with x in Hc by ring.
  rewrite Hc. discriminate.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   2. The three facts. *)

Lemma rcpVR_rtls : forall ly S (W : RA0n.world rsegs) m md,
  RG0n.AR rsegs B ly S W m md ->
  forall DT TS' C T DB k, SMC.asan_tls_cells m ART.RT_TP DT TS' C T DB k ->
  Forall (fun iv => LX.rng (PB.RNG_W (RA0n.w_H W)) (fst iv) (snd iv - fst iv)) (FP.fp_tls ART.RT_TP DT TS' C T DB k).
Proof.
  intros ly S W m md HAR DT TS' C T DB k Hcells.
  pose proof HAR as (HM & _).
  pose proof (RG0n.am_layout _ _ _ _ HM) as LO.
  (* the rows of image A's const table *)
  assert (Hrow : forall c, In c (AF.Tfib_const ly) ->
            RG0f.cell_holds B ly (RG0n.aview rsegs (RA0n.w_H W) m) c)
    by (intros c Hc; exact (PWF.pw_row B TS ly S W m md c HAR Hc)).
  pose proof (AF.ts_tp B TS) as Htp.
  assert (Htsd : RG0f.ly_tsd ly = 0x5fcbb8)
    by (rewrite (RG0n.am_tsd _ _ _ _ HM), (AF.ts_tsd B TS); reflexivity).
  (* the owned extents of the thread cells *)
  pose proof (proj1 (Forall_forall _ _) (RG0f.lo_app ly LO)) as Happ.
  assert (AT : RG0f.in_app (RG0f.ly_T ly) RG0f.kThreadObjSize)
    by exact (Happ (RG0f.ly_T ly, RG0f.kThreadObjSize)
                ltac:(unfold RG0f.owned_extents; cbn [In]; tauto)).
  assert (AC : RG0f.in_app (RG0f.ly_C ly) 256)
    by exact (Happ (RG0f.ly_C ly, 256) ltac:(unfold RG0f.owned_extents; cbn [In]; tauto)).
  assert (AD : RG0f.in_app (RG0f.ly_D ly) 4096)
    by exact (Happ (RG0f.ly_D ly, 4096) ltac:(unfold RG0f.owned_extents; cbn [In]; tauto)).
  destruct (PWF.pw_ext_range _ _ AT) as [LT0 LT1].
  destruct (PWF.pw_ext_range _ _ AC) as [LC0 LC1].
  destruct (PWF.pw_ext_range _ _ AD) as [LD0 LD1].
  unfold RG0f.kThreadObjSize in LT1.
  (* 1. the values (ProgWorldTlsApart.v step 1): each word asan_tls_cells reads is the AR row at its address *)
  destruct Hcells as (_ & _ & HDT & _ & _ & Hk & HK & HTS0 & HC0 & HT0 & _ & _ & _ & _ & _ & _ & HDB0 & _ & _).
  change (2 ^ 32) with 4294967296 in Hk.
  (* TP - 8 holds DT = TP + 32 *)
  assert (RDT : LM.bytes_at rsegs m (ART.RT_TP - 8) (LM.le8 (Z_to_bv 64 0x5db830))).
  { apply (PWF.pw_c8_bytes B ly W m (RG0f.ATp (-8)) (RG0f.ANum 0x5db830));
      [apply Hrow; vr_in | cbn [RG0f.aeval]; rewrite Htp; reflexivity | reflexivity | vr_num | vr_num]. }
  pose proof (PWTA.le8_inj _ _ (PWTA.bytes_at_uniq _ _ _ _ HDT RDT ltac:(rewrite !LM.length_le8; reflexivity)))
    as EDT.
  subst DT.
  (* TP - 88 holds TS = ly_tsd *)
  assert (RTS : LM.bytes_at rsegs m (ART.RT_TP - 88) (LM.le8 (Z_to_bv 64 0x5fcbb8))).
  { apply (PWF.pw_c8_bytes B ly W m (RG0f.ATp (-88)) (RG0f.ATsd 0));
      [apply Hrow; vr_in | cbn [RG0f.aeval]; rewrite Htp; reflexivity
       | cbn [RG0f.aeval]; rewrite Htsd; reflexivity | vr_num | vr_num]. }
  pose proof (PWTA.le8_inj _ _ (PWTA.bytes_at_uniq _ _ _ _ HTS0 RTS ltac:(rewrite !LM.length_le8; reflexivity)))
    as ETS.
  subst TS'.
  (* TSD_KEY holds k = 0 *)
  assert (RK : LM.bytes_at rsegs m SMC.TSD_KEY (LM.le4 (Z_to_bv 64 0))).
  { apply (PWF.pw_z4_bytes B ly W m (RG0f.ANum 0xa80e4));
      [apply Hrow; vr_in | reflexivity | vr_num | vr_num | vr_num]. }
  pose proof (PWTA.bytes_at_uniq _ _ _ _ HK RK ltac:(rewrite !LM.length_le4; reflexivity)) as EK.
  unfold LM.le4 in EK.
  rewrite (PWF.pw_u64 k), (PWF.pw_u64 0) in EK by vr_num.
  pose proof (LM.bytes_le_to_Z_to_le_bytes 4 k ltac:(lia)) as EK2.
  rewrite EK, (LM.bytes_le_to_Z_to_le_bytes 4 0) in EK2 by lia.
  change (8 * Z.of_nat 4) with 32 in EK2.
  rewrite (Z.mod_small k (2 ^ 32) Hk) in EK2. change (0 mod 2 ^ 32) with 0 in EK2.
  subst k.
  (* TS + 8 * k holds C = ly_C *)
  rewrite (PWF.pw_u64 0x5fcbb8) in HC0 by vr_num.
  assert (RC : LM.bytes_at rsegs m (0x5fcbb8 + 8 * 0) (LM.le8 (Z_to_bv 64 (RG0f.ly_C ly)))).
  { apply (PWF.pw_c8_bytes B ly W m (RG0f.ATsd 0) (RG0f.AC 0));
      [apply Hrow; vr_in | cbn [RG0f.aeval]; rewrite Htsd; reflexivity
       | cbn [RG0f.aeval]; lia | vr_num | vr_num]. }
  pose proof (PWTA.le8_inj _ _ (PWTA.bytes_at_uniq _ _ _ _ HC0 RC ltac:(rewrite !LM.length_le8; reflexivity)))
    as EC.
  subst C.
  (* C + 152 holds T = ly_T *)
  rewrite (PWF.pw_u64 (RG0f.ly_C ly)) in HT0 by vr_num.
  assert (RT : LM.bytes_at rsegs m (RG0f.ly_C ly + 152) (LM.le8 (Z_to_bv 64 (RG0f.ly_T ly)))).
  { apply (PWF.pw_c8_bytes B ly W m (RG0f.AC 152) (RG0f.AT 0));
      [apply Hrow; vr_in | reflexivity | cbn [RG0f.aeval]; lia | vr_num | vr_num]. }
  pose proof (PWTA.le8_inj _ _ (PWTA.bytes_at_uniq _ _ _ _ HT0 RT ltac:(rewrite !LM.length_le8; reflexivity)))
    as ET.
  subst T.
  (* TP + 8 holds DB = ly_D *)
  assert (RDB : LM.bytes_at rsegs m (ART.RT_TP + 8) (LM.le8 (Z_to_bv 64 (RG0f.ly_D ly)))).
  { apply (PWF.pw_c8_bytes B ly W m (RG0f.ATp 8) (RG0f.AD 0));
      [apply Hrow; vr_in | cbn [RG0f.aeval]; rewrite Htp; reflexivity
       | cbn [RG0f.aeval]; lia | vr_num | vr_num]. }
  pose proof (PWTA.le8_inj _ _ (PWTA.bytes_at_uniq _ _ _ _ HDB0 RDB ltac:(rewrite !LM.length_le8; reflexivity)))
    as EDB.
  subst DB.
  (* 2. each cell is visible: the image cells (below IMG_HI), and the const rows at C+152, T+48, T+56, DB+24 *)
  unfold FP.fp_tls.
  rewrite (PWF.pw_u64 0x5db830), (PWF.pw_u64 0x5fcbb8), (PWF.pw_u64 (RG0f.ly_C ly)),
          (PWF.pw_u64 (RG0f.ly_T ly)), (PWF.pw_u64 (RG0f.ly_D ly)) by vr_num.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  all: try (apply vr_img_rng; vr_num).
  - (* C + 152 *)
    apply vr_rng; [lia | lia | vr_num |]. intros x Hx.
    apply (vr_c8_vis ly W m (RG0f.AC 152) (RG0f.AT 0) x); [apply Hrow; vr_in | cbn [RG0f.aeval]; lia].
  - (* T + 48, 16 bytes: the rows at T + 48 and T + 56 *)
    apply vr_rng; [lia | lia | vr_num |]. intros x Hx.
    destruct (Z_lt_le_dec x (RG0f.ly_T ly + 56)) as [Hlt|Hge].
    + apply (vr_c8_vis ly W m (RG0f.AT 48) (RG0f.ANum 0x5dbf48) x); [apply Hrow; vr_in | cbn [RG0f.aeval]; lia].
    + apply (vr_c8_vis ly W m (RG0f.AT 56) (RG0f.ANum 0x5dc024) x); [apply Hrow; vr_in | cbn [RG0f.aeval]; lia].
  - (* DB + 24 *)
    apply vr_rng; [lia | lia | vr_num |]. intros x Hx.
    apply (vr_c8_vis ly W m (RG0f.AD 24) (RG0f.ATp 0) x); [apply Hrow; vr_in | cbn [RG0f.aeval]; lia].
Qed.

Lemma rcpVR_fw1 : forall ly S (W : RA0n.world rsegs) m md,
  RG0n.AR rsegs B ly S W m md ->
  Forall (fun iv => LX.rng (PB.RNG_W (RA0n.w_H W)) (fst iv) (snd iv - fst iv)) (FP.fp_w [1%nat] (RG0f.ly_F ly)).
Proof.
  intros ly S W m md HAR.
  pose proof HAR as (M & _).
  pose proof (RG0n.am_layout _ _ _ _ M) as LO.
  pose proof (proj1 (Forall_forall _ _) (RG0f.lo_app _ LO) _ (PWF.pw_F_in_owned ly)) as F1.
  cbn [fst snd] in F1. destruct (PWF.pw_ext_range _ _ F1) as [F0 F2].
  unfold RG0f.kFakeStackSize in F2.
  (* class 1's offsets in the side stack *)
  assert (EH : SMC.fs_hint (RG0f.ly_F ly) 1 = RG0f.ly_F ly + 8)
    by (transitivity (RG0f.ly_F ly + SMC.fs_hint 0 1); [unfold SMC.fs_hint; ring | reflexivity]).
  assert (EL : SMC.fs_flag (RG0f.ly_F ly) 1 0 = RG0f.ly_F ly + 20480)
    by (transitivity (RG0f.ly_F ly + SMC.fs_flag 0 1 0); [unfold SMC.fs_flag; ring | reflexivity]).
  assert (EF0 : SMC.fs_frame (RG0f.ly_F ly) 1 0 = RG0f.ly_F ly + 1085440)
    by (transitivity (RG0f.ly_F ly + SMC.fs_frame 0 1 0); [unfold SMC.fs_frame; ring | reflexivity]).
  assert (EF1 : SMC.fs_frame (RG0f.ly_F ly) 1 (SMC.fs_M 1) = RG0f.ly_F ly + 2134016)
    by (transitivity (RG0f.ly_F ly + SMC.fs_frame 0 1 (SMC.fs_M 1)); [unfold SMC.fs_frame; ring | reflexivity]).
  assert (EM : SMC.fs_M 1 = 8192) by reflexivity.
  unfold FP.fp_w. cbn [flat_map app FP.fp_w1].
  rewrite EF1, EH, EL, EF0, EM.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  1-3: apply PB.rng_of_visible; apply (PZ.pz_side_vis B ly S W m md); [exact HAR | lia | lia | unfold SMC.FS_SIZE; lia].
  (* the class-1 frames' shadow: inside the shadow of the frame area, present (pz_Fsh_present) *)
  apply PB.rng_of_visible.
  assert (Q0 : 0 <= RG0f.ly_F ly / 8) by (apply Z.div_pos; lia).
  assert (Q1 : RG0f.ly_F ly / 8 <= RG0f.ly_F ly) by (apply Z.div_le_upper_bound; lia).
  assert (D1 : ART.shadow_addr (RG0f.ly_F ly + 1085440) = RG0f.ly_F ly / 8 + 135680 + ART.ASAN_K)
    by (unfold ART.shadow_addr; Z.div_mod_to_equations; lia).
  assert (D2 : ART.shadow_addr (RG0f.ly_F ly + 2134016) = RG0f.ly_F ly / 8 + 266752 + ART.ASAN_K)
    by (unfold ART.shadow_addr; Z.div_mod_to_equations; lia).
  assert (D0 : RG0f.shadow_addr (RG0f.ly_F ly + RG0f.kFakeFramesOff) = RG0f.SHADOW_OFF + (RG0f.ly_F ly / 8 + 4608))
    by (unfold RG0f.shadow_addr, RG0f.kFakeFramesOff; Z.div_mod_to_equations; lia).
  rewrite D1, D2.
  apply (PZ.pz_rv_of_present _ m).
  - unfold ART.ASAN_K. lia.
  - unfold ART.ASAN_K. change (2 ^ 64) with 18446744073709551616. lia.
  - intros a Ha. apply (PZ.pz_Fsh_present B ly S W m md a HAR).
    rewrite D0. change ((RG0f.kFakeStackSize - RG0f.kFakeFramesOff) / 8) with 1441792.
    unfold RG0f.SHADOW_OFF. unfold ART.ASAN_K in Ha. lia.
Qed.

Lemma rcpVR_fss : forall ly S (W : RA0n.world rsegs) m md,
  RG0n.AR rsegs B ly S W m md ->
  LX.rng (PB.RNG_W (RA0n.w_H W)) (RG0f.ly_F ly) (SMC.fs_frame (RG0f.ly_F ly) 0 0 - RG0f.ly_F ly).
Proof.
  intros ly S W m md HAR.
  assert (E : SMC.fs_frame (RG0f.ly_F ly) 0 0 = RG0f.ly_F ly + 36864)
    by (transitivity (RG0f.ly_F ly + SMC.fs_frame 0 0 0); [unfold SMC.fs_frame; ring | reflexivity]).
  rewrite E. apply PB.rng_of_visible.
  apply (PZ.pz_side_vis B ly S W m md); [exact HAR | lia | lia | unfold SMC.FS_SIZE; lia].
Qed.
End VR.
