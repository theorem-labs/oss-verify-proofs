(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/ProgWorldCtlRt.v (a working branch 26edf006f53, blob 8412b144221; re-synced to a working branch a48c4068c6e (an earlier version, blob a3a164a580b, not in this delivery), the same blob on a working branch 1d23ced37fd: A's core Requires now name lib.Reusable, and nth_Z_to_le_bytes rewrites the instantiated Z.pow_add_r 2 8 (8 * Z.of_nat i); B takes both; then to a working branch fec8db0a380: inconst decides const-table membership by lib/Reusable/YConstIn.v's in_const_tbl (Required as A does; B's earlier index lookup in_nth / inconst_from is gone), and Z_to_bv_bv_unsigned (3 uses) / length_Z_to_le_bytes (1) are written stdpp.bitvector.definitions.Z_to_bv_bv_unsigned / LinuxProcessSemantics.LinuxProcessSem.BvBase.length_Z_to_le_bytes, the constants `About` names at each use in this file (Locate / About probe, a Theorem Labs lane); B takes both): the same helpers, the same two lemmas (ctl_tls_of_AR, ctlrt_of_AR) and the same proofs over image B (asan-ubsan).  Differences from A: module paths (A.Prog.X -> B.Prog.X; A.ACtlK / ACtlCut / ProgBridge / ProgWorld / AsanRT / Img0 -> B.*; A.AB1v / AE2k / ACfn / AF0m -> lib.Reusable.YB1v / YE2k / YCfn / YF0m); every core module Required as A writes it (`From ...fuzz_ctrl.lib.Reusable Require X`, the core copy; porter 04:33Z); Lib.Mem / Lib.Frame, which also exist as lib/B/Bz/Lib/X, Required as `From ...fuzz_ctrl.lib.Lib Require Mem Frame` and named lib.Lib.X (fix_require6.py, as lib/B/ProgWorld.v on the base; A: `Require Lib.Mem Lib.Frame`, Lib.X); every image-A address and value replaced by image B's, each checked by the proof against the B module constant named in the comment beside it (B.AsanRT, B.Prog.asan_stack_malloc_c, lib.Reusable.YF0m rows) or, where no B module names it, by the asan-ubsan symtab symbol + offset in the comment; the image hull end 0x5fe000 is written by name (B.Prog.ImgBounds.IMG_HI, one extra Require); ro_not_errno is stated with lib.Reusable.YF0m.TFIB_ERRNO by name (A: the literal); the TS witness and the TSD fact are stated with B.AsanRT.RT_TSDMAIN by name and the DT witness as B.AsanRT.RT_TP + 32 (A: literals).  Then to a working branch 713d4f2d52f (lib/A/ProgWorldCtlRt.v 241ab4d6fa1 (the blob this tree had at release c5e779efe8c), the same at da635d1b018): the asan_cells and ro_agree conjuncts are factored out of ctlrt_of_AR into asan_cells_of_AR / ro_agree_of_AR (route (C), for B.ProgWorldCtlRtC.ctl_rt_C_of_AR); B moves its own proof text into the two lemmas the same way, and ctlrt_of_AR's statement is unchanged. *)
(* lib/B/ProgWorldCtlRt.v -- proofs of lib/B/ProgWorld.v's ctl_tls_of_AR_stmt and ctlrt_of_AR_stmt (image B,
   fuzz_ctrl.asan-ubsan).  Nothing here edits ProgWorld.v.  rule 24: no function of the image is proved here. *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YK04 YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0i YA0n YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YE01 YP09 YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.asan_stack_malloc_c B.Prog.RcAsanFP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v Reusable.YE2k Reusable.YCfn Reusable.YF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ACtlK B.ACtlCut B.ProgBridge B.ProgWorld.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.asan_memcpy_cF B.Prog.CtrlBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.AsanRT B.Img0 B.Prog.ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YConstIn.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Existing Instance lib.Reusable.YE2k.tfib_sink_head.

Notation segs := lib.Reusable.YB1v.tfibsegs (only parsing).

(* ---------------------------------------------------------------------------------------------------------
   0. The byte bridge: a const row of the core's world (cell_holds over aview) is a ctrl `bytes_at` over mrd.
   Image-independent: the same statements and proofs as image A's. *)

Lemma pow2_nz : forall k : Z, 0 <= k -> 2 ^ k <> 0.
Proof. intros k Hk. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk). lia. Qed.

Lemma nth_Z_to_le_bytes : forall (n : nat) (z : Z) (i : nat), (i < n)%nat ->
  nth_error (Z_to_le_bytes n z) i = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat i))).
Proof.
  induction n as [|n IH]; intros z i Hi; [lia|].
  destruct i as [|i]; cbn [Z_to_le_bytes nth_error].
  - rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
  - rewrite (IH (Z.shiftr z 8) i ltac:(lia)). f_equal. f_equal.
    replace (8 * Z.of_nat (S i)) with (8 + 8 * Z.of_nat i) by lia.
    rewrite !Z.shiftr_div_pow2 by lia.
    rewrite (Z.pow_add_r 2 8 (8 * Z.of_nat i)) by lia.
    rewrite Z.div_div by (first [apply pow2_nz | apply Z.pow_pos_nonneg]; lia).
    reflexivity.
Qed.

Lemma le_byte_shiftr : forall (z : Z) (w k : nat), (k < w)%nat ->
  Z_to_bv 8 (lib.Reusable.YG0f.le_byte z w k) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
  intros z w k Hk. apply lib.Lib.Mem.Z_to_bv8_mod.
  unfold lib.Reusable.YG0f.le_byte.
  change (2 ^ 8) with 256. rewrite Z.mod_mod by lia.
  change 256 with (2 ^ 8). apply lib.Lib.Mem.shiftr_mod_mod8; lia.
Qed.

(* A word cell is compared mod 2^64 (a Theorem Labs lane 04:13Z): a cell stated as `le8 (Z_to_bv 64 (-2048))` against the row
   value 0xfffffffffffff800 is equal as a word, not as Z. *)
Lemma le8_eq : forall v z, v mod 2 ^ 64 = z mod 2 ^ 64 -> lib.Lib.Mem.le8 (lib.Lib.Mem.wa v) = Z_to_le_bytes 8 z.
Proof.
  intros v z H. unfold lib.Lib.Mem.le8, word_to_le_bytes, lib.Lib.Mem.wa.
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 v) with (v mod 2 ^ 64).
  rewrite H. apply (lib.Lib.Mem.Z_to_le_bytes_mod 8 z 64). cbn [Z.of_nat]. lia.
Qed.

Lemma le4_eq : forall v z, v mod 2 ^ 32 = z mod 2 ^ 32 -> lib.Lib.Mem.le4 (lib.Lib.Mem.wa v) = Z_to_le_bytes 4 z.
Proof.
  intros v z H. unfold lib.Lib.Mem.le4, lib.Lib.Mem.wa.
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 v) with (v mod 2 ^ 64).
  rewrite (lib.Lib.Mem.Z_to_le_bytes_mod 4 v 64) by (cbn [Z.of_nat]; lia).
  rewrite <- (lib.Lib.Mem.Z_to_le_bytes_mod 4 v 32) by (cbn [Z.of_nat]; lia).
  rewrite <- (lib.Lib.Mem.Z_to_le_bytes_mod 4 z 32) by (cbn [Z.of_nat]; lia).
  rewrite H. reflexivity.
Qed.

Lemma le1_eq : forall v z, v mod 2 ^ 8 = z mod 2 ^ 8 -> [Z_to_bv 8 v] = Z_to_le_bytes 1 z.
Proof.
  intros v z H. cbn [Z_to_le_bytes].
  apply f_equal2; [apply lib.Lib.Mem.Z_to_bv8_mod; exact H | reflexivity].
Qed.

Section Bridge.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.

(* the core's view is None at a hidden byte, so a row's byte is visible *)
Lemma aview_some_vis : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) (a v : Z),
  lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m a = Some v ->
  lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W m a v Hv.
  destruct (lib.Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:E; [exfalso|reflexivity].
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict in Hv.
  rewrite E in Hv. unfold lib.Reusable.YK11.seg_rom in Hv.
  rewrite (lib.Reusable.YK04.memory_read1_hidden segs (lib.Reusable.YA0n.w_H W)
             (lib.Reusable.YA0n.w_Hoff W) (Z_to_bv 64 a) E) in Hv.
  cbn in Hv. discriminate Hv.
Qed.

Lemma mrd_of_aview : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) (a v : Z),
  lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m a = Some v ->
  lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa a) = Some (Z_to_bv 8 v).
Proof.
  intros W m a v Hv.
  pose proof (aview_some_vis W m a v Hv) as Hh.
  rewrite (B.ProgWorld.aview_vis_mrd W m a Hh) in Hv.
  unfold lib.Lib.Mem.wa.
  destruct (lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a)) as [b|] eqn:Em; cbn [option_map] in Hv;
    [|discriminate Hv].
  injection Hv as <-. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* A z1 / z4 / z8 / c8 row that holds over the view is a bytes_at over mrd. *)
Lemma cell_bytes_at : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte)
    (B : lib.Reusable.YG0f.asyms) (ly : lib.Reusable.YG0f.alayout)
    (ea ev : lib.Reusable.YG0f.aexp) (w : nat) (A : Z) (bs : list byte),
  lib.Reusable.YG0f.cell_holds B ly (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m)
    (lib.Reusable.YG0f.ACell ea w (lib.Reusable.YG0f.AV ev)) ->
  A = lib.Reusable.YG0f.aeval B ly ea -> 0 <= A -> A + Z.of_nat w <= 2 ^ 64 ->
  bs = Z_to_le_bytes w (lib.Reusable.YG0f.aeval B ly ev) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m A bs.
Proof.
  intros W m B ly ea ev w A bs Hc -> H0 H1 ->.
  unfold lib.Lib.Mem.bytes_at. rewrite LinuxProcessSemantics.LinuxProcessSem.BvBase.length_Z_to_le_bytes.
  split; [exact H0|]. split; [exact H1|].
  intros i Hi.
  unfold lib.Reusable.YG0f.cell_holds in Hc.
  cbn [lib.Reusable.YG0f.c_val lib.Reusable.YG0f.c_at lib.Reusable.YG0f.c_w] in Hc.
  specialize (Hc i Hi).
  rewrite (nth_Z_to_le_bytes w (lib.Reusable.YG0f.aeval B ly ev) i Hi).
  rewrite (mrd_of_aview W m _ _ Hc).
  apply (f_equal (@Some byte)). apply le_byte_shiftr. exact Hi.
Qed.

(* image-independent: the core's application window (YG0f.kLowShadowBeg / kHighMemBeg) *)
Lemma in_app_bounds : forall (lo len : Z),
  lib.Reusable.YG0f.in_app lo len -> 4096 <= lo /\ lo + len <= 0x7fffff800000.
Proof.
  intros lo len [H0 [H|[H1 H2]]];
    pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [CR _];
    unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in *; lia.
Qed.

End Bridge.

(* Membership of a const row in image B's const table.  Was a lookup by index (in_nth: nth_error (Tfib_const ly) k =
   Some c by reflexivity for k = 0, 1, ...), itself replacing A's in_eq / in_cons walk, which is quadratic in the
   table's length: on a Theorem Labs lane's RECORD table (Tfib_const_abs alone has 2135 rows) that walk took 1606 s / 13 GB
   for this file (cb build-20261029T044841Z.log, a Theorem Labs lane).  Now lib/Reusable/YConstIn.v's in_const_tbl,
   as A: ONE vm_compute of `existsb (row_eqb row) tbl` on a closed goal (YConstIn.v:8-11). *)
Ltac inconst :=
  unfold lib.Reusable.YF0m.Tfib_const;
  lib.Reusable.YConstIn.in_const_tbl.

(* numeric side goals: unfold the image constants (never the comparisons, which lia must still see) *)
Ltac bnd :=
  cbn [lib.Reusable.YG0f.aeval];
  cbv beta delta [B.AsanRT.RT_TP B.AsanRT.RT_TSDMAIN lib.Reusable.YF0m.TFIB_TP lib.Reusable.YF0m.TFIB_TSD
                  B.AsanRT.CELL_K B.AsanRT.GOT_CELL_K B.AsanRT.INITED B.AsanRT.REPLACE
                  B.AsanRT.GOT_REPLACE B.AsanRT.UAR B.AsanRT.GOT_UAR B.AsanRT.CANPOISON
                  B.AsanRT.HIEND B.AsanRT.GOT_HIEND B.AsanRT.MIDBEG B.AsanRT.GOT_MIDBEG
                  B.AsanRT.MIDEND B.AsanRT.GOT_MIDEND B.AsanRT.REAL_MEMCPY B.AsanRT.REAL_MEMSET
                  B.AsanRT.GOT_REAL_MEMSET B.AsanRT.ASAN_K B.AsanRT.MUSL_MEMCPY B.AsanRT.MUSL_MEMSET
                  B.Prog.asan_stack_malloc_c.TLS_INDEX B.Prog.asan_stack_malloc_c.REAL_TLS_GET_ADDR
                  B.Prog.asan_stack_malloc_c.MUSL_TLS_GET_ADDR B.Prog.asan_stack_malloc_c.TSD_KEY_INITED
                  B.Prog.asan_stack_malloc_c.TSD_KEY B.Prog.asan_stack_malloc_c.GOT_CF
                  B.Prog.asan_stack_malloc_c.CF B.Prog.asan_stack_malloc_c.GOT_VERBOSITY
                  B.Prog.asan_stack_malloc_c.VERBOSITY B.Prog.asan_stack_malloc_c.DTLS_TPOFF];
  try change (2 ^ 64) with 18446744073709551616;
  try change (2 ^ 32) with 4294967296;
  lia.

(* ---------------------------------------------------------------------------------------------------------
   1. ctl_tls_of_AR: the thread cells of the fake-stack stretches, from AR's const rows.  Image B's rows are
   lib/Reusable/YF0m.v's (a Theorem Labs lane's start-up files of record); each address / value below is checked by the proof against
   the B constant named beside it.  TP = B.AsanRT.RT_TP = YF0m.TFIB_TP = 0x5dc650 (builtin_tls+200). *)
Section TlsOfAR.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {LS : lib.Reusable.YO09.lib_shape}.
Variable B : lib.Reusable.YG0f.asyms.

Lemma ctl_tls_of_AR : B.ProgWorld.ctl_tls_of_AR_stmt B.
Proof.
  unfold B.ProgWorld.ctl_tls_of_AR_stmt.
  intros HTS HL ly S W m md HAR.
  destruct HAR as (HM & _ & _ & _ & _).
  destruct HM as [Hwf Huniv Hsyms Hlay Hplaced Hconst Hconstown Hcells Hfa Hflags Hdepot Hshadow
                  Hzshadow Hjunk Hareas Hclient Hzero Hlytsd Hstatimg].
  (* the rows of image B's const table *)
  assert (Hrow : forall c, In c (lib.Reusable.YF0m.Tfib_const ly) ->
            lib.Reusable.YG0f.cell_holds B ly (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m) c).
  { intros c Hc. apply (proj1 (Forall_forall _ _) Hconst).
    rewrite (lib.Reusable.YF0m.ts_const B HTS ly). exact Hc. }
  (* the image's symbol values *)
  pose proof (lib.Reusable.YF0m.ts_tp B HTS) as Htp.
  pose proof (lib.Reusable.YF0m.ts_tsd B HTS) as Htsd.
  (* TS: YF0m.TFIB_TSD = B.AsanRT.RT_TSDMAIN = 0x5fd9f8 (__pthread_tsd_main+0) *)
  assert (Htsdly : lib.Reusable.YG0f.ly_tsd ly = B.AsanRT.RT_TSDMAIN) by (rewrite Hlytsd, Htsd; reflexivity).
  (* the layout bounds of the owned areas the thread cells live in *)
  pose proof (proj1 (Forall_forall _ _) (lib.Reusable.YG0f.lo_app ly Hlay)) as Happ.
  assert (HT : 4096 <= lib.Reusable.YG0f.ly_T ly /\ lib.Reusable.YG0f.ly_T ly + 4096 <= 0x7fffff800000).
  { apply in_app_bounds.
    exact (Happ (lib.Reusable.YG0f.ly_T ly, lib.Reusable.YG0f.kThreadObjSize)
             ltac:(unfold lib.Reusable.YG0f.owned_extents; cbn [In]; tauto)). }
  assert (HC : 4096 <= lib.Reusable.YG0f.ly_C ly /\ lib.Reusable.YG0f.ly_C ly + 256 <= 0x7fffff800000).
  { apply in_app_bounds.
    exact (Happ (lib.Reusable.YG0f.ly_C ly, 256)
             ltac:(unfold lib.Reusable.YG0f.owned_extents; cbn [In]; tauto)). }
  assert (HD : 4096 <= lib.Reusable.YG0f.ly_D ly /\ lib.Reusable.YG0f.ly_D ly + 4096 <= 0x7fffff800000).
  { apply in_app_bounds.
    exact (Happ (lib.Reusable.YG0f.ly_D ly, 4096)
             ltac:(unfold lib.Reusable.YG0f.owned_extents; cbn [In]; tauto)). }
  destruct HT as [HT0 HT1]. destruct HC as [HC0 HC1]. destruct HD as [HD0 HD1].
  (* the five thread pointers: DT = TP + 32 (0x5dc670, builtin_tls+232), TS = RT_TSDMAIN, C, T, DB *)
  exists (lib.Lib.Mem.wa (B.AsanRT.RT_TP + 32)), (lib.Lib.Mem.wa B.AsanRT.RT_TSDMAIN),
         (lib.Lib.Mem.wa (lib.Reusable.YG0f.ly_C ly)), (lib.Lib.Mem.wa (lib.Reusable.YG0f.ly_T ly)),
         (lib.Lib.Mem.wa (lib.Reusable.YG0f.ly_D ly)).
  unfold B.Prog.asan_stack_malloc_c.asan_tls_cells.
  rewrite (lib.Lib.Mem.wa_unsigned (B.AsanRT.RT_TP + 32) ltac:(bnd)).
  rewrite (lib.Lib.Mem.wa_unsigned B.AsanRT.RT_TSDMAIN ltac:(bnd)).
  rewrite (lib.Lib.Mem.wa_unsigned (lib.Reusable.YG0f.ly_C ly) ltac:(bnd)).
  rewrite (lib.Lib.Mem.wa_unsigned (lib.Reusable.YG0f.ly_T ly) ltac:(bnd)).
  rewrite (lib.Lib.Mem.wa_unsigned (lib.Reusable.YG0f.ly_D ly) ltac:(bnd)).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
          (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))))))))).
  (* 1. TLS_INDEX (asan_stack_malloc_c.TLS_INDEX = 0xa15d0, .got+0xd40): the two words at 0xa15d0 / 0xa15d8;
        the second is -2048 as a word, row value 0xfffffffffffff800, closed mod 2^64 by le8_eq *)
  - apply (proj2 (lib.Lib.Mem.bytes_at_app B.Img0.rsegs m _ _ _)). split.
    + eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa15d0) (lib.Reusable.YG0f.ANum 1) 8%nat);
        [apply Hrow; inconst | reflexivity | bnd | bnd | apply le8_eq; reflexivity].
    + rewrite lib.Lib.Mem.length_le8.
      eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa15d8)
                (lib.Reusable.YG0f.ANum 0xfffffffffffff800) 8%nat);
        [apply Hrow; inconst | bnd | bnd | bnd | apply le8_eq; vm_compute; reflexivity].
  (* 2. REAL_TLS_GET_ADDR = 0xa2690 (__interception::real___tls_get_addr) holds MUSL_TLS_GET_ADDR = 0x99624
        (__tls_get_addr) *)
  - eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa2690) (lib.Reusable.YG0f.ANum 0x99624) 8%nat);
      [apply Hrow; inconst | reflexivity | bnd | bnd | apply le8_eq; reflexivity].
  (* 3. TP - 8 holds DT = TP + 32 (YF0m row z8 (ATp (-8)) 0x5dc670) *)
  - eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ATp (-8)) (lib.Reusable.YG0f.ANum 0x5dc670) 8%nat);
      [apply Hrow; inconst | cbn [lib.Reusable.YG0f.aeval]; rewrite Htp; bnd | bnd | bnd
       | apply le8_eq; reflexivity].
  (* 4. DT + 8 = 0x5dc678 (builtin_tls+240) holds TP + 2048 = 0x5dce50 (builtin_tls+2248) *)
  - eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0x5dc678) (lib.Reusable.YG0f.ANum 0x5dce50) 8%nat);
      [apply Hrow; inconst | bnd | bnd | bnd | apply le8_eq; vm_compute; reflexivity].
  (* 5. TSD_KEY_INITED = 0xa8f20 (__asan::tsd_key_inited) *)
  - eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa8f20) (lib.Reusable.YG0f.ANum 1) 1%nat);
      [apply Hrow; inconst | reflexivity | bnd | bnd | apply le1_eq; reflexivity].
  (* 6. the key index bounds *)
  - bnd.
  (* 8. TSD_KEY = 0xa8f24 (__asan::tsd_key) *)
  - eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa8f24) (lib.Reusable.YG0f.ANum 0) 4%nat);
      [apply Hrow; inconst | reflexivity | bnd | bnd | apply le4_eq; reflexivity].
  (* 9. TP - 88 holds TS = the TSD main block *)
  - eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ATp (-88)) (lib.Reusable.YG0f.ATsd 0) 8%nat);
      [apply Hrow; inconst | cbn [lib.Reusable.YG0f.aeval]; rewrite Htp; bnd | bnd | bnd
       | cbn [lib.Reusable.YG0f.aeval]; rewrite Htsdly; apply le8_eq; reflexivity].
  (* 10. TS + 8 * k holds C *)
  - eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ATsd 0) (lib.Reusable.YG0f.AC 0) 8%nat);
      [apply Hrow; inconst | cbn [lib.Reusable.YG0f.aeval]; rewrite Htsdly; bnd | bnd | bnd
       | cbn [lib.Reusable.YG0f.aeval]; apply le8_eq; f_equal; lia].
  (* 11. C + 152 holds T *)
  - eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.AC 152) (lib.Reusable.YG0f.AT 0) 8%nat);
      [apply Hrow; inconst | cbn [lib.Reusable.YG0f.aeval]; reflexivity | bnd | bnd
       | cbn [lib.Reusable.YG0f.aeval]; apply le8_eq; f_equal; lia].
  (* 12. the two words at T + 48: YF0m rows z8 (AT 48) 0x5dcd88 (builtin_tls+2048) and z8 (AT 56) 0x5dce64
         (builtin_tls+2268); no B module names them *)
  - exists (lib.Lib.Mem.wa 0x5dcd88), (lib.Lib.Mem.wa 0x5dce64).
    apply (proj2 (lib.Lib.Mem.bytes_at_app B.Img0.rsegs m _ _ _)). split.
    + eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.AT 48) (lib.Reusable.YG0f.ANum 0x5dcd88) 8%nat);
        [apply Hrow; inconst | cbn [lib.Reusable.YG0f.aeval]; reflexivity | bnd | bnd
         | apply le8_eq; reflexivity].
    + rewrite lib.Lib.Mem.length_le8.
      eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.AT 56) (lib.Reusable.YG0f.ANum 0x5dce64) 8%nat);
        [apply Hrow; inconst | cbn [lib.Reusable.YG0f.aeval]; bnd | bnd | bnd
         | apply le8_eq; reflexivity].
  (* 13. GOT_CF = 0xa08e0 (.got+0x50) holds CF = 0x13b1e8 (__sanitizer::common_flags_dont_use) *)
  - eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa08e0) (lib.Reusable.YG0f.ANum 0x13b1e8) 8%nat);
      [apply Hrow; inconst | reflexivity | bnd | bnd | apply le8_eq; reflexivity].
  (* 14. CF + 137 = 0x13b271 (common_flags_dont_use+137) *)
  - eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0x13b271) (lib.Reusable.YG0f.ANum 1) 1%nat);
      [apply Hrow; inconst | bnd | bnd | bnd | apply le1_eq; reflexivity].
  (* 15. GOT_VERBOSITY = 0xa0940 (.got+0xb0) holds VERBOSITY = 0x139158 (__sanitizer::current_verbosity) *)
  - eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa0940) (lib.Reusable.YG0f.ANum 0x139158) 8%nat);
      [apply Hrow; inconst | reflexivity | bnd | bnd | apply le8_eq; reflexivity].
  (* 16. VERBOSITY *)
  - eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0x139158) (lib.Reusable.YG0f.ANum 0) 4%nat);
      [apply Hrow; inconst | reflexivity | bnd | bnd | apply le4_eq; reflexivity].
  (* 17. DTLS_TPOFF = 0xa15e0 (.got+0xd50) *)
  - eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa15e0) (lib.Reusable.YG0f.ANum 8) 8%nat);
      [apply Hrow; inconst | reflexivity | bnd | bnd | apply le8_eq; reflexivity].
  (* 18. TP + 8 holds DB *)
  - eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ATp 8) (lib.Reusable.YG0f.AD 0) 8%nat);
      [apply Hrow; inconst | cbn [lib.Reusable.YG0f.aeval]; rewrite Htp; bnd | bnd | bnd
       | cbn [lib.Reusable.YG0f.aeval]; apply le8_eq; f_equal; lia].
  (* 19. DB <> 0 *)
  - lia.
  (* 20. DB + 24 holds TP *)
  - eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.AD 24) (lib.Reusable.YG0f.ATp 0) 8%nat);
      [apply Hrow; inconst | cbn [lib.Reusable.YG0f.aeval]; reflexivity | bnd | bnd
       | cbn [lib.Reusable.YG0f.aeval]; rewrite Htp; apply le8_eq; reflexivity].
Qed.

End TlsOfAR.

(* ---------------------------------------------------------------------------------------------------------
   2. Image B's segments: where ro_addr can be true, and where the rom ends (the shadow lies above every
   segment, so a shadow byte the view sees is a byte of mem). *)

Lemma find_segment_some_spec : forall (l : list Segment) (addr n : Z) (s : Segment),
  find_segment l addr n = Some s ->
  In s l /\ Z.of_N (seg_base s) <= addr /\ addr + n <= Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
  induction l as [|sg t IH]; intros addr n s H; cbn in H; [discriminate H|].
  destruct (andb (Z.leb (Z.of_N (seg_base sg)) addr)
                 (Z.leb (addr + n) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))) eqn:E.
  - injection H as <-. apply andb_prop in E as [E1 E2].
    apply Z.leb_le in E1. apply Z.leb_le in E2. split; [left; reflexivity | lia].
  - destruct (IH addr n s H) as (Hin & Hb). split; [right; exact Hin | exact Hb].
Qed.

(* every loaded segment of image B ends at or below ImgBounds.IMG_HI = 0x5fe000 (ProgBridge.rsegs_spans: the last
   segment is [0xa2000, 0xa2000 + 0x55c000)) *)
Lemma seg_rom_none_high : forall a : Z, B.Prog.ImgBounds.IMG_HI <= a < 2 ^ 64 ->
  lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 a) = None.
Proof.
  intros a Ha. change lib.Reusable.YB1v.tfibsegs with B.Img0.rsegs.
  unfold B.Prog.ImgBounds.IMG_HI in Ha.
  unfold lib.Reusable.YK11.seg_rom, memory_read.
  destruct (find_segment B.Img0.rsegs (bv_unsigned (Z_to_bv 64 a)) (Z.of_N 1)) as [s|] eqn:E;
    [exfalso | reflexivity].
  destruct (find_segment_some_spec _ _ _ _ E) as (Hin & Hb1 & Hb2).
  assert (Hu : bv_unsigned (Z_to_bv 64 a) = a).
  { rewrite Z_to_bv_unsigned. change (bv_wrap 64 a) with (a mod 2 ^ 64). apply Z.mod_small. lia. }
  rewrite Hu in Hb1, Hb2.
  pose proof (in_map (fun s0 : Segment => (Z.of_N (seg_base s0), Z.of_N (seg_size s0))) _ s Hin) as Hm.
  rewrite B.ProgBridge.rsegs_spans in Hm. cbn [In] in Hm.
  destruct Hm as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as E1a E1b; lia.
Qed.

(* the errno word (YF0m.TFIB_ERRNO = 0x5dc5ac, builtin_tls+36) lies in a writable segment, so ro_addr is false
   there (ts_errno, by computation) *)
Lemma ro_not_errno : forall a : word, lib.Lib.Mem.ro_addr B.Img0.rsegs a = true ->
  ~ (lib.Reusable.YF0m.TFIB_ERRNO <= bv_unsigned a < lib.Reusable.YF0m.TFIB_ERRNO + 4).
Proof.
  intros a Ha [H1 H2]. unfold lib.Reusable.YF0m.TFIB_ERRNO in H1, H2.
  assert (Hb : a = Z_to_bv 64 (bv_unsigned a)) by (symmetry; apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned).
  assert (Hv : bv_unsigned a = 0x5dc5ac \/ bv_unsigned a = 0x5dc5ad \/ bv_unsigned a = 0x5dc5ae \/
               bv_unsigned a = 0x5dc5af) by lia.
  rewrite Hb in Ha.
  destruct Hv as [E|[E|[E|E]]]; rewrite E in Ha; vm_compute in Ha; discriminate Ha.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   3. The decisions the shadow case split needs (no classical axiom).  Image-independent. *)

Lemma exists_in_dec : forall {X : Type} (P : X -> Prop) (l : list X),
  (forall x, {P x} + {~ P x}) -> {exists x, In x l /\ P x} + {~ (exists x, In x l /\ P x)}.
Proof.
  intros X P l Hd. induction l as [|x t IH].
  - right. intros (y & [] & _).
  - destruct (Hd x) as [H|H]; [left; exists x; split; [left; reflexivity | exact H]|].
    destruct IH as [H2|IH].
    + left. destruct H2 as (y & Hy & HP). exists y. split; [right; exact Hy | exact HP].
    + right. intros (y & [Hy|Hy] & HP); [subst y; exact (H HP) | exact (IH (ex_intro _ y (conj Hy HP)))].
Qed.

Lemma in_zr_dec : forall (a : Z) (r : Z * Z),
  {lib.Reusable.YG0n.in_zr a r} + {~ lib.Reusable.YG0n.in_zr a r}.
Proof.
  intros a r. unfold lib.Reusable.YG0n.in_zr.
  destruct (Z_le_dec (fst r) a) as [H1|H1]; [|right; lia].
  destruct (Z_lt_dec a (fst r + snd r)) as [H2|H2]; [left; lia | right; lia].
Qed.

Lemma exists_zr_dec : forall (a : Z) (l : list (Z * Z)),
  {Exists (lib.Reusable.YG0n.in_zr a) l} + {~ Exists (lib.Reusable.YG0n.in_zr a) l}.
Proof.
  intros a. induction l as [|r t IH].
  - right. intros H. inversion H.
  - destruct (in_zr_dec a r) as [H|H]; [left; apply Exists_cons_hd; exact H|].
    destruct IH as [H2|H2]; [left; apply Exists_cons_tl; exact H2|].
    right. intros HE. inversion HE; subst; [exact (H ltac:(assumption)) | exact (H2 ltac:(assumption))].
Qed.

Lemma chunk_client_dec : forall (B : lib.Reusable.YG0f.asyms) (ly : lib.Reusable.YG0f.alayout) (a : Z)
    (k : lib.Reusable.YG00.chunk),
  {lib.Reusable.YG00.ck_state k = lib.Reusable.YG00.CAllocated /\
   lib.Reusable.YG0f.sptr_addr B ly (lib.Reusable.YG00.ck_user k) <= a <
   lib.Reusable.YG0f.sptr_addr B ly (lib.Reusable.YG00.ck_user k) + lib.Reusable.YG00.ck_n k} +
  {~ (lib.Reusable.YG00.ck_state k = lib.Reusable.YG00.CAllocated /\
      lib.Reusable.YG0f.sptr_addr B ly (lib.Reusable.YG00.ck_user k) <= a <
      lib.Reusable.YG0f.sptr_addr B ly (lib.Reusable.YG00.ck_user k) + lib.Reusable.YG00.ck_n k)}.
Proof.
  intros B ly a k. destruct (lib.Reusable.YG00.ck_state k) eqn:Ek.
  - destruct (Z_le_dec (lib.Reusable.YG0f.sptr_addr B ly (lib.Reusable.YG00.ck_user k)) a) as [A1|A1];
      [|right; intros (_ & ?); lia].
    destruct (Z_lt_dec a (lib.Reusable.YG0f.sptr_addr B ly (lib.Reusable.YG00.ck_user k)
                          + lib.Reusable.YG00.ck_n k)) as [A2|A2];
      [left; split; [reflexivity | lia] | right; intros (_ & ?); lia].
  - right. intros (Hc & _). discriminate Hc.
Qed.

Lemma frame_client_dec : forall (ly : lib.Reusable.YG0f.alayout) (a : Z) (cp : Z * Z),
  {lib.Reusable.YG0n.in_zr a (lib.Reusable.YG0f.frame_addr ly (fst cp) (snd cp),
                              lib.Reusable.YG00.fs_frame_bytes (fst cp)) \/
   lib.Reusable.YG0n.in_zr a
     (lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr ly (fst cp) (snd cp)),
      lib.Reusable.YG00.fs_frame_bytes (fst cp) / 8)} +
  {~ (lib.Reusable.YG0n.in_zr a (lib.Reusable.YG0f.frame_addr ly (fst cp) (snd cp),
                                 lib.Reusable.YG00.fs_frame_bytes (fst cp)) \/
      lib.Reusable.YG0n.in_zr a
        (lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr ly (fst cp) (snd cp)),
         lib.Reusable.YG00.fs_frame_bytes (fst cp) / 8))}.
Proof.
  intros ly a cp.
  destruct (in_zr_dec a (lib.Reusable.YG0f.frame_addr ly (fst cp) (snd cp),
                         lib.Reusable.YG00.fs_frame_bytes (fst cp))) as [D1|D1]; [left; left; exact D1|].
  destruct (in_zr_dec a (lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr ly (fst cp) (snd cp)),
                         lib.Reusable.YG00.fs_frame_bytes (fst cp) / 8)) as [D2|D2];
    [left; right; exact D2 | right; intros [X|X]; [exact (D1 X) | exact (D2 X)]].
Qed.

Lemma aclient_byte_dec : forall (B : lib.Reusable.YG0f.asyms) (ly : lib.Reusable.YG0f.alayout)
    (S : lib.Reusable.YG00.astate) (a : Z),
  {lib.Reusable.YG0n.aclient_byte B ly S a} + {~ lib.Reusable.YG0n.aclient_byte B ly S a}.
Proof.
  intros B ly S a. unfold lib.Reusable.YG0n.aclient_byte.
  destruct (exists_in_dec _ (lib.Reusable.YG00.st_chunks S) (chunk_client_dec B ly a)) as [H1|H1].
  { left. left. exact H1. }
  destruct (exists_in_dec _ (lib.Reusable.YG01.frames S) (frame_client_dec ly a)) as [H2|H2].
  { left. right. exact H2. }
  right. intros [X|X]; [exact (H1 X) | exact (H2 X)].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   4. ctlrt_of_AR: ACtlCut.ctl_rt (asan_cells_at /\ shadow_rw_at /\ ro_agree_at) from AR. *)
Section CtlRt.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.

Lemma range_vis_at : forall (B : lib.Reusable.YG0f.asyms) (ly : lib.Reusable.YG0f.alayout)
    (rd : lib.Reusable.YG0f.reader) (e : lib.Reusable.YG0f.aexp) (n a : Z),
  lib.Reusable.YG0f.range_vis B ly rd (e, n) ->
  lib.Reusable.YG0f.aeval B ly e <= a < lib.Reusable.YG0f.aeval B ly e + n -> rd a <> None.
Proof.
  intros B ly rd e n a HR Hb Hnone.
  apply (HR (a - lib.Reusable.YG0f.aeval B ly e) ltac:(cbn [snd]; lia)).
  cbn [fst] in *.
  replace (lib.Reusable.YG0f.aeval B ly e + (a - lib.Reusable.YG0f.aeval B ly e)) with a by lia.
  exact Hnone.
Qed.

(* a client byte (live chunk user bytes, live fake frames and their shadow) is visible in the view *)
Lemma aclient_vis : forall (B : lib.Reusable.YG0f.asyms) (ly : lib.Reusable.YG0f.alayout)
    (S : lib.Reusable.YG00.astate) (rd : lib.Reusable.YG0f.reader) (a : Z),
  Forall (lib.Reusable.YG0f.range_vis B ly rd) (lib.Reusable.YG0n.aclient S) ->
  lib.Reusable.YG0n.aclient_byte B ly S a -> rd a <> None.
Proof.
  intros B ly S rd a HF HC.
  pose proof (proj1 (Forall_forall _ _) HF) as HV. clear HF.
  destruct HC as [(k & Hin & Hst & Hlo & Hhi) | (cp & Hin & [Hr | Hr])].
  - assert (Hmem : In (lib.Reusable.YG0f.sptr_exp (lib.Reusable.YG00.ck_user k), lib.Reusable.YG00.ck_n k)
                      (lib.Reusable.YG0n.aclient S)).
    { unfold lib.Reusable.YG0n.aclient. apply in_or_app. left. apply in_flat_map.
      exists k. split; [exact Hin|]. unfold lib.Reusable.YG0n.chunk_user. rewrite Hst. left. reflexivity. }
    apply (range_vis_at B ly rd _ _ a (HV _ Hmem)).
    unfold lib.Reusable.YG0f.sptr_addr in Hlo, Hhi. lia.
  - assert (Hmem : In (lib.Reusable.YG0f.AF (lib.Reusable.YG0f.fs_frame_off (fst cp) (snd cp)),
                       lib.Reusable.YG00.fs_frame_bytes (fst cp)) (lib.Reusable.YG0n.aclient S)).
    { unfold lib.Reusable.YG0n.aclient. apply in_or_app. right. apply in_or_app. left.
      apply (in_map (fun cp0 : Z * Z =>
                       (lib.Reusable.YG0f.AF (lib.Reusable.YG0f.fs_frame_off (fst cp0) (snd cp0)),
                        lib.Reusable.YG00.fs_frame_bytes (fst cp0)))). exact Hin. }
    apply (range_vis_at B ly rd _ _ a (HV _ Hmem)).
    unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YG0f.frame_addr in Hr. cbn [fst snd] in Hr.
    cbn [lib.Reusable.YG0f.aeval]. lia.
  - assert (Hmem : In (lib.Reusable.YG0f.ASh
                         (lib.Reusable.YG0f.AF (lib.Reusable.YG0f.fs_frame_off (fst cp) (snd cp))),
                       lib.Reusable.YG00.fs_frame_bytes (fst cp) / 8) (lib.Reusable.YG0n.aclient S)).
    { unfold lib.Reusable.YG0n.aclient. apply in_or_app. right. apply in_or_app. right.
      apply (in_map (fun cp0 : Z * Z =>
                       (lib.Reusable.YG0f.ASh
                          (lib.Reusable.YG0f.AF (lib.Reusable.YG0f.fs_frame_off (fst cp0) (snd cp0))),
                        lib.Reusable.YG00.fs_frame_bytes (fst cp0) / 8))). exact Hin. }
    apply (range_vis_at B ly rd _ _ a (HV _ Hmem)).
    unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YG0f.frame_addr in Hr. cbn [fst snd] in Hr.
    cbn [lib.Reusable.YG0f.aeval]. lia.
Qed.

(* above the image the view falls back to nothing, so a visible byte there is a byte of mem *)
Lemma mem_some_of_aview_high : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) (a : Z),
  B.Prog.ImgBounds.IMG_HI <= a < 2 ^ 64 ->
  lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m a <> None ->
  m (Z_to_bv 64 a) <> None.
Proof.
  intros W m a Ha Hv Hm. apply Hv.
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict.
  destruct (lib.Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:E.
  - rewrite (seg_rom_none_high a Ha). reflexivity.
  - rewrite Hm, (seg_rom_none_high a Ha). reflexivity.
Qed.

Variable B : lib.Reusable.YG0f.asyms.

(* The asan_cells and ro_agree conjuncts of ctl_rt, factored out of ctlrt_of_AR (route (C), a Theorem Labs lane 09:20Z) so that
   ProgWorldCtlRtC.ctl_rt_C_of_AR states them WITHOUT AR_states_vis0_shadow.  ctlrt_of_AR's statement is unchanged;
   its proof now applies these two lemmas. *)
Lemma asan_cells_of_AR : lib.Reusable.YF0m.CtrlTSyms B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md,
    lib.Reusable.YG0n.AR segs B ly S W m md -> B.ACtlK.asan_cells_at m.
Proof.
  intros HTS ly S W m md HAR.
  destruct HAR as (HM & _).
  destruct HM as [Hwf Huniv Hsyms Hlay Hplaced Hconst Hconstown Hcells Hfa Hflags Hdepot Hshadow
                  Hzshadow Hjunk Hareas Hclient Hzero Hlytsd Hstatimg].
  assert (Hrow : forall c, In c (lib.Reusable.YF0m.Tfib_const ly) ->
            lib.Reusable.YG0f.cell_holds B ly (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m) c).
  { intros c Hc. apply (proj1 (Forall_forall _ _) Hconst).
    rewrite (lib.Reusable.YF0m.ts_const B HTS ly). exact Hc. }
    (* asan_cells: the 17 runtime cells of B.AsanRT, each an absolute const row of YF0m *)
    unfold B.ACtlK.asan_cells_at, B.AsanRT.asan_cells.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
            (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))))))).
    (* CELL_K = 0xa96b8 (__asan_shadow_memory_dynamic_address) holds ASAN_K = 0x7fff8000 *)
    + eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa96b8)
                (lib.Reusable.YG0f.ANum 0x7fff8000) 8%nat);
        [apply Hrow; inconst | reflexivity | bnd | bnd | apply le8_eq; reflexivity].
    (* GOT_CELL_K = 0xa08f0 (.got+0x60) *)
    + eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa08f0)
                (lib.Reusable.YG0f.ANum 0xa96b8) 8%nat);
        [apply Hrow; inconst | reflexivity | bnd | bnd | apply le8_eq; reflexivity].
    (* INITED = 0xaa398 (__asan::asan_inited) *)
    + eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xaa398) (lib.Reusable.YG0f.ANum 1) 1%nat);
        [apply Hrow; inconst | reflexivity | bnd | bnd | apply le1_eq; reflexivity].
    (* REPLACE = 0xaa399 (__asan::replace_intrin_cached) *)
    + eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xaa399) (lib.Reusable.YG0f.ANum 1) 1%nat);
        [apply Hrow; inconst | reflexivity | bnd | bnd | apply le1_eq; reflexivity].
    (* GOT_REPLACE = 0xa1458 (.got+0xbc8) *)
    + eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa1458)
                (lib.Reusable.YG0f.ANum 0xaa399) 8%nat);
        [apply Hrow; inconst | reflexivity | bnd | bnd | apply le8_eq; reflexivity].
    (* UAR = 0xa96c0 (__asan_option_detect_stack_use_after_return) *)
    + eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa96c0) (lib.Reusable.YG0f.ANum 1) 4%nat);
        [apply Hrow; inconst | reflexivity | bnd | bnd | apply le4_eq; reflexivity].
    (* GOT_UAR = 0xa0948 (.got+0xb8) *)
    + eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa0948)
                (lib.Reusable.YG0f.ANum 0xa96c0) 8%nat);
        [apply Hrow; inconst | reflexivity | bnd | bnd | apply le8_eq; reflexivity].
    (* CANPOISON = 0xa8f1c (__asan::can_poison_memory) *)
    + eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa8f1c) (lib.Reusable.YG0f.ANum 1) 1%nat);
        [apply Hrow; inconst | reflexivity | bnd | bnd | apply le1_eq; reflexivity].
    (* HIEND = 0xaa3a0 (__asan::kHighMemEnd) *)
    + eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xaa3a0)
                (lib.Reusable.YG0f.ANum 0x7fffffffffff) 8%nat);
        [apply Hrow; inconst | reflexivity | bnd | bnd | apply le8_eq; reflexivity].
    (* GOT_HIEND = 0xa0908 (.got+0x78) *)
    + eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa0908)
                (lib.Reusable.YG0f.ANum 0xaa3a0) 8%nat);
        [apply Hrow; inconst | reflexivity | bnd | bnd | apply le8_eq; reflexivity].
    (* MIDBEG = 0xaa3a8 (__asan::kMidMemBeg) *)
    + eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xaa3a8) (lib.Reusable.YG0f.ANum 0) 8%nat);
        [apply Hrow; inconst | reflexivity | bnd | bnd | apply le8_eq; reflexivity].
    (* GOT_MIDBEG = 0xa08f8 (.got+0x68) *)
    + eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa08f8)
                (lib.Reusable.YG0f.ANum 0xaa3a8) 8%nat);
        [apply Hrow; inconst | reflexivity | bnd | bnd | apply le8_eq; reflexivity].
    (* MIDEND = 0xaa3b0 (__asan::kMidMemEnd) *)
    + eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xaa3b0) (lib.Reusable.YG0f.ANum 0) 8%nat);
        [apply Hrow; inconst | reflexivity | bnd | bnd | apply le8_eq; reflexivity].
    (* GOT_MIDEND = 0xa0900 (.got+0x70) *)
    + eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa0900)
                (lib.Reusable.YG0f.ANum 0xaa3b0) 8%nat);
        [apply Hrow; inconst | reflexivity | bnd | bnd | apply le8_eq; reflexivity].
    (* REAL_MEMCPY = 0xa2750 (__interception::real_memcpy) holds MUSL_MEMCPY = 0x98a30 (memcpy) *)
    + eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa2750)
                (lib.Reusable.YG0f.ANum 0x98a30) 8%nat);
        [apply Hrow; inconst | reflexivity | bnd | bnd | apply le8_eq; reflexivity].
    (* REAL_MEMSET = 0xa2758 (__interception::real_memset) holds MUSL_MEMSET = 0x98e34 (memset) *)
    + eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa2758)
                (lib.Reusable.YG0f.ANum 0x98e34) 8%nat);
        [apply Hrow; inconst | reflexivity | bnd | bnd | apply le8_eq; reflexivity].
    (* GOT_REAL_MEMSET = 0xa0910 (.got+0x80) *)
    + eapply (cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa0910)
                (lib.Reusable.YG0f.ANum 0xa2758) 8%nat);
        [apply Hrow; inconst | reflexivity | bnd | bnd | apply le8_eq; reflexivity].
Qed.

Lemma ro_agree_of_AR : lib.Reusable.YF0m.CtrlTSyms B -> B.ProgWorld.AR_states_owned_ro B ->
  forall (RLO RHI : Z) ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md,
    lib.Reusable.YG0n.AR segs B ly S W m md ->
    B.Prog.CtrlBase.arodata_okP segs RLO RHI B (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m) ->
    B.ACtlK.ro_agree_at m.
Proof.
  intros HTS Howned RLO RHI ly S W m md HAR0 Hro.
    (* ro_agree: the kept read-only view, owned rows and the writable errno word *)
    apply (B.ProgWorld.ro_agree_of_view W m).
    intros a Ha.
    destruct (exists_zr_dec (bv_unsigned a) (lib.Reusable.YG0f.as_owned_static B)) as [Ho|Ho].
    + exact (Howned ly S W m md HAR0 a Ha Ho).
    + assert (Hin : B.Prog.CtrlBase.in_roP segs RLO RHI (bv_unsigned a)).
      { left. unfold lib.Lib.Mem.ro_addr in Ha.
        destruct (find_segment B.Img0.rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate Ha].
        destruct (find_segment_some_spec _ _ _ _ E) as (Hins & Hb1 & Hb2).
        exists s. split; [exact Hins|].
        destruct (seg_writable s) eqn:Ew; [cbn in Ha; discriminate Ha|].
        split; [reflexivity | lia]. }
      assert (Herr : ~ (lib.Reusable.YG0f.as_errno B <= bv_unsigned a <
                        lib.Reusable.YG0f.as_errno B + 4)).
      { rewrite (lib.Reusable.YF0m.ts_errno B HTS). exact (ro_not_errno a Ha). }
      pose proof (Hro (bv_unsigned a) Hin Ho Herr) as Hg.
      rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hg. exact Hg.
Qed.

Lemma ctlrt_of_AR : B.ProgWorld.ctlrt_of_AR_stmt B.
Proof.
  unfold B.ProgWorld.ctlrt_of_AR_stmt.
  intros HTS HL Hvis0 Howned RLO RHI ly S W m md HAR Hro.
  pose proof HAR as HAR0.
  destruct HAR as (HM & _ & _ & _ & HHS).
  destruct HHS as [HPres HZ].
  destruct HM as [Hwf Huniv Hsyms Hlay Hplaced Hconst Hconstown Hcells Hfa Hflags Hdepot Hshadow
                  Hzshadow Hjunk Hareas Hclient Hzero Hlytsd Hstatimg].
  unfold B.ACtlCut.ctl_rt.
  refine (conj (asan_cells_of_AR HTS ly S W m md HAR0)
            (conj _ (ro_agree_of_AR HTS Howned RLO RHI ly S W m md HAR0 Hro))).
    unfold B.ACtlK.shadow_rw_at, B.AsanRT.shadow_rw.
    intros a Hsh.
    assert (Hband : lib.Reusable.YG0f.in_band_rw a).
    { unfold lib.Reusable.YG0f.in_band_rw, lib.Reusable.YG0f.kLowShadowBeg,
             lib.Reusable.YG0f.kLowShadowEnd, lib.Reusable.YG0f.kHighShadowBeg,
             lib.Reusable.YG0f.kHighShadowEnd.
      unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END,
             B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG in Hsh.
      destruct Hsh as [[H1 H2]|[H1 H2]]; [left|right]; lia. }
    assert (Hhigh : B.Prog.ImgBounds.IMG_HI <= a < 2 ^ 64).
    { unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END,
             B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG in Hsh.
      unfold B.Prog.ImgBounds.IMG_HI.
      change (2 ^ 64) with 18446744073709551616.
      destruct Hsh as [[H1 H2]|[H1 H2]]; lia. }
    assert (Hm : m (Z_to_bv 64 a) <> None).
    { destruct (aclient_byte_dec B ly S a) as [Hcl|Hcl].
      - apply (mem_some_of_aview_high W m a Hhigh).
        exact (aclient_vis B ly S (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m) a Hclient Hcl).
      - destruct (exists_zr_dec a (lib.Reusable.YG0f.ly_vis0 ly)) as [Hv|Hv].
        + destruct (lib.Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:EH.
          * exact (HPres a Hband Hcl (or_introl EH)).
          * exact (Hvis0 ly S W m md HAR0 a Hsh Hv EH).
        + exact (HPres a Hband Hcl (or_intror Hv)). }
    destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em; [|exfalso; exact (Hm eq_refl)].
    split.
    + unfold wview, lib.Lib.Mem.wa. rewrite Em. discriminate.
    + exists b. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Em. reflexivity.
Qed.

End CtlRt.
