(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/ProgWorldTlsApart.v (a working branch 75a3f0b4794,
   blob 1f4f062c65a): the same lemma / definition / Ltac names, Sections and proof steps over image B (asan-ubsan), except one added step in img_cls's proof (unfold ASAN_GT).
   Differences from A: module paths (A.ProgWorld / A.ProgWorld_Fs / A.Prog.X / A.AsanRT / A.Img0 -> B.*; the core files
   A.AF0m / A.AB1v -> lib.Reusable.YF0m / YB1v; the doubled lib/Lib/Mem.v named lib.Lib.Mem, as lib/B/ProgWorld_Fs.v
   does); and A's four image numerals are image B's constants by NAME, never a number: TS = ly_tsd = 0x5fcbb8 ->
   B.AsanRT.RT_TSDMAIN (= 0x5fd9f8, __pthread_tsd_main in the asan-ubsan symtab; = YF0m.TFIB_TSD), DT = 0x5db830 ->
   B.AsanRT.RT_TP + 32 (= 0x5dc670, builtin_tls+232; YF0m row `z8 (ATp (-8)) 0x5dc670`), the TSD_KEY row address
   0xa80e4 -> B.Prog.asan_stack_malloc_c.TSD_KEY (= 0xa8f24, __asan::tsd_key; YF0m row `z4 (ANum 0xa8f24) 0x0`), and
   img_cls's bound 0x5fe000 -> B.Prog.asan_stack_malloc_c.ASAN_GT (= 0x5fe000 in both images, B/ProgWorld_Fs.v header);
   so bnd also unfolds B.AsanRT.RT_TSDMAIN and ASAN_GT.  img_cls is the one statement that differs from A's (ASAN_GT
   by name for A's literal 0x5fe000; the same value).  Image-INDEPENDENT numerals kept from A (the shadow mapping, the
   same in both images): 0x7fff7000 = YG0f.kLowShadowBeg, 0x10007fff8000 = YG0f.kHighMemBeg = kHighShadowEnd,
   0x7fff8000 = B.AsanRT.ASAN_K (= A.AsanRT.ASAN_K), 0x800000000000 = YG0f.kHighMemEnd and 0x100000000000 = its eighth;
   2 ^ 32 / 2 ^ 64 as numerals.  rule 24: no function proved. *)
(* lib/B/ProgWorldTlsApart.v -- fuzz_ctrl image B (libreac v1.9.0, asan-ubsan): proof of ProgWorld.v's
   fp_tls_apart_stmt (Section TlsApart).  ITERATION-ONLY; type-check evidence on the planning core only, never
   acceptance.  rule 24: no function proved.  This is a bridge lemma over the core's world (AR / aview / cell_holds),
   not a proof of any binary function.

   Route (the statement's own comment, ProgWorld.v Section 15):
   1. The cells' VALUES.  Two byte lists that bytes_at reads at one address are equal (bytes_at_uniq), so the words
      asan_tls_cells names at TP-8, TP-88, TSD_KEY, TS+8k, C+152 and TP+8 are the AR const rows that
      ProgWorldCtlRt.ctl_tls_of_AR reads (YF0m.Tfib_const, via ProgWorld_Fs.pw_c8_bytes / pw_z4_bytes):
      DT = TP+32, TS = ly_tsd = RT_TSDMAIN, k = 0, C = ly_C, T = ly_T, DB = ly_D.
   2. A class split.  Every cell of fp_tls is in pw_cls (below ly_F or above ly_F + kFakeStackSize, and in low or high
      application memory); every range of fp_w cs ly_F and the stack window's shadow is in pd_cls (inside
      (ly_F, kFakeStackSize), or inside [ASAN_K, kHighMemBeg)); a pw_cls range and a pd_cls range are ly_dj (cls_fp_dj).
      The image cells end at or below ASAN_GT <= ly_F (ProgWorld_Fs.pw_F_above).  C+152 / T+48 / DB+24 lie in the owned
      extents (ly_C, 256) / (ly_T, kThreadObjSize) / (ly_D, 4096): apart from (ly_F, kFakeStackSize) by layout_ok
      lo_disj, and in application memory by lo_app.  The side-stack offsets of each class c <= 6 are one closed
      vm_compute (fs_offs_ok_le6). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0f YG0n YG0d YConstIn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.asan_stack_malloc_c B.Prog.RcAsanFP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YF0m YB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.AsanRT B.Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorld B.ProgWorld_Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation segs := lib.Reusable.YB1v.tfibsegs (only parsing).

(* ---------------------------------------------------------------------------------------------------------
   1. Byte-list uniqueness. *)

Lemma list_eq_nth : forall (X : Type) (l l' : list X), length l = length l' ->
  (forall i, (i < length l)%nat -> nth_error l i = nth_error l' i) -> l = l'.
Proof.
  intros X l. induction l as [|x l IH]; intros [|y l'] Hl H; cbn [length] in Hl; try discriminate Hl.
  - reflexivity.
  - pose proof (H 0%nat ltac:(cbn [length]; lia)) as H0. cbn [nth_error] in H0.
    injection H0 as Exy. subst y. f_equal. apply IH; [lia|].
    intros i Hi. exact (H (S i) ltac:(cbn [length]; lia)).
Qed.

Lemma bytes_at_uniq : forall (m : word -> option byte) (a : Z) (bs bs' : list byte),
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs' -> length bs = length bs' ->
  bs = bs'.
Proof.
  intros m a bs bs' (_ & _ & H) (_ & _ & H') Hl.
  apply list_eq_nth; [exact Hl|]. intros i Hi.
  rewrite <- (H i Hi), <- (H' i ltac:(lia)). reflexivity.
Qed.

Lemma le8_inj : forall v v' : word, lib.Lib.Mem.le8 v = lib.Lib.Mem.le8 v' -> v = v'.
Proof.
  intros v v' H. rewrite <- (lib.Lib.Mem.le_bytes_to_word_le8 v), H. apply lib.Lib.Mem.le_bytes_to_word_le8.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   2. The two classes and their disjointness.  The bounds are the shadow mapping's (image-independent):
   0x7fff7000 = YG0f.kLowShadowBeg, 0x10007fff8000 = YG0f.kHighMemBeg, 0x7fff8000 = B.AsanRT.ASAN_K. *)

(* a cell range: below the side stack or above it, and in low or high application memory *)
Definition pw_cls (F : Z) (w : Z * Z) : Prop :=
  (snd w <= F \/ F + lib.Reusable.YG0f.kFakeStackSize <= fst w) /\ (snd w <= 0x7fff7000 \/ 0x10007fff8000 <= fst w).

(* a write range: inside the side stack, or inside [ASAN_K, kHighMemBeg) (the shadow of application memory) *)
Definition pd_cls (F : Z) (d : Z * Z) : Prop :=
  (F <= fst d /\ snd d <= F + lib.Reusable.YG0f.kFakeStackSize) \/ (0x7fff8000 <= fst d /\ snd d <= 0x10007fff8000).

Lemma cls_fp_dj : forall F (Wl Dl : list (Z * Z)),
  Forall (pw_cls F) Wl -> Forall (pd_cls F) Dl -> B.Prog.RcAsanFP.fp_dj Wl Dl.
Proof.
  intros F Wl Dl HW HD. unfold B.Prog.RcAsanFP.fp_dj.
  eapply Forall_impl; [|exact HW]. intros w Hw. cbv beta.
  eapply Forall_impl; [|exact HD]. intros d Hd. cbv beta.
  red. unfold pw_cls, pd_cls in *. lia.
Qed.

(* image B's cells end at or below ASAN_GT (B.Prog.asan_stack_malloc_c.ASAN_GT, by name; A writes its value) *)
Lemma img_cls : forall F a b, B.Prog.asan_stack_malloc_c.ASAN_GT <= F -> b <= B.Prog.asan_stack_malloc_c.ASAN_GT ->
  pw_cls F (a, b).
Proof. intros F a b HF Hb. unfold pw_cls; cbn [fst snd]. unfold B.Prog.asan_stack_malloc_c.ASAN_GT in *. lia. Qed.

Lemma sh_lo : forall x, 0 <= x -> 0x7fff8000 <= B.AsanRT.shadow_addr x.
Proof.
  intros x Hx. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
  pose proof (Z.div_pos x 8 Hx ltac:(lia)). lia.
Qed.

Lemma sh_hi : forall x, x <= 0x800000000000 -> B.AsanRT.shadow_addr x <= 0x10007fff8000.
Proof.
  intros x Hx. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
  assert (H : x / 8 <= 0x800000000000 / 8) by (apply Z.div_le_mono; lia).
  change (0x800000000000 / 8) with 0x100000000000 in H. lia.
Qed.

(* the side-stack offsets of class c (c <= 6) inside [0, kFakeStackSize): one closed check per class *)
Definition fs_offs_ok (c : nat) : bool :=
  (0 <=? B.Prog.asan_stack_malloc_c.fs_hint 0 c) &&
  (B.Prog.asan_stack_malloc_c.fs_hint 0 c + 8 <=? lib.Reusable.YG0f.kFakeStackSize) &&
  (0 <=? B.Prog.asan_stack_malloc_c.fs_flag 0 c 0) &&
  (B.Prog.asan_stack_malloc_c.fs_flag 0 c 0 + B.Prog.asan_stack_malloc_c.fs_M c
     <=? lib.Reusable.YG0f.kFakeStackSize) &&
  (0 <=? B.Prog.asan_stack_malloc_c.fs_frame 0 c 0) &&
  (B.Prog.asan_stack_malloc_c.fs_frame 0 c (B.Prog.asan_stack_malloc_c.fs_M c)
     <=? lib.Reusable.YG0f.kFakeStackSize).

Lemma fs_offs_ok_le6 : forall c, (c <= 6)%nat -> fs_offs_ok c = true.
Proof. intros c Hc. do 7 (destruct c as [|c]; [vm_compute; reflexivity|]). lia. Qed.

Lemma fp_w1_cls : forall F c d, (c <= 6)%nat -> 0 <= F -> F + lib.Reusable.YG0f.kFakeStackSize <= 0x800000000000 ->
  In d (B.Prog.RcAsanFP.fp_w1 F c) -> pd_cls F d.
Proof.
  intros F c d Hc HF0 HF1 Hd.
  pose proof (fs_offs_ok_le6 c Hc) as Hb. unfold fs_offs_ok in Hb.
  rewrite !andb_true_iff, !Z.leb_le in Hb.
  destruct Hb as (((((B1 & B2) & B3) & B4) & B5) & B6).
  assert (E1 : B.Prog.asan_stack_malloc_c.fs_hint F c = F + B.Prog.asan_stack_malloc_c.fs_hint 0 c)
    by (unfold B.Prog.asan_stack_malloc_c.fs_hint; ring).
  assert (E2 : B.Prog.asan_stack_malloc_c.fs_flag F c 0 = F + B.Prog.asan_stack_malloc_c.fs_flag 0 c 0)
    by (unfold B.Prog.asan_stack_malloc_c.fs_flag; ring).
  assert (E3 : forall j, B.Prog.asan_stack_malloc_c.fs_frame F c j = F + B.Prog.asan_stack_malloc_c.fs_frame 0 c j)
    by (intros j; unfold B.Prog.asan_stack_malloc_c.fs_frame; ring).
  unfold B.Prog.RcAsanFP.fp_w1 in Hd. cbn [In] in Hd.
  destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; unfold pd_cls; cbn [fst snd]; rewrite ?E1, ?E2, ?E3.
  - left. lia.
  - left. lia.
  - left. lia.
  - right. split; [apply sh_lo | apply sh_hi]; lia.
Qed.

(* membership of a const row in image B's const table (as ProgWorldCtlRt's inconst) *)
Local Ltac inconst := unfold lib.Reusable.YF0m.Tfib_const; lib.Reusable.YConstIn.in_const_tbl.

(* numeric side goals: unfold the image constants (never the comparisons, which lia must still see) *)
Local Ltac bnd :=
  cbn [lib.Reusable.YG0f.aeval];
  cbv beta delta [B.AsanRT.RT_TP B.AsanRT.RT_TSDMAIN lib.Reusable.YF0m.TFIB_TP lib.Reusable.YF0m.TFIB_TSD
                  B.Prog.asan_stack_malloc_c.TLS_INDEX B.Prog.asan_stack_malloc_c.REAL_TLS_GET_ADDR
                  B.Prog.asan_stack_malloc_c.TSD_KEY_INITED B.Prog.asan_stack_malloc_c.TSD_KEY
                  B.Prog.asan_stack_malloc_c.GOT_CF B.Prog.asan_stack_malloc_c.CF
                  B.Prog.asan_stack_malloc_c.GOT_VERBOSITY B.Prog.asan_stack_malloc_c.VERBOSITY
                  B.Prog.asan_stack_malloc_c.DTLS_TPOFF B.Prog.asan_stack_malloc_c.ASAN_GT];
  try change (2 ^ 64) with 18446744073709551616;
  try change (2 ^ 32) with 4294967296;
  lia.

(* ---------------------------------------------------------------------------------------------------------
   3. fp_tls_apart. *)
Section TlsApart.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.

(* a range inside an application-memory extent that is apart from the side stack *)
Lemma owned_cls : forall F e len a b, lib.Reusable.YG0f.in_app e len ->
  e + len <= F \/ F + lib.Reusable.YG0f.kFakeStackSize <= e -> e <= a -> b <= e + len -> pw_cls F (a, b).
Proof.
  intros F e len a b [_ HA] HD Ha Hb. unfold pw_cls; cbn [fst snd].
  unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in HA. lia.
Qed.

Variable B : lib.Reusable.YG0f.asyms.

Lemma fp_tls_apart : B.ProgWorld.fp_tls_apart_stmt B.
Proof.
  unfold B.ProgWorld.fp_tls_apart_stmt.
  intros HTS _ ly S W m md cs lo hi HAR Hcs Hlo Hhi DT TS C T DB k Hcells.
  pose proof (B.ProgWorld_Fs.pw_F_above B ly S W m md HAR) as HGT.
  unfold B.Prog.asan_stack_malloc_c.ASAN_GT in HGT.
  destruct HAR as (HM & _).
  pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ HM) as LO.
  (* the rows of image B's const table *)
  assert (Hrow : forall c, In c (lib.Reusable.YF0m.Tfib_const ly) ->
            lib.Reusable.YG0f.cell_holds B ly (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m) c).
  { intros c Hc. apply (proj1 (Forall_forall _ _) (lib.Reusable.YG0n.am_const _ _ _ _ HM)).
    rewrite (lib.Reusable.YF0m.ts_const B HTS ly). exact Hc. }
  pose proof (lib.Reusable.YF0m.ts_tp B HTS) as Htp.
  assert (Htsd : lib.Reusable.YG0f.ly_tsd ly = B.AsanRT.RT_TSDMAIN)
    by (rewrite (lib.Reusable.YG0n.am_tsd _ _ _ _ HM), (lib.Reusable.YF0m.ts_tsd B HTS); reflexivity).
  (* the owned extents the thread cells and the side stack live in *)
  pose proof (proj1 (Forall_forall _ _) (lib.Reusable.YG0f.lo_app ly LO)) as Happ.
  assert (AT : lib.Reusable.YG0f.in_app (lib.Reusable.YG0f.ly_T ly) lib.Reusable.YG0f.kThreadObjSize)
    by exact (Happ (lib.Reusable.YG0f.ly_T ly, lib.Reusable.YG0f.kThreadObjSize)
                ltac:(unfold lib.Reusable.YG0f.owned_extents; cbn [In]; tauto)).
  assert (AF : lib.Reusable.YG0f.in_app (lib.Reusable.YG0f.ly_F ly) lib.Reusable.YG0f.kFakeStackSize)
    by exact (Happ (lib.Reusable.YG0f.ly_F ly, lib.Reusable.YG0f.kFakeStackSize)
                ltac:(unfold lib.Reusable.YG0f.owned_extents; cbn [In]; tauto)).
  assert (AC : lib.Reusable.YG0f.in_app (lib.Reusable.YG0f.ly_C ly) 256)
    by exact (Happ (lib.Reusable.YG0f.ly_C ly, 256) ltac:(unfold lib.Reusable.YG0f.owned_extents; cbn [In]; tauto)).
  assert (AD : lib.Reusable.YG0f.in_app (lib.Reusable.YG0f.ly_D ly) 4096)
    by exact (Happ (lib.Reusable.YG0f.ly_D ly, 4096) ltac:(unfold lib.Reusable.YG0f.owned_extents; cbn [In]; tauto)).
  destruct (B.ProgWorld_Fs.pw_ext_range _ _ AT) as [LT0 LT1].
  destruct (B.ProgWorld_Fs.pw_ext_range _ _ AF) as [LF0 LF1].
  destruct (B.ProgWorld_Fs.pw_ext_range _ _ AC) as [LC0 LC1].
  destruct (B.ProgWorld_Fs.pw_ext_range _ _ AD) as [LD0 LD1].
  unfold lib.Reusable.YG0f.kThreadObjSize in LT1.
  (* (ly_T, kThreadObjSize), (ly_C, 256) and (ly_D, 4096) are apart from the side stack (lo_disj) *)
  pose proof (lib.Reusable.YG0f.lo_disj ly LO) as DJ.
  unfold lib.Reusable.YG0f.static_extents, lib.Reusable.YG0f.owned_extents in DJ.
  cbn [app lib.Reusable.YG0f.pairwise] in DJ.
  destruct DJ as (_ & _ & DJT & DJF & _).
  assert (DTF : lib.Reusable.YG0f.zdisjoint (lib.Reusable.YG0f.ly_T ly, lib.Reusable.YG0f.kThreadObjSize)
                  (lib.Reusable.YG0f.ly_F ly, lib.Reusable.YG0f.kFakeStackSize))
    by (apply (proj1 (Forall_forall _ _) DJT); cbn [In]; tauto).
  assert (DFC : lib.Reusable.YG0f.zdisjoint (lib.Reusable.YG0f.ly_F ly, lib.Reusable.YG0f.kFakeStackSize)
                  (lib.Reusable.YG0f.ly_C ly, 256))
    by (apply (proj1 (Forall_forall _ _) DJF); cbn [In]; tauto).
  assert (DFD : lib.Reusable.YG0f.zdisjoint (lib.Reusable.YG0f.ly_F ly, lib.Reusable.YG0f.kFakeStackSize)
                  (lib.Reusable.YG0f.ly_D ly, 4096))
    by (apply (proj1 (Forall_forall _ _) DJF); cbn [In]; tauto).
  unfold lib.Reusable.YG0f.zdisjoint in DTF, DFC, DFD. cbn [fst snd] in DTF, DFC, DFD.
  (* the stack lies in high application memory *)
  pose proof (lib.Reusable.YG0f.lo_top ly LO) as (_ & _ & _ & HSH & _ & _ & HSL).
  (* 1. the values of the thread pointers: each word asan_tls_cells reads is the AR row at its address *)
  destruct Hcells as (_ & _ & HDT & _ & _ & Hk & HK & HTS0 & HC0 & HT0 & _ & _ & _ & _ & _ & _ & HDB0 & _ & _).
  change (2 ^ 32) with 4294967296 in Hk.
  (* TP - 8 holds DT = TP + 32 (YF0m row `z8 (ATp (-8)) 0x5dc670`) *)
  assert (RDT : lib.Lib.Mem.bytes_at B.Img0.rsegs m (B.AsanRT.RT_TP - 8)
                  (lib.Lib.Mem.le8 (Z_to_bv 64 (B.AsanRT.RT_TP + 32)))).
  { apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ATp (-8))
             (lib.Reusable.YG0f.ANum (B.AsanRT.RT_TP + 32)));
      [apply Hrow; inconst | cbn [lib.Reusable.YG0f.aeval]; rewrite Htp; reflexivity | reflexivity | bnd | bnd]. }
  pose proof (le8_inj _ _ (bytes_at_uniq _ _ _ _ HDT RDT ltac:(rewrite !lib.Lib.Mem.length_le8; reflexivity))) as EDT.
  subst DT.
  (* TP - 88 holds TS = ly_tsd (YF0m row `c8 (ATp (-88)) (ATsd 0)`) *)
  assert (RTS : lib.Lib.Mem.bytes_at B.Img0.rsegs m (B.AsanRT.RT_TP - 88)
                  (lib.Lib.Mem.le8 (Z_to_bv 64 B.AsanRT.RT_TSDMAIN))).
  { apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ATp (-88)) (lib.Reusable.YG0f.ATsd 0));
      [apply Hrow; inconst | cbn [lib.Reusable.YG0f.aeval]; rewrite Htp; reflexivity
       | cbn [lib.Reusable.YG0f.aeval]; rewrite Htsd; reflexivity | bnd | bnd]. }
  pose proof (le8_inj _ _ (bytes_at_uniq _ _ _ _ HTS0 RTS ltac:(rewrite !lib.Lib.Mem.length_le8; reflexivity))) as ETS.
  subst TS.
  (* TSD_KEY holds k = 0 (YF0m row `z4 (ANum 0xa8f24) 0x0`) *)
  assert (RK : lib.Lib.Mem.bytes_at B.Img0.rsegs m B.Prog.asan_stack_malloc_c.TSD_KEY
                 (lib.Lib.Mem.le4 (Z_to_bv 64 0))).
  { apply (B.ProgWorld_Fs.pw_z4_bytes B ly W m (lib.Reusable.YG0f.ANum B.Prog.asan_stack_malloc_c.TSD_KEY));
      [apply Hrow; inconst | reflexivity | bnd | bnd | bnd]. }
  pose proof (bytes_at_uniq _ _ _ _ HK RK ltac:(rewrite !lib.Lib.Mem.length_le4; reflexivity)) as EK.
  unfold lib.Lib.Mem.le4 in EK.
  rewrite (B.ProgWorld_Fs.pw_u64 k), (B.ProgWorld_Fs.pw_u64 0) in EK by bnd.
  pose proof (lib.Lib.Mem.bytes_le_to_Z_to_le_bytes 4 k ltac:(lia)) as EK2.
  rewrite EK, (lib.Lib.Mem.bytes_le_to_Z_to_le_bytes 4 0) in EK2 by lia.
  change (8 * Z.of_nat 4) with 32 in EK2.
  rewrite (Z.mod_small k (2 ^ 32) Hk) in EK2. change (0 mod 2 ^ 32) with 0 in EK2.
  subst k.
  (* TS + 8 * k holds C = ly_C (YF0m row `c8 (ATsd 0) (AC 0)`) *)
  rewrite (B.ProgWorld_Fs.pw_u64 B.AsanRT.RT_TSDMAIN) in HC0 by bnd.
  assert (RC : lib.Lib.Mem.bytes_at B.Img0.rsegs m (B.AsanRT.RT_TSDMAIN + 8 * 0)
                 (lib.Lib.Mem.le8 (Z_to_bv 64 (lib.Reusable.YG0f.ly_C ly)))).
  { apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ATsd 0) (lib.Reusable.YG0f.AC 0));
      [apply Hrow; inconst | cbn [lib.Reusable.YG0f.aeval]; rewrite Htsd; reflexivity
       | cbn [lib.Reusable.YG0f.aeval]; lia | bnd | bnd]. }
  pose proof (le8_inj _ _ (bytes_at_uniq _ _ _ _ HC0 RC ltac:(rewrite !lib.Lib.Mem.length_le8; reflexivity))) as EC.
  subst C.
  (* C + 152 holds T = ly_T (YF0m row `c8 (AC 152) (AT 0)`) *)
  rewrite (B.ProgWorld_Fs.pw_u64 (lib.Reusable.YG0f.ly_C ly)) in HT0 by bnd.
  assert (RT : lib.Lib.Mem.bytes_at B.Img0.rsegs m (lib.Reusable.YG0f.ly_C ly + 152)
                 (lib.Lib.Mem.le8 (Z_to_bv 64 (lib.Reusable.YG0f.ly_T ly)))).
  { apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.AC 152) (lib.Reusable.YG0f.AT 0));
      [apply Hrow; inconst | reflexivity | cbn [lib.Reusable.YG0f.aeval]; lia | bnd | bnd]. }
  pose proof (le8_inj _ _ (bytes_at_uniq _ _ _ _ HT0 RT ltac:(rewrite !lib.Lib.Mem.length_le8; reflexivity))) as ET.
  subst T.
  (* TP + 8 holds DB = ly_D (YF0m row `c8 (ATp 8) (AD 0)`) *)
  assert (RDB : lib.Lib.Mem.bytes_at B.Img0.rsegs m (B.AsanRT.RT_TP + 8)
                  (lib.Lib.Mem.le8 (Z_to_bv 64 (lib.Reusable.YG0f.ly_D ly)))).
  { apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ATp 8) (lib.Reusable.YG0f.AD 0));
      [apply Hrow; inconst | cbn [lib.Reusable.YG0f.aeval]; rewrite Htp; reflexivity
       | cbn [lib.Reusable.YG0f.aeval]; lia | bnd | bnd]. }
  pose proof (le8_inj _ _ (bytes_at_uniq _ _ _ _ HDB0 RDB ltac:(rewrite !lib.Lib.Mem.length_le8; reflexivity))) as EDB.
  subst DB.
  (* 2. the class split *)
  unfold B.Prog.RcAsanFP.fp_tls.
  rewrite (B.ProgWorld_Fs.pw_u64 (B.AsanRT.RT_TP + 32)), (B.ProgWorld_Fs.pw_u64 B.AsanRT.RT_TSDMAIN),
          (B.ProgWorld_Fs.pw_u64 (lib.Reusable.YG0f.ly_C ly)), (B.ProgWorld_Fs.pw_u64 (lib.Reusable.YG0f.ly_T ly)),
          (B.ProgWorld_Fs.pw_u64 (lib.Reusable.YG0f.ly_D ly)) by bnd.
  apply (cls_fp_dj (lib.Reusable.YG0f.ly_F ly)).
  - repeat apply Forall_cons; try apply Forall_nil;
      first [ apply img_cls; [exact HGT | bnd]
            | apply (owned_cls _ (lib.Reusable.YG0f.ly_C ly) 256); [exact AC | lia | lia | lia]
            | apply (owned_cls _ (lib.Reusable.YG0f.ly_T ly) lib.Reusable.YG0f.kThreadObjSize);
                [exact AT | lia | lia | unfold lib.Reusable.YG0f.kThreadObjSize; lia]
            | apply (owned_cls _ (lib.Reusable.YG0f.ly_D ly) 4096); [exact AD | lia | lia | lia] ].
  - apply Forall_forall. intros d Hd. apply in_app_or in Hd as [Hd|Hd].
    + unfold B.Prog.RcAsanFP.fp_w in Hd. apply in_flat_map in Hd as (c & Hc & Hd).
      apply (fp_w1_cls _ c d); [exact (proj1 (Forall_forall _ _) Hcs c Hc) | lia | lia | exact Hd].
    + destruct Hd as [<-|[]]. unfold pd_cls; cbn [fst snd]. right.
      unfold lib.Reusable.YG0f.kHighMemBeg, lib.Reusable.YG0f.kHighMemEnd in HSH, HSL.
      split; [apply sh_lo | apply sh_hi]; lia.
Qed.

End TlsApart.

Print Assumptions fp_tls_apart.
