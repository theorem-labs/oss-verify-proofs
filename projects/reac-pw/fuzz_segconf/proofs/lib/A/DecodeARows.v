(* libreac/fuzz_decode image A (fuzz_decode.asan): proofs of premise rows of the closing composition
   lib/A/DecodeClose.v, the facts about the ASan runtime around calloc.  Each lemma below has the type of the
   DecodeClose.v hypothesis it names, at the composition's free symbol record B; a row that reads the image's
   start-up cells takes [GrantSyms B] (lib/A/AF0m.v) as the one named premise HA_TFIBSYMS.  The image-B twin is
   lib/B/DecodeBRows.v (dec_b_*, origin/cold/h-decbox-a7-rowsB 0c5218b14d0).

     dec_a_rt_unw    : H_CALLOC_RT_UNW    bridge from lib/A/AFl4.v tfib_unwind_ok
     dec_a_img_cover : H_CALLOC_IMG_COVER acall_pre -> AR -> ALedger -> lib/A/AF0x.v img_cover_of_ledger
     dec_a_cells     : H_CALLOC_CELLS     the start-up cells from ARm's const and thread cells (lib/A/AF0x.v
                                          tfib_const_lookup / tfib_const_lookup_sym, YG0n.v thread_cells)
     dec_a_img_const : H_CALLOC_IMG_CONST the three cells as rows of the record (ts_const, cell_lookup)
     dec_a_inst      : H_CALLOC_INST      as_inst B = DEC_A_instance (ts_inst)

   The image bounds: DecodeCallocRt.v's dec_img_cover is stated at lib/Reusable/YImgTop.v's IMG_LO / IMG_TOP and the
   core's img_cover (lib/A/AF0x.v) at TFIB_IMG_LO / TFIB_IMG_END; AF0x.v's TFIB_IMG_LO_eq / TFIB_IMG_END_eq make the
   two the same.  The segments are the same term: lib/A/DecodeTFIB.v decodesegs0 and lib/A/AB1v.v tfibsegs are both
   Asan.M.loaded_segments.  No Axiom, Parameter or Admitted. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK04 YM05 YI04 YO0d YA0n YG00 YG0f YG0n YG0d.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require CallocImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v DecodeCalloc DecodeCallocRt
DecodeCallocWrap.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import DecodeCallocKit.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AFl4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Local Abbreviation segs := tfibsegs.

(* The two image-cover predicates agree (YImgTop.v:26-29 against AF0x.v:29-31, :43-45). *)
Lemma dec_img_cover_iff : forall ly, dec_img_cover ly <-> img_cover ly.
Proof.
intros ly. unfold dec_img_cover, img_cover, CallocImgTop.IMG_LO, CallocImgTop.IMG_TOP, kImgLo, kImgEnd, TFIB_IMG_LO,
TFIB_IMG_END. tauto.
Qed.

(* ===================================================================================================== *)
(* Row H_CALLOC_RT_UNW (DecodeClose.v:271).  DecodeCallocRt.v's unwind_specP is cgif's tfib_unwind_spec premise
   for premise; at image A's parameters it is lib/A/AFl0.v tfib_unwind_spec up to the names of equal constants
   (DEC_A_UnwindImpl = A_UnwindImpl = 0x59e44, DEC_A_TP = TFIB_TP = 0x5d3d58, DEC_A_TSD = TFIB_TSD = 0x5f5100, the
   five cells 0xa1a98 / 0xa0620 / 0xa0624 / 0x98d20 / 0x130860, TSD_OFF = 88, UNW_STK = 144, BST_SIZE = 2064) and of
   the image cover (dec_img_cover_iff). *)
Lemma dec_a_rt_unw : forall (fx : YK11.FPState) (rc : YM05.RunCeil), decode_unwind_spec_A.
Proof.
intros fx rc. unfold decode_unwind_spec_A, unwind_specP.
intros W ly regs mem md this pc0 bp ra0 nfp0 ch. cbv zeta. intros LY IMG.
exact (@AFl4.tfib_unwind_ok _ _ W ly regs mem md this pc0 bp ra0 nfp0 ch LY (proj1 (dec_img_cover_iff ly) IMG)).
Qed.

Section rows.
(* The composition's symbol record (DecodeClose.v:117 Variable B). *)
Variable B : asyms.
(* The relocated core's symbol facts for B (lib/A/AF0m.v:399 GrantSyms). *)
Hypothesis HA_TFIBSYMS : SegBSyms B.

(* ===================================================================================================== *)
(* Row H_CALLOC_IMG_COVER (DecodeClose.v:265-266).  acall_pre starts with AR (YG0d.v:226-228), AR holds the
   ledger (YG0n.v:490-491), and the ledger covers the image (AF0x.v:63 img_cover_of_ledger). *)
Lemma dec_a_img_cover : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  forall ly S W regs mem md ch, acall_pre segs B ly S W regs mem md ch -> dec_img_cover ly.
Proof.
intros fx rc ly S W regs mem md ch (HAR & _). destruct HAR as (_ & HL & _).
apply (proj2 (dec_img_cover_iff ly)). exact (img_cover_of_ledger ly S md HL).
Qed.

(* ===================================================================================================== *)
(* Row H_CALLOC_CELLS (DecodeClose.v:273-274).  Every one of dec_cells_A's sixteen conjuncts is a cell ARm holds:
   - the literal cells are rows of Tfib_const_abs (lib/A/AF0m.v): z1 0xa1a98 1, z4 0xa1abc 0x1e, z1 0xa0620 1,
     z4 0xa0624 0, z8 0x98d20 0x130860, z8 0x130860 0x1000, z8 0x98d30 0x1328e8, and z8 0x132908 0x1e00010000,
     whose byte 2 is the fast-unwind byte 0x13290a = 1;
   - the thread cells are rows of Tfib_const_sym: c8 (ATp (-88)) (ATsd 0), c8 (ATsd 0) (AC 0), c8 (AC 152) (AT 0),
     z1 (AT 40) 0, c8 (AT 8) (ATop 0), c8 (AT 16) (ATop (- kStackSpan)), with as_tp B = TFIB_TP (ts_tp) and
     ly_tsd ly = as_tsd B = TFIB_TSD (am_tsd, ts_tsd);
   - the unwinding flag is YG0n.v:114 thread_cells, one of acells (am_cells), and the byte is off the image
     (the thread object lies in zone3, AF0x.v:74 zone3_intro), so a present byte. *)
Lemma dec_a_cells : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  forall ly S W regs mem md ch, acall_pre segs B ly S W regs mem md ch -> dec_cells_A ly W mem.
Proof.
intros fx rc ly S W regs mem md ch (HAR & _). destruct HAR as (M & HL & _).
pose proof (img_cover_of_ledger ly S md HL) as IMG.
pose proof (am_layout B ly S _ M) as LY.
assert (LIT : forall a (w : nat) v, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum v))) ->
  val_mem segs (mrestrict (w_H W) mem) a w v).
{ intros a w v E. exact (tfib_const_lookup B HA_TFIBSYMS ly S (w_H W) mem a w v M E). }
assert (SYM : forall e (w : nat) e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) ->
  val_mem segs (mrestrict (w_H W) mem) (aeval B ly e) w (aeval B ly e')).
{ intros e w e' E. exact (tfib_const_lookup_sym B HA_TFIBSYMS ly S (w_H W) mem e w e' M E). }
assert (UNW : val_mem segs (mrestrict (w_H W) mem) (ly_T ly + t_unwinding) 1 0).
{ replace (ly_T ly + t_unwinding) with (aeval B ly (AT t_unwinding)) by reflexivity.
  replace 0 with (aeval B ly (ANum 0)) by reflexivity.
  apply (cell_holds_val_mem B ly (w_H W) mem (AT t_unwinding) 1 (ANum 0)).
  apply (proj1 (Forall_forall _ _) (am_cells B ly S _ M)).
  unfold acells. do 8 (apply in_or_app; right). left. reflexivity. }
assert (TSD : ly_tsd ly = DEC_A_TSD) by (rewrite (am_tsd B ly S _ M), (ts_tsd B HA_TFIBSYMS); reflexivity).
unfold dec_cells_A. cbv zeta.
split; [apply LIT; vm_compute; reflexivity|].
split; [apply LIT; vm_compute; reflexivity|].
split; [apply LIT; vm_compute; reflexivity|].
split; [apply LIT; vm_compute; reflexivity|].
split.
{ pose proof (SYM (ATp (-88)) 8%nat (ATsd 0) ltac:(vm_compute; reflexivity)) as X. cbn [aeval] in X.
  rewrite (ts_tp B HA_TFIBSYMS), TSD, Z.add_0_r in X. exact X. }
split.
{ pose proof (SYM (ATsd 0) 8%nat (AC 0) ltac:(vm_compute; reflexivity)) as X. cbn [aeval] in X.
  rewrite TSD, !Z.add_0_r in X. exact X. }
split.
{ pose proof (SYM (AC 152) 8%nat (AT 0) ltac:(vm_compute; reflexivity)) as X. cbn [aeval] in X.
  rewrite Z.add_0_r in X. exact X. }
split.
{ exact (SYM (AT 40) 1%nat (ANum 0) ltac:(vm_compute; reflexivity)). }
split.
{ pose proof (SYM (AT 8) 8%nat (ATop 0) ltac:(vm_compute; reflexivity)) as X. cbn [aeval] in X.
  rewrite Z.add_0_r in X. exact X. }
split.
{ pose proof (SYM (AT 16) 8%nat (ATop (- kStackSpan)) ltac:(vm_compute; reflexivity)) as X. cbn [aeval] in X.
  rewrite Z.add_opp_r in X. exact X. }
split; [exact UNW|].
split.
{ assert (TZ : zone3 (ly_T ly) kThreadObjSize).
  { pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
    destruct HD as (_ & _ & D3 & _).
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail
      (Forall_inv_tail (Forall_inv_tail D3))))))) as X.
    assert (TH : in_app (ly_T ly) kThreadObjSize).
    { pose proof (lo_app ly LY) as HH. unfold owned_extents in HH. do 2 apply Forall_inv_tail in HH.
      apply Forall_inv in HH. exact HH. }
    exact (zone3_intro ly (ly_T ly) kThreadObjSize IMG ltac:(unfold kThreadObjSize; lia) TH X). }
  eapply mbyte_off_apresent.
  - apply (zone3_off_img _ _ _ TZ). unfold t_unwinding, kThreadObjSize. lia.
  - rewrite <- (Z.add_0_r (ly_T ly + t_unwinding)). exact (UNW 0%nat ltac:(lia)). }
split; [apply LIT; vm_compute; reflexivity|].
split; [apply LIT; vm_compute; reflexivity|].
split; [apply LIT; vm_compute; reflexivity|].
pose proof (LIT 0x13db48 8%nat 0x1e00010000 ltac:(vm_compute; reflexivity)) as X.
intros k Hk. destruct k as [|k]; [|lia].
replace (DEC_A_cf_fast + Z.of_nat 0) with (0x13db48 + Z.of_nat 2) by reflexivity.
rewrite (X 2%nat ltac:(lia)). reflexivity.
Qed.

(* ===================================================================================================== *)
(* Row H_CALLOC_IMG_CONST (DecodeClose.v:275-278, its third conjunct restated in the record's form
   `c8 (AInst o_space) (ASp 0)`, as DecodeCallocEntry.v / DecodeCallocTop.v state it).  The
   three cells are rows of Tfib_const (lib/A/AF0m.v): z8 (ANum 0x98d60) 0x9abc0 and z8 (ANum 0x9abc0) 0x92474 of
   Tfib_const_abs, c8 (AInst o_space) (ASp 0) of Tfib_const_sym; ts_const makes Tfib_const B's as_const, and each
   row is found by AF0x.v cell_lookup (cell_lookup_In). *)
Lemma dec_a_img_const : forall ly,
  In (z8 (ANum DEC_A_got_real_memset) DEC_A_real_memset) (as_const B ly) /\
  In (z8 (ANum DEC_A_real_memset) DEC_A_memset) (as_const B ly) /\
  In (c8 (AInst o_space) (ASp 0)) (as_const B ly).
Proof.
intros ly. rewrite (ts_const B HA_TFIBSYMS ly).
split; [|split].
- apply (cell_lookup_In _ (ANum DEC_A_got_real_memset)). vm_compute. reflexivity.
- apply (cell_lookup_In _ (ANum DEC_A_real_memset)). vm_compute. reflexivity.
- apply (cell_lookup_In _ (AInst o_space)). vm_compute. reflexivity.
Qed.

(* ===================================================================================================== *)
(* Row H_CALLOC_INST (the composition's new row beside DecodeClose.v:267 H_CALLOC_TP, the premise HINST of
   DecodeCallocEntry.v / DecodeCallocTop.v).  ts_inst gives as_inst B = TFIB_INST = 0x9d758, the
   address of __asan::instance (.symtab of the unstripped twin: _ZN6__asanL8instanceE 0x9d758, 3632 bytes, .bss),
   which asan_calloc forms at A 0x31c00 `auipc a0, 0x6c` + 0x31c08 `addi s2, a0, -1192`. *)
Lemma dec_a_inst : as_inst B = DEC_A_instance.
Proof. rewrite (ts_inst B HA_TFIBSYMS). reflexivity. Qed.

End rows.
