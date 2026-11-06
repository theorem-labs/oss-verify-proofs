(* libreac/fuzz_decode image B (fuzz_decode.asan-ubsan): proofs of six premise rows of the closing composition
   lib/B/DecodeBClose.v, the facts about the ASan runtime around calloc.  Each lemma below has the type of the
   DecodeBClose.v hypothesis it names, at the composition's free symbol record B; a row that reads the image's
   start-up cells takes [TfibSyms B] as the one named premise HB_TFIBSYMS.

     dec_b_rt_unw    : H_CALLOC_RT_UNW    bridge from lib/B/YFl4.v tfib_unwind_ok
     dec_b_img_cover : H_CALLOC_IMG_COVER acall_pre -> AR -> ALedger -> lib/B/YF0x.v img_cover_of_ledger
     dec_b_cells     : H_CALLOC_CELLS     the start-up cells from ARm's const and thread cells (lib/B/YF0x.v
                                          tfib_const_lookup / tfib_const_lookup_sym, YG0n.v thread_cells)

   The image bounds: DecodeCallocRt.v's dec_img_cover is stated at lib/Reusable/YImgTop.v's IMG_LO / IMG_TOP and the
   core's img_cover (lib/B/YF0x.v) at TFIB_IMG_LO / TFIB_IMG_END; YImgTop.v's IMG_LO_val / IMG_TOP_val make the
   two the same.  The segments are the same term: lib/A/DecodeTFIB.v decodesegsB0 and lib/B/YB1v.v tfibsegs are both
   AsanUbsan.M.loaded_segments.  No Axiom, Parameter or Admitted. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0s YK04 YM05 YI04 YO0d YA0n YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import DecodeCallocKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc DecodeCallocRt DecodeCallocWrapB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YB1v YF0m YF0x YFl0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require YFl4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Local Abbreviation segs := decodesegsB0.

(* The two image-cover predicates agree (YImgTop.v:32-35 against YF0x.v:25, :37). *)
Lemma dec_img_cover_iff : forall ly, dec_img_cover ly <-> img_cover ly.
Proof.
intros ly. unfold dec_img_cover, img_cover. rewrite YImgTop.IMG_LO_val, YImgTop.IMG_TOP_val.
unfold TFIB_IMG_LO, TFIB_IMG_END. tauto.
Qed.

(* ===================================================================================================== *)
(* Row H_CALLOC_RT_UNW (DecodeBClose.v:253).  DecodeCallocRt.v's unwind_specP is cgif's tfib_unwind_spec premise
   for premise; at image B's parameters it is lib/B/YFl0.v tfib_unwind_spec up to the names of equal constants
   (DEC_B_UnwindImpl = A_UnwindImpl = 0x59e90, DEC_B_TP = TFIB_TP = 0x5d42d8, DEC_B_TSD = TFIB_TSD = 0x5f5680, the
   five cells, TSD_OFF = 88, UNW_STK = 144, BST_SIZE = 2064) and of the image cover (dec_img_cover_iff). *)
Lemma dec_b_rt_unw : forall (fx : YK11.FPState) (rc : YM05.RunCeil), decode_unwind_spec_B.
Proof.
intros fx rc. unfold decode_unwind_spec_B, unwind_specP.
intros W ly regs mem md this pc0 bp ra0 nfp0 ch. cbv zeta. intros LY IMG.
exact (@YFl4.tfib_unwind_ok _ _ W ly regs mem md this pc0 bp ra0 nfp0 ch LY (proj1 (dec_img_cover_iff ly) IMG)).
Qed.

Section rows.
(* The composition's symbol record (DecodeBClose.v:111 Variable B). *)
Variable B : asyms.
(* The relocated core's symbol facts for B (lib/B/YF0m.v:321 TfibSyms), the composition's HB_TFIBSYMS. *)
Hypothesis HB_TFIBSYMS : TfibSyms B.

(* ===================================================================================================== *)
(* Row H_CALLOC_IMG_COVER (DecodeBClose.v:247-248).  acall_pre starts with AR (YG0d.v:226-228), AR holds the
   ledger (YG0n.v:490-491), and the ledger covers the image (YF0x.v:55 img_cover_of_ledger). *)
Lemma dec_b_img_cover : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  forall ly S W regs mem md ch, acall_pre segs B ly S W regs mem md ch -> dec_img_cover ly.
Proof.
intros fx rc ly S W regs mem md ch (HAR & _). destruct HAR as (_ & HL & _).
apply (proj2 (dec_img_cover_iff ly)). exact (img_cover_of_ledger ly S md HL).
Qed.

(* ===================================================================================================== *)
(* Row H_CALLOC_CELLS (DecodeBClose.v:255-256).  Every one of dec_cells_B's sixteen conjuncts is a cell ARm holds:
   - the literal cells are rows of Tfib_const_abs (lib/B/YF0m.v): z1 0xa2018 1, z4 0xa203c 0x1e, z1 0xa0ba0 1,
     z4 0xa0ba4 0, z8 0x992c8 0x130de0, z8 0x130de0 0x1000, z8 0x992d8 0x132e68, and z8 0x132e88 0x1e00010000,
     whose byte 2 is the fast-unwind byte 0x132e8a = 1;
   - the thread cells are rows of Tfib_const_sym: c8 (ATp (-88)) (ATsd 0), c8 (ATsd 0) (AC 0), c8 (AC 152) (AT 0),
     z1 (AT 40) 0, c8 (AT 8) (ATop 0), c8 (AT 16) (ATop (- kStackSpan)), with as_tp B = TFIB_TP (ts_tp) and
     ly_tsd ly = as_tsd B = TFIB_TSD (am_tsd, ts_tsd);
   - the unwinding flag is YG0n.v:114 thread_cells, one of acells (am_cells), and the byte is off the image
     (YFl4.v:91 unw_off), so a present byte. *)
Lemma dec_b_cells : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  forall ly S W regs mem md ch, acall_pre segs B ly S W regs mem md ch -> dec_cells_B ly W mem.
Proof.
intros fx rc ly S W regs mem md ch (HAR & _). destruct HAR as (M & HL & _).
pose proof (img_cover_of_ledger ly S md HL) as IMG.
pose proof (am_layout B ly S _ M) as LY.
assert (LIT : forall a (w : nat) v, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum v))) ->
  val_mem segs (mrestrict (w_H W) mem) a w v).
{ intros a w v E. exact (tfib_const_lookup B HB_TFIBSYMS ly S (w_H W) mem a w v M E). }
assert (SYM : forall e (w : nat) e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) ->
  val_mem segs (mrestrict (w_H W) mem) (aeval B ly e) w (aeval B ly e')).
{ intros e w e' E. exact (tfib_const_lookup_sym B HB_TFIBSYMS ly S (w_H W) mem e w e' M E). }
assert (UNW : val_mem segs (mrestrict (w_H W) mem) (ly_T ly + t_unwinding) 1 0).
{ replace (ly_T ly + t_unwinding) with (aeval B ly (AT t_unwinding)) by reflexivity.
  replace 0 with (aeval B ly (ANum 0)) by reflexivity.
  apply (cell_holds_val_mem B ly (w_H W) mem (AT t_unwinding) 1 (ANum 0)).
  apply (proj1 (Forall_forall _ _) (am_cells B ly S _ M)).
  unfold acells. do 8 (apply in_or_app; right). left. reflexivity. }
assert (TSD : ly_tsd ly = DEC_B_TSD) by (rewrite (am_tsd B ly S _ M), (ts_tsd B HB_TFIBSYMS); reflexivity).
unfold dec_cells_B. cbv zeta.
split; [apply LIT; vm_compute; reflexivity|].
split; [apply LIT; vm_compute; reflexivity|].
split; [apply LIT; vm_compute; reflexivity|].
split; [apply LIT; vm_compute; reflexivity|].
split.
{ pose proof (SYM (ATp (-88)) 8%nat (ATsd 0) ltac:(vm_compute; reflexivity)) as X. cbn [aeval] in X.
  rewrite (ts_tp B HB_TFIBSYMS), TSD, Z.add_0_r in X. exact X. }
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
pose proof (LIT 0x132e88 8%nat 0x1e00010000 ltac:(vm_compute; reflexivity)) as X.
intros k Hk. destruct k as [|k]; [|lia].
replace (DEC_B_cf_fast + Z.of_nat 0) with (0x132e88 + Z.of_nat 2) by reflexivity.
rewrite (X 2%nat ltac:(lia)). reflexivity.
Qed.

(* ===================================================================================================== *)
(* Support of the IMG_CONST restatement (a Theorem Labs lane's ruling 14:11Z; DecodeBClose.v H_CALLOC_IMG_CONST, now stated
   with the symbol record's `c8 (AInst o_space) (ASp 0)`).  With HB_TFIBSYMS the three cells are rows of Tfib_const
   (lib/B/YF0m.v): z8 (ANum 0x99308) 0x9b168, z8 (ANum 0x9b168) 0x92a1c and Tfib_const_sym's c8 (AInst o_space)
   (ASp 0).  Membership is by search (YF0x.v cell_lookup / cell_lookup_In), not by row index. *)
Lemma dec_b_img_const : forall ly,
  In (z8 (ANum DEC_B_got_real_memset) DEC_B_real_memset) (as_const B ly) /\
  In (z8 (ANum DEC_B_real_memset) DEC_B_memset) (as_const B ly) /\
  In (c8 (AInst o_space) (ASp 0)) (as_const B ly).
Proof.
intros ly. rewrite (ts_const B HB_TFIBSYMS ly). split; [|split].
- apply (cell_lookup_In (Tfib_const ly) (ANum DEC_B_got_real_memset)). vm_compute. reflexivity.
- apply (cell_lookup_In (Tfib_const ly) (ANum DEC_B_real_memset)). vm_compute. reflexivity.
- apply (cell_lookup_In (Tfib_const ly) (AInst o_space)). vm_compute. reflexivity.
Qed.

(* Row H_CALLOC_INST (DecodeBClose.v, beside H_CALLOC_TP): the record's instance address is the image's, by ts_inst
   (lib/B/YF0m.v TFIB_INST = 0x9dcd8 = lib/A/DecodeCalloc.v DEC_B_instance). *)
Lemma dec_b_inst : as_inst B = DEC_B_instance.
Proof. rewrite (ts_inst B HB_TFIBSYMS). reflexivity. Qed.

End rows.
