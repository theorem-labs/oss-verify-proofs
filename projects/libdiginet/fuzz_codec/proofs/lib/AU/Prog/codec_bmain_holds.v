(* The walk of fuzz_codec's entry function LLVMFuzzerTestOneInput at image B (fuzz_codec.asan-ubsan), closed: the
   segment lemmas of the codec_bmain_* files composed by codec_bmain_inv.v bmain_of_segments into the walk from the
   entry to the return, and the walk turned into the contract codec_lib_contract_x by bmain_contract_of_walk.

   The type of codec_bmain_holds is lib/AU/Prog/CPgCloseU.v codecU_bmain_T: Section w below is that file's Section T
   with codecU_bmain_T's binders (ROB after SK) and codecU_bmain_stmt's premises in their order, and the theorem
   takes all of them (Proof using All), so the closing takes it with `exact codec_bmain_holds`. It is not stated by
   that name because the closing requires this file. The callee entries are numerals there and the BM_ names of
   codec_bmain_inv.v in the segment lemmas; the two are convertible. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0s YK14 YK15 YK18 YP09 YI00 YI04 YI08 YI09 YI16 YN3v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG05 YG0q YG0t YCbp.
From OSSVerify.libdiginet.fuzz_codec.images Require AsanUbsan.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCeh YCfm YF0m YD2l.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Rt Require Import SetShadowDef.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import
CPgBaseU CPgEncU CPgChkU CodecRo CodecGlobs CPgWalkU CPgWalkRoU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require codec_bmain_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require
codec_bmain_entry codec_bmain_head codec_bmain_rda codec_bmain_rdb codec_bmain_rdx_12 codec_bmain_rdx_13
codec_bmain_rdx_14 codec_bmain_enc0 codec_bmain_enc1 codec_bmain_enc2 codec_bmain_enc3 codec_bmain_enc4
codec_bmain_enc5 codec_bmain_enc6 codec_bmain_enc7 codec_bmain_enc8 codec_bmain_enc9 codec_bmain_enc10
codec_bmain_enc11 codec_bmain_oweh codec_bmain_owe0 codec_bmain_owe1 codec_bmain_owe2 codec_bmain_owe3
codec_bmain_owe4 codec_bmain_owe5 codec_bmain_oweb_6 codec_bmain_oweb_7 codec_bmain_oweb_8 codec_bmain_oweb_9
codec_bmain_oweb_10 codec_bmain_oweb_11 codec_bmain_run codec_bmain_chk codec_bmain_latch codec_bmain_exit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* a kind of run() and owe() is one of 0 .. 11 *)
Lemma bm_kind12 : forall (P : Z -> Prop),
  P 0 -> P 1 -> P 2 -> P 3 -> P 4 -> P 5 -> P 6 -> P 7 -> P 8 -> P 9 -> P 10 -> P 11 ->
  forall kind, 0 <= kind <= 11 -> P kind.
Proof.
intros P H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 kind Hk.
rewrite <- (Z2Nat.id kind) by lia.
assert (Hn : (Z.to_nat kind < 12)%nat) by lia.
destruct (Z.to_nat kind) as [|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]; try assumption.
lia.
Qed.

(* codecU_bmain_T's binders: the instances, the image's symbols, the meter, the sink, the two library bounds; then
   codecU_bmain_stmt's premises *)
Section w.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : @ro_tfa_below_ofl SK}.
Context {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variables XM_LIB XN_LIB : Z -> Z.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AIL : asink_img_laws tfibsegs B K.
Hypothesis HXN : forall n, 0 <= XN_LIB n.
Hypothesis LEAF : forall pl fs (Kl : lleaf -> TSet), LIBK pl fs Kl = Kl (LL 0 fs []).
Hypothesis ASM3 : astack_malloc_realizes tfibsegs B 3.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet 0x51f84.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy 0x51ae8.
Hypothesis ASSF5 : aset_shadow_realizes tfibsegs B 0x54ab0 0xf5.
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis IV : img_shadow_vis tfibsegs B.
Hypothesis RF : cpw_rows_free B CB_ROSTRS.
Hypothesis CPERS : cdcU_check_pers_specX tfibsegs B MT CB_RLO CB_RHI CB_PERS CB_ROSTRS 0x8391c.
Hypothesis POF : cdcU_pers_of_specX tfibsegs B MT 0x8513c CB_PERS.
Hypothesis CTA : cdcU_text_arg_specX tfibsegs B MT 0x83ba0.
Hypothesis CS7 : cdcU_check_seg7_specX tfibsegs B MT CB_RLO CB_RHI CB_SEG7 CB_GLYPH CB_ROSTRS 0x84148.
Hypothesis CTC : cdcU_check_text_counter_specX tfibsegs B MT CB_RLO CB_RHI CB_SEG7 CB_GLYPH CB_ROSTRS 0x841c4.
Hypothesis COC : cdcU_owed_counter_text_specX tfibsegs B MT CB_RLO CB_RHI CB_GLYPH CB_ROSTRS 0x84474.
Hypothesis CTS : cdcU_check_text_scribble_specX tfibsegs B MT 0x83dbc.
Hypothesis CMASKS : cdcU_check_masks_specX tfibsegs B MT 0x84974.
Hypothesis ACR : cdcU_check_refusal_specX tfibsegs B MT 0x84bc4.
Hypothesis ACG : cdcU_check_range_specX tfibsegs B MT 0x84c84.
Hypothesis ACB : cdcU_check_bytes_specX tfibsegs B MT 0x84d40.
Hypothesis FADER : cdcU_fader_specX tfibsegs B MT 0x8540c.
Hypothesis BUTTON : cdcU_button_specX tfibsegs B MT 0x855dc.
Hypothesis TOUCH : cdcU_touch_specX tfibsegs B MT 0x85744.
Hypothesis VPOT : cdcU_vpot_specX tfibsegs B MT 0x85914.
Hypothesis JOG : cdcU_jog_specX tfibsegs B MT 0x85a8c.
Hypothesis SYSEX : cdcU_sysex_specX tfibsegs B MT 0x85174.
Hypothesis RING : cdcU_ring_specX tfibsegs B MT 0x85c1c.
Hypothesis METER : cdcU_meter_specX tfibsegs B MT 0x85f4c.
Hypothesis SLEDS : cdcU_sleds_specX tfibsegs B MT 0x861d0.
Hypothesis CLEDS : cdcU_cleds_specX tfibsegs B MT 0x8648c.
Hypothesis SCRIBBLE : cdcU_scribble_specX tfibsegs B MT 0x866c4.
Hypothesis COUNTER : cdcU_counter_specX tfibsegs B MT 0x86ee4.
Hypothesis OSX : cdcU_owe_sysex_specX tfibsegs B MT 0x84e8c.

(* RD0 .. RD11 *)
Lemma bm_rd_run_all : forall kind, 0 <= kind <= 11 -> codec_bmain_inv.seg_rd_run B MT K XM_LIB kind.
Proof.
intros kind Hk. destruct (Z_le_gt_dec kind 5) as [H5 | H5].
- exact (codec_bmain_rda.seg_rd_run_0_5 B MT K XM_LIB TL LAWS kind ltac:(lia)).
- exact (codec_bmain_rdb.seg_rdb_holds B MT K XM_LIB TL LAWS AMEMCPY kind ltac:(lia)).
Qed.

(* ENC0 .. ENC11 *)
Lemma bm_enc_all : forall kind, 0 <= kind <= 11 -> codec_bmain_inv.seg_enc B MT K XM_LIB kind.
Proof.
apply bm_kind12.
- exact (codec_bmain_enc0.seg_enc0_holds B MT K XM_LIB MTL TL LAWS GM IV FADER).
- exact (codec_bmain_enc1.seg_enc1_holds B MT K XM_LIB MTL TL LAWS BUTTON).
- exact (codec_bmain_enc2.seg_enc2_holds B MT K XM_LIB MTL TL LAWS GM IV TOUCH).
- exact (codec_bmain_enc3.seg_enc3_holds B MT K XM_LIB MTL TL LAWS GM IV VPOT).
- exact (codec_bmain_enc4.seg_enc4_holds B MT K XM_LIB MTL TL LAWS JOG).
- exact (codec_bmain_enc5.seg_enc5_holds B MT K XM_LIB MTL TL LAWS GM IV RING).
- exact (codec_bmain_enc6.seg_enc6_holds B MT K XM_LIB MTL TL LAWS GM IV METER).
- exact (codec_bmain_enc7.seg_enc7_holds B MT K XM_LIB MTL TL LAWS GM IV SLEDS).
- exact (codec_bmain_enc8.seg_enc8_holds B MT K XM_LIB MTL TL LAWS GM IV CLEDS).
- exact (codec_bmain_enc9.seg_enc9_holds B MT K XM_LIB MTL TL LAWS GM IV SCRIBBLE).
- exact (codec_bmain_enc10.seg_enc10_holds B MT K XM_LIB MTL TL LAWS GM IV COUNTER).
- exact (codec_bmain_enc11.seg_enc11_holds B MT K XM_LIB MTL TL LAWS SYSEX).
Qed.

(* OWE0 .. OWE11 *)
Lemma bm_owe_all : forall kind, 0 <= kind <= 11 -> codec_bmain_inv.seg_owe B MT K XM_LIB kind.
Proof.
apply bm_kind12.
- exact (codec_bmain_owe0.seg_owe0_holds B MT K XM_LIB TL LAWS GM IV).
- exact (codec_bmain_owe1.seg_owe1_holds B MT K XM_LIB TL LAWS).
- exact (codec_bmain_owe2.seg_owe2_holds B MT K XM_LIB TL LAWS GM IV).
- exact (codec_bmain_owe3.seg_owe3_holds B MT K XM_LIB TL LAWS GM IV).
- exact (codec_bmain_owe4.seg_owe4_holds B MT K XM_LIB TL LAWS).
- exact (codec_bmain_owe5.seg_owe5_holds B MT K XM_LIB TL LAWS GM IV AMEMCPY).
- exact (codec_bmain_oweb_6.seg_owe6_holds B MT K XM_LIB TL LAWS GM IV).
- exact (codec_bmain_oweb_7.seg_owe7_holds B MT K XM_LIB TL LAWS GM IV).
- exact (codec_bmain_oweb_8.seg_owe8_holds B MT K XM_LIB TL LAWS GM IV).
- exact (codec_bmain_oweb_9.seg_owe9_holds B MT K XM_LIB TL LAWS MTL AMEMCPY OSX GM IV).
- exact (codec_bmain_oweb_10.seg_owe10_holds B MT K XM_LIB TL LAWS AMEMCPY GM IV).
- exact (codec_bmain_oweb_11.seg_owe11_holds B MT K XM_LIB TL LAWS MTL OSX).
Qed.

(* the walk from the entry to the return *)
Lemma bm_walk : forall g W2 c2, codec_bmain_inv.inv_entry g W2 c2 -> codec_bmain_inv.e_pre B MT K XM_LIB g ->
  SRr tfibsegs W2 c2 (codec_bmain_inv.inv_retj B MT g).
Proof.
exact (codec_bmain_inv.bmain_of_segments B MT K XM_LIB
  (codec_bmain_entry.seg_entry_holds B MT K XM_LIB MTL MTF TL LAWS ML FFL GM IV RF CPERS ASM3 SMP)
  (codec_bmain_head.seg_head_holds B MT K XM_LIB MTL TL LAWS ML AMEMSET GM POF)
  bm_rd_run_all
  (codec_bmain_rdx_12.seg_rd12_holds B MT K XM_LIB MTL TL LAWS GM IV CTA CTS)
  (codec_bmain_rdx_13.seg_rd13_holds B MT K XM_LIB MTL TL LAWS GM IV RF CTA CS7 CTC COC)
  (codec_bmain_rdx_14.seg_rd14_holds B MT K XM_LIB MTL TL LAWS CMASKS)
  (codec_bmain_run.seg_run_holds B MT K XM_LIB TL LAWS ML)
  bm_enc_all
  (codec_bmain_oweh.seg_oweh_holds B MT K XM_LIB TL LAWS AMEMSET)
  bm_owe_all
  (codec_bmain_chk.seg_chk_holds B MT K XM_LIB MTL TL LAWS ACR ACG ACB)
  (codec_bmain_latch.seg_latch_holds B MT K XM_LIB TL LAWS ML)
  (codec_bmain_exit.seg_exit_holds B MT K XM_LIB MTF TL LAWS ML ASF FFL ASSF5)).
Qed.

Theorem codec_bmain_holds :
  codec_lib_contract_x tfibsegs B MT K XM_LIB XN_LIB CB_RLO CB_RHI A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof using All.
exact (codec_bmain_inv.bmain_contract_of_walk B MT K XM_LIB XN_LIB MTL AIL HXN LEAF bm_walk).
Qed.
End w.
Arguments codec_bmain_holds : clear implicits.

