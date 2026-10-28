(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK04 YG00 YG0a YG01 YG05 YG0f YG0n YG0s YG0t YG0q YG0d YCbq YC5d YCbp.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20 YC7y YC7x YC21.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m AF0l ACej AD2l ACeh ACei AF0u AE2r AE2q ACex ACey ACf5 ACfh ACfk ACfj ACfn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YE02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require AE2o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Lemma tfib_lib_consts_chk :
forallb (fun r => ((fst r + snd r <=? 0x103b0) || (0x103b8 <=? fst r)) && ((fst r + snd r <=? 0x9ec10) || (0x9ec28 <=? fst r)))%bool
Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.
Theorem TfibB_libS : TfibLib TfibB.
Proof.
constructor; try reflexivity.
-   cbn [as_errno TfibB]. unfold TFIB_ERRNO, kLowMemEnd. lia.
-
intros a Ha. cbn [as_errno TfibB] in Ha. unfold TFIB_ERRNO in Ha. unfold in_img.
assert (Hb : nth_error (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs) 3 = Some (0x9f000, 0x55c000))
by (vm_compute; reflexivity).
rewrite nth_error_map in Hb. destruct (nth_error tfibsegs 3) as [sg|] eqn:E; [|discriminate Hb]. cbn in Hb. injection Hb as H1 H2.
exists sg. split; [exact (nth_error_In _ 3 E) | rewrite H1, H2; lia].
-   intros a Ha. cbn [as_owned_static as_errno TfibB]. unfold TFIB_ERRNO. unfold lib_const_addr in Ha. split; [|lia].
intros HE. apply Exists_exists in HE as (r & Hr & [H1 H2]).
pose proof (proj1 (forallb_forall _ _) tfib_lib_consts_chk r Hr) as Hb. cbn beta in Hb.
apply andb_prop in Hb as [Hb1 Hb2]. apply Bool.orb_prop in Hb1 as [Hb1|Hb1]; apply Z.leb_le in Hb1;
apply Bool.orb_prop in Hb2 as [Hb2|Hb2]; apply Z.leb_le in Hb2; lia.
-   cbn [as_gp TfibB]. unfold TFIB_GP. lia.
Qed.
Lemma tfib_ro_segs_chk :
forallb (fun s : Segment => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? A_ofl_head))%bool tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.
#[export] Instance tfib_ROB : @ro_tfa_below_ofl tfib_sink_head.
Proof.
intros a [(s & Hin & Hw & Hr) | Hr]; cbn [YI16.sk_ofl_head tfib_sink_head].
- pose proof (proj1 (forallb_forall _ _) tfib_ro_segs_chk s Hin) as Hb. cbn beta in Hb. rewrite Hw in Hb. cbn [orb] in Hb.
apply Z.leb_le in Hb. lia.
- unfold A_ofl_head. lia.
Qed.
Lemma tfib_HRO : forall (B : asyms) rd, arodata_ok B rd -> arodata_okP tfibsegs 0x9da38 0x9eca8 B rd.
Proof. intros B rd H a Ha. exact (H a Ha). Qed.
Definition XN0 : xnums :=
mkXN (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0).
Definition XL0 : Z -> Z := fun _ => 0.
Lemma XN0_newgif_pos : forall n, 0 <= n -> 0 <= xm_newgif XN0 n. Proof. intros; cbn; lia. Qed.
Lemma XN0_newgif_le : forall n, 0 <= n -> 0 <= xn_newgif XN0 n <= xm_newgif XN0 n. Proof. intros; cbn; lia. Qed.
Lemma XN0_addframe_le : forall n, 0 <= n -> 0 <= xn_addframe XN0 n <= xm_addframe XN0 n. Proof. intros; cbn; lia. Qed.
Lemma XN0_close_le : forall n, 0 <= n -> 0 <= xn_close XN0 n <= xm_close XN0 n. Proof. intros; cbn; lia. Qed.
Lemma XL0_HXL : forall n ngp, 0 <= ngp < 2 ^ 16 -> RT_NEED1 ameter_triv + xm_newgif XN0 ngp + mo_free ameter_triv <= XL0 n.
Proof. intros. unfold RT_NEED1, ACC_pal, XL0. cbn. lia. Qed.
Lemma XL0_HXL2 : forall n ngp N, 0 <= ngp < 2 ^ 16 -> 1 <= N <= 100000000 ->
RT_NEED1 ameter_triv + xn_newgif XN0 ngp + mo_free ameter_triv + 15 * (RFC_COST ameter_triv N + xn_addframe XN0 N + (mo_free ameter_triv + mo_free ameter_triv)) + RFC_COST ameter_triv N + xm_addframe XN0 N <= XL0 n /\
RT_NEED1 ameter_triv + xn_newgif XN0 ngp + mo_free ameter_triv + 16 * (RFC_COST ameter_triv N + xn_addframe XN0 N + (mo_free ameter_triv + mo_free ameter_triv)) + RFC_COST ameter_triv N + xm_close XN0 N <= XL0 n.
Proof. intros. unfold RT_NEED1, ACC_pal, RFC_COST, XL0. cbn. lia. Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Lemma link_ML : model_laws (as_universe B).
Proof. exact (model_laws_ok (as_universe B) (ts_universe B HB)). Qed.
Lemma link_SMP : stack_malloc_progressP B.
Proof. intros s cid W Hc Hn. exact (stack_malloc_progress (as_universe B) s cid W Hc Hn). Qed.
Lemma link_FFL : frame_flag_lawP tfibsegs B.
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (tfib_img_cover ly S md L) as [C1 C2]. unfold TFIB_IMG_LO, TFIB_IMG_END in C1, C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma link_ASF : astack_free_law tfibsegs B.
Proof. exact (astack_free_law_ok tfibsegs B). Qed.
Lemma link_ASM2 : astack_malloc_realizes tfibsegs B 2.
Proof. exact (stack_malloc2_contract B LAWS HB). Qed.
Lemma link_AMEMSET : aintrin_realizes tfibsegs B OSet ACep.A_asan_memset.
Proof.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
exact (asan_memset_realizes B LAWS HB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.
Lemma link_AMEMCPY : aintrin_realizes tfibsegs B OCpy ACep.A_asan_memcpy.
Proof.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc.
exact (asan_memcpy_realizes B LAWS HB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc).
Qed.
End c.
Section e.
Let B : asyms := TfibB.
Let HB : TfibSyms B := TfibB_syms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Hypothesis AMALLOC : amalloc_realizes tfibsegs B.
Hypothesis AFREE : afree_realizes tfibsegs B.
Hypothesis AIL : asink_img_laws tfibsegs B tfib_K.
Let AUNLINKX : aunlink_x tfibsegs B tfib_K 0x9c9cc := AE2o.tfib_aunlink_x B LAWS HB AIL.
Variable wfn : Z.
Hypothesis TNEWGIFX : tnewgif_x tfibsegs tfib_K B ameter_triv XN0 A_cgif_newgif CTX_cgif_newgif wfn 0x9da38 0x9eca8.
Hypothesis TADDFX : taddframe_specX tfibsegs tfib_K B ameter_triv XN0 A_cgif_addframe CTX_cgif_addframe wfn 0x9da38 0x9eca8.
Hypothesis TCLOSEX : tclose_specX tfibsegs tfib_K B ameter_triv XN0 A_cgif_close CTX_cgif_close wfn 0x9da38 0x9eca8.
Theorem tfib_lib_x_closed : tfib_lib_contract_x B ameter_triv XL0 XL0 0x9da38 0x9eca8.
Proof.
pose proof (tl_env B TfibB_libS) as errno_low.
exact (tfib_lib_x B ameter_triv (ameter_triv_laws) TfibB_libS LAWS (link_ML B HB) (link_ASM2 B HB) (link_SMP B) (link_ASF B) (link_FFL B)
(ameter_triv_fs_laws) (link_AMEMSET B HB) (link_AMEMCPY B HB)
(amalloc04_rule_triv tfibsegs B tfib_segs_low errno_low LAWS (link_ML B HB) AMALLOC)
(afree04_rule_triv tfibsegs B tfib_segs_low errno_low LAWS (link_ML B HB) AFREE)
(afree_null04_rule_triv tfibsegs B tfib_segs_low errno_low LAWS (link_ML B HB) AFREE)
AIL XN0 XL0 wfn 0x9da38 0x9eca8 TNEWGIFX AUNLINKX XN0_newgif_pos XN0_newgif_le (tfib_HRO B) TADDFX TCLOSEX XN0_addframe_le XN0_close_le
XL0_HXL XL0_HXL2).
Qed.
End e.
End b.
Section f. Context {rc : YM05.RunCeil}.
Hypothesis AMALLOC : forall fx : YK11.FPState, @amalloc_realizes fx rc tfibsegs TfibB.
Hypothesis AFREE : forall fx : YK11.FPState, @afree_realizes fx rc tfibsegs TfibB.
Hypothesis AIL : asink_img_laws tfibsegs TfibB tfib_K.
Variable wfn : Z.
Hypothesis TNEWGIFX : forall fx : YK11.FPState,
@tnewgif_x fx rc tfib_sink_head tfibsegs tfib_K TfibB ameter_triv XN0 A_cgif_newgif CTX_cgif_newgif wfn 0x9da38 0x9eca8.
Hypothesis TADDFX : forall fx : YK11.FPState,
@taddframe_specX fx rc tfib_sink_head tfibsegs tfib_K TfibB ameter_triv XN0 A_cgif_addframe CTX_cgif_addframe wfn 0x9da38 0x9eca8.
Hypothesis TCLOSEX : forall fx : YK11.FPState,
@tclose_specX fx rc tfib_sink_head tfibsegs tfib_K TfibB ameter_triv XN0 A_cgif_close CTX_cgif_close wfn 0x9da38 0x9eca8.
Theorem tfib_lib_x_all : tfib_lib_contract_x_all TfibB ameter_triv XL0 XL0 0x9da38 0x9eca8.
Proof. intros fx. exact (tfib_lib_x_closed (AMALLOC fx) (AFREE fx) AIL wfn (TNEWGIFX fx) (TADDFX fx) (TCLOSEX fx)). Qed.
End f.
