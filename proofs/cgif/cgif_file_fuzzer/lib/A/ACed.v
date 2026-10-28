(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YP0b YK04 YG00 YG0a YG01 YG05 YG0f YG0n YG0s YG0t YG0q YG0d YCbq YC5d YCbp.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC7y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0m AF0l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YF0p.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACej AD2l ACeh.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AF0s AF0u AE2r AE2q AE2z AE2s AF0w AF0q AD1u.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0w YI0x YI0y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AI12.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC1f YC20 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition XN0 : xnums :=
mkXN (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0).
Ltac xn0_tac := intros; cbn; lia.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Remark tfibX_segs0 : @pa_segs _ _ PB_tfib = tfibsegs.   Proof. reflexivity. Qed.
Remark tfibX_segs1 : @pa_segs _ _ PB_tfib1 = tfibsegs.   Proof. reflexivity. Qed.
Remark tfibX_relro0 : (@pa_relro_lo _ _ PB_tfib, @pa_relro_hi _ _ PB_tfib) = (0x9da38, 0x9eca8).   Proof. reflexivity. Qed.
Remark tfibX_relro1 : (@pa_relro_lo _ _ PB_tfib1, @pa_relro_hi _ _ PB_tfib1) = (0x9da38, 0x9eca8).   Proof. reflexivity. Qed.
Remark tfibX_base0 : @pa_val _ _ PB_tfib A_TEXT = 0x81404.   Proof. reflexivity. Qed.
Lemma tfibX_lib_consts_chk :
forallb (fun r => ((fst r + snd r <=? 0x103b0) || (0x103b8 <=? fst r)) && ((fst r + snd r <=? 0x9ec10) || (0x9ec28 <=? fst r)))%bool
Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.
Theorem tfibX_lib : TfibLib TfibB.
Proof.
constructor; try reflexivity.
- cbn [as_errno TfibB]. unfold TFIB_ERRNO, kLowMemEnd. lia.
- intros a Ha. cbn [as_errno TfibB] in Ha. unfold TFIB_ERRNO in Ha. unfold in_img.
assert (Hb : nth_error (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs) 3 = Some (0x9f000, 0x55c000))
by (vm_compute; reflexivity).
rewrite nth_error_map in Hb. destruct (nth_error tfibsegs 3) as [sg|] eqn:E; [|discriminate Hb]. cbn in Hb. injection Hb as H1 H2.
exists sg. split; [exact (nth_error_In _ 3 E) | rewrite H1, H2; lia].
- intros a Ha. cbn [as_owned_static as_errno TfibB]. unfold TFIB_ERRNO. unfold lib_const_addr in Ha. split; [|lia].
intros HE. apply Exists_exists in HE as (r & Hr & [H1 H2]).
pose proof (proj1 (forallb_forall _ _) tfibX_lib_consts_chk r Hr) as Hb. cbn beta in Hb.
apply andb_prop in Hb as [Hb1 Hb2]. apply Bool.orb_prop in Hb1 as [Hb1|Hb1]; apply Z.leb_le in Hb1;
apply Bool.orb_prop in Hb2 as [Hb2|Hb2]; apply Z.leb_le in Hb2; lia.
- cbn [as_gp TfibB]. unfold TFIB_GP. lia.
Qed.
Lemma tfibX_ro_segs_chk :
forallb (fun s : Segment => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? A_ofl_head))%bool tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tfibX_ro_below : forall a, in_roP tfibsegs 0x9da38 0x9eca8 a -> a < A_ofl_head.
Proof.
intros a [(s & Hin & Hw & Hr) | Hr].
- pose proof (proj1 (forallb_forall _ _) tfibX_ro_segs_chk s Hin) as Hb. cbn beta in Hb. rewrite Hw in Hb. cbn [orb] in Hb.
apply Z.leb_le in Hb. lia.
- unfold A_ofl_head. lia.
Qed.
#[export] Instance tfibX_RO0 : @YC20.ro_below_ofl (@pa_segs _ _ PB_tfib) (@pa_relro_lo _ _ PB_tfib) (@pa_relro_hi _ _ PB_tfib) tfib_sink_head.
Proof. intros a Ha. exact (tfibX_ro_below a Ha). Qed.
#[export] Instance tfibX_RO1 : @YC20.ro_below_ofl (@pa_segs _ _ PB_tfib1) (@pa_relro_lo _ _ PB_tfib1) (@pa_relro_hi _ _ PB_tfib1) tfib_sink_head.
Proof. intros a Ha. exact (tfibX_ro_below a Ha). Qed.
#[local] Abbreviation B := TfibB.
#[local] Abbreviation HB := TfibB_syms.
Let HD : forall t, as_dhash B t = tfib_dhash t := fun t => eq_refl.
Definition tfibX_LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Lemma tfibX_ML : model_laws (as_universe B).
Proof. exact (model_laws_ok (as_universe B) (ts_universe B HB)). Qed.
Definition tfibX_env : api_env tfibsegs B := tl_env B tfibX_lib.
Lemma tfibX_PALib0 : PALib (PI := PB_tfib) B.
Proof.
constructor.
- reflexivity.
- reflexivity.
- left. vm_compute. discriminate.
- exact tfibX_env.
- reflexivity.
- reflexivity.
- vm_compute. split; reflexivity.
Qed.
Lemma tfibX_PALib1 : PALib (PI := PB_tfib1) B.
Proof.
constructor.
- reflexivity.
- reflexivity.
- left. vm_compute. discriminate.
- exact tfibX_env.
- reflexivity.
- reflexivity.
- vm_compute. split; reflexivity.
Qed.
Definition tfibX_AIL : asink_img_laws tfibsegs B tfib_K := tfib_AIL B HB.
Definition tfibX_AMALLOC : amalloc_realizes tfibsegs B := tfib_amalloc_realizes B HB HD.
Definition tfibX_AFREE : afree_realizes tfibsegs B := afree_realizes_closed B HB HD.
Definition tfibX_AMALLOC4 : amalloc04_rule tfibsegs B ameter_triv := amalloc04_rule_triv tfibsegs B tfib_segs_low tfibX_env tfibX_LAWS tfibX_ML tfibX_AMALLOC.
Definition tfibX_AFREE4 : afree04_rule tfibsegs B ameter_triv := afree04_rule_triv tfibsegs B tfib_segs_low tfibX_env tfibX_LAWS tfibX_ML tfibX_AFREE.
Definition tfibX_AFREEN4 : afree_null04_rule tfibsegs B ameter_triv := afree_null04_rule_triv tfibsegs B tfib_segs_low tfibX_env tfibX_LAWS tfibX_ML tfibX_AFREE.
Lemma tfibX_PALibF0 : PALibF (PI := PB_tfib) B.
Proof.
constructor.
- reflexivity.
- vm_compute. split; intros X; discriminate X.
- reflexivity.
- reflexivity.
- reflexivity.
- vm_compute. repeat split; first [ discriminate | left; discriminate | right; discriminate ].
Qed.
Lemma tfibX_PALibF1 : PALibF (PI := PB_tfib1) B.
Proof.
constructor.
- reflexivity.
- vm_compute. split; intros X; discriminate X.
- reflexivity.
- reflexivity.
- reflexivity.
- vm_compute. repeat split; first [ discriminate | left; discriminate | right; discriminate ].
Qed.
Lemma tfibX_ASM1 : astack_malloc_realizes tfibsegs B 1.
Proof. exact (AF0s.stack_malloc1_contract B tfibX_LAWS HB). Qed.
Lemma tfibX_ASM2 : astack_malloc_realizes tfibsegs B 2.
Proof. exact (AF0u.stack_malloc2_contract B tfibX_LAWS HB). Qed.
Lemma tfibX_SMP : stack_malloc_progressP B.
Proof. intros s cid W Hc Hn. exact (stack_malloc_progress (as_universe B) s cid W Hc Hn). Qed.
Lemma tfibX_ASF : astack_free_law tfibsegs B.
Proof. exact (astack_free_law_ok tfibsegs B). Qed.
Lemma tfibX_FFL : frame_flag_lawP tfibsegs B.
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ tfibX_LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ tfibX_LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (tfib_img_cover ly S md L) as [C1 C2]. unfold TFIB_IMG_LO, TFIB_IMG_END in C1, C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma tfibX_AMEMSET : aintrin_realizes tfibsegs B OSet (@pa_sigma _ _ PB_tfib AS_asan_memset).
Proof.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
exact (asan_memset_realizes B tfibX_LAWS HB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.
Lemma tfibX_AMEMCPY : aintrin_realizes tfibsegs B OCpy (@pa_sigma _ _ PB_tfib AS_asan_memcpy).
Proof.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc.
exact (asan_memcpy_realizes B tfibX_LAWS HB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc).
Qed.
Remark tfibX_sigma1 : forall s, @pa_sigma _ _ PB_tfib1 s = @pa_sigma _ _ PB_tfib s.   Proof. reflexivity. Qed.
Lemma tfibX_AMEMCMP : amemcmp_realizes tfibsegs B (@pa_sigma _ _ PB_tfib AS_memcmp).
Proof. exact (memcmp_icpt_contract B tfibX_LAWS HB). Qed.
Lemma tfibX_ABCMP : abcmp_realizes tfibsegs B (@pa_sigma _ _ PB_tfib AS_memcmp_2).
Proof. exact (bcmp_icpt_contract B tfibX_LAWS HB). Qed.
End b.
Ltac tfibX_universe_in :=
apply memZL_In; vm_compute; reflexivity.
Ltac tfibX_universe :=
let t := fresh "t" in let Ht := fresh "Ht" in
intros t Ht; cbv [In] in Ht;
repeat (destruct Ht as [<- | Ht]; [tfibX_universe_in|]); destruct Ht.
