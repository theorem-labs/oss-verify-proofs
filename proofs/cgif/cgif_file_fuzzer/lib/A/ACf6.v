(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z YI5s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej ACeh ACem ACek ACei ACep.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCeo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACel ACer ACfm ACf5 ACf9.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition CGB : Z := 96 + 48 + 3 * 65536 + 3 * (40 + 100000000 + 3 * 65536).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Lemma cgif_blocks_in_g : forall g s N, In (g, CGIF_SIZE) (cgif_blocks g s N).
Proof. intros. left. reflexivity. Qed.
Lemma cgif_blocks_in_raw : forall g s N, In (cg_raw s, RAW_SIZE) (cgif_blocks g s N).
Proof. intros. right. left. reflexivity. Qed.
Lemma frames_blocks_in : forall N fs f, In (Some f) fs -> In (fr_ptr f, FRAME_SIZE) (frames_blocks N fs).
Proof.
intros N fs f. induction fs as [|o fs IH]; intros H; [destruct H|].
destruct H as [-> | H]; cbn; [left; reflexivity|].
apply in_app_iff. right. apply IH. exact H.
Qed.
Lemma cgif_blocks_in_frame : forall g s N f, In (Some f) (cg_frames s) -> In (fr_ptr f, FRAME_SIZE) (cgif_blocks g s N).
Proof. intros g s N f H. right. right. apply in_app_iff. right. apply frames_blocks_in. exact H. Qed.
Lemma tcgif_at_blocks_kept : forall (H H' : word -> bool) (m m' : word -> option byte) g s N,
tcgif_at (mrestrict H m) g s ->
(forall b sz, In (b, sz) (cgif_blocks g s N) -> blk_kept H H' m m' b (req_size sz)) ->
tcgif_at (mrestrict H' m') g s.
Proof.
intros H H' m m' g s N Hat K.
apply (tcgif_at_kept H H' m m' g s Hat).
- exact (K g CGIF_SIZE (cgif_blocks_in_g g s N)).
- exact (K (cg_raw s) RAW_SIZE (cgif_blocks_in_raw g s N)).
- intros f Hf. exact (K (fr_ptr f) FRAME_SIZE (cgif_blocks_in_frame g s N f Hf)).
Qed.
Lemma rt_region_kept_eq : forall E (H H2 : word -> bool) (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview tfibsegs H2 m2 a = aview tfibsegs H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept tfibsegs E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview tfibsegs). apply Hav. exact Ha.
- intros _. apply (apresent_writable tfibsegs). apply Hp. exact Ha.
Qed.
Lemma blk_kept_frame : forall E rs (H : word -> bool) (m m' : word -> option byte) b n,
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall a, b <= a < b + n -> 0 <= a < 2 ^ 64 /\ ~ in_wrange E rs a) ->
blk_kept H H m m' b n.
Proof.
intros E rs H m m' b n HF Hno i Hi. destruct (Hno (b + i) ltac:(lia)) as [Hr Hn].
apply (aview_eq_of tfibsegs). apply HF. rewrite unsigned_lit_small by lia. exact Hn.
Qed.
Lemma blk_kept_trans : forall H1 H2 H3 (m1 m2 m3 : word -> option byte) b n,
blk_kept H1 H2 m1 m2 b n -> blk_kept H2 H3 m2 m3 b n -> blk_kept H1 H3 m1 m3 b n.
Proof. intros H1 H2 H3 m1 m2 m3 b n K1 K2 i Hi. rewrite (K2 i Hi). apply K1. exact Hi. Qed.
Lemma blk_kept_refl : forall H m b n, blk_kept H H m m b n.
Proof. intros H m b n i Hi. reflexivity. Qed.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Lemma blk_kept_acall : forall lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) b sz,
acall_kept tfibsegs B lyc Sc W memc W2 mem2 slo shi Er -> In (b, sz) (ablocks B lyc Sc) ->
(forall i, 0 <= i < req_size sz -> ~ Er (b + i)) ->
blk_kept (w_H W) (w_H W2) memc mem2 b (req_size sz).
Proof. intros lyc Sc W memc W2 mem2 slo shi Er b sz (_ & K2 & _) Hin HnE i Hi. exact (K2 b sz i Hin Hi (HnE i Hi)). Qed.
Lemma ablocks_perm_twice : forall ly S W mem md l1 l2 x,
AR tfibsegs B ly S W mem md -> Permutation (ablocks B ly S) (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros ly S W mem md l1 l2 x HAR HP H1 H2.
apply in_split in H1 as (a1 & a2 & E1). apply in_split in H2 as (c1 & c2 & E2). subst l1 l2.
assert (HP2 : Permutation (ablocks B ly S) (x :: x :: ((a1 ++ a2) ++ c1) ++ c2)).
{ eapply Permutation_trans; [exact HP|].
eapply Permutation_trans. { apply Permutation_app; [apply Permutation_sym; apply (Permutation_middle a1 a2 x) | apply Permutation_refl]. }
change ((x :: a1 ++ a2) ++ c1 ++ x :: c2) with (x :: ((a1 ++ a2) ++ (c1 ++ x :: c2))).
apply perm_skip.
replace ((a1 ++ a2) ++ (c1 ++ x :: c2)) with (((a1 ++ a2) ++ c1) ++ x :: c2) by (first [rewrite app_assoc; reflexivity | rewrite <- app_assoc; reflexivity]).
change (x :: ((a1 ++ a2) ++ c1) ++ c2) with (x :: (((a1 ++ a2) ++ c1) ++ c2)).
apply Permutation_sym. apply (Permutation_middle ((a1 ++ a2) ++ c1) c2 x). }
assert (Hx : In x (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HP2 | left; reflexivity]).
destruct x as [b m].
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hx) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (sep_blocks_perm tfibsegs B LAWS ly S W mem md _ _ _ HAR HP2) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
pose proof (req_size_pos m ltac:(lia)). lia.
Qed.
Lemma tmp_not_entry : forall ly S W mem md pre entry b,
AR tfibsegs B ly S W mem md -> Permutation (ablocks B ly S) (pre ++ entry) -> In b pre -> ~ In b entry.
Proof. intros ly S W mem md pre entry b HAR HP Hb He. exact (ablocks_perm_twice ly S W mem md pre entry b HAR HP Hb He). Qed.
Lemma tcgif_at_ngp : forall m g s, tcgif_at m g s -> 0 <= cg_ngp s < 65536.
Proof.
intros m g s (Hg & _ & _). cbn [obj_at tcgif_vals LAY_CGIF] in Hg. unfold field_ok in Hg. cbn [fst snd Z.of_N] in Hg.
change (2 ^ (8 * 2)) with 65536 in Hg. tauto.
Qed.
Lemma frame_at_nlp : forall m f, obj_at tfibsegs m (fr_ptr f) LAY_Frame (frame_vals f) -> 0 <= fr_nlp f < 65536.
Proof.
intros m f Hf. cbn [obj_at frame_vals LAY_Frame LAY_FrameConfig app] in Hf. unfold field_ok in Hf. cbn [fst snd Z.of_N] in Hf.
change (2 ^ (8 * 2)) with 65536 in Hf. tauto.
Qed.
Lemma frame_blocks_bsum : forall m N f, obj_at tfibsegs m (fr_ptr f) LAY_Frame (frame_vals f) -> 0 <= N ->
bsum (frame_blocks N f) <= 40 + N + 3 * 65536.
Proof.
intros m N f Hf HN. pose proof (frame_at_nlp m f Hf) as Hn. unfold frame_blocks.
rewrite !bsum_cons. destruct (Z.land (fr_attr f) 1 =? 0); cbn [bsum fold_right snd]; unfold FRAME_SIZE; lia.
Qed.
Lemma cgif_blocks_bsum : forall m g s N, tcgif_at m g s -> cgif_wf s N -> bsum (cgif_blocks g s N) <= CGB.
Proof.
intros m g s N Hat Hwf.
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & Hngp & _ & _).
pose proof (tcgif_at_ngp m g s Hat) as Hn. destruct Hat as (Hg & Hr & Hf).
unfold cgif_blocks. rewrite !bsum_cons, bsum_app. cbn [snd].
assert (Hpal : bsum (pal_blocks s) <= 3 * 65536).
{ unfold pal_blocks. destruct (Z.eqb_spec (Z.land (cg_attr s) 4) 0); cbn [bsum fold_right snd]; lia. }
assert (HN0 : 0 <= N) by nia.
assert (Hfr : forall fs, (forall f, In (Some f) fs -> obj_at tfibsegs m (fr_ptr f) LAY_Frame (frame_vals f)) ->
bsum (frames_blocks N fs) <= Z.of_nat (length fs) * (40 + N + 3 * 65536)).
{ intros fs. induction fs as [|o fs IH]; intros Hfs; [cbn; lia|].
change (frames_blocks N (o :: fs)) with (match o with Some f => frame_blocks N f | None => [] end ++ frames_blocks N fs).
rewrite bsum_app. cbn [length]. rewrite Nat2Z.inj_succ.
specialize (IH ltac:(intros f Hf'; apply Hfs; right; exact Hf')).
destruct o as [f|].
- pose proof (frame_blocks_bsum m N f (Hfs f ltac:(left; reflexivity)) HN0). lia.
- cbn [bsum fold_right]. lia. }
specialize (Hfr (cg_frames s) Hf). rewrite Hlen in Hfr. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hfr.
unfold CGB, CGIF_SIZE, RAW_SIZE. lia.
Qed.
Lemma range_addressable_stack : forall ly S W mem md a len,
AR tfibsegs B ly S W mem md -> ly_stk_lo ly <= a -> a + len <= ly_stk_hi ly -> 0 <= len ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF a len.
Proof.
intros ly S W mem md a len HAR Hlo Hhi Hlen.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _).
pose proof (al_zshadow _ _ LAWS _ _ _ _ _ (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(left; reflexivity)) as Hz. cbn [fst snd] in Hz.
unfold page_aligned in Hpal, Hpah.
pose proof (Z.div_mod (ly_stk_lo ly) 4096 ltac:(lia)) as A. pose proof (Z.div_mod (ly_stk_hi ly) 4096 ltac:(lia)) as C.
rewrite Hpal, Z.add_0_r in A. rewrite Hpah, Z.add_0_r in C.
assert (Hm1 : ly_stk_lo ly mod 8 = 0) by (rewrite A; replace (4096 * (ly_stk_lo ly / 4096)) with ((512 * (ly_stk_lo ly / 4096)) * 8) by lia; apply Z_mod_mult).
assert (Hm2 : (ly_stk_hi ly - ly_stk_lo ly) mod 8 = 0).
{ rewrite A, C. replace (4096 * (ly_stk_hi ly / 4096) - 4096 * (ly_stk_lo ly / 4096)) with ((512 * (ly_stk_hi ly / 4096) - 512 * (ly_stk_lo ly / 4096)) * 8) by lia. apply Z_mod_mult. }
eapply range_addressable_sub; [apply zero_shadow_range; [exact Hm1 | exact Hm2 | exact Hz] | lia | lia].
Qed.
End d.
End c.
Ltac not_in_wrange AG wtac :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr; wtac Hr | ]);
destruct Hin.
Ltac cgif_kept_run HFr HPin HJx Hfin EFA AG KA :=
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict ?Hh ?m0) (mrestrict _ ?m1) =>
lazymatch type of HPin with forall x, In x ?pre -> In x (ablocks ?B ?lyx ?Sx) =>
assert (KA : forall b sz, In (b, sz) pre -> blk_kept Hh Hh m0 m1 b (req_size sz));
[ let b := fresh "b" in let sz := fresh "sz" in let Hb := fresh "Hb" in let Hbx := fresh "Hbx" in
let Hb4096 := fresh "Hb4096'" in let Hbceil := fresh "Hbceil'" in let HdBF := fresh "HdBF" in
let a := fresh "a" in let Ha := fresh "Ha" in
let L := rnLAWS in
intros b sz Hb; pose proof (HPin _ Hb) as Hbx;
destruct (al_blocks _ _ L _ _ _ _ _ b sz (proj1 HJx) Hbx) as (_ & Hb4096 & Hbceil & _);
pose proof (sep_block_frame tfibsegs _ L lyx Sx _ _ _ b sz 2 _ (proj1 HJx) Hbx Hfin) as HdBF;
unfold zdisjoint in HdBF; cbn [fst snd] in HdBF; change (fs_frame_bytes 2) with 256 in HdBF; rewrite EFA in HdBF;
repeat match goal with F := frame_addr _ _ _ |- _ => progress (fold F in HdBF) end;
lazymatch goal with QC0 : _ <= alloc_ceiling <= _ |- _ =>
apply (blk_kept_frame Ef rs Hh m0 m1 b (req_size sz) HFr);
intros a Ha; split; [clear - Ha Hb4096 Hbceil QC0; lia|];
not_in_wrange AG ltac:(fun Hr => first
[ exfalso; clear - Hr; lia
| clear - Hr Ha HdBF; lia
| lazymatch goal with Qsp1 : _ - 144 <= _ <= _ - 128 |- _ =>
lazymatch goal with Qceil : alloc_ceiling <= ly_stk_lo _ |- _ =>
lazymatch goal with Qslo : ly_stk_lo _ + _ <= _ |- _ =>
lazymatch goal with QFFS : LLVMF_STK = _ |- _ =>
lazymatch goal with QC1 : _ <= alloc_ceiling <= _ |- _ =>
first [ clear - Hr Ha Hbceil Qsp1 Qceil Qslo QFFS QC1; lia
| match goal with |- ?g => match type of Hbceil with ?t => idtac "KEPTW-LIA" t g end end; fail ]
| _ => idtac "NO-C1"; fail end | _ => idtac "NO-FFS"; fail end | _ => idtac "NO-SLO"; fail end | _ => idtac "NO-CEIL"; fail end | _ => idtac "NO-SP1"; fail end
| match goal with |- ?g => match type of Hr with ?t => idtac "KEPTW-FAIL" t g end end ]) end
| ] end end.
Fixpoint rt_trim_nth (rs : smem) (i : nat) (lo hi : Z) : smem :=
match rs, i with
| [], _ => []
| r :: t, O => rt_trim_region r lo hi :: t
| r :: t, S i' => r :: rt_trim_nth t i' lo hi
end.
Ltac trim_nth HS i lo hi :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (rt_trim_nth rs i lo hi) in
let HS3 := fresh "HS3" in
pose proof (st_ok_submem tfibsegs Ex ssx msx rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
