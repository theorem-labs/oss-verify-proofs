(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN3v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Export YI04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YI16.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis errno_low : errno_addr B + 4 <= alloc_ceiling.
Hypothesis IMG : img_laws B MR.
Local Notation segs := (ms_segs B).
Context {SK : sink_head}.
Local Notation heap_ok := (YI04.heap_ok MR).
Local Notation errno_ok := (YI04.errno_ok B).
Local Notation stack_ok := (YI04.stack_ok B).
Local Notation fn_pre := (YI04.fn_pre B MR).
Definition img_kept (FP : list (Z * Z)) (mem mem' : word -> option byte) : Prop :=
forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
~ (errno_addr B <= a < errno_addr B + 4) ->
~ (sink_open_fp FP /\ sk_ofl_head <= a < sk_ofl_head + 8) ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a).
Lemma img_kept_refl : forall FP m, img_kept FP m m.
Proof. intros FP m a _ _ _ _ _. split; [reflexivity | tauto]. Qed.
Lemma img_kept_trans : forall FP m1 m2 m3, img_kept FP m1 m2 -> img_kept FP m2 m3 -> img_kept FP m1 m3.
Proof.
intros FP m1 m2 m3 H1 H2 a Ha Hs Hc He Hk. destruct (H1 a Ha Hs Hc He Hk) as [E1 E2]. destruct (H2 a Ha Hs Hc He Hk) as [F1 F2].
split; [rewrite F1; exact E1 | rewrite E2; exact F2].
Qed.
Lemma img_kept_mono : forall FP1 FP m m', (sink_open_fp FP1 -> sink_open_fp FP) -> img_kept FP1 m m' -> img_kept FP m m'.
Proof.
intros FP1 FP m m' HF H a Ha Hs Hc He Hk. apply (H a Ha Hs Hc He). intros [Ho Hr]. apply Hk. split; [|exact Hr].
exact (HF Ho).
Qed.
Lemma img_not_owned : forall L A mem md a,
MR L A mem md -> in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) -> ~ owned B L A a.
Proof.
intros L A mem md a HM Ha Hs Hc [Ho|Ho]; [|exact (Hs Ho)]. exact (Hc (il_ctx IMG L A mem md a HM Ha Ho)).
Qed.
Definition journal (STK sp0 : Z) (FP : list (Z * Z))
(L : layout) (A : astate) (mem : word -> option byte) (md : Model)
(L' : layout) (A' : astate) (mem' : word -> option byte) (md' : Model) : Prop :=
heap_ok L' A' mem' md' /\
os_step FP md md' /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
(forall a n i, In (a, n) (blocks L A) -> In (a, n) (blocks L' A') -> 0 <= i < n ->
~ inFP FP (a + i) -> mbyte segs mem' (a + i) = mbyte segs mem (a + i)) /\
(forall a n i, In (a, n) (blocks L A) -> ~ In (a, n) (blocks L' A') -> 0 <= i < n -> inFP FP (a + i)) /\
stack_ok STK sp0 mem' /\ errno_ok mem' /\
img_kept FP mem mem'.
Lemma blocks_In : forall L A a n, In (a, n) (blocks L A) <-> exists p, ptr_addr L p = a /\ In (p, n) (user_blocks A).
Proof.
intros L A a n. unfold blocks. rewrite in_map_iff. split.
- intros ([p m] & H & Hin). cbn in H. injection H as <- <-. exists p. auto.
- intros (p & <- & Hin). exists (p, n). auto.
Qed.
Lemma heap_blocks : forall L A mem md a n i,
heap_ok L A mem md -> In (a, n) (blocks L A) -> 0 <= i < n ->
present mem (a + i) /\ 4096 <= a /\ a + n <= alloc_ceiling /\ ~ owned B L A (a + i).
Proof.
intros L A mem md a n i (HM & _) Hin Hi. apply blocks_In in Hin as (p & <- & Hin).
exact (mr_blocks B MR LAWS L A mem md p n i HM Hin Hi).
Qed.
Lemma heap_blocks_range : forall L A mem md a n,
heap_ok L A mem md -> In (a, n) (blocks L A) -> 0 < n -> 4096 <= a /\ a + n <= alloc_ceiling /\ a mod 16 = 0.
Proof.
intros L A mem md a n (HM & HW & _) Hin Hn. apply blocks_In in Hin as (p & <- & Hin).
pose proof (mr_blocks_aligned B MR LAWS L A mem md p n HM Hin) as Hal.
destruct (mr_blocks B MR LAWS L A mem md p n 0 HM Hin ltac:(lia)) as (_ & H1 & H2 & _). auto.
Qed.
Lemma heap_owned_low : forall L A mem md a, heap_ok L A mem md -> owned B L A a -> 0 <= a < alloc_ceiling.
Proof. intros L A mem md a (HM & _) Ho. exact (mr_owned_low B MR LAWS L A mem md a HM Ho). Qed.
Lemma heap_model : forall L A mem md, heap_ok L A mem md ->
m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = [].
Proof. intros L A mem md (HM & _). exact (mr_model B MR LAWS L A mem md HM). Qed.
Lemma present_writable : forall mem a, present mem a -> writable_at segs mem a.
Proof.
intros mem a [b Hb]. unfold writable_at, wview. rewrite Hb. discriminate.
Qed.
Lemma with_vmmaps_self : forall md, md = with_vmmaps (m_vmmaps md) md.
Proof. intros md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.
Lemma with_vmmaps_twice : forall v1 v2 md, with_vmmaps v2 (with_vmmaps v1 md) = with_vmmaps v2 md.
Proof. intros v1 v2 md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.
Lemma journal_init : forall STK FP L A regs mem md,
fn_pre STK L A regs mem md -> journal STK (spZ regs) FP L A mem md L A mem md.
Proof.
intros STK FP L A regs mem md (HH & Hra & Hst & Htp & Herr).
split; [exact HH|]. split; [apply os_step_refl|].
split; [intros a Ha Hna; split; [reflexivity | tauto]|].
split; [intros; reflexivity|]. split; [intros a n i H1 H2; exfalso; exact (H2 H1)|].
split; [exact Hst|]. split; [exact Herr | apply img_kept_refl].
Qed.
Lemma mbyte_eq_of : forall (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> mbyte segs m' a = mbyte segs m a.
Proof. intros m m' a H. unfold mbyte. rewrite H. reflexivity. Qed.
Lemma writable_iff_of : forall (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> (writable_at segs m a <-> writable_at segs m' a).
Proof. intros m m' a H. unfold writable_at, wview. rewrite H. tauto. Qed.
Lemma pairwise_in2 : forall {X} (R : X -> X -> Prop) l x y,
pairwise R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
intros X R l. induction l as [|z l IH]; intros x y HP Hx Hy Hne; cbn in *; [destruct Hx|].
destruct HP as [Hz HP]. destruct Hx as [<-|Hx], Hy as [<-|Hy].
- congruence.
- left. apply Hz. exact Hy.
- right. apply Hz. exact Hx.
- apply IH; assumption.
Qed.
Lemma heap_sep_in2 : forall L A mem md x y,
heap_ok L A mem md -> In x (blocks L A) -> In y (blocks L A) -> x <> y ->
fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
intros L A mem md x y (HM & _) Hx Hy Hne.
destruct (pairwise_in2 _ _ x y (mr_blocks_disjoint B MR LAWS L A mem md HM) Hx Hy Hne) as [H|H];
unfold ranges_disjoint in H; lia.
Qed.
Lemma wr_byte_low : forall STK sp0 FP (L : layout) (A : astate) Lc Ac memc mdc a,
heap_ok Lc Ac memc mdc -> wr_byte STK sp0 FP (blocks L A) (blocks Lc Ac) a ->
(sp0 - STK <= a < sp0) \/ (a < alloc_ceiling /\ ~ owned B Lc Ac a /\
exists b n, In (b, n) (blocks Lc Ac) /\ b <= a < b + n /\
(inFP FP a \/ ~ In (b, n) (blocks L A))).
Proof.
intros STK sp0 FP L A Lc Ac memc mdc a HH [Hs | [(Hfp & b & n & Hin & Hr) | (b & n & Hin & Hn0 & Hr)]].
- left. exact Hs.
- right. destruct (heap_blocks Lc Ac memc mdc b n (a - b) HH Hin ltac:(lia)) as (_ & _ & Hc & Hno).
replace (b + (a - b)) with a in Hno by lia. split; [lia|]. split; [exact Hno|]. exists b, n. auto.
- right. destruct (heap_blocks Lc Ac memc mdc b n (a - b) HH Hin ltac:(lia)) as (_ & _ & Hc & Hno).
replace (b + (a - b)) with a in Hno by lia. split; [lia|]. split; [exact Hno|]. exists b, n. auto.
Qed.
Lemma journal_exec : forall STK sp0 FP L A mem md Lc Ac memc mdc memc' (W : Z -> Prop),
journal STK sp0 FP L A mem md Lc Ac memc mdc ->
(forall x : word, ~ W (bv_unsigned x) -> memc' x = memc x) ->
mem_grows memc memc' ->
(forall a, W a -> wr_byte STK sp0 FP (blocks L A) (blocks Lc Ac) a) ->
journal STK sp0 FP L A mem md Lc Ac memc' mdc.
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc memc' W
(HH & Hvm & Hhigh & Hblk & Hgone & Hst & Herr & Himg) Hfr Hgr HW0.
clear errno_low.
pose proof alloc_ceiling_val as Hac.
destruct Hst as (Hal & Hstk0 & Hceil & H63 & Hstw).
assert (HW : forall a, W a -> _) by (intros a Ha; exact (wr_byte_low STK sp0 FP L A Lc Ac memc mdc a HH (HW0 a Ha))).
clear HW0.
assert (HWlow : forall a, W a -> a < sp0 /\ ~ owned B Lc Ac a).
{ intros a Ha. destruct (HW a Ha) as [Hs | (Hc & Hno & _)].
- split; [lia|]. intros Ho. pose proof (heap_owned_low _ _ _ _ a HH Ho). lia.
- split; [lia | exact Hno]. }
assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ W a -> memc' (Z_to_bv 64 a) = memc (Z_to_bv 64 a)).
{ intros a Ha HWa. apply Hfr. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact HWa. }
split.
{ destruct HH as (HM & HW' & HB). split; [|split; assumption].
destruct (mr_model B MR LAWS _ _ _ _ HM) as (Hh & Hl & Hmat).
eapply (mr_frame B MR LAWS); [exact HM | | | | reflexivity | exact Hh | exact Hl | exact Hmat].
- intros a Ho. apply mbyte_eq_of. pose proof (mr_owned_low B MR LAWS _ _ _ _ a HM Ho).
apply Heqw; [lia|]. intros HWa. exact (proj2 (HWlow a HWa) Ho).
- intros a Ho Hp. eapply present_grows; eauto.
- intros p n i Hin Hi. eapply present_grows; [exact Hgr|].
exact (proj1 (mr_blocks B MR LAWS _ _ _ _ p n i HM Hin Hi)). }
split; [exact Hvm|]. split.
{ intros a Ha Hna. assert (E1 : memc' (Z_to_bv 64 a) = memc (Z_to_bv 64 a)).
{ apply Heqw; [lia|]. intros HWa.
destruct (HW a HWa) as [Hs | (Hc & _)]; [exact (Hna Hs) | lia]. }
destruct (Hhigh a Ha Hna) as [H1 H2]. split.
- rewrite <- H1. apply mbyte_eq_of. exact E1.
- rewrite H2. apply writable_iff_of. exact E1. }
split.
{ intros a n i H1 H2 Hi Hnf. rewrite <- (Hblk a n i H1 H2 Hi Hnf). apply mbyte_eq_of.
destruct (heap_blocks Lc Ac memc mdc a n i HH H2 Hi) as (_ & Hlo & Hhi & _).
apply Heqw; [lia|]. intros HWa. destruct (HW _ HWa) as [Hs | (_ & _ & b & m & Hbin & Hr & [Hfp | Hnot])]; [lia | exact (Hnf Hfp) |].
assert (Hne : (b, m) <> (a, n)) by (intros E; rewrite E in Hnot; exact (Hnot H1)).
destruct (heap_sep_in2 Lc Ac memc mdc (b, m) (a, n) HH Hbin H2 Hne) as [Hd|Hd]; cbn [fst snd] in Hd; lia. }
split; [exact Hgone|]. split.
{ split; [exact Hal|]. split; [exact Hstk0|]. split; [exact Hceil|]. split; [exact H63|].
intros a Ha. eapply writable_at_grows; [exact Hgr|]. apply Hstw. exact Ha. }
split; [intros a Ha; eapply writable_at_grows; [exact Hgr|]; apply Herr; exact Ha|].
eapply img_kept_trans; [exact Himg|]. intros a Ha Hs Hc He _.
assert (E1 : memc' (Z_to_bv 64 a) = memc (Z_to_bv 64 a)).
{ pose proof (il_low IMG a Ha) as Hlow.
assert (Ha0 : 0 <= a).
{ destruct Ha as [_ (sg & _ & Hr)]. pose proof (bv_unsigned_in_range _ (fst sg)). lia. }
apply Heqw; [lia|]. intros HWa. destruct (HW a HWa) as [Hsk | (_ & _ & b & m & Hbin & Hr & _)]; [lia|].
apply blocks_In in Hbin as (q & Hq & Hqin).
apply (il_blocks IMG Lc Ac memc mdc q m (a - b) (proj1 HH) Hqin ltac:(lia)). rewrite Hq.
replace (b + (a - b)) with a by lia. exact Ha. }
split; [apply mbyte_eq_of; exact E1 | apply writable_iff_of; exact E1].
Qed.
Lemma sptr_eq_dec : forall p q : sptr, {p = q} + {p <> q}.
Proof. intros [r o] [r' o']. destruct (Nat.eq_dec r r'); [|right; congruence].
destruct (Z.eq_dec o o'); [left; congruence | right; congruence]. Defined.
Lemma spn_eq_dec : forall x y : sptr * Z, {x = y} + {x <> y}.
Proof. intros [p n] [q m]. destruct (sptr_eq_dec p q); [|right; congruence].
destruct (Z.eq_dec n m); [left; congruence | right; congruence]. Defined.
Lemma zz_eq_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. intros [p n] [q m]. destruct (Z.eq_dec p q); [|right; congruence].
destruct (Z.eq_dec n m); [left; congruence | right; congruence]. Defined.
Lemma journal_call : forall STK sp0 FP L A mem md Lc Ac memc mdc regs_c (Efp : Z -> Prop) L2 A2 regs2 mem2 md2,
journal STK sp0 FP L A mem md Lc Ac memc mdc ->
call_post B MR Lc Ac regs_c memc mdc Efp L2 A2 regs2 mem2 md2 ->
sp0 - STK <= spZ regs_c - ALLOC_STACK -> spZ regs_c <= sp0 ->
(forall a, Efp a -> exists b n, In (b, n) (blocks Lc Ac) /\ b <= a < b + n /\ (inFP FP a \/ ~ In (b, n) (blocks L A))) ->
(forall p n i, In (p, n) (user_blocks Ac) -> ~ In (p, n) (user_blocks A2) -> 0 <= i < n ->
Efp (ptr_addr Lc p + i)) ->
journal STK sp0 FP L A mem md L2 A2 mem2 md2.
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs_c Efp L2 A2 regs2 mem2 md2
HJ0 (HM2 & HW2 & HB2 & Hle & Hstab & Hregs & (vm2 & Hvm2) & Hfr & Hkeep & Hscr)
Hlo Hhi HE1 Hg.
pose proof HJ0 as (HH & Hvm & Hhigh & Hblk & Hgone & Hst & Herr & Himg).
assert (HE0 : forall a, Efp a -> a < alloc_ceiling /\
(inFP FP a \/ exists b n, In (b, n) (blocks Lc Ac) /\ ~ In (b, n) (blocks L A) /\ b <= a < b + n)).
{ intros a Ha. destruct (HE1 a Ha) as (b & n & Hbin & Hr & Hor).
destruct (heap_blocks Lc Ac memc mdc b n (a - b) HH Hbin ltac:(lia)) as (_ & _ & Hc & _).
split; [lia|]. destruct Hor as [Hf|Hn]; [left; exact Hf | right; exists b, n; auto]. }
pose proof alloc_ceiling_val as Hac. pose proof errno_low as Hel.
destruct Hst as (Hal & Hstk0 & Hceil & H63 & Hstw).
assert (HH2 : heap_ok L2 A2 mem2 md2) by (split; [exact HM2 | split; assumption]).
assert (HE : forall a a0 n0, Efp a -> In (a0, n0) (blocks L A) -> In (a0, n0) (blocks Lc Ac) -> a0 <= a < a0 + n0 ->
inFP FP a).
{ intros a a0 n0 Ha H0 Hc Hr. destruct (HE0 a Ha) as [_ [Hfp | (b & m & Hbin & Hbn & Hbr)]]; [exact Hfp|].
assert (Hne : (b, m) <> (a0, n0)) by (intros E; rewrite E in Hbn; exact (Hbn H0)).
destruct (heap_sep_in2 Lc Ac memc mdc (b, m) (a0, n0) HH Hbin Hc Hne) as [Hd|Hd]; cbn [fst snd] in Hd; lia. }
assert (ALLOC_STACK = 8192) as Has by reflexivity.
assert (Hfree : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs_c - ALLOC_STACK <= a < spZ regs_c) ->
mbyte segs mem2 a = mbyte segs memc a /\ (writable_at segs memc a <-> writable_at segs mem2 a)).
{ intros a Ha Hns. apply Hfr.
- left. exact Ha.
- intros Ho. pose proof (heap_owned_low _ _ _ _ a HH Ho). lia.
- intros Ho. pose proof (heap_owned_low _ _ _ _ a HH2 Ho). lia.
- unfold scratch. intros [Hs|Hs]; [exact (Hns Hs) | lia].
- intros He. destruct (HE0 a He). lia. }
split; [exact HH2|]. split.
{ rewrite Hvm2. apply os_step_then_vmmaps. exact Hvm. }
split.
{ intros a Ha Hna. destruct (Hfree a ltac:(lia) ltac:(lia)) as [E1 E2]. destruct (Hhigh a Ha Hna) as [F1 F2].
split; [rewrite E1; exact F1 | rewrite F2; exact E2]. }
split.
{ intros a n i H1 H2 Hi Hnf.
destruct (in_dec zz_eq_dec (a, n) (blocks Lc Ac)) as [Hc|Hc].
- rewrite <- (Hblk a n i H1 Hc Hi Hnf).
pose proof Hc as Hc0. apply blocks_In in Hc as (p & Hp & Hpc).
destruct (in_dec spn_eq_dec (p, n) (user_blocks A2)) as [Hp2|Hp2].
+ rewrite <- Hp. apply (Hkeep p n i Hpc Hp2 Hi).
+ exfalso. apply Hnf. apply (HE (a + i) a n); [rewrite <- Hp; apply (Hg p n i Hpc Hp2 Hi) | exact H1 | exact Hc0 | lia].
- exfalso. exact (Hnf (Hgone a n i H1 Hc Hi)). }
split.
{ intros a n i H1 H2 Hi.
destruct (in_dec zz_eq_dec (a, n) (blocks Lc Ac)) as [Hc|Hc]; [|exact (Hgone a n i H1 Hc Hi)].
pose proof Hc as Hc0. apply blocks_In in Hc as (p & Hp & Hpc).
destruct (in_dec spn_eq_dec (p, n) (user_blocks A2)) as [Hp2|Hp2].
- exfalso. apply H2. apply blocks_In. exists p. split; [|exact Hp2]. rewrite (Hstab p n Hpc Hp2). exact Hp.
- apply (HE (a + i) a n); [rewrite <- Hp; apply (Hg p n i Hpc Hp2 Hi) | exact H1 | exact Hc0 | lia]. }
split.
{ split; [exact Hal|]. split; [exact Hstk0|]. split; [exact Hceil|]. split; [exact H63|].
intros a Ha. destruct (Z_lt_le_dec a (spZ regs_c - ALLOC_STACK)) as [Hb|Hb].
- apply (proj1 (proj2 (Hfree a ltac:(lia) ltac:(lia)))). apply Hstw. exact Ha.
- destruct (Z_lt_le_dec a (spZ regs_c)) as [Hb2|Hb2].
+ apply Hscr. unfold scratch. left. lia.
+ apply (proj1 (proj2 (Hfree a ltac:(lia) ltac:(lia)))). apply Hstw. exact Ha. }
split; [intros a Ha; apply Hscr; unfold scratch; right; exact Ha|].
eapply img_kept_trans; [exact Himg|]. intros a Ha Hs Hc He _.
pose proof (il_low IMG a Ha) as Hlow.
apply Hfr.
- right. exact Ha.
- exact (img_not_owned Lc Ac memc mdc a (proj1 HH) Ha Hs Hc).
- exact (img_not_owned L2 A2 mem2 md2 a HM2 Ha Hs Hc).
- unfold scratch. intros [Hsk|Hsk]; [lia | exact (He Hsk)].
- intros Hea. destruct (HE1 a Hea) as (b & n & Hbin & Hr & _).
apply blocks_In in Hbin as (q & Hq & Hqin).
apply (il_blocks IMG Lc Ac memc mdc q n (a - b) (proj1 HH) Hqin ltac:(lia)). rewrite Hq.
replace (b + (a - b)) with a by lia. exact Ha.
Qed.
Lemma fn_pre_of_journal : forall STK sp0 FP L A mem md Lc Ac regs_c memc mdc STK1,
journal STK sp0 FP L A mem md Lc Ac memc mdc ->
YK0s.ret_ok (getr regs_c 1) -> spZ regs_c mod 16 = 0 -> 0 <= STK1 ->
sp0 - STK <= spZ regs_c - STK1 -> spZ regs_c <= sp0 ->
getr regs_c 4 = Z_to_bv 64 (ms_tp B) ->
fn_pre STK1 Lc Ac regs_c memc mdc.
Proof.
intros STK sp0 FP L A mem md Lc Ac regs_c memc mdc STK1 (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & Herr & _)
Hra Hal16 Hstk1 Hlo Hhi Htp.
split; [exact HH|]. split; [exact Hra|]. split; [| split; [exact Htp | exact Herr]].
split; [exact Hal16|]. split; [exact Hstk1|]. split; [lia|]. split; [lia|].
intros a Ha. apply Hstw. lia.
Qed.
Lemma journal_sub : forall STK sp0 FP L A mem md Lc Ac memc mdc STK1 sp1 FP1 L2 A2 mem2 md2,
journal STK sp0 FP L A mem md Lc Ac memc mdc ->
journal STK1 sp1 FP1 Lc Ac memc mdc L2 A2 mem2 md2 ->
sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
(forall a, inFP FP1 a -> inFP FP a /\ a < alloc_ceiling) ->
journal STK sp0 FP L A mem md L2 A2 mem2 md2.
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc STK1 sp1 FP1 L2 A2 mem2 md2
(HH & Hvm & Hhigh & Hblk & Hgone & Hst & Herr & Himg)
(HH2 & Hvm2 & Hhigh2 & Hblk2 & Hgone2 & Hst2 & Herr2 & Himg2) Hlo Hhi HF.
pose proof alloc_ceiling_val as Hac.
destruct Hst as (Hal & Hstk0 & Hceil & H63 & Hstw). destruct Hst2 as (Hal2 & Hstk2 & Hceil2 & H632 & Hstw2).
split; [exact HH2|]. split.
{ eapply os_step_trans; [| exact Hvm | exact Hvm2]. intros Ho. exact (proj1 (HF _ Ho)). }
split.
{ intros a Ha Hna. destruct (Hhigh2 a Ha ltac:(lia)) as [E1 E2]. destruct (Hhigh a Ha Hna) as [F1 F2].
split; [rewrite E1; exact F1 | rewrite F2; exact E2]. }
split.
{ intros a n i H1 H2 Hi Hnf.
destruct (in_dec zz_eq_dec (a, n) (blocks Lc Ac)) as [Hc|Hc].
- rewrite <- (Hblk a n i H1 Hc Hi Hnf). apply (Hblk2 a n i Hc H2 Hi).
intros Hf. exact (Hnf (proj1 (HF _ Hf))).
- exfalso. exact (Hnf (Hgone a n i H1 Hc Hi)). }
split.
{ intros a n i H1 H2 Hi.
destruct (in_dec zz_eq_dec (a, n) (blocks Lc Ac)) as [Hc|Hc]; [|exact (Hgone a n i H1 Hc Hi)].
apply (proj1 (HF _ (Hgone2 a n i Hc H2 Hi))). }
split.
{ split; [exact Hal|]. split; [exact Hstk0|]. split; [exact Hceil|]. split; [exact H63|].
intros a Ha. destruct (Z_lt_le_dec a (sp1 - STK1)) as [Hb|Hb].
- apply (proj1 (proj2 (Hhigh2 a ltac:(lia) ltac:(lia)))). apply Hstw. exact Ha.
- destruct (Z_lt_le_dec a sp1) as [Hb2|Hb2].
+ apply Hstw2. lia.
+ apply (proj1 (proj2 (Hhigh2 a ltac:(lia) ltac:(lia)))). apply Hstw. exact Ha. }
split; [exact Herr2 | eapply img_kept_trans; [exact Himg | eapply img_kept_mono; [|exact Himg2]; intros Ho; exact (proj1 (HF _ Ho))]].
Qed.
Lemma pairwise_app_mid : forall {X} (R : X -> X -> Prop) b1 x b2 y,
pairwise R (b1 ++ x :: b2) -> In y (b1 ++ b2) -> R x y \/ R y x.
Proof.
intros X R b1. induction b1 as [|z b1 IH]; intros x b2 y HP Hin; cbn in *.
- left. apply (proj1 HP). exact Hin.
- destruct Hin as [<-|Hin].
+ right. apply (proj1 HP). apply in_app_iff. right. left. reflexivity.
+ apply (IH x b2 y (proj2 HP) Hin).
Qed.
Lemma heap_sep : forall L A mem md b1 x b2 y,
heap_ok L A mem md -> blocks L A = b1 ++ x :: b2 -> In y (b1 ++ b2) ->
fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
intros L A mem md b1 x b2 y (HM & _) HB Hin.
pose proof (mr_blocks_disjoint B MR LAWS L A mem md HM) as HP. rewrite HB in HP.
destruct (pairwise_app_mid _ b1 x b2 y HP Hin) as [H|H]; unfold ranges_disjoint in H; lia.
Qed.
Lemma heap_sep_perm : forall L A mem md x rest y,
heap_ok L A mem md -> Permutation (blocks L A) (x :: rest) -> In y rest ->
fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
intros L A mem md x rest y HH HP Hin.
destruct (Permutation_vs_cons_inv HP) as (b1 & b2 & HB).
eapply (heap_sep L A mem md b1 x b2 y HH HB).
apply (Permutation_in y (l:=rest)); [|exact Hin]. apply Permutation_sym.
apply (Permutation_app_inv b1 b2 [] rest x). rewrite <- HB. exact HP.
Qed.
Lemma blocks_perm_in : forall L A (x : Z * Z) rest y,
Permutation (blocks L A) (x :: rest) -> (y = x \/ In y rest) -> In y (blocks L A).
Proof.
intros L A x rest y HP Hy. apply (Permutation_in y (Permutation_sym HP)). destruct Hy as [->|Hy]; [left; reflexivity | right; exact Hy].
Qed.
Lemma regs_preserved_trans : forall r1 r2 r3,
regs_preserved r1 r2 -> regs_preserved r2 r3 -> regs_preserved r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). apply H1. exact Hr. Qed.
Lemma map_addr_stable : forall (L L' : layout) (l l' : list (sptr * Z)),
incl l l' ->
(forall q m, In (q, m) l' -> ptr_addr L' q = ptr_addr L q) ->
map (fun b : sptr * Z => (ptr_addr L' (fst b), snd b)) l = map (fun b : sptr * Z => (ptr_addr L (fst b), snd b)) l.
Proof.
intros L L' l l' Hi Hs. induction l as [|[q m] l IH]; [reflexivity|]. cbn [map fst snd].
rewrite (Hs q m) by (apply Hi; left; reflexivity). rewrite IH; [reflexivity|]. intros x Hx. apply Hi. right. exact Hx.
Qed.
Theorem cg_free : free_realizes B MR ->
forall STK sp0 FP L A mem md Lc Ac regs_c memc mdc p n,
journal STK sp0 FP L A mem md Lc Ac memc mdc ->
In (p, n) (user_blocks Ac) -> getr regs_c 10 = Z_to_bv 64 (ptr_addr Lc p) ->
YK0s.ret_ok (getr regs_c 1) -> spZ regs_c mod 16 = 0 ->
sp0 - STK <= spZ regs_c - ALLOC_STACK -> spZ regs_c <= sp0 ->
getr regs_c 4 = Z_to_bv 64 (ms_tp B) ->
(In (ptr_addr Lc p, n) (blocks L A) -> forall i, 0 <= i < n -> inFP FP (ptr_addr Lc p + i)) ->
SR segs (mkCfg (mkst regs_c (Z_to_bv 64 (ms_free B)) memc (seg_rom segs)) mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 (getr regs_c 1) mem2 (seg_rom segs)) md2 /\
journal STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved regs_c regs2 /\
rm1 (ptr_addr Lc p, n) (blocks Lc Ac) (blocks L2 A2) /\
(forall a m i, In (a, m) (blocks L2 A2) -> 0 <= i < m ->
mbyte segs mem2 (a + i) = mbyte segs memc (a + i)) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs_c - ALLOC_STACK <= a < spZ regs_c) ->
mbyte segs mem2 a = mbyte segs memc a /\ (writable_at segs memc a <-> writable_at segs mem2 a)) /\
st_init_done A2 = true).
Proof.
intros HFR STK sp0 FP L A mem md Lc Ac regs_c memc mdc p n HJ Hin Ha0 Hra Hal16 Hlo Hhi Htp HFP.
pose proof HJ as (HH & Hvm & Hhigh & Hblk & Hgone & Hst & Herr & Himg).
pose proof alloc_ceiling_val as Hac. pose proof errno_low as Hel.
assert (ALLOC_STACK = 8192) as Has by reflexivity.
destruct Hst as (Hal & Hstk0 & Hceil & H63 & Hstw).
destruct HH as (HM & HW & HB).
assert (Hpre : call_pre B MR Lc Ac regs_c memc mdc).
{ split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact Hra|].
split; [exact Hal16|]. split; [lia|]. split; [lia|]. split.
{ intros a Ha. apply Hstw. lia. }
split; [exact Htp|]. split; [exact Herr|].
intros Hf. rewrite (init_done_of_block Ac (p, n) HW Hin) in Hf. discriminate. }
eapply SR_mono; [eapply (free_SR B MR HFR); [exact Hpre | exact Hin | exact Ha0]|].
intros c' ([[] A2] & tr & Hcp & (L2 & regs2 & mem2 & md2 & -> & Hpost & (l1 & l2 & E1 & E2))). cbn [snd] in *.
pose proof (free_keeps_init_done (Some p) Ac tr tt A2 (init_done_of_block Ac (p, n) HW Hin) (cpath_yields _ _ _ Hcp)) as Hid2.
pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hregs & Hvm2 & Hfr & Hkeep & Hscr).
assert (HH2 : heap_ok L2 A2 mem2 md2) by (split; [exact HM2 | split; assumption]).
assert (Hsub : forall q m, In (q, m) (user_blocks A2) -> In (q, m) (user_blocks Ac)).
{ intros q m Hq. rewrite E2 in Hq. rewrite E1. apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff; [left|right; right]; exact Hq. }
pose proof (mr_blocks B MR LAWS Lc Ac memc mdc p n) as Hpb.
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split.
{ eapply journal_call; [exact HJ | exact Hpost | exact Hlo | exact Hhi | |].
- intros a Ha. cbn beta in Ha. exists (ptr_addr Lc p), n.
split; [apply blocks_In; exists p; auto|]. split; [lia|].
destruct (in_dec zz_eq_dec (ptr_addr Lc p, n) (blocks L A)) as [H0|H0]; [|right; exact H0].
left. replace a with (ptr_addr Lc p + (a - ptr_addr Lc p)) by lia. apply (HFP H0). lia.
- intros q m i Hq Hnq Hi. cbn beta. rewrite E1 in Hq. rewrite E2 in Hnq.
apply in_app_iff in Hq as [Hq|[Hq|Hq]].
+ exfalso. apply Hnq. apply in_app_iff. left. exact Hq.
+ injection Hq as -> ->. lia.
+ exfalso. apply Hnq. apply in_app_iff. right. exact Hq. }
split; [exact Hregs|]. split.
{ exists (map (fun b : sptr * Z => (ptr_addr Lc (fst b), snd b)) l1), (map (fun b : sptr * Z => (ptr_addr Lc (fst b), snd b)) l2).
unfold blocks. rewrite E1, E2, !map_app. cbn [map fst snd]. split; [reflexivity|].
rewrite (map_addr_stable Lc L2 l1 (user_blocks A2)); [| rewrite E2; intros x Hx; apply in_app_iff; left; exact Hx | intros q m Hq; apply (Hstab q m); [apply Hsub; exact Hq | exact Hq]].
rewrite (map_addr_stable Lc L2 l2 (user_blocks A2)); [| rewrite E2; intros x Hx; apply in_app_iff; right; exact Hx | intros q m Hq; apply (Hstab q m); [apply Hsub; exact Hq | exact Hq]].
reflexivity. }
split.
{ intros a m i Ham Hi. apply blocks_In in Ham as (q & Hq & Hqin).
rewrite (Hstab q m (Hsub q m Hqin) Hqin) in Hq. rewrite <- Hq. apply (Hkeep q m i); [apply Hsub; exact Hqin | exact Hqin | exact Hi]. }
split; [|exact Hid2].
intros a Ha Hns. apply Hfr.
- left. lia.
- intros Ho. pose proof (mr_owned_low B MR LAWS _ _ _ _ a HM Ho). lia.
- intros Ho. pose proof (mr_owned_low B MR LAWS _ _ _ _ a HM2 Ho). lia.
- unfold scratch. intros [Hs|Hs]; [exact (Hns Hs) | lia].
- cbn beta. intros He. destruct (Hpb 0 HM Hin ltac:(lia)) as (_ & _ & Hc & _). lia.
Qed.
Theorem cg_malloc : malloc_realizes B MR ->
forall STK sp0 FP L A mem md Lc Ac regs_c memc mdc n,
journal STK sp0 FP L A mem md Lc Ac memc mdc ->
st_init_done Ac = true ->
getr regs_c 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 62 ->
YK0s.ret_ok (getr regs_c 1) -> spZ regs_c mod 16 = 0 ->
sp0 - STK <= spZ regs_c - ALLOC_STACK -> spZ regs_c <= sp0 ->
getr regs_c 4 = Z_to_bv 64 (ms_tp B) ->
SR segs (mkCfg (mkst regs_c (Z_to_bv 64 (ms_malloc B)) memc (seg_rom segs)) mdc)
(fun c' => exists L2 A2 regs2 mem2 md2 (res : Z),
c' = mkCfg (mkst regs2 (getr regs_c 1) mem2 (seg_rom segs)) md2 /\
journal STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved regs_c regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
((res = 0 /\ blocks L2 A2 = blocks Lc Ac)
\/ (res <> 0 /\ res mod 16 = 0 /\
(exists b1 b2, blocks L2 A2 = b1 ++ (res, n) :: b2 /\ blocks Lc Ac = b1 ++ b2) /\
(forall blc i, In (res, n) blc -> 0 <= i < n -> wr_byte STK sp0 FP (blocks L A) blc (res + i)))) /\
(forall a m i, In (a, m) (blocks Lc Ac) -> 0 <= i < m ->
mbyte segs mem2 (a + i) = mbyte segs memc (a + i)) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs_c - ALLOC_STACK <= a < spZ regs_c) ->
mbyte segs mem2 a = mbyte segs memc a /\ (writable_at segs memc a <-> writable_at segs mem2 a))).
Proof.
intros HMA STK sp0 FP L A mem md Lc Ac regs_c memc mdc n HJ Hid Ha0 Hn Hra Hal16 Hlo Hhi Htp.
pose proof HJ as (HH & Hvm & Hhigh & Hblk & Hgone & Hst & Herr & Himg).
pose proof alloc_ceiling_val as Hac. pose proof errno_low as Hel.
assert (ALLOC_STACK = 8192) as Has by reflexivity.
destruct Hst as (Hal & Hstk0 & Hceil & H63 & Hstw).
destruct HH as (HM & HW & HB).
assert (Hpre : call_pre B MR Lc Ac regs_c memc mdc).
{ split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact Hra|].
split; [exact Hal16|]. split; [lia|]. split; [lia|]. split.
{ intros a Ha. apply Hstw. lia. }
split; [exact Htp|]. split; [exact Herr|].
intros Hf. rewrite Hid in Hf. discriminate. }
eapply SR_mono; [eapply (malloc_SR B MR HMA); [exact Hpre | exact Ha0 | exact Hn]|].
intros c' ([p A2] & tr & Hcp & (L2 & regs2 & mem2 & md2 & -> & Hpost & Hres)). cbn [fst snd] in *.
pose proof (malloc_keeps_init_done n Ac tr p A2 Hid (cpath_yields _ _ _ Hcp)) as Hid2.
pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hregs & Hvm2 & Hfr & Hkeep & Hscr).
assert (HH2 : heap_ok L2 A2 mem2 md2) by (split; [exact HM2 | split; assumption]).
assert (Hsub : forall q m, In (q, m) (user_blocks Ac) -> In (q, m) (user_blocks A2)).
{ intros q m Hq. destruct p as [p0|].
- destruct Hres as (_ & _ & (l1 & l2 & E1 & E2) & _). rewrite E1. rewrite E2 in Hq.
apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff; [left; exact Hq | right; right; exact Hq].
- destruct Hres as [_ E]. rewrite E. exact Hq. }
assert (HJ2 : journal STK sp0 FP L A mem md L2 A2 mem2 md2).
{ eapply journal_call; [exact HJ | exact Hpost | exact Hlo | exact Hhi | intros a Ha; destruct Ha |].
intros q m i Hq Hnq Hi. exact (Hnq (Hsub q m Hq)). }
assert (Hkeepc : forall a m i, In (a, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte segs mem2 (a + i) = mbyte segs memc (a + i)).
{ intros a m i Ham Hi. apply blocks_In in Ham as (q & Hq & Hqin). rewrite <- Hq.
apply (Hkeep q m i Hqin (Hsub q m Hqin) Hi). }
assert (Hhighc : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs_c - ALLOC_STACK <= a < spZ regs_c) ->
mbyte segs mem2 a = mbyte segs memc a /\ (writable_at segs memc a <-> writable_at segs mem2 a)).
{ intros a Ha Hns. apply Hfr.
- left. lia.
- intros Ho. pose proof (mr_owned_low B MR LAWS _ _ _ _ a HM Ho). lia.
- intros Ho. pose proof (mr_owned_low B MR LAWS _ _ _ _ a HM2 Ho). lia.
- unfold scratch. intros [Hs|Hs]; [exact (Hns Hs) | lia].
- intros F; exact F. }
assert (Hmapc : map (fun b : sptr * Z => (ptr_addr L2 (fst b), snd b)) (user_blocks Ac) = blocks Lc Ac).
{ unfold blocks. apply (map_addr_stable Lc L2 (user_blocks Ac) (user_blocks Ac)); [intros x Hx; exact Hx|].
intros q m Hq. exact (Hstab q m Hq (Hsub q m Hq)). }
exists L2, A2, regs2, mem2, md2.
destruct p as [p0|].
- destruct Hres as (Hr10 & Hnz & (l1 & l2 & E1 & E2) & _).
exists (ptr_addr L2 p0). split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [exact Hregs|].
split; [exact Hr10|]. split; [| split; [exact Hkeepc | exact Hhighc]].
right. split; [exact Hnz|].
assert (Hin2 : In (p0, n) (user_blocks A2)) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
split; [exact (mr_blocks_aligned B MR LAWS L2 A2 mem2 md2 p0 n HM2 Hin2)|].
assert (HB2eq : blocks L2 A2 = map (fun b : sptr * Z => (ptr_addr L2 (fst b), snd b)) l1 ++ (ptr_addr L2 p0, n) ::
map (fun b : sptr * Z => (ptr_addr L2 (fst b), snd b)) l2).
{ unfold blocks. rewrite E1, map_app. reflexivity. }
assert (HBceq : blocks Lc Ac = map (fun b : sptr * Z => (ptr_addr L2 (fst b), snd b)) l1 ++
map (fun b : sptr * Z => (ptr_addr L2 (fst b), snd b)) l2).
{ rewrite <- Hmapc, E2, map_app. reflexivity. }
split; [eexists _, _; split; [exact HB2eq | exact HBceq]|].
intros blc i Hinb Hi.
assert (Hin2' : In (ptr_addr L2 p0, n) (blocks L2 A2)) by (apply blocks_In; exists p0; auto).
destruct (in_dec zz_eq_dec (ptr_addr L2 p0, n) (blocks L A)) as [H0|H0].
+ right. left. split; [| exists (ptr_addr L2 p0), n; split; [exact Hinb | lia]].
apply (Hgone _ _ i H0); [|exact Hi].
intros Hc. rewrite HBceq in Hc.
pose proof (mr_blocks_disjoint B MR LAWS L2 A2 mem2 md2 HM2) as HP. rewrite HB2eq in HP.
destruct (pairwise_app_mid _ _ _ _ _ HP Hc) as [Hd|Hd]; unfold ranges_disjoint in Hd; cbn [fst snd] in Hd; lia.
+ right. right. exists (ptr_addr L2 p0), n. split; [exact Hinb|]. split; [exact H0 | lia].
- destruct Hres as [Hr10 E].
exists 0. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [exact Hregs|].
split; [exact Hr10|]. split; [| split; [exact Hkeepc | exact Hhighc]].
left. split; [reflexivity|]. rewrite <- Hmapc. unfold blocks. rewrite E. reflexivity.
Qed.
Theorem cg_free_null : free_null_realizes B ->
forall regs mem md,
YK0s.ret_ok (getr regs 1) -> getr regs 10 = Z_to_bv 64 0 -> m_halted md = None -> m_vm_lazy md = [] ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
(fun c' => c' = mkCfg (mkst regs (getr regs 1) mem (seg_rom segs)) md).
Proof. intros HFN. exact HFN. Qed.
Lemma journal_os : forall STK sp0 FP L A mem md L' A' mem' md',
journal STK sp0 FP L A mem md L' A' mem' md' -> os_step FP md md'.
Proof. intros STK sp0 FP L A mem md L' A' mem' md' (_ & H & _). exact H. Qed.
Lemma journal_img : forall STK sp0 FP L A mem md L' A' mem' md',
journal STK sp0 FP L A mem md L' A' mem' md' -> img_kept FP mem mem'.
Proof. intros STK sp0 FP L A mem md L' A' mem' md' (_ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.
Lemma journal_of_plain : forall STK sp0 FP L A mem md L' A' mem' md',
YI04.journal B MR STK sp0 FP L A mem md L' A' mem' md' -> journal STK sp0 FP L A mem md L' A' mem' md'.
Proof.
intros STK sp0 FP L A mem md L' A' mem' md' (HH & (vm & ->) & Hhigh & Hblk & Hgone & Hst & Herr & Himg).
split; [exact HH|]. split; [apply os_step_vmmaps|]. split; [exact Hhigh|]. split; [exact Hblk|]. split; [exact Hgone|].
split; [exact Hst|]. split; [exact Herr|]. intros a Ha Hs Hc He _. exact (Himg a Ha Hs Hc He).
Qed.
End e.
Section g.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis errno_low : errno_addr B + 4 <= alloc_ceiling.
Hypothesis IMG : img_laws B MR.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok (ms_segs B) tbl.
Local Notation segs := (ms_segs B).
Context {SK : sink_head}.
Local Notation memcpy_spec := (YI04.memcpy_spec B).
Lemma SR_run_J : forall n E ss ss' st ms STK sp0 FP L A mem md Lc Ac mdc Q,
st_ok segs E ss ms ->
sym_runN segs tbl n ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
wr_ok E (ss_mem ss) STK sp0 FP (blocks L A) (blocks Lc Ac) ->
(forall ms', st_ok segs E ss' ms' -> journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') -> mem_grows (ms_mem ms) (ms_mem ms') ->
SR segs (mkCfg ms' mdc) Q) ->
SR segs (mkCfg ms mdc) Q.
Proof.
intros n E ss ss' st ms STK sp0 FP L A mem md Lc Ac mdc Q HS Hrun Hst HJ Hwr Hk.
destruct (msteps_run_gen segs tbl tbl_ok n E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & Hfr).
destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
apply (SR_msteps segs ms ms' mdc Q Hh Hl Hms). apply Hk.
- destruct st; [exact HS' | destruct Hst | exact HS'].
- eapply (journal_exec B MR LAWS IMG); [exact HJ | exact Hfr | apply (msteps_mem_grows segs); exact Hms | exact Hwr].
- exact Hfr.
- apply (msteps_mem_grows segs). exact Hms.
Qed.
Lemma SR_run_to_J : forall n stop E ss ss' st ms STK sp0 FP L A mem md Lc Ac mdc Q,
st_ok segs E ss ms ->
sym_run_toN segs tbl n stop ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
wr_ok E (ss_mem ss) STK sp0 FP (blocks L A) (blocks Lc Ac) ->
(forall ms', st_ok segs E ss' ms' -> journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') -> mem_grows (ms_mem ms) (ms_mem ms') ->
SR segs (mkCfg ms' mdc) Q) ->
SR segs (mkCfg ms mdc) Q.
Proof.
intros n stop E ss ss' st ms STK sp0 FP L A mem md Lc Ac mdc Q HS Hrun Hst HJ Hwr Hk.
destruct (msteps_run_to_gen segs tbl tbl_ok n stop E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & Hfr).
destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
apply (SR_msteps segs ms ms' mdc Q Hh Hl Hms). apply Hk.
- destruct st; [exact HS' | destruct Hst | exact HS'].
- eapply (journal_exec B MR LAWS IMG); [exact HJ | exact Hfr | apply (msteps_mem_grows segs); exact Hms | exact Hwr].
- exact Hfr.
- apply (msteps_mem_grows segs). exact Hms.
Qed.
Lemma jfree : free_realizes B MR ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc a n (o : Z) spw tpw raw,
st_ok segs E ss ms -> ss_pc ss = ms_free B -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
In (a, n) (blocks Lc Ac) ->
getr (ms_regs ms) 10 = Z_to_bv 64 a ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ALLOC_STACK - o <= STK ->
getr (ms_regs ms) 4 = tpw -> tpw = Z_to_bv 64 (ms_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
(In (a, n) (blocks L A) -> forall i, 0 <= i < n -> inFP FP (a + i)) ->
SR segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\
rm1 (a, n) (blocks Lc Ac) (blocks L2 A2) /\
(forall b m i, In (b, m) (blocks L2 A2) -> 0 <= i < m ->
mbyte segs mem2 (b + i) = mbyte segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 + o - ALLOC_STACK <= x < sp0 + o) ->
mbyte segs mem2 x = mbyte segs (ms_mem ms) x /\
(writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x))).
Proof.
intros HFR E ss ms STK sp0 FP L A mem md Lc Ac mdc a n o spw tpw raw
HS Hpc Hrv HJ Hin Ha0 Hsp HE2 Hspw Hal Hneg Hbud Htp Htpw Hra Hraw HFP.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof alloc_ceiling_val as Hac. assert (ALLOC_STACK = 8192) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. cbn [sv_denot]. rewrite HE2, Hspw. apply unsigned_lit_small. lia. }
rewrite (st_ok_mkst segs E ss ms HS Hrv), Hpc.
apply blocks_In in Hin as (p & Hp & Hpin).
eapply SR_mono.
{ eapply (cg_free B MR LAWS errno_low IMG HFR STK sp0 FP L A mem md Lc Ac (ms_regs ms) (ms_mem ms) mdc p n HJ Hpin).
- rewrite Hp. exact Ha0.
- rewrite Hra. exact Hraw.
- rewrite Hsp'. rewrite Z.add_mod, Hal16, Hal by lia. reflexivity.
- rewrite Hsp'. lia.
- rewrite Hsp'. lia.
- rewrite Htp. exact Htpw.
- rewrite Hp. exact HFP. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi).
exists L2, A2, regs2, mem2, md2. rewrite Hra. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
rewrite Hp in Hrm. split; [exact Hrm|]. split; [exact Hkeep|].
intros x Hx Hnx. apply Hhi; [exact Hx|]. rewrite Hsp'. exact Hnx.
Qed.
Lemma jmalloc : malloc_realizes B MR ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc n (o : Z) spw tpw raw,
st_ok segs E ss ms -> ss_pc ss = ms_malloc B -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
st_init_done Ac = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 62 ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ALLOC_STACK - o <= STK ->
getr (ms_regs ms) 4 = tpw -> tpw = Z_to_bv 64 (ms_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SR segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2 (res : Z),
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved (ms_regs ms) regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
((res = 0 /\ blocks L2 A2 = blocks Lc Ac)
\/ (res <> 0 /\ res mod 16 = 0 /\
(exists b1 b2, blocks L2 A2 = b1 ++ (res, n) :: b2 /\ blocks Lc Ac = b1 ++ b2) /\
(forall blc i, In (res, n) blc -> 0 <= i < n -> wr_byte STK sp0 FP (blocks L A) blc (res + i)))) /\
(forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m ->
mbyte segs mem2 (b + i) = mbyte segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 + o - ALLOC_STACK <= x < sp0 + o) ->
mbyte segs mem2 x = mbyte segs (ms_mem ms) x /\
(writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x))).
Proof.
intros HMA E ss ms STK sp0 FP L A mem md Lc Ac mdc n o spw tpw raw
HS Hpc Hrv HJ Hid Ha0 Hn Hsp HE2 Hspw Hal Hneg Hbud Htp Htpw Hra Hraw.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof alloc_ceiling_val as Hac. assert (ALLOC_STACK = 8192) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. cbn [sv_denot]. rewrite HE2, Hspw. apply unsigned_lit_small. lia. }
rewrite (st_ok_mkst segs E ss ms HS Hrv), Hpc.
eapply SR_mono.
{ eapply (cg_malloc B MR LAWS errno_low IMG HMA STK sp0 FP L A mem md Lc Ac (ms_regs ms) (ms_mem ms) mdc n HJ Hid Ha0 Hn).
- rewrite Hra. exact Hraw.
- rewrite Hsp'. rewrite Z.add_mod, Hal16, Hal by lia. reflexivity.
- rewrite Hsp'. lia.
- rewrite Hsp'. lia.
- rewrite Htp. exact Htpw. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hr10 & Hres & Hkeep & Hhi).
exists L2, A2, regs2, mem2, md2, res. rewrite Hra. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|].
split; [exact HP2|]. split; [exact Hr10|]. split; [exact Hres|]. split; [exact Hkeep|].
intros x Hx Hnx. apply Hhi; [exact Hx|]. rewrite Hsp'. exact Hnx.
Qed.
Lemma jcall : forall E ss ms STK sp0 FP L A mem md Lc Ac mdc STK1 FP1
(K : layout -> astate -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) raw,
st_ok segs E ss ms -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
getr (ms_regs ms) 1 = raw ->
(fn_pre B MR STK1 Lc Ac (ms_regs ms) (ms_mem ms) mdc ->
SR segs (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK1 (spZ (ms_regs ms)) FP1 Lc Ac (ms_mem ms) mdc L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\ K L2 A2 regs2 mem2 md2)) ->
YK0s.ret_ok raw -> spZ (ms_regs ms) mod 16 = 0 -> 0 <= STK1 ->
sp0 - STK <= spZ (ms_regs ms) - STK1 -> spZ (ms_regs ms) <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp B) ->
(forall a, inFP FP1 a -> inFP FP a /\ a < alloc_ceiling) ->
SR segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
journal B MR STK1 (spZ (ms_regs ms)) FP1 Lc Ac (ms_mem ms) mdc L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\ K L2 A2 regs2 mem2 md2).
Proof.
intros E ss ms STK sp0 FP L A mem md Lc Ac mdc STK1 FP1 K raw HS Hrv HJ Hra Hcallee Hraw Hal16 Hstk1 Hlo Hhi Htp HF.
rewrite (st_ok_mkst segs E ss ms HS Hrv).
eapply SR_mono.
{ apply Hcallee. eapply (fn_pre_of_journal B MR); [exact HJ | rewrite Hra; exact Hraw | exact Hal16 | exact Hstk1 | exact Hlo | exact Hhi | exact Htp]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
eapply (journal_sub B MR); [exact HJ | exact HJ1 | exact Hlo | exact Hhi | exact HF].
Qed.
Lemma jfree_null : free_null_realizes B ->
forall E ss ms md raw,
st_ok segs E ss ms -> ss_pc ss = ms_free B -> ss_resv ss = None ->
m_halted md = None -> m_vm_lazy md = [] ->
getr (ms_regs ms) 10 = Z_to_bv 64 0 ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SR segs (mkCfg ms md) (fun c' => c' = mkCfg (mkst (ms_regs ms) raw (ms_mem ms) (seg_rom segs)) md).
Proof.
intros HFN E ss ms md raw HS Hpc Hrv Hh Hl Ha0 Hra Hraw.
rewrite (st_ok_mkst segs E ss ms HS Hrv), Hpc. cbn [ms_regs ms_mem mkst]. rewrite <- Hra.
apply (cg_free_null B HFN); [rewrite Hra; exact Hraw | exact Ha0 | exact Hh | exact Hl].
Qed.
Lemma memcpy_clob_in : forall r : reg,
r <> 5%bv -> r <> 6%bv -> r <> 7%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv ->
r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> r <> 28%bv -> reg_in r MEMCPY_CLOB = false.
Proof.
intros r. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [intros; first [reflexivity | congruence] |]). destruct Hin.
Qed.
Lemma memcpy_clob_out : forall r : reg, reg_in r MEMCPY_CLOB = false ->
r <> 5%bv /\ r <> 6%bv /\ r <> 7%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\
r <> 15%bv /\ r <> 16%bv /\ r <> 17%bv /\ r <> 28%bv.
Proof.
intros r Hr. repeat split; intros ->; vm_compute in Hr; discriminate.
Qed.
Lemma rdn_of_present : forall (m : word -> option byte) n a,
(forall i, 0 <= i < Z.of_nat n -> present m (a + i)) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
exists bs, rdn segs m (Z_to_bv 64 a) n = Some bs /\ length bs = n.
Proof.
intros m n. induction n as [|n IH]; intros a Hp Ha Hnw.
- exists []. split; reflexivity.
- destruct (Hp 0 ltac:(lia)) as [b Hb]. rewrite Z.add_0_r in Hb.
destruct (IH (a + 1)) as (bs & Hbs & Hlen); [intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by lia; apply Hp; lia | lia | lia |].
exists (b :: bs). split; [|cbn; lia]. cbn [rdn]. rewrite Hb.
replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)); [rewrite Hbs; reflexivity|].
apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_unsigned 1) with 1. rewrite <- Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma store_ok_of_present : forall (m : word -> option byte) n a,
(forall i, 0 <= i < Z.of_nat n -> present m (a + i)) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
store_ok segs m (Z_to_bv 64 a) n = true.
Proof.
intros m n a Hp Ha Hnw. destruct n as [|n']; [reflexivity|].
apply store_ok_of_all; [rewrite unsigned_lit_small by lia; lia|].
intros x Hx. rewrite unsigned_lit_small in Hx by lia.
destruct (Hp (bv_unsigned x - a) ltac:(lia)) as [b Hb]. replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in Hb by lia.
rewrite Z_to_bv_bv_unsigned in Hb. unfold wview. rewrite Hb. discriminate.
Qed.
Lemma jmemcpy : forall pcm, memcpy_spec pcm ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc d src n raw,
st_ok segs E ss ms -> ss_pc ss = pcm -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 11 = Z_to_bv 64 src -> getr (ms_regs ms) 12 = Z_to_bv 64 n ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
0 <= n -> 0 <= d -> 0 <= src -> d + n < 2 ^ 64 -> src + n < 2 ^ 64 ->
(forall i, 0 <= i < n -> present (ms_mem ms) (d + i)) ->
(forall i, 0 <= i < n -> present (ms_mem ms) (src + i)) ->
(d + n <= src \/ src + n <= d) ->
(forall a, d <= a < d + n -> wr_byte STK sp0 FP (blocks L A) (blocks Lc Ac) a) ->
SR segs (mkCfg ms mdc)
(fun c' => exists regs2 mem2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) mdc /\
journal B MR STK sp0 FP L A mem md Lc Ac mem2 mdc /\
getr regs2 10 = Z_to_bv 64 d /\
(forall r, reg_in r MEMCPY_CLOB = false -> getr regs2 r = getr (ms_regs ms) r) /\
(forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> mem2 x = ms_mem ms x) /\
mem_grows (ms_mem ms) mem2 /\
(forall i, 0 <= i < n -> mbyte segs mem2 (d + i) = mbyte segs (ms_mem ms) (src + i))).
Proof.
intros pcm HM E ss ms STK sp0 FP L A mem md Lc Ac mdc d src n raw HS Hpc Hrv HJ H10 H11 H12 H1 Hraw
Hn Hd Hs Hdn Hsn Hpd Hps Hdisj HW.
destruct (rdn_of_present (ms_mem ms) (Z.to_nat n) src ltac:(intros i Hi; apply Hps; lia) Hs ltac:(lia)) as (bs & Hbs & Hlen).
pose proof (store_ok_of_present (ms_mem ms) (Z.to_nat n) d ltac:(intros i Hi; apply Hpd; lia) Hd ltac:(lia)) as Hst.
rewrite <- Hlen in Hst.
destruct (HM bs (Z_to_bv 64 d) (Z_to_bv 64 src) (Z_to_bv 64 n) (ms_mem ms) (seg_rom segs) (ms_regs ms) H10 H11 H12)
as (regs2 & Hms & Ha0 & Hfr).
{ rewrite unsigned_lit_small by lia. lia. }
{ rewrite Hlen. exact Hbs. }
{ exact Hst. }
{ rewrite unsigned_lit_small by lia. lia. }
{ rewrite unsigned_lit_small by lia. lia. }
{ rewrite !unsigned_lit_small by lia. lia. }
rewrite (st_ok_mkst segs E ss ms HS Hrv), Hpc.
destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
eapply SR_msteps; [exact Hh | exact Hl | exact Hms |].
apply SR_ret. exists regs2, (wbytes (ms_mem ms) (Z_to_bv 64 d) bs). rewrite H1, Hraw.
assert (Hout : forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> wbytes (ms_mem ms) (Z_to_bv 64 d) bs x = ms_mem ms x).
{ intros x Hx. destruct Hx as [Hx|Hx].
- apply wbytes_below; rewrite unsigned_lit_small by lia; lia.
- apply wbytes_above. rewrite unsigned_lit_small by lia. lia. }
split; [reflexivity|]. split.
{ eapply (journal_exec B MR LAWS IMG) with (W := fun a => d <= a < d + n); [exact HJ | | apply wbytes_grows | exact HW].
intros x Hx. apply Hout. lia. }
split; [exact Ha0|]. split.
{ intros r Hr. destruct (memcpy_clob_out r Hr) as (?&?&?&?&?&?&?&?&?&?&?). apply Hfr; assumption. }
split; [exact Hout|]. split; [apply wbytes_grows|].
intros i Hi. rewrite (wbytes_mbyte segs bs (ms_mem ms) d (d + i)) by lia.
replace ((d <=? d + i) && (d + i <? d + Z.of_nat (length bs))) with true.
2:{ symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
apply rdn_mbytes in Hbs. destruct Hbs as [_ Hb].
replace (Z.to_nat (d + i - d)) with (Z.to_nat i) by lia.
rewrite <- (Hb (Z.to_nat i)) by lia.
replace (src + Z.of_nat (Z.to_nat i)) with (src + i) by lia. reflexivity.
Qed.
End g.
End c.
Ltac jrun LAWS tblok HS HJ :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in
let IMG := lazymatch goal with IMG : img_laws _ _ |- _ => IMG end in
eapply (SR_run_J _ _ LAWS IMG _ tblok FUEL E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HJ);
clear Hrun;
[ | clear HS HJ;
try match type of ms with machine_state => clear ms | _ => idtac end;
let HF := fresh "HF" in let HG := fresh "HG" in
intros ms' HS HJ HF HG;
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
let rsv := eval vm_compute in rs in change (frame_of E1 rsv m1 m2) in HF end ]
end
end
end.
Ltac jrun_to LAWS tblok HS HJ stop :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_run_toN segs tbl FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in
let IMG := lazymatch goal with IMG : img_laws _ _ |- _ => IMG end in
eapply (SR_run_to_J _ _ LAWS IMG _ tblok FUEL stop E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HJ);
clear Hrun;
[ | clear HS HJ;
try match type of ms with machine_state => clear ms | _ => idtac end;
let HF := fresh "HF" in let HG := fresh "HG" in
intros ms' HS HJ HF HG;
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
let rsv := eval vm_compute in rs in change (frame_of E1 rsv m1 m2) in HF end ]
end
end
end.
