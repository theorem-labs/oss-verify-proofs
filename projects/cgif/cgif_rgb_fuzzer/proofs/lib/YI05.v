(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK15 YN06 YK1b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0e YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN02 YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section J.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis errno_low : errno_addr B + 4 <= alloc_ceiling.
Hypothesis IMG : img_laws B MR.
Local Notation segs := (ms_segs B).
Lemma journal_call_k : forall stk STK sp0 FP L A mem md Lc Ac memc mdc regs_c (Efp : Z -> Prop) L2 A2 regs2 mem2 md2,
journal B MR STK sp0 FP L A mem md Lc Ac memc mdc ->
call_post_k B MR stk Lc Ac regs_c memc mdc Efp L2 A2 regs2 mem2 md2 ->
0 <= stk -> sp0 - STK <= spZ regs_c - stk -> spZ regs_c <= sp0 ->
(forall a, Efp a -> exists b n, In (b, n) (blocks Lc Ac) /\ b <= a < b + n /\ (inFP FP a \/ ~ In (b, n) (blocks L A))) ->
(forall p n i, In (p, n) (user_blocks Ac) -> ~ In (p, n) (user_blocks A2) -> 0 <= i < n ->
Efp (ptr_addr Lc p + i)) ->
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2.
Proof.
intros stk STK sp0 FP L A mem md Lc Ac memc mdc regs_c Efp L2 A2 regs2 mem2 md2
HJ0 (HM2 & HW2 & HB2 & Hle & Hstab & Hregs & (vm2 & Hvm2) & Hfr & Hkeep & Hscr)
Hstk Hlo Hhi HE1 Hg.
pose proof HJ0 as (HH & Hvm & Hhigh & Hblk & Hgone & Hst & Herr & Himg).
assert (HE0 : forall a, Efp a -> a < alloc_ceiling /\
(inFP FP a \/ exists b n, In (b, n) (blocks Lc Ac) /\ ~ In (b, n) (blocks L A) /\ b <= a < b + n)).
{ intros a Ha. destruct (HE1 a Ha) as (b & n & Hbin & Hr & Hor).
destruct (heap_blocks B MR LAWS Lc Ac memc mdc b n (a - b) HH Hbin ltac:(lia)) as (_ & _ & Hc & _).
split; [lia|]. destruct Hor as [Hf|Hn]; [left; exact Hf | right; exists b, n; auto]. }
pose proof (proj1 alloc_ceiling_val) as Hac.
destruct Hst as (Hal & Hstk0 & Hceil & H63 & Hstw).
assert (HH2 : heap_ok MR L2 A2 mem2 md2) by (split; [exact HM2 | split; assumption]).
assert (HE : forall a a0 n0, Efp a -> In (a0, n0) (blocks L A) -> In (a0, n0) (blocks Lc Ac) -> a0 <= a < a0 + n0 ->
inFP FP a).
{ intros a a0 n0 Ha H0 Hc Hr. destruct (HE0 a Ha) as [_ [Hfp | (b & m & Hbin & Hbn & Hbr)]]; [exact Hfp|].
assert (Hne : (b, m) <> (a0, n0)) by (intros E; rewrite E in Hbn; exact (Hbn H0)).
destruct (heap_sep_in2 B MR LAWS Lc Ac memc mdc (b, m) (a0, n0) HH Hbin Hc Hne) as [Hd|Hd]; cbn [fst snd] in Hd; lia. }
assert (Hfree : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs_c - stk <= a < spZ regs_c) ->
mbyte segs mem2 a = mbyte segs memc a /\ (writable_at segs memc a <-> writable_at segs mem2 a)).
{ intros a Ha Hns. apply Hfr.
- left. exact Ha.
- intros Ho. pose proof (heap_owned_low B MR LAWS _ _ _ _ a HH Ho). lia.
- intros Ho. pose proof (heap_owned_low B MR LAWS _ _ _ _ a HH2 Ho). lia.
- unfold scratch_k. intros [Hs|Hs]; [exact (Hns Hs) | lia].
- intros He. destruct (HE0 a He). lia. }
split; [exact HH2|]. split.
{ exists vm2. rewrite Hvm2. destruct Hvm as [vm ->]. apply with_vmmaps_twice. }
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
intros a Ha. destruct (Z_lt_le_dec a (spZ regs_c - stk)) as [Hb|Hb].
- apply (proj1 (proj2 (Hfree a ltac:(lia) ltac:(lia)))). apply Hstw. exact Ha.
- destruct (Z_lt_le_dec a (spZ regs_c)) as [Hb2|Hb2].
+ apply Hscr. unfold scratch_k. left. lia.
+ apply (proj1 (proj2 (Hfree a ltac:(lia) ltac:(lia)))). apply Hstw. exact Ha. }
split; [intros a Ha; apply Hscr; unfold scratch_k; right; exact Ha|].
eapply img_kept_trans; [exact Himg|]. intros a Ha Hs Hc He.
pose proof (il_low IMG a Ha) as Hlow.
apply Hfr.
- right. exact Ha.
- exact (img_not_owned B MR IMG Lc Ac memc mdc a (proj1 HH) Ha Hs Hc).
- exact (img_not_owned B MR IMG L2 A2 mem2 md2 a HM2 Ha Hs Hc).
- unfold scratch_k. intros [Hsk|Hsk]; [lia | exact (He Hsk)].
- intros Hea. destruct (HE1 a Hea) as (b & n & Hbin & Hr & _).
apply blocks_In in Hbin as (q & Hq & Hqin).
apply (il_blocks IMG Lc Ac memc mdc q n (a - b) (proj1 HH) Hqin ltac:(lia)). rewrite Hq.
replace (b + (a - b)) with a by lia. exact Ha.
Qed.


End J.
End c.
