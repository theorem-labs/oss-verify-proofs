(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0s YK15 YM06 YK1b.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0e YO0d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM02 YI04.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
Theorem cg_calloc : calloc_realizes B MR ->
forall pc STK sp0 FP L A mem md Lc Ac regs_c memc mdc m n,
ms_calloc B = Some pc ->
journal B MR STK sp0 FP L A mem md Lc Ac memc mdc ->
st_init_done Ac = true ->
getr regs_c 10 = Z_to_bv 64 m -> getr regs_c 11 = Z_to_bv 64 n -> 0 <= m -> 0 <= n -> m * n < 4096 ->
YK0s.ret_ok (getr regs_c 1) -> spZ regs_c mod 16 = 0 ->
sp0 - STK <= spZ regs_c - CALLOC_STACK -> spZ regs_c <= sp0 ->
getr regs_c 4 = Z_to_bv 64 (ms_tp B) ->
SR segs (mkCfg (mkst regs_c (Z_to_bv 64 pc) memc (seg_rom segs)) mdc)
(fun c' => exists L2 A2 regs2 mem2 md2 (res : Z),
c' = mkCfg (mkst regs2 (getr regs_c 1) mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved regs_c regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
((res = 0 /\ blocks L2 A2 = blocks Lc Ac)
\/ (res <> 0 /\ res mod 16 = 0 /\
(exists b1 b2, blocks L2 A2 = b1 ++ (res, m * n) :: b2 /\ blocks Lc Ac = b1 ++ b2) /\
(forall blc i, In (res, m * n) blc -> 0 <= i < m * n -> wr_byte STK sp0 FP (blocks L A) blc (res + i)) /\
(forall i, 0 <= i < m * n -> mbyte segs mem2 (res + i) = Some (Z_to_bv 8 0)))) /\
(forall a k i, In (a, k) (blocks Lc Ac) -> 0 <= i < k ->
mbyte segs mem2 (a + i) = mbyte segs memc (a + i)) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs_c - CALLOC_STACK <= a < spZ regs_c) ->
mbyte segs mem2 a = mbyte segs memc a /\ (writable_at segs memc a <-> writable_at segs mem2 a))).
Proof.
intros HCA pc STK sp0 FP L A mem md Lc Ac regs_c memc mdc m n Hpc HJ Hid Ha0 Ha1 Hm Hn Hmn Hra Hal16 Hlo Hhi Htp.
pose proof HJ as (HH & Hvm & Hhigh & Hblk & Hgone & Hst & Herr & Himg).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof errno_low as Hel.
assert (CALLOC_STACK = 8224) as Has by reflexivity.
destruct Hst as (Hal & Hstk0 & Hceil & H63 & Hstw).
destruct HH as (HM & HW & HB).
assert (Hpre : call_pre_k B MR CALLOC_STACK Lc Ac regs_c memc mdc).
{ split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact Hra|].
split; [exact Hal16|]. split; [lia|]. split; [lia|]. split.
{ intros a Ha. apply Hstw. lia. }
split; [exact Htp|]. split; [exact Herr|].
intros Hf. rewrite Hid in Hf. discriminate. }
eapply SR_mono.
{ eapply (mreal_SR segs _ _ _ (HCA pc Lc Ac regs_c memc mdc m n Hpc Hpre Ha0 Ha1 Hm Hn Hmn)). apply malloc_safe; [exact HW | nia]. }
intros c' ([p A2] & tr & Hcp & (L2 & regs2 & mem2 & md2 & -> & Hpost & Hres)). cbn [fst snd] in *.
pose proof (malloc_keeps_init_done (m * n) Ac tr p A2 Hid (cpath_yields _ _ _ Hcp)) as Hid2.
pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hregs & Hvm2 & Hfr & Hkeep & Hscr).
assert (HH2 : heap_ok MR L2 A2 mem2 md2) by (split; [exact HM2 | split; assumption]).
assert (Hsub : forall q k, In (q, k) (user_blocks Ac) -> In (q, k) (user_blocks A2)).
{ intros q k Hq. destruct p as [p0|].
- destruct Hres as (_ & _ & (l1 & l2 & E1 & E2) & _). rewrite E1. rewrite E2 in Hq.
apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff; [left; exact Hq | right; right; exact Hq].
- destruct Hres as [_ E]. rewrite E. exact Hq. }
assert (HJ2 : journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2).
{ eapply (journal_call_k CALLOC_STACK); [exact HJ | exact Hpost | lia | exact Hlo | exact Hhi | intros a Ha; destruct Ha |].
intros q k i Hq Hnq Hi. exact (Hnq (Hsub q k Hq)). }
assert (Hkeepc : forall a k i, In (a, k) (blocks Lc Ac) -> 0 <= i < k -> mbyte segs mem2 (a + i) = mbyte segs memc (a + i)).
{ intros a k i Ham Hi. apply blocks_In in Ham as (q & Hq & Hqin). rewrite <- Hq.
apply (Hkeep q k i Hqin (Hsub q k Hqin) Hi). }
assert (Hhighc : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs_c - CALLOC_STACK <= a < spZ regs_c) ->
mbyte segs mem2 a = mbyte segs memc a /\ (writable_at segs memc a <-> writable_at segs mem2 a)).
{ intros a Ha Hns. apply Hfr.
- left. lia.
- intros Ho. pose proof (mr_owned_low B MR LAWS _ _ _ _ a HM Ho). lia.
- intros Ho. pose proof (mr_owned_low B MR LAWS _ _ _ _ a HM2 Ho). lia.
- unfold scratch_k. intros [Hs|Hs]; [exact (Hns Hs) | lia].
- intros F; exact F. }
assert (Hmapc : map (fun b : sptr * Z => (ptr_addr L2 (fst b), snd b)) (user_blocks Ac) = blocks Lc Ac).
{ unfold blocks. apply (map_addr_stable Lc L2 (user_blocks Ac) (user_blocks Ac)); [intros x Hx; exact Hx|].
intros q k Hq. exact (Hstab q k Hq (Hsub q k Hq)). }
exists L2, A2, regs2, mem2, md2.
destruct p as [p0|].
- destruct Hres as (Hr10 & Hnz & (l1 & l2 & E1 & E2) & Hzero).
exists (ptr_addr L2 p0). split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [exact Hregs|].
split; [exact Hr10|]. split; [| split; [exact Hkeepc | exact Hhighc]].
right. split; [exact Hnz|].
assert (Hin2 : In (p0, m * n) (user_blocks A2)) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
split; [exact (mr_blocks_aligned B MR LAWS L2 A2 mem2 md2 p0 (m * n) HM2 Hin2)|].
assert (HB2eq : blocks L2 A2 = map (fun b : sptr * Z => (ptr_addr L2 (fst b), snd b)) l1 ++ (ptr_addr L2 p0, m * n) ::
map (fun b : sptr * Z => (ptr_addr L2 (fst b), snd b)) l2).
{ unfold blocks. rewrite E1, map_app. reflexivity. }
assert (HBceq : blocks Lc Ac = map (fun b : sptr * Z => (ptr_addr L2 (fst b), snd b)) l1 ++
map (fun b : sptr * Z => (ptr_addr L2 (fst b), snd b)) l2).
{ rewrite <- Hmapc, E2, map_app. reflexivity. }
split; [eexists _, _; split; [exact HB2eq | exact HBceq]|].
split; [|exact Hzero].
intros blc i Hinb Hi.
assert (Hin2' : In (ptr_addr L2 p0, m * n) (blocks L2 A2)) by (apply blocks_In; exists p0; auto).
destruct (in_dec zz_eq_dec (ptr_addr L2 p0, m * n) (blocks L A)) as [H0|H0].
+ right. left. split; [| exists (ptr_addr L2 p0), (m * n); split; [exact Hinb | lia]].
apply (Hgone _ _ i H0); [|exact Hi].
intros Hc. rewrite HBceq in Hc.
pose proof (mr_blocks_disjoint B MR LAWS L2 A2 mem2 md2 HM2) as HP. rewrite HB2eq in HP.
destruct (pairwise_app_mid _ _ _ _ _ HP Hc) as [Hd|Hd]; unfold ranges_disjoint in Hd; cbn [fst snd] in Hd; lia.
+ right. right. exists (ptr_addr L2 p0), (m * n). split; [exact Hinb|]. split; [exact H0 | lia].
- destruct Hres as [Hr10 E].
exists 0. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [exact Hregs|].
split; [exact Hr10|]. split; [| split; [exact Hkeepc | exact Hhighc]].
left. split; [reflexivity|]. rewrite <- Hmapc. unfold blocks. rewrite E. reflexivity.
Qed.
Lemma jcalloc_at : calloc_realizes B MR ->
forall pc E ss ms STK sp0 FP L A mem md Lc Ac mdc m n spc raw,
ms_calloc B = Some pc ->
st_ok segs E ss ms -> ss_pc ss = pc -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
st_init_done Ac = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 m -> getr (ms_regs ms) 11 = Z_to_bv 64 n -> 0 <= m -> 0 <= n -> m * n < 4096 ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> 0 <= spc < 2 ^ 64 -> spc mod 16 = 0 ->
sp0 - STK <= spc - CALLOC_STACK -> spc <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp B) ->
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
(exists b1 b2, blocks L2 A2 = b1 ++ (res, m * n) :: b2 /\ blocks Lc Ac = b1 ++ b2) /\
(forall blc i, In (res, m * n) blc -> 0 <= i < m * n -> wr_byte STK sp0 FP (blocks L A) blc (res + i)) /\
(forall i, 0 <= i < m * n -> mbyte segs mem2 (res + i) = Some (Z_to_bv 8 0)))) /\
(forall b k i, In (b, k) (blocks Lc Ac) -> 0 <= i < k ->
mbyte segs mem2 (b + i) = mbyte segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - CALLOC_STACK <= x < spc) ->
mbyte segs mem2 x = mbyte segs (ms_mem ms) x /\
(writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x))).
Proof.
intros HCA pc E ss ms STK sp0 FP L A mem md Lc Ac mdc m n spc raw
Hpc HS Hsspc Hrv HJ Hid Ha0 Ha1 Hm Hn Hmn Hsp Hspc Hal Hlo Hhi Htp Hra Hraw.
assert (Hsp' : spZ (ms_regs ms) = spc).
{ unfold spZ. rewrite Hsp. apply unsigned_lit_small. exact Hspc. }
rewrite (st_ok_mkst segs E ss ms HS Hrv), Hsspc.
eapply SR_mono.
{ eapply (cg_calloc HCA pc STK sp0 FP L A mem md Lc Ac (ms_regs ms) (ms_mem ms) mdc m n Hpc HJ Hid Ha0 Ha1 Hm Hn Hmn).
- rewrite Hra. exact Hraw.
- rewrite Hsp'. exact Hal.
- rewrite Hsp'. exact Hlo.
- rewrite Hsp'. exact Hhi.
- exact Htp. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hr10 & Hres & Hkeep & Hhi2).
exists L2, A2, regs2, mem2, md2, res. rewrite Hra. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|].
split; [exact HP2|]. split; [exact Hr10|]. split; [exact Hres|]. split; [exact Hkeep|].
intros x Hx Hnx. apply Hhi2; [exact Hx|]. rewrite Hsp'. exact Hnx.
Qed.
End J.
End c.
