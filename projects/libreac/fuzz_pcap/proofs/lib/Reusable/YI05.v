(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI05.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO0e YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM02.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI06 YI16 YI07.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Export YN00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section G.
Variable B : malloc_syms.
Variable MR : MR_t.
Let segs := ms_segs B.
Lemma malloc_SR_res_g : malloc_realizes_g B MR ->
forall L A regs mem md n g b,
call_pre B MR L A regs mem md -> getr regs 10 = Z_to_bv 64 n -> word_mem segs mem (ms_guard B) g ->
res_ok A b -> room b n ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md)
(fun c' => exists p A' tr, cpath04 (malloc n A) tr (Some p, A') /\
malloc_leaf_g B MR L A regs mem md n g (Some p, A') c' /\ res_ok A' (rb_malloc b n)).
Proof.
intros HM L A regs mem md n g b Hpre Hn Hg HR HRm.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof (room_size n b HRm) as [_ Hn62].
eapply SR_mono.
{ apply (mreal_SR04 segs _ _ _ (HM L A regs mem md n g Hpre Hn Hn62 Hg)); [apply malloc_safe; [exact HW | lia] | exact (malloc_ok04_res A b n HW HR HRm)]. }
intros c' ([r A'] & tr & Hp & HL). destruct (malloc_leaf04_res A b n tr r A' HW HR HRm Hp) as [[p ->] HR'].
exists p, A', tr. auto.
Qed.
End G.
Section d.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis errno_low : errno_addr B + 4 <= alloc_ceiling.
Hypothesis IMG : img_laws B MR.
Local Notation segs := (ms_segs B).
Context {SK : sink_head}.
Theorem cg_free_res : free_realizes B MR ->
forall STK sp0 FP L A mem md Lc Ac regs_c memc mdc p n b,
journal B MR STK sp0 FP L A mem md Lc Ac memc mdc ->
In (p, n) (user_blocks Ac) -> res_ok Ac b -> getr regs_c 10 = Z_to_bv 64 (ptr_addr Lc p) ->
YK0s.ret_ok (getr regs_c 1) -> spZ regs_c mod 16 = 0 ->
sp0 - STK <= spZ regs_c - ALLOC_STACK -> spZ regs_c <= sp0 ->
getr regs_c 4 = Z_to_bv 64 (ms_tp B) ->
(In (ptr_addr Lc p, n) (blocks L A) -> forall i, 0 <= i < n -> inFP FP (ptr_addr Lc p + i)) ->
SR segs (mkCfg (mkst regs_c (Z_to_bv 64 (ms_free B)) memc (seg_rom segs)) mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 (getr regs_c 1) mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved regs_c regs2 /\
rm1 (ptr_addr Lc p, n) (blocks Lc Ac) (blocks L2 A2) /\
(forall a m i, In (a, m) (blocks L2 A2) -> 0 <= i < m ->
mbyte segs mem2 (a + i) = mbyte segs memc (a + i)) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs_c - ALLOC_STACK <= a < spZ regs_c) ->
mbyte segs mem2 a = mbyte segs memc a /\ (writable_at segs memc a <-> writable_at segs mem2 a)) /\
st_init_done A2 = true /\ res_ok A2 (rb_free b n)).
Proof.
intros HFR STK sp0 FP L A mem md Lc Ac regs_c memc mdc p n b HJ Hin HRb Ha0 Hra Hal16 Hlo Hhi Htp HFP.
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
eapply SR_mono; [eapply (free_SR_res B MR HFR); [exact Hpre | exact Hin | exact Ha0 | exact HRb]|].
intros c' (A2 & tr & Hcp & (L2 & regs2 & mem2 & md2 & -> & Hpost & (l1 & l2 & E1 & E2)) & HRES). cbn [snd] in *.
pose proof (free_keeps_init_done (Some p) Ac tr tt A2 (init_done_of_block Ac (p, n) HW Hin) (cpath04_yields _ _ _ Hcp)) as Hid2.
pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hregs & Hvm2 & Hfr & Hkeep & Hscr).
assert (HH2 : heap_ok MR L2 A2 mem2 md2) by (split; [exact HM2 | split; assumption]).
assert (Hsub : forall q m, In (q, m) (user_blocks A2) -> In (q, m) (user_blocks Ac)).
{ intros q m Hq. rewrite E2 in Hq. rewrite E1. apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff; [left|right; right]; exact Hq. }
pose proof (mr_blocks B MR LAWS Lc Ac memc mdc p n) as Hpb.
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split.
{ eapply (journal_call B MR LAWS errno_low IMG); [exact HJ | exact Hpost | exact Hlo | exact Hhi | |].
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
split; [|split; [exact Hid2 | exact HRES]].
intros a Ha Hns. apply Hfr.
- left. lia.
- intros Ho. pose proof (mr_owned_low B MR LAWS _ _ _ _ a HM Ho). lia.
- intros Ho. pose proof (mr_owned_low B MR LAWS _ _ _ _ a HM2 Ho). lia.
- unfold scratch. intros [Hs|Hs]; [exact (Hns Hs) | lia].
- cbn beta. intros He. destruct (Hpb 0 HM Hin ltac:(lia)) as (_ & _ & Hc & _). lia.
Qed.
Lemma cg_malloc_post :
forall STK sp0 FP L A mem md Lc Ac regs_c memc mdc n b p0 A2 tr c',
journal B MR STK sp0 FP L A mem md Lc Ac memc mdc ->
st_init_done Ac = true ->
sp0 - STK <= spZ regs_c - ALLOC_STACK -> spZ regs_c <= sp0 ->
cpath04 (malloc n Ac) tr (Some p0, A2) ->
malloc_leaf B MR Lc Ac regs_c memc mdc n (Some p0, A2) c' -> res_ok A2 (rb_malloc b n) ->
exists L2 regs2 mem2 md2 (res : Z),
c' = mkCfg (mkst regs2 (getr regs_c 1) mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved regs_c regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
(res <> 0 /\ res mod 16 = 0 /\
(exists b1 b2, blocks L2 A2 = b1 ++ (res, n) :: b2 /\ blocks Lc Ac = b1 ++ b2) /\
(forall blc i, In (res, n) blc -> 0 <= i < n -> wr_byte STK sp0 FP (blocks L A) blc (res + i))) /\
(forall a m i, In (a, m) (blocks Lc Ac) -> 0 <= i < m ->
mbyte segs mem2 (a + i) = mbyte segs memc (a + i)) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs_c - ALLOC_STACK <= a < spZ regs_c) ->
mbyte segs mem2 a = mbyte segs memc a /\ (writable_at segs memc a <-> writable_at segs mem2 a)) /\
res_ok A2 (rb_malloc b n).
Proof.
intros STK sp0 FP L A mem md Lc Ac regs_c memc mdc n b p0 A2 tr c' HJ Hid Hlo Hhi Hcp HL HRES.
pose proof HJ as (HH & Hvm & Hhigh & Hblk & Hgone & Hst & Herr & Himg).
pose proof alloc_ceiling_val as Hac. pose proof errno_low as Hel.
assert (ALLOC_STACK = 8192) as Has by reflexivity.
destruct Hst as (Hal & Hstk0 & Hceil & H63 & Hstw).
destruct HH as (HM & HW & HB).
destruct HL as (L2 & regs2 & mem2 & md2 & -> & Hpost & Hres). cbn [fst snd] in *.
pose proof (malloc_keeps_init_done n Ac tr (Some p0) A2 Hid (cpath04_yields _ _ _ Hcp)) as Hid2.
pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hregs & Hvm2 & Hfr & Hkeep & Hscr).
assert (HH2 : heap_ok MR L2 A2 mem2 md2) by (split; [exact HM2 | split; assumption]).
destruct Hres as (Hr10 & Hnz & (l1 & l2 & E1 & E2) & _).
assert (Hsub : forall q m, In (q, m) (user_blocks Ac) -> In (q, m) (user_blocks A2)).
{ intros q m Hq. rewrite E1. rewrite E2 in Hq.
apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff; [left; exact Hq | right; right; exact Hq]. }
assert (HJ2 : journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2).
{ eapply (journal_call B MR LAWS errno_low IMG); [exact HJ | exact Hpost | exact Hlo | exact Hhi | intros a Ha; destruct Ha |].
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
exists L2, regs2, mem2, md2, (ptr_addr L2 p0).
split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [exact Hregs|].
split; [exact Hr10|]. split; [| split; [exact Hkeepc | split; [exact Hhighc | exact HRES]]].
split; [exact Hnz|].
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
Qed.
Theorem cg_malloc_res : malloc_realizes B MR ->
forall STK sp0 FP L A mem md Lc Ac regs_c memc mdc n b,
journal B MR STK sp0 FP L A mem md Lc Ac memc mdc ->
st_init_done Ac = true ->
getr regs_c 10 = Z_to_bv 64 n -> res_ok Ac b -> room b n ->
YK0s.ret_ok (getr regs_c 1) -> spZ regs_c mod 16 = 0 ->
sp0 - STK <= spZ regs_c - ALLOC_STACK -> spZ regs_c <= sp0 ->
getr regs_c 4 = Z_to_bv 64 (ms_tp B) ->
SR segs (mkCfg (mkst regs_c (Z_to_bv 64 (ms_malloc B)) memc (seg_rom segs)) mdc)
(fun c' => exists L2 A2 regs2 mem2 md2 (res : Z),
c' = mkCfg (mkst regs2 (getr regs_c 1) mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved regs_c regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
(res <> 0 /\ res mod 16 = 0 /\
(exists b1 b2, blocks L2 A2 = b1 ++ (res, n) :: b2 /\ blocks Lc Ac = b1 ++ b2) /\
(forall blc i, In (res, n) blc -> 0 <= i < n -> wr_byte STK sp0 FP (blocks L A) blc (res + i))) /\
(forall a m i, In (a, m) (blocks Lc Ac) -> 0 <= i < m ->
mbyte segs mem2 (a + i) = mbyte segs memc (a + i)) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs_c - ALLOC_STACK <= a < spZ regs_c) ->
mbyte segs mem2 a = mbyte segs memc a /\ (writable_at segs memc a <-> writable_at segs mem2 a)) /\
res_ok A2 (rb_malloc b n)).
Proof.
intros HMA STK sp0 FP L A mem md Lc Ac regs_c memc mdc n b HJ Hid Ha0 HRb HRm Hra Hal16 Hlo Hhi Htp.
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
eapply SR_mono; [eapply (malloc_SR_res B MR HMA); [exact Hpre | exact Ha0 | exact HRb | exact HRm]|].
intros c' (p0 & A2 & tr & Hcp & HL & HRES).
destruct (cg_malloc_post STK sp0 FP L A mem md Lc Ac regs_c memc mdc n b p0 A2 tr c' HJ Hid Hlo Hhi Hcp HL HRES)
as (L2 & regs2 & mem2 & md2 & res & H). exists L2, A2, regs2, mem2, md2, res. exact H.
Qed.
Theorem cg_malloc_g_res : malloc_realizes_g B MR ->
forall STK sp0 FP L A mem md Lc Ac regs_c memc mdc n g b,
journal B MR STK sp0 FP L A mem md Lc Ac memc mdc ->
st_init_done Ac = true ->
getr regs_c 10 = Z_to_bv 64 n -> res_ok Ac b -> room b n ->
YK0s.ret_ok (getr regs_c 1) -> spZ regs_c mod 16 = 0 ->
sp0 - STK <= spZ regs_c - ALLOC_STACK -> spZ regs_c <= sp0 ->
getr regs_c 4 = Z_to_bv 64 (ms_tp B) ->
word_mem segs memc (ms_guard B) g ->
SR segs (mkCfg (mkst regs_c (Z_to_bv 64 (ms_malloc B)) memc (seg_rom segs)) mdc)
(fun c' => exists L2 A2 regs2 mem2 md2 (res : Z),
c' = mkCfg (mkst regs2 (getr regs_c 1) mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved regs_c regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
(res <> 0 /\ res mod 16 = 0 /\
(exists b1 b2, blocks L2 A2 = b1 ++ (res, n) :: b2 /\ blocks Lc Ac = b1 ++ b2) /\
(forall blc i, In (res, n) blc -> 0 <= i < n -> wr_byte STK sp0 FP (blocks L A) blc (res + i))) /\
(forall a m i, In (a, m) (blocks Lc Ac) -> 0 <= i < m ->
mbyte segs mem2 (a + i) = mbyte segs memc (a + i)) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs_c - ALLOC_STACK <= a < spZ regs_c) ->
mbyte segs mem2 a = mbyte segs memc a /\ (writable_at segs memc a <-> writable_at segs mem2 a)) /\
res_ok A2 (rb_malloc b n) /\
word_mem segs mem2 (ms_guard B) g).
Proof.
intros HMA STK sp0 FP L A mem md Lc Ac regs_c memc mdc n g b HJ Hid Ha0 HRb HRm Hra Hal16 Hlo Hhi Htp Hg.
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
eapply SR_mono; [eapply (malloc_SR_res_g B MR HMA); [exact Hpre | exact Ha0 | exact Hg | exact HRb | exact HRm]|].
intros c' (p0 & A2 & tr & Hcp & [HL Hg2] & HRES).
destruct (cg_malloc_post STK sp0 FP L A mem md Lc Ac regs_c memc mdc n b p0 A2 tr c' HJ Hid Hlo Hhi Hcp HL HRES)
as (L2 & regs2 & mem2 & md2 & res & H). exists L2, A2, regs2, mem2, md2, res.
destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9). subst c'. cbn [cfg_ms ms_mem mkst] in Hg2.
split; [reflexivity|]. repeat (split; [assumption|]). exact Hg2.
Qed.
End d.
Section e.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis errno_low : errno_addr B + 4 <= alloc_ceiling.
Hypothesis IMG : img_laws B MR.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok (ms_segs B) tbl.
Local Notation segs := (ms_segs B).
Context {SK : sink_head}.
Lemma jfree_res : free_realizes B MR ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc a n (o : Z) spw tpw raw b,
st_ok segs E ss ms -> ss_pc ss = ms_free B -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
In (a, n) (blocks Lc Ac) -> res_ok Ac b ->
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
(writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x)) /\
res_ok A2 (rb_free b n)).
Proof.
intros HFR E ss ms STK sp0 FP L A mem md Lc Ac mdc a n o spw tpw raw b
HS Hpc Hrv HJ Hin HRb Ha0 Hsp HE2 Hspw Hal Hneg Hbud Htp Htpw Hra Hraw HFP.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof alloc_ceiling_val as Hac. assert (ALLOC_STACK = 8192) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. cbn [sv_denot]. rewrite HE2, Hspw. apply unsigned_lit_small. lia. }
rewrite (st_ok_mkst segs E ss ms HS Hrv), Hpc.
apply blocks_In in Hin as (p & Hp & Hpin).
eapply SR_mono.
{ eapply (cg_free_res B MR LAWS errno_low IMG HFR STK sp0 FP L A mem md Lc Ac (ms_regs ms) (ms_mem ms) mdc p n b HJ Hpin HRb).
- rewrite Hp. exact Ha0.
- rewrite Hra. exact Hraw.
- rewrite Hsp'. rewrite Z.add_mod, Hal16, Hal by lia. reflexivity.
- rewrite Hsp'. lia.
- rewrite Hsp'. lia.
- rewrite Htp. exact Htpw.
- rewrite Hp. exact HFP. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi & _ & HRES).
exists L2, A2, regs2, mem2, md2. rewrite Hra. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
rewrite Hp in Hrm. split; [exact Hrm|]. split; [exact Hkeep|]. split; [|exact HRES].
intros x Hx Hnx. apply Hhi; [exact Hx|]. rewrite Hsp'. exact Hnx.
Qed.
Lemma jmalloc_res : malloc_realizes B MR ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc n (o : Z) spw tpw raw b,
st_ok segs E ss ms -> ss_pc ss = ms_malloc B -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
st_init_done Ac = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 n -> res_ok Ac b -> room b n ->
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
(res <> 0 /\ res mod 16 = 0 /\
(exists b1 b2, blocks L2 A2 = b1 ++ (res, n) :: b2 /\ blocks Lc Ac = b1 ++ b2) /\
(forall blc i, In (res, n) blc -> 0 <= i < n -> wr_byte STK sp0 FP (blocks L A) blc (res + i))) /\
(forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m ->
mbyte segs mem2 (b + i) = mbyte segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 + o - ALLOC_STACK <= x < sp0 + o) ->
mbyte segs mem2 x = mbyte segs (ms_mem ms) x /\
(writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x)) /\
res_ok A2 (rb_malloc b n)).
Proof.
intros HMA E ss ms STK sp0 FP L A mem md Lc Ac mdc n o spw tpw raw b
HS Hpc Hrv HJ Hid Ha0 HRb HRm Hsp HE2 Hspw Hal Hneg Hbud Htp Htpw Hra Hraw.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof alloc_ceiling_val as Hac. assert (ALLOC_STACK = 8192) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. cbn [sv_denot]. rewrite HE2, Hspw. apply unsigned_lit_small. lia. }
rewrite (st_ok_mkst segs E ss ms HS Hrv), Hpc.
eapply SR_mono.
{ eapply (cg_malloc_res B MR LAWS errno_low IMG HMA STK sp0 FP L A mem md Lc Ac (ms_regs ms) (ms_mem ms) mdc n b HJ Hid Ha0 HRb HRm).
- rewrite Hra. exact Hraw.
- rewrite Hsp'. rewrite Z.add_mod, Hal16, Hal by lia. reflexivity.
- rewrite Hsp'. lia.
- rewrite Hsp'. lia.
- rewrite Htp. exact Htpw. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hr10 & Hres & Hkeep & Hhi & HRES).
exists L2, A2, regs2, mem2, md2, res. rewrite Hra. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|].
split; [exact HP2|]. split; [exact Hr10|]. split; [exact Hres|]. split; [exact Hkeep|]. split; [|exact HRES].
intros x Hx Hnx. apply Hhi; [exact Hx|]. rewrite Hsp'. exact Hnx.
Qed.
Lemma jmalloc_sub_g_res : malloc_realizes_g B MR ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc n (o : Z) spw tpw raw g b,
st_ok segs E ss ms -> ss_pc ss = ms_malloc B -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
st_init_done Ac = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 n -> 0 < n -> res_ok Ac b -> room b n ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ALLOC_STACK - o <= STK ->
getr (ms_regs ms) 4 = tpw -> tpw = Z_to_bv 64 (ms_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
word_mem segs (ms_mem ms) (ms_guard B) g ->
SR segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2 (res : Z),
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
journal B MR ALLOC_STACK (sp0 + o) [] Lc Ac (ms_mem ms) mdc L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved (ms_regs ms) regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
(res <> 0 /\ res mod 16 = 0 /\
(exists b1 b2, blocks L2 A2 = b1 ++ (res, n) :: b2 /\ blocks Lc Ac = b1 ++ b2) /\
~ In (res, n) (blocks Lc Ac) /\ 4096 <= res /\ res + n <= alloc_ceiling) /\
(forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m ->
mbyte segs mem2 (b + i) = mbyte segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 + o - ALLOC_STACK <= x < sp0 + o) ->
mbyte segs mem2 x = mbyte segs (ms_mem ms) x /\
(writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x)) /\
res_ok A2 (rb_malloc b n) /\
word_mem segs mem2 (ms_guard B) g).
Proof.
intros HMA E ss ms STK sp0 FP L A mem md Lc Ac mdc n o spw tpw raw g b
HS Hpc Hrv HJ Hid Ha0 Hn HRb HRm Hsp HE2 Hspw Hal Hneg Hbud Htp Htpw Hra Hraw Hg.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof alloc_ceiling_val as Hac. assert (ALLOC_STACK = 8192) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. cbn [sv_denot]. rewrite HE2, Hspw. apply unsigned_lit_small. lia. }
assert (Hal16' : spZ (ms_regs ms) mod 16 = 0) by (rewrite Hsp'; rewrite Z.add_mod, Hal16, Hal by lia; reflexivity).
assert (HPRE1 : YI04.fn_pre B MR ALLOC_STACK Lc Ac (ms_regs ms) (ms_mem ms) mdc).
{ apply (fn_pre_of_journal B MR STK sp0 FP L A mem md Lc Ac (ms_regs ms) (ms_mem ms) mdc ALLOC_STACK HJ);
[rewrite Hra; exact Hraw | exact Hal16' | lia | rewrite Hsp'; lia | rewrite Hsp'; lia | rewrite Htp; exact Htpw]. }
pose proof (journal_init B MR ALLOC_STACK [] Lc Ac (ms_regs ms) (ms_mem ms) mdc HPRE1) as HJ1.
rewrite Hsp' in HJ1.
rewrite (st_ok_mkst segs E ss ms HS Hrv), Hpc.
eapply SR_mono.
{ eapply (cg_malloc_g_res B MR LAWS errno_low IMG HMA ALLOC_STACK (sp0 + o) [] Lc Ac (ms_mem ms) mdc Lc Ac (ms_regs ms) (ms_mem ms) mdc n g b HJ1 Hid Ha0 HRb HRm).
- rewrite Hra. exact Hraw.
- exact Hal16'.
- rewrite Hsp'. lia.
- rewrite Hsp'. lia.
- rewrite Htp. exact Htpw.
- exact Hg. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hr10 & Hres & Hkeep & Hhi & HRES & Hg2).
exists L2, A2, regs2, mem2, md2, res. rewrite Hra. split; [reflexivity|]. split.
{ eapply (journal_sub B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ALLOC_STACK (sp0 + o) [] L2 A2 mem2 md2 HJ HJ2); [lia | lia |].
intros x (r & [] & _). }
split; [exact HJ2|]. split; [exact Hid2|]. split; [exact HP2|]. split; [exact Hr10|]. split.
{ destruct Hres as (Hnz & Hm16 & (b1 & b2 & HB2 & HBc) & Wp).
assert (Hin2 : In (res, n) (blocks L2 A2)) by (rewrite HB2; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range B MR LAWS L2 A2 mem2 md2 res n (proj1 HJ2) Hin2 ltac:(lia)) as (R0 & R1 & _).
split; [exact Hnz|]. split; [exact Hm16|]. split; [exists b1, b2; auto|]. split; [|lia].
intros Hold. destruct (Wp [(res, n)] 0 ltac:(left; reflexivity) ltac:(lia)) as [Hstk | [((xr & [] & _) & _) | (bb & m & [<-|[]] & Hnot & _)]].
- lia.
- exact (Hnot Hold). }
split; [exact Hkeep|]. split; [|split; [exact HRES | exact Hg2]].
intros x Hx Hnx. apply Hhi; [exact Hx|]. rewrite Hsp'. exact Hnx.
Qed.
Lemma jmalloc_sub_res : malloc_realizes B MR ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc n (o : Z) spw tpw raw b,
st_ok segs E ss ms -> ss_pc ss = ms_malloc B -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
st_init_done Ac = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 n -> 0 < n -> res_ok Ac b -> room b n ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ALLOC_STACK - o <= STK ->
getr (ms_regs ms) 4 = tpw -> tpw = Z_to_bv 64 (ms_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SR segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2 (res : Z),
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
journal B MR ALLOC_STACK (sp0 + o) [] Lc Ac (ms_mem ms) mdc L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved (ms_regs ms) regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
(res <> 0 /\ res mod 16 = 0 /\
(exists b1 b2, blocks L2 A2 = b1 ++ (res, n) :: b2 /\ blocks Lc Ac = b1 ++ b2) /\
~ In (res, n) (blocks Lc Ac) /\ 4096 <= res /\ res + n <= alloc_ceiling) /\
(forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m ->
mbyte segs mem2 (b + i) = mbyte segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 + o - ALLOC_STACK <= x < sp0 + o) ->
mbyte segs mem2 x = mbyte segs (ms_mem ms) x /\
(writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x)) /\
res_ok A2 (rb_malloc b n)).
Proof.
intros HMA E ss ms STK sp0 FP L A mem md Lc Ac mdc n o spw tpw raw b
HS Hpc Hrv HJ Hid Ha0 Hn HRb HRm Hsp HE2 Hspw Hal Hneg Hbud Htp Htpw Hra Hraw.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof alloc_ceiling_val as Hac. assert (ALLOC_STACK = 8192) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. cbn [sv_denot]. rewrite HE2, Hspw. apply unsigned_lit_small. lia. }
assert (Hal16' : spZ (ms_regs ms) mod 16 = 0) by (rewrite Hsp'; rewrite Z.add_mod, Hal16, Hal by lia; reflexivity).
assert (HPRE1 : YI04.fn_pre B MR ALLOC_STACK Lc Ac (ms_regs ms) (ms_mem ms) mdc).
{ apply (fn_pre_of_journal B MR STK sp0 FP L A mem md Lc Ac (ms_regs ms) (ms_mem ms) mdc ALLOC_STACK HJ);
[rewrite Hra; exact Hraw | exact Hal16' | lia | rewrite Hsp'; lia | rewrite Hsp'; lia | rewrite Htp; exact Htpw]. }
pose proof (journal_init B MR ALLOC_STACK [] Lc Ac (ms_regs ms) (ms_mem ms) mdc HPRE1) as HJ1.
rewrite Hsp' in HJ1.
rewrite (st_ok_mkst segs E ss ms HS Hrv), Hpc.
eapply SR_mono.
{ eapply (cg_malloc_res B MR LAWS errno_low IMG HMA ALLOC_STACK (sp0 + o) [] Lc Ac (ms_mem ms) mdc Lc Ac (ms_regs ms) (ms_mem ms) mdc n b HJ1 Hid Ha0 HRb HRm).
- rewrite Hra. exact Hraw.
- exact Hal16'.
- rewrite Hsp'. lia.
- rewrite Hsp'. lia.
- rewrite Htp. exact Htpw. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hr10 & Hres & Hkeep & Hhi & HRES).
exists L2, A2, regs2, mem2, md2, res. rewrite Hra. split; [reflexivity|]. split.
{ eapply (journal_sub B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ALLOC_STACK (sp0 + o) [] L2 A2 mem2 md2 HJ HJ2); [lia | lia |].
intros x (r & [] & _). }
split; [exact HJ2|]. split; [exact Hid2|]. split; [exact HP2|]. split; [exact Hr10|]. split.
{ destruct Hres as (Hnz & Hm16 & (b1 & b2 & HB2 & HBc) & Wp).
assert (Hin2 : In (res, n) (blocks L2 A2)) by (rewrite HB2; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range B MR LAWS L2 A2 mem2 md2 res n (proj1 HJ2) Hin2 ltac:(lia)) as (R0 & R1 & _).
split; [exact Hnz|]. split; [exact Hm16|]. split; [exists b1, b2; auto|]. split; [|lia].
intros Hold. destruct (Wp [(res, n)] 0 ltac:(left; reflexivity) ltac:(lia)) as [Hstk | [((xr & [] & _) & _) | (bb & m & [<-|[]] & Hnot & _)]].
- lia.
- exact (Hnot Hold). }
split; [exact Hkeep|]. split; [|exact HRES].
intros x Hx Hnx. apply Hhi; [exact Hx|]. rewrite Hsp'. exact Hnx.
Qed.
Lemma jfree_sub_res : free_realizes B MR ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc a n (o : Z) spw tpw raw b,
st_ok segs E ss ms -> ss_pc ss = ms_free B -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
In (a, n) (blocks Lc Ac) -> 0 < n -> res_ok Ac b ->
getr (ms_regs ms) 10 = Z_to_bv 64 a ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ALLOC_STACK - o <= STK ->
getr (ms_regs ms) 4 = tpw -> tpw = Z_to_bv 64 (ms_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
(forall i, 0 <= i < n -> inFP FP (a + i)) ->
SR segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
journal B MR ALLOC_STACK (sp0 + o) [(a, a + n)] Lc Ac (ms_mem ms) mdc L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\
rm1 (a, n) (blocks Lc Ac) (blocks L2 A2) /\
(forall b m i, In (b, m) (blocks L2 A2) -> 0 <= i < m ->
mbyte segs mem2 (b + i) = mbyte segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 + o - ALLOC_STACK <= x < sp0 + o) ->
mbyte segs mem2 x = mbyte segs (ms_mem ms) x /\
(writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x)) /\
res_ok A2 (rb_free b n)).
Proof.
intros HFR E ss ms STK sp0 FP L A mem md Lc Ac mdc a n o spw tpw raw b
HS Hpc Hrv HJ Hin Hn0 HRb Ha0 Hsp HE2 Hspw Hal Hneg Hbud Htp Htpw Hra Hraw HFP.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof alloc_ceiling_val as Hac. assert (ALLOC_STACK = 8192) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. cbn [sv_denot]. rewrite HE2, Hspw. apply unsigned_lit_small. lia. }
assert (Hal16' : spZ (ms_regs ms) mod 16 = 0) by (rewrite Hsp'; rewrite Z.add_mod, Hal16, Hal by lia; reflexivity).
assert (HPRE1 : YI04.fn_pre B MR ALLOC_STACK Lc Ac (ms_regs ms) (ms_mem ms) mdc).
{ apply (fn_pre_of_journal B MR STK sp0 FP L A mem md Lc Ac (ms_regs ms) (ms_mem ms) mdc ALLOC_STACK HJ);
[rewrite Hra; exact Hraw | exact Hal16' | lia | rewrite Hsp'; lia | rewrite Hsp'; lia | rewrite Htp; exact Htpw]. }
pose proof (journal_init B MR ALLOC_STACK [(a, a + n)] Lc Ac (ms_regs ms) (ms_mem ms) mdc HPRE1) as HJ1.
rewrite Hsp' in HJ1.
rewrite (st_ok_mkst segs E ss ms HS Hrv), Hpc.
pose proof Hin as Hin0. apply blocks_In in Hin as (p & Hp & Hpin).
eapply SR_mono.
{ eapply (cg_free_res B MR LAWS errno_low IMG HFR ALLOC_STACK (sp0 + o) [(a, a + n)] Lc Ac (ms_mem ms) mdc Lc Ac (ms_regs ms) (ms_mem ms) mdc p n b HJ1 Hpin HRb).
- rewrite Hp. exact Ha0.
- rewrite Hra. exact Hraw.
- exact Hal16'.
- rewrite Hsp'. lia.
- rewrite Hsp'. lia.
- rewrite Htp. exact Htpw.
- rewrite Hp. intros _ i Hi. exists (a, a + n). split; [left; reflexivity | cbn [fst snd]; lia]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi & _ & HRES).
exists L2, A2, regs2, mem2, md2. rewrite Hra. split; [reflexivity|]. split.
{ eapply (journal_sub B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ALLOC_STACK (sp0 + o) [(a, a + n)] L2 A2 mem2 md2 HJ HJ2); [lia | lia |].
intros x (r & [<-|[]] & Hx). cbn [fst snd] in Hx. split; [replace x with (a + (x - a)) by lia; apply HFP; lia|].
destruct (heap_blocks B MR LAWS Lc Ac (ms_mem ms) mdc a n (x - a) HH Hin0 ltac:(lia)) as (_ & _ & Hc & _). lia. }
split; [exact HJ2|]. split; [exact HP2|].
rewrite Hp in Hrm. split; [exact Hrm|]. split; [exact Hkeep|]. split; [|exact HRES].
intros x Hx Hnx. apply Hhi; [exact Hx|]. rewrite Hsp'. exact Hnx.
Qed.
End e.
End c.
