(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02
YI06 UI5b YI09 YI08 YI0r YI0o UI1w YI05.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Lemma jfree_at_res :
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw b,
st_ok ubs0segs E ss ms -> ss_pc ss = ubs0_A_free -> ss_resv ss = None ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
In (a, n) (blocks Lc Ac) -> res_ok Ac b ->
getr (ms_regs ms) 10 = Z_to_bv 64 a ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> 0 <= spc < 2 ^ 64 -> spc mod 16 = 0 ->
sp0 - STK <= spc - ALLOC_STACK -> spc <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
(In (a, n) (blocks L A) -> forall i, 0 <= i < n -> inFP FP (a + i)) ->
SR ubs0segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\
rm1 (a, n) (blocks Lc Ac) (blocks L2 A2) /\
(forall b' m i, In (b', m) (blocks L2 A2) -> 0 <= i < m -> mbyte ubs0segs mem2 (b' + i) = mbyte ubs0segs (ms_mem ms) (b' + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - ALLOC_STACK <= x < spc) ->
mbyte ubs0segs mem2 x = mbyte ubs0segs (ms_mem ms) x /\ (writable_at ubs0segs (ms_mem ms) x <-> writable_at ubs0segs mem2 x)) /\
st_init_done A2 = true /\ res_ok A2 (rb_free b n)).
Proof using IMG LAWS.
intros E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw b HS Hpc Hrv HJ Hin HRb Ha0 Hsp Hspc Hal Hlo Hhi Htp Hra Hraw HFP.
assert (Hsp' : spZ (ms_regs ms) = spc) by (unfold spZ; rewrite Hsp; apply unsigned_lit_small; exact Hspc).
rewrite (st_ok_mkst ubs0segs E ss ms HS Hrv), Hpc.
apply blocks_In in Hin as (p & Hp & Hpin).
eapply SR_mono.
{ eapply (cg_free_res ubs0_msyms MR LAWS ubs0_errno_low IMG (aa_free API) STK sp0 FP L A mem md Lc Ac (ms_regs ms) (ms_mem ms) mdc p n b HJ Hpin HRb).
- rewrite Hp. exact Ha0.
- rewrite Hra. exact Hraw.
- rewrite Hsp'. exact Hal.
- rewrite Hsp'. exact Hlo.
- rewrite Hsp'. exact Hhi.
- exact Htp.
- rewrite Hp. exact HFP. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2 & Hid2 & HR2).
exists L2, A2, regs2, mem2, md2. rewrite Hra. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
rewrite Hp in Hrm. split; [exact Hrm|]. split; [exact Hkeep|]. split; [| split; [exact Hid2 | exact HR2]].
intros x Hx Hnx. apply Hhi2; [exact Hx|]. rewrite Hsp'. exact Hnx.
Qed.
Lemma jfree_tok_res :
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw b,
st_ok ubs0segs E ss ms -> ss_pc ss = ubs0_A_free -> ss_resv ss = None ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc -> st_init_done Ac = true ->
(In (a, n) (blocks Lc Ac) /\ ftok FP (blocks L A) (a, n)) -> res_ok Ac b ->
getr (ms_regs ms) 10 = Z_to_bv 64 a ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> 0 <= spc < 2 ^ 64 -> spc mod 16 = 0 ->
sp0 - STK <= spc - ALLOC_STACK -> spc <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SR ubs0segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved (ms_regs ms) regs2 /\
rm1 (a, n) (blocks Lc Ac) (blocks L2 A2) /\
(forall b' m i, In (b', m) (blocks L2 A2) -> 0 <= i < m -> mbyte ubs0segs mem2 (b' + i) = mbyte ubs0segs (ms_mem ms) (b' + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - ALLOC_STACK <= x < spc) ->
mbyte ubs0segs mem2 x = mbyte ubs0segs (ms_mem ms) x /\ (writable_at ubs0segs (ms_mem ms) x <-> writable_at ubs0segs mem2 x)) /\
res_ok A2 (rb_free b n)).
Proof using IMG LAWS.
intros E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw b HS Hpc Hrv HJ Hid [Hin Htok] HRb Ha0 Hsp Hspc Hal Hlo Hhi Htp Hra Hraw.
eapply SR_mono.
{ eapply (jfree_at_res E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw b);
[ exact HS | exact Hpc | exact Hrv | exact HJ | exact Hin | exact HRb | exact Ha0 | exact Hsp | exact Hspc | exact Hal | exact Hlo | exact Hhi
| exact Htp | exact Hra | exact Hraw | ].
intros H0 i Hi. exact (Htok H0 i Hi). }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2 & Hid2 & HR2).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [exact HP2|].
split; [exact Hrm|]. split; [exact Hkeep|]. split; [exact Hhi2 | exact HR2].
Qed.
Lemma jmalloc_at_res :
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc n spc raw b,
st_ok ubs0segs E ss ms -> ss_pc ss = ubs0_A_malloc -> ss_resv ss = None ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
st_init_done Ac = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 n -> res_ok Ac b -> room b n ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> 0 <= spc < 2 ^ 64 -> spc mod 16 = 0 ->
sp0 - STK <= spc - ALLOC_STACK -> spc <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SR ubs0segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2 (res : Z),
c' = mkCfg (mkst regs2 raw mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved (ms_regs ms) regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
(res <> 0 /\ res mod 16 = 0 /\
(exists b1 b2, blocks L2 A2 = b1 ++ (res, n) :: b2 /\ blocks Lc Ac = b1 ++ b2) /\
(forall blc i, In (res, n) blc -> 0 <= i < n -> wr_byte STK sp0 FP (blocks L A) blc (res + i))) /\
(forall b' m i, In (b', m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs0segs mem2 (b' + i) = mbyte ubs0segs (ms_mem ms) (b' + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - ALLOC_STACK <= x < spc) ->
mbyte ubs0segs mem2 x = mbyte ubs0segs (ms_mem ms) x /\ (writable_at ubs0segs (ms_mem ms) x <-> writable_at ubs0segs mem2 x)) /\
res_ok A2 (rb_malloc b n)).
Proof using IMG LAWS.
intros E ss ms STK sp0 FP L A mem md Lc Ac mdc n spc raw b HS Hpc Hrv HJ Hid Ha0 HRb HRm Hsp Hspc Hal Hlo Hhi Htp Hra Hraw.
assert (Hsp' : spZ (ms_regs ms) = spc) by (unfold spZ; rewrite Hsp; apply unsigned_lit_small; exact Hspc).
rewrite (st_ok_mkst ubs0segs E ss ms HS Hrv), Hpc.
eapply SR_mono.
{ eapply (cg_malloc_res ubs0_msyms MR LAWS ubs0_errno_low IMG (aa_malloc API) STK sp0 FP L A mem md Lc Ac (ms_regs ms) (ms_mem ms) mdc n b HJ Hid Ha0 HRb HRm).
- rewrite Hra. exact Hraw.
- rewrite Hsp'. exact Hal.
- rewrite Hsp'. exact Hlo.
- rewrite Hsp'. exact Hhi.
- exact Htp. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hr10 & Hres & Hkeep & Hhi2 & HR2).
exists L2, A2, regs2, mem2, md2, res. rewrite Hra. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|].
split; [exact HP2|]. split; [exact Hr10|]. split; [exact Hres|]. split; [exact Hkeep|]. split; [|exact HR2].
intros x Hx Hnx. apply Hhi2; [exact Hx|]. rewrite Hsp'. exact Hnx.
Qed.
Lemma res_range_of_post : forall L2 A2 mem2 md2 res n,
heap_ok MR L2 A2 mem2 md2 -> 0 < n ->
(exists b1 b2, blocks L2 A2 = b1 ++ (res, n) :: b2 /\ True) \/ In (res, n) (blocks L2 A2) ->
4096 <= res /\ res + n <= alloc_ceiling /\ res mod 16 = 0.
Proof using LAWS.
intros L2 A2 mem2 md2 res n HH Hn Hin.
assert (Hin' : In (res, n) (blocks L2 A2)).
{ destruct Hin as [(b1 & b2 & HB & _) | Hin]; [| exact Hin]. rewrite HB. apply in_app_iff. right. left. reflexivity. }
exact (heap_blocks_range _ _ LAWS _ _ _ _ res n HH Hin' Hn).
Qed.
End S.
End c.
