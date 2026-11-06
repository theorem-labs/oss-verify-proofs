(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI06 YI08 YI0t.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Export YI0m.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI06.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section J.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis errno_low : errno_addr B + 4 <= alloc_ceiling.
Hypothesis IMG : img_laws B MR.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok (ms_segs B) tbl.
Context {SK : sink_head}.
Local Notation memset_spec := (YI0m.memset_spec B).
Local Notation segs := (ms_segs B).
Lemma wr_ok_cons_win : forall E r rs STK sp0 FP bl0 blc n b,
r_base r = Some n -> bv_unsigned (ew E n) = b ->
(r_wlo r < r_whi r -> sp0 - STK <= b + r_wlo r /\ b + r_whi r <= sp0) ->
wr_ok E rs STK sp0 FP bl0 blc -> wr_ok E (r :: rs) STK sp0 FP bl0 blc.
Proof.
intros E r rs STK sp0 FP bl0 blc n b Hb Hn Hw H a (r' & [<-|Hin] & Ha).
- left. rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha. specialize (Hw ltac:(lia)). lia.
- apply H. exists r'. auto.
Qed.
Lemma journal_sub_gen : forall STK sp0 FP L A mem md Lc Ac memc mdc STK1 sp1 FP1 L2 A2 mem2 md2,
journal B MR STK sp0 FP L A mem md Lc Ac memc mdc ->
journal B MR STK1 sp1 FP1 Lc Ac memc mdc L2 A2 mem2 md2 ->
sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
(forall a, inFP FP1 a -> (inFP FP a /\ a < alloc_ceiling) \/
(exists b n, In (b, n) (blocks Lc Ac) /\ ~ In (b, n) (blocks L A) /\ b <= a < b + n)) ->
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2.
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc STK1 sp1 FP1 L2 A2 mem2 md2
(HH & Hvm & Hhigh & Hblk & Hgone & Hst & Herr & Himg)
(HH2 & Hvm2 & Hhigh2 & Hblk2 & Hgone2 & Hst2 & Herr2 & Himg2) Hlo Hhi HF.
assert (HT : sink_open_fp FP1 -> sink_open_fp FP).
{ intros Ho. destruct (HF _ Ho) as [[H _] | (b & n & Hb & _ & Hr)]; [exact H|]. exfalso.
destruct (heap_blocks_range B MR LAWS Lc Ac memc mdc b n HH Hb ltac:(lia)) as (H4096 & _). lia. }
pose proof (proj1 alloc_ceiling_val) as Hac.
destruct Hst as (Hal & Hstk0 & Hceil & H63 & Hstw). destruct Hst2 as (Hal2 & Hstk2 & Hceil2 & H632 & Hstw2).
assert (HF' : forall a n i, In (a, n) (blocks L A) -> In (a, n) (blocks Lc Ac) -> 0 <= i < n ->
inFP FP1 (a + i) -> inFP FP (a + i)).
{ intros a n i H0 Hc Hi Hf. destruct (HF _ Hf) as [[H _] | (b & m & Hbin & Hbn & Hr)]; [exact H|].
exfalso. assert (Hne : (b, m) <> (a, n)) by (intros E; rewrite E in Hbn; exact (Hbn H0)).
destruct (heap_sep_in2 B MR LAWS Lc Ac memc mdc (b, m) (a, n) HH Hbin Hc Hne) as [Hd|Hd]; cbn [fst snd] in Hd; lia. }
split; [exact HH2|]. split.
{ eapply os_step_trans; [exact HT | exact Hvm | exact Hvm2]. }
split.
{ intros a Ha Hna. destruct (Hhigh2 a Ha ltac:(lia)) as [E1 E2]. destruct (Hhigh a Ha Hna) as [F1 F2].
split; [rewrite E1; exact F1 | rewrite F2; exact E2]. }
split.
{ intros a n i H1 H2 Hi Hnf.
destruct (in_dec zz_eq_dec (a, n) (blocks Lc Ac)) as [Hc|Hc].
- rewrite <- (Hblk a n i H1 Hc Hi Hnf). apply (Hblk2 a n i Hc H2 Hi).
intros Hf. exact (Hnf (HF' a n i H1 Hc Hi Hf)).
- exfalso. exact (Hnf (Hgone a n i H1 Hc Hi)). }
split.
{ intros a n i H1 H2 Hi.
destruct (in_dec zz_eq_dec (a, n) (blocks Lc Ac)) as [Hc|Hc]; [|exact (Hgone a n i H1 Hc Hi)].
apply (HF' a n i H1 Hc Hi). exact (Hgone2 a n i Hc H2 Hi). }
split.
{ split; [exact Hal|]. split; [exact Hstk0|]. split; [exact Hceil|]. split; [exact H63|].
intros a Ha. destruct (Z_lt_le_dec a (sp1 - STK1)) as [Hb|Hb].
- apply (proj1 (proj2 (Hhigh2 a ltac:(lia) ltac:(lia)))). apply Hstw. exact Ha.
- destruct (Z_lt_le_dec a sp1) as [Hb2|Hb2].
+ apply Hstw2. lia.
+ apply (proj1 (proj2 (Hhigh2 a ltac:(lia) ltac:(lia)))). apply Hstw. exact Ha. }
split; [exact Herr2 | eapply img_kept_trans; [exact Himg | eapply img_kept_mono; [exact HT | exact Himg2]]].
Qed.
Lemma memset_clob_out : forall r : reg, reg_in r MEMSET_CLOB = false ->
r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\ r <> 15%bv /\ r <> 16%bv.
Proof. intros r Hr. repeat split; intros ->; vm_compute in Hr; discriminate. Qed.
Lemma jmemset : forall pcm, memset_spec pcm ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc d c n raw,
st_ok segs E ss ms -> ss_pc ss = pcm -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 11 = Z_to_bv 64 c -> getr (ms_regs ms) 12 = Z_to_bv 64 n ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
0 <= n -> 0 <= d -> d + n < 2 ^ 64 -> 0 <= c < 256 ->
(forall i, 0 <= i < n -> present (ms_mem ms) (d + i)) ->
(forall a, d <= a < d + n -> wr_byte STK sp0 FP (blocks L A) (blocks Lc Ac) a) ->
SR segs (mkCfg ms mdc)
(fun c' => exists regs2 mem2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) mdc /\
journal B MR STK sp0 FP L A mem md Lc Ac mem2 mdc /\
getr regs2 10 = Z_to_bv 64 d /\
(forall r, reg_in r MEMSET_CLOB = false -> getr regs2 r = getr (ms_regs ms) r) /\
(forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> mem2 x = ms_mem ms x) /\
mem_grows (ms_mem ms) mem2 /\
(forall i, 0 <= i < n -> mbyte segs mem2 (d + i) = Some (Z_to_bv 8 c))).
Proof.
intros pcm HM E ss ms STK sp0 FP L A mem md Lc Ac mdc d c n raw HS Hpc Hrv HJ H10 H11 H12 H1 Hraw
Hn Hd Hdn Hc Hpd HW.
pose proof (store_ok_of_present B (ms_mem ms) (Z.to_nat n) d ltac:(intros i Hi; apply Hpd; lia) Hd ltac:(lia)) as Hst.
destruct (HM (Z_to_bv 64 d) (Z_to_bv 64 c) (Z_to_bv 64 n) (Z.to_nat n) (ms_mem ms) (seg_rom segs) (ms_regs ms) H10 H11 H12)
as (regs2 & Hms & Ha0 & Hfr).
{ rewrite unsigned_lit_small by lia. lia. }
{ exact Hst. }
{ rewrite unsigned_lit_small by lia. lia. }
rewrite (st_ok_mkst segs E ss ms HS Hrv), Hpc.
destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
eapply SR_msteps; [exact Hh | exact Hl | exact Hms |].
set (bs := repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 c) mod 256)) (Z.to_nat n)).
assert (Hlen : length bs = Z.to_nat n) by (subst bs; apply repeat_length).
apply SR_ret. exists regs2, (wbytes (ms_mem ms) (Z_to_bv 64 d) bs). rewrite H1, Hraw.
assert (Hout : forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> wbytes (ms_mem ms) (Z_to_bv 64 d) bs x = ms_mem ms x).
{ intros x Hx. destruct Hx as [Hx|Hx].
- apply wbytes_below; rewrite ?Hlen, unsigned_lit_small by lia; lia.
- apply wbytes_above. rewrite Hlen, unsigned_lit_small by lia. lia. }
split; [reflexivity|]. split.
{ eapply (journal_exec B MR LAWS IMG) with (W := fun a => d <= a < d + n); [exact HJ | | apply wbytes_grows | exact HW].
intros x Hx. apply Hout. lia. }
split; [exact Ha0|]. split.
{ intros r Hr. destruct (memset_clob_out r Hr) as (?&?&?&?&?&?). apply Hfr; assumption. }
split; [exact Hout|]. split; [apply wbytes_grows|].
intros i Hi. rewrite (wbytes_mbyte segs bs (ms_mem ms) d (d + i)) by (rewrite ?Hlen; lia).
rewrite ?Hlen.
replace ((d <=? d + i) && (d + i <? d + Z.of_nat (Z.to_nat n))) with true.
2:{ symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
subst bs. rewrite nth_error_repeat by lia. f_equal. f_equal.
rewrite unsigned_lit_small by lia. apply Z.mod_small. lia.
Qed.
Lemma jmalloc_at : malloc_realizes B MR ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc n spc raw,
st_ok segs E ss ms -> ss_pc ss = ms_malloc B -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
st_init_done Ac = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 62 ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> 0 <= spc < 2 ^ 64 -> spc mod 16 = 0 ->
sp0 - STK <= spc - ALLOC_STACK -> spc <= sp0 ->
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
(exists b1 b2, blocks L2 A2 = b1 ++ (res, n) :: b2 /\ blocks Lc Ac = b1 ++ b2) /\
(forall blc i, In (res, n) blc -> 0 <= i < n -> wr_byte STK sp0 FP (blocks L A) blc (res + i)))) /\
(forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m ->
mbyte segs mem2 (b + i) = mbyte segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - ALLOC_STACK <= x < spc) ->
mbyte segs mem2 x = mbyte segs (ms_mem ms) x /\
(writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x))).
Proof.
intros HMA E ss ms STK sp0 FP L A mem md Lc Ac mdc n spc raw
HS Hpc Hrv HJ Hid Ha0 Hn Hsp Hspc Hal Hlo Hhi Htp Hra Hraw.
assert (Hsp' : spZ (ms_regs ms) = spc).
{ unfold spZ. rewrite Hsp. apply unsigned_lit_small. exact Hspc. }
rewrite (st_ok_mkst segs E ss ms HS Hrv), Hpc.
eapply SR_mono.
{ eapply (cg_malloc B MR LAWS errno_low IMG HMA STK sp0 FP L A mem md Lc Ac (ms_regs ms) (ms_mem ms) mdc n HJ Hid Ha0 Hn).
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
Lemma jfree_at : free_realizes B MR ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw,
st_ok segs E ss ms -> ss_pc ss = ms_free B -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
In (a, n) (blocks Lc Ac) ->
getr (ms_regs ms) 10 = Z_to_bv 64 a ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> 0 <= spc < 2 ^ 64 -> spc mod 16 = 0 ->
sp0 - STK <= spc - ALLOC_STACK -> spc <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp B) ->
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
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - ALLOC_STACK <= x < spc) ->
mbyte segs mem2 x = mbyte segs (ms_mem ms) x /\
(writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x)) /\
st_init_done A2 = true).
Proof.
intros HFR E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw
HS Hpc Hrv HJ Hin Ha0 Hsp Hspc Hal Hlo Hhi Htp Hra Hraw HFP.
assert (Hsp' : spZ (ms_regs ms) = spc).
{ unfold spZ. rewrite Hsp. apply unsigned_lit_small. exact Hspc. }
rewrite (st_ok_mkst segs E ss ms HS Hrv), Hpc.
apply blocks_In in Hin as (p & Hp & Hpin).
eapply SR_mono.
{ eapply (cg_free B MR LAWS errno_low IMG HFR STK sp0 FP L A mem md Lc Ac (ms_regs ms) (ms_mem ms) mdc p n HJ Hpin).
- rewrite Hp. exact Ha0.
- rewrite Hra. exact Hraw.
- rewrite Hsp'. exact Hal.
- rewrite Hsp'. exact Hlo.
- rewrite Hsp'. exact Hhi.
- exact Htp.
- rewrite Hp. exact HFP. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2 & Hid2).
exists L2, A2, regs2, mem2, md2. rewrite Hra. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
rewrite Hp in Hrm. split; [exact Hrm|]. split; [exact Hkeep|]. split; [|exact Hid2].
intros x Hx Hnx. apply Hhi2; [exact Hx|]. rewrite Hsp'. exact Hnx.
Qed.
Lemma jfree_opt : free_realizes B MR -> free_null_realizes B ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw,
st_ok segs E ss ms -> ss_pc ss = ms_free B -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
(a = 0 \/ (In (a, n) (blocks Lc Ac) /\ ~ In (a, n) (blocks L A))) ->
getr (ms_regs ms) 10 = Z_to_bv 64 a ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> 0 <= spc < 2 ^ 64 -> spc mod 16 = 0 ->
sp0 - STK <= spc - ALLOC_STACK -> spc <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SR segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\
(a = 0 /\ blocks L2 A2 = blocks Lc Ac \/ a <> 0 /\ rm1 (a, n) (blocks Lc Ac) (blocks L2 A2)) /\
(forall b m i, In (b, m) (blocks L2 A2) -> 0 <= i < m ->
mbyte segs mem2 (b + i) = mbyte segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - ALLOC_STACK <= x < spc) ->
mbyte segs mem2 x = mbyte segs (ms_mem ms) x /\
(writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x))).
Proof.
intros HFR HFN E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw
HS Hpc Hrv HJ Ha Ha0 Hsp Hspc Hal Hlo Hhi Htp Hra Hraw.
destruct (Z.eq_dec a 0) as [Hz | Hnz].
- subst a. destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
eapply SR_mono; [eapply (jfree_null B HFN); try eassumption|].
intros c' ->. exists Lc, Ac, (ms_regs ms), (ms_mem ms), mdc.
split; [reflexivity|]. split; [exact HJ|]. split; [intros r Hr; reflexivity|].
split; [left; split; reflexivity|]. split; [intros; reflexivity|]. intros x _ _. split; [reflexivity | tauto].
- destruct Ha as [Hz | [Hin Hnot]]; [lia|].
eapply SR_mono; [eapply (jfree_at HFR); try eassumption; intros H0; exfalso; exact (Hnot H0)|].
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2 & _).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
split; [right; split; [exact Hnz | exact Hrm]|]. split; [exact Hkeep | exact Hhi2].
Qed.
Lemma journal_stack_w : forall STK sp0 FP L A mem md L' A' mem' md',
journal B MR STK sp0 FP L A mem md L' A' mem' md' -> forall a, sp0 - STK <= a < sp0 -> writable_at segs mem' a.
Proof. intros STK sp0 FP L A mem md L' A' mem' md' (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hw) & _) a Ha. apply Hw. exact Ha. Qed.
Lemma journal_heap : forall STK sp0 FP L A mem md L' A' mem' md',
journal B MR STK sp0 FP L A mem md L' A' mem' md' -> heap_ok MR L' A' mem' md'.
Proof. intros STK sp0 FP L A mem md L' A' mem' md' (HH & _). exact HH. Qed.
Lemma journal_mem_eq : forall STK sp0 FP L A mem md L' A' mem1 mem2 md',
journal B MR STK sp0 FP L A mem md L' A' mem1 md' -> (forall x, mem2 x = mem1 x) ->
journal B MR STK sp0 FP L A mem md L' A' mem2 md'.
Proof.
intros STK sp0 FP L A mem md L' A' mem1 mem2 md' HJ Heq.
eapply (journal_exec B MR LAWS IMG) with (W := fun _ => False); [exact HJ | intros x _; apply Heq | | intros a F; destruct F].
intros x Hx. rewrite Heq. exact Hx.
Qed.
End J.
End e.
