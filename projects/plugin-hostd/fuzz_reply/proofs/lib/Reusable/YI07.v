(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI07.v, with its module paths changed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO0e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI06 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Export YN00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition errno_rng (B : malloc_syms) (a : Z) : Prop := errno_addr B <= a < errno_addr B + 4.
Definition head_rng {SK : sink_head} (a : Z) : Prop := sk_ofl_head <= a < sk_ofl_head + 8.
Class sys_laws (B : malloc_syms) {SK : sink_head} : Prop := mkSysLaws {
sl_errno : forall a, errno_rng B a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE);
sl_head : forall a, head_rng a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE)
}.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis IMG : img_laws B MR.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok (ms_segs B) tbl.
Local Notation segs := (ms_segs B).
Context {SK : sink_head}.
Lemma SR_run_J_ecall : forall n E ss ss' ms STK sp0 FP L A mem md Lc Ac mdc Q,
st_ok segs E ss ms ->
sym_runN segs tbl n ss = (ss', RS_ecall) ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
wr_ok E (ss_mem ss) STK sp0 FP (blocks L A) (blocks Lc Ac) ->
(forall ms', st_ok_ecall segs E ss' ms' -> journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') -> mem_grows (ms_mem ms) (ms_mem ms') ->
SR segs (mkCfg ms' mdc) Q) ->
SR segs (mkCfg ms mdc) Q.
Proof.
intros n E ss ss' ms STK sp0 FP L A mem md Lc Ac mdc Q HS Hrun HJ Hwr Hk.
destruct (msteps_run_gen segs tbl tbl_ok n E ss ss' RS_ecall ms HS Hrun) as (ms' & Hms & HS' & Hfr).
destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
apply (SR_msteps segs ms ms' mdc Q Hh Hl Hms). apply Hk.
- exact HS'.
- eapply (journal_exec B MR LAWS IMG); [exact HJ | exact Hfr | apply (msteps_mem_grows segs); exact Hms | exact Hwr].
- exact Hfr.
- apply (msteps_mem_grows segs). exact Hms.
Qed.
Lemma journal_os_upd : forall STK sp0 FP L A mem md Lc Ac memc mdc fds' fs' pins',
journal B MR STK sp0 FP L A mem md Lc Ac memc mdc ->
sink_open_fp FP -> fds_rel (m_fds mdc) fds' -> fs_rel (m_fs mdc) fs' ->
(Fs.fs_sorted (m_fs mdc) = true -> Fs.fs_sorted fs' = true) ->
journal B MR STK sp0 FP L A mem md Lc Ac memc (os_upd (m_vmmaps mdc) fds' fs' pins' mdc).
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc fds' fs' pins' HJ Ho Hf Hs Hso.
destruct HJ as (HH & Hos & J3 & J4 & J5 & J6 & J7 & J8).
split; [|split; [|exact (conj J3 (conj J4 (conj J5 (conj J6 (conj J7 J8)))))]].
- destruct HH as (HM & HW & HBd). split; [|split; assumption].
destruct (mr_model B MR LAWS _ _ _ _ HM) as (Hh & Hl & Hmat).
apply (mr_frame B MR LAWS Lc Ac memc memc mdc _ HM); try reflexivity; auto.
intros p n i Hin Hi. exact (proj1 (mr_blocks B MR LAWS Lc Ac memc mdc p n i HM Hin Hi)).
- eapply os_step_trans_same; [exact Hos|]. apply os_step_intro; assumption.
Qed.
Context {SL : sys_laws B}.
Local Notation errno_rng := (errno_rng B).
Definition sys_rng (FP : list (Z * Z)) (a : Z) : Prop := errno_rng a \/ (sink_open_fp FP /\ head_rng a).
Lemma sys_rng_img : forall FP a, sys_rng FP a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE).
Proof. intros FP a [He | [_ Hh]]; [exact (sl_errno a He) | exact (sl_head a Hh)]. Qed.
Lemma sys_not_owned : forall FP L A mem md a, MR L A mem md -> sys_rng FP a -> ~ owned B L A a.
Proof.
intros FP L A mem md a HM Ha. destruct (sys_rng_img FP a Ha) as (Hi & Hs & Hc). intros [Ho | Ho]; [|exact (Hs Ho)].
exact (Hc (il_ctx IMG L A mem md a HM Hi Ho)).
Qed.
Lemma journal_exec_errno : forall STK sp0 FP L A mem md Lc Ac memc mdc memc' (W : Z -> Prop),
journal B MR STK sp0 FP L A mem md Lc Ac memc mdc ->
(forall x : word, ~ W (bv_unsigned x) -> memc' x = memc x) ->
mem_grows memc memc' ->
(forall a, W a -> wr_byte STK sp0 FP (blocks L A) (blocks Lc Ac) a \/ sys_rng FP a) ->
journal B MR STK sp0 FP L A mem md Lc Ac memc' mdc.
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc memc' W
(HH & Hvm & Hhigh & Hblk & Hgone & Hst & Herr & Himg) Hfr Hgr HW0.
pose proof alloc_ceiling_val as Hac.
destruct Hst as (Hal & Hstk0 & Hceil & H63 & Hstw).
assert (Hlowi : forall a, sys_rng FP a -> 0 <= a < alloc_ceiling).
{ intros a Ha. destruct (sys_rng_img FP a Ha) as (Hi & _). split; [|exact (il_low IMG a Hi)].
destruct Hi as [_ (sg & _ & Hr)]. pose proof (bv_unsigned_in_range _ (fst sg)). lia. }
assert (HW : forall a, W a -> ((sp0 - STK <= a < sp0) \/ (a < alloc_ceiling /\ ~ owned B Lc Ac a /\
exists b n, In (b, n) (blocks Lc Ac) /\ b <= a < b + n /\
(inFP FP a \/ ~ In (b, n) (blocks L A)))) \/ sys_rng FP a).
{ intros a Ha. destruct (HW0 a Ha) as [Hw | He]; [left | right; exact He].
exact (wr_byte_low B MR LAWS STK sp0 FP L A Lc Ac memc mdc a HH Hw). }
clear HW0.
assert (HWlow : forall a, W a -> a < sp0 /\ ~ owned B Lc Ac a).
{ intros a Ha. destruct (HW a Ha) as [[Hs | (Hc & Hno & _)] | He].
- split; [lia|]. intros Ho. pose proof (heap_owned_low B MR LAWS _ _ _ _ a HH Ho). lia.
- split; [lia | exact Hno].
- split; [pose proof (Hlowi a He); lia | exact (sys_not_owned FP _ _ _ _ a (proj1 HH) He)]. }
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
destruct (HW a HWa) as [[Hs | (Hc & _)] | He]; [exact (Hna Hs) | lia | pose proof (Hlowi a He); lia]. }
destruct (Hhigh a Ha Hna) as [H1 H2]. split.
- rewrite <- H1. apply mbyte_eq_of. exact E1.
- rewrite H2. apply writable_iff_of. exact E1. }
split.
{ intros a n i H1 H2 Hi Hnf. rewrite <- (Hblk a n i H1 H2 Hi Hnf). apply mbyte_eq_of.
destruct (heap_blocks B MR LAWS Lc Ac memc mdc a n i HH H2 Hi) as (_ & Hlo & Hhi & _).
apply Heqw; [lia|]. intros HWa.
destruct (HW _ HWa) as [[Hs | (_ & _ & b & m & Hbin & Hr & [Hfp | Hnot])] | He]; [lia | exact (Hnf Hfp) | |].
- assert (Hne : (b, m) <> (a, n)) by (intros E; rewrite E in Hnot; exact (Hnot H1)).
destruct (heap_sep_in2 B MR LAWS Lc Ac memc mdc (b, m) (a, n) HH Hbin H2 Hne) as [Hd|Hd]; cbn [fst snd] in Hd; lia.
-
apply blocks_In in H2 as (q & Hq & Hqin).
apply (il_blocks IMG Lc Ac memc mdc q n i (proj1 HH) Hqin Hi). rewrite Hq. exact (proj1 (sys_rng_img FP _ He)). }
split; [exact Hgone|]. split.
{ split; [exact Hal|]. split; [exact Hstk0|]. split; [exact Hceil|]. split; [exact H63|].
intros a Ha. eapply writable_at_grows; [exact Hgr|]. apply Hstw. exact Ha. }
split; [intros a Ha; eapply writable_at_grows; [exact Hgr|]; apply Herr; exact Ha|].
eapply img_kept_trans; [exact Himg|]. intros a Ha Hs Hc He Hk.
assert (E1 : memc' (Z_to_bv 64 a) = memc (Z_to_bv 64 a)).
{ pose proof (il_low IMG a Ha) as Hlow.
assert (Ha0 : 0 <= a).
{ destruct Ha as [_ (sg & _ & Hr)]. pose proof (bv_unsigned_in_range _ (fst sg)). lia. }
apply Heqw; [lia|]. intros HWa.
destruct (HW a HWa) as [[Hsk | (_ & _ & b & m & Hbin & Hr & _)] | [Hen | Hhd]]; [lia | | exact (He Hen) | exact (Hk Hhd)].
apply blocks_In in Hbin as (q & Hq & Hqin).
apply (il_blocks IMG Lc Ac memc mdc q m (a - b) (proj1 HH) Hqin ltac:(lia)). rewrite Hq.
replace (b + (a - b)) with a by lia. exact Ha. }
split; [apply mbyte_eq_of; exact E1 | apply writable_iff_of; exact E1].
Qed.
Definition wr_okE (E : env) (rs : smem) (STK sp0 : Z) (FP : list (Z * Z)) (bl0 blc : list (Z * Z)) : Prop :=
forall a, in_wrange E rs a -> wr_byte STK sp0 FP bl0 blc a \/ sys_rng FP a.
Lemma wr_okE_of_wr_ok : forall E rs STK sp0 FP bl0 blc, wr_ok E rs STK sp0 FP bl0 blc -> wr_okE E rs STK sp0 FP bl0 blc.
Proof. intros E rs STK sp0 FP bl0 blc H a Ha. left. exact (H a Ha). Qed.
Lemma wr_okE_nil : forall E STK sp0 FP bl0 blc, wr_okE E [] STK sp0 FP bl0 blc.
Proof. intros E STK sp0 FP bl0 blc a (r & Hin & _). destruct Hin. Qed.
Lemma wr_okE_cons_ok : forall E r rs STK sp0 FP bl0 blc,
wr_ok E [r] STK sp0 FP bl0 blc -> wr_okE E rs STK sp0 FP bl0 blc -> wr_okE E (r :: rs) STK sp0 FP bl0 blc.
Proof.
intros E r rs STK sp0 FP bl0 blc H1 H a (r' & [<-|Hin] & Ha).
- left. apply H1. exists r. split; [left; reflexivity | exact Ha].
- apply H. exists r'. auto.
Qed.
Lemma wr_okE_cons_errno : forall E r rs STK sp0 FP bl0 blc n,
r_base r = Some n -> bv_unsigned (ew E n) = ms_tp B -> ms_errno_off B <= r_wlo r -> r_whi r <= ms_errno_off B + 4 ->
wr_okE E rs STK sp0 FP bl0 blc -> wr_okE E (r :: rs) STK sp0 FP bl0 blc.
Proof.
intros E r rs STK sp0 FP bl0 blc n Hb Hn Hlo Hhi H a (r' & [<-|Hin] & Ha).
- right. left. rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha. unfold YI07.errno_rng, errno_addr. lia.
- apply H. exists r'. auto.
Qed.
Lemma wr_okE_cons_head : forall E r rs STK sp0 FP bl0 blc,
r_base r = None -> sink_open_fp FP -> sk_ofl_head <= r_wlo r -> r_whi r <= sk_ofl_head + 8 ->
wr_okE E rs STK sp0 FP bl0 blc -> wr_okE E (r :: rs) STK sp0 FP bl0 blc.
Proof.
intros E r rs STK sp0 FP bl0 blc Hb Hop Hlo Hhi H a (r' & [<-|Hin] & Ha).
- right. right. split; [exact Hop|]. rewrite Hb in Ha. cbn [base_val] in Ha. unfold head_rng. lia.
- apply H. exists r'. auto.
Qed.
Lemma SR_run_JE : forall n E ss ss' st ms STK sp0 FP L A mem md Lc Ac mdc Q,
st_ok segs E ss ms ->
sym_runN segs tbl n ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
wr_okE E (ss_mem ss) STK sp0 FP (blocks L A) (blocks Lc Ac) ->
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
- eapply journal_exec_errno; [exact HJ | exact Hfr | apply (msteps_mem_grows segs); exact Hms | exact Hwr].
- exact Hfr.
- apply (msteps_mem_grows segs). exact Hms.
Qed.
Lemma SR_run_JE_ecall : forall n E ss ss' ms STK sp0 FP L A mem md Lc Ac mdc Q,
st_ok segs E ss ms ->
sym_runN segs tbl n ss = (ss', RS_ecall) ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
wr_okE E (ss_mem ss) STK sp0 FP (blocks L A) (blocks Lc Ac) ->
(forall ms', st_ok_ecall segs E ss' ms' -> journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') -> mem_grows (ms_mem ms) (ms_mem ms') ->
SR segs (mkCfg ms' mdc) Q) ->
SR segs (mkCfg ms mdc) Q.
Proof.
intros n E ss ss' ms STK sp0 FP L A mem md Lc Ac mdc Q HS Hrun HJ Hwr Hk.
destruct (msteps_run_gen segs tbl tbl_ok n E ss ss' RS_ecall ms HS Hrun) as (ms' & Hms & HS' & Hfr).
destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
apply (SR_msteps segs ms ms' mdc Q Hh Hl Hms). apply Hk.
- exact HS'.
- eapply journal_exec_errno; [exact HJ | exact Hfr | apply (msteps_mem_grows segs); exact Hms | exact Hwr].
- exact Hfr.
- apply (msteps_mem_grows segs). exact Hms.
Qed.
Lemma SR_run_to_JE : forall n stop E ss ss' st ms STK sp0 FP L A mem md Lc Ac mdc Q,
st_ok segs E ss ms ->
sym_run_toN segs tbl n stop ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
wr_okE E (ss_mem ss) STK sp0 FP (blocks L A) (blocks Lc Ac) ->
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
- eapply journal_exec_errno; [exact HJ | exact Hfr | apply (msteps_mem_grows segs); exact Hms | exact Hwr].
- exact Hfr.
- apply (msteps_mem_grows segs). exact Hms.
Qed.
Lemma jmemcpy_rd : forall pcm, YI04.memcpy_spec B pcm ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc d src n raw bs,
st_ok segs E ss ms -> ss_pc ss = pcm -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 11 = Z_to_bv 64 src -> getr (ms_regs ms) 12 = Z_to_bv 64 n ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
0 <= d -> 0 <= src -> d + n < 2 ^ 64 -> src + n < 2 ^ 64 ->
(forall i, 0 <= i < n -> present (ms_mem ms) (d + i)) ->
rdn segs (ms_mem ms) (Z_to_bv 64 src) (length bs) = Some bs -> n = Z.of_nat (length bs) ->
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
intros pcm HM E ss ms STK sp0 FP L A mem md Lc Ac mdc d src n raw bs HS Hpc Hrv HJ H10 H11 H12 H1 Hraw
Hd Hs Hdn Hsn Hpd Hbs Hlen Hdisj HW.
assert (Hn : 0 <= n) by lia.
pose proof (store_ok_of_present B (ms_mem ms) (Z.to_nat n) d ltac:(intros i Hi; apply Hpd; lia) Hd ltac:(lia)) as Hst.
replace (Z.to_nat n) with (length bs) in Hst by lia.
destruct (HM bs (Z_to_bv 64 d) (Z_to_bv 64 src) (Z_to_bv 64 n) (ms_mem ms) (seg_rom segs) (ms_regs ms) H10 H11 H12)
as (regs2 & Hms & Ha0 & Hfr).
{ rewrite unsigned_lit_small by lia. lia. }
{ exact Hbs. }
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
Lemma jfree_sub : free_realizes B MR -> errno_addr B + 4 <= alloc_ceiling ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc a n (o : Z) spw tpw raw,
st_ok segs E ss ms -> ss_pc ss = ms_free B -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
In (a, n) (blocks Lc Ac) -> 0 < n ->
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
(writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x))).
Proof.
intros HFR errno_low E ss ms STK sp0 FP L A mem md Lc Ac mdc a n o spw tpw raw
HS Hpc Hrv HJ Hin Hn0 Ha0 Hsp HE2 Hspw Hal Hneg Hbud Htp Htpw Hra Hraw HFP.
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
{ eapply (cg_free B MR LAWS errno_low IMG HFR ALLOC_STACK (sp0 + o) [(a, a + n)] Lc Ac (ms_mem ms) mdc Lc Ac (ms_regs ms) (ms_mem ms) mdc p n HJ1 Hpin).
- rewrite Hp. exact Ha0.
- rewrite Hra. exact Hraw.
- exact Hal16'.
- rewrite Hsp'. lia.
- rewrite Hsp'. lia.
- rewrite Htp. exact Htpw.
- rewrite Hp. intros _ i Hi. exists (a, a + n). split; [left; reflexivity | cbn [fst snd]; lia]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi & _).
exists L2, A2, regs2, mem2, md2. rewrite Hra. split; [reflexivity|]. split.
{ eapply (journal_sub B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ALLOC_STACK (sp0 + o) [(a, a + n)] L2 A2 mem2 md2 HJ HJ2); [lia | lia |].
intros x (r & [<-|[]] & Hx). cbn [fst snd] in Hx. split; [replace x with (a + (x - a)) by lia; apply HFP; lia|].
destruct (heap_blocks B MR LAWS Lc Ac (ms_mem ms) mdc a n (x - a) HH Hin0 ltac:(lia)) as (_ & _ & Hc & _). lia. }
split; [exact HJ2|]. split; [exact HP2|].
rewrite Hp in Hrm. split; [exact Hrm|]. split; [exact Hkeep|].
intros x Hx Hnx. apply Hhi; [exact Hx|]. rewrite Hsp'. exact Hnx.
Qed.
Lemma malloc_SR_g : malloc_realizes_g B MR ->
forall L A regs mem md n g,
call_pre B MR L A regs mem md -> getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 62 -> word_mem segs mem (ms_guard B) g ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md)
(fun c' => exists r tr, cpath (malloc n A) tr r /\ malloc_leaf_g B MR L A regs mem md n g r c').
Proof.
intros HM L A regs mem md n g Hpre Hn Hrange Hg.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
apply (mreal_SR segs _ _ _ (HM L A regs mem md n g Hpre Hn Hrange Hg)). apply malloc_safe; [exact HW | lia].
Qed.
Theorem cg_malloc_g : malloc_realizes_g B MR -> errno_addr B + 4 <= alloc_ceiling ->
forall STK sp0 FP L A mem md Lc Ac regs_c memc mdc n g,
journal B MR STK sp0 FP L A mem md Lc Ac memc mdc ->
st_init_done Ac = true ->
getr regs_c 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 62 ->
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
((res = 0 /\ blocks L2 A2 = blocks Lc Ac)
\/ (res <> 0 /\ res mod 16 = 0 /\
(exists b1 b2, blocks L2 A2 = b1 ++ (res, n) :: b2 /\ blocks Lc Ac = b1 ++ b2) /\
(forall blc i, In (res, n) blc -> 0 <= i < n -> wr_byte STK sp0 FP (blocks L A) blc (res + i)))) /\
(forall a m i, In (a, m) (blocks Lc Ac) -> 0 <= i < m ->
mbyte segs mem2 (a + i) = mbyte segs memc (a + i)) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs_c - ALLOC_STACK <= a < spZ regs_c) ->
mbyte segs mem2 a = mbyte segs memc a /\ (writable_at segs memc a <-> writable_at segs mem2 a)) /\
word_mem segs mem2 (ms_guard B) g).
Proof.
intros HMA errno_low STK sp0 FP L A mem md Lc Ac regs_c memc mdc n g HJ Hid Ha0 Hn Hra Hal16 Hlo Hhi Htp Hg.
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
eapply SR_mono; [eapply (malloc_SR_g HMA); [exact Hpre | exact Ha0 | exact Hn | exact Hg]|].
intros c' ([p A2] & tr & Hcp & ((L2 & regs2 & mem2 & md2 & -> & Hpost & Hres) & Hg2)). cbn [fst snd cfg_ms ms_mem mkst] in *.
pose proof (malloc_keeps_init_done n Ac tr p A2 Hid (cpath_yields _ _ _ Hcp)) as Hid2.
pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hregs & Hvm2 & Hfr & Hkeep & Hscr).
assert (HH2 : heap_ok MR L2 A2 mem2 md2) by (split; [exact HM2 | split; assumption]).
assert (Hsub : forall q m, In (q, m) (user_blocks Ac) -> In (q, m) (user_blocks A2)).
{ intros q m Hq. destruct p as [p0|].
- destruct Hres as (_ & _ & (l1 & l2 & E1 & E2) & _). rewrite E1. rewrite E2 in Hq.
apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff; [left; exact Hq | right; right; exact Hq].
- destruct Hres as [_ E]. rewrite E. exact Hq. }
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
exists L2, A2, regs2, mem2, md2.
destruct p as [p0|].
- destruct Hres as (Hr10 & Hnz & (l1 & l2 & E1 & E2) & _).
exists (ptr_addr L2 p0). split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [exact Hregs|].
split; [exact Hr10|]. split; [| split; [exact Hkeepc | split; [exact Hhighc | exact Hg2]]].
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
split; [exact Hr10|]. split; [| split; [exact Hkeepc | split; [exact Hhighc | exact Hg2]]].
left. split; [reflexivity|]. rewrite <- Hmapc. unfold blocks. rewrite E. reflexivity.
Qed.
Lemma jmalloc_sub : malloc_realizes B MR -> errno_addr B + 4 <= alloc_ceiling ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc n (o : Z) spw tpw raw,
st_ok segs E ss ms -> ss_pc ss = ms_malloc B -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
st_init_done Ac = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 n -> 0 < n < 2 ^ 62 ->
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
((res = 0 /\ blocks L2 A2 = blocks Lc Ac)
\/ (res <> 0 /\ res mod 16 = 0 /\
(exists b1 b2, blocks L2 A2 = b1 ++ (res, n) :: b2 /\ blocks Lc Ac = b1 ++ b2) /\
~ In (res, n) (blocks Lc Ac) /\ 4096 <= res /\ res + n <= alloc_ceiling)) /\
(forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m ->
mbyte segs mem2 (b + i) = mbyte segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 + o - ALLOC_STACK <= x < sp0 + o) ->
mbyte segs mem2 x = mbyte segs (ms_mem ms) x /\
(writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x))).
Proof.
intros HMA errno_low E ss ms STK sp0 FP L A mem md Lc Ac mdc n o spw tpw raw
HS Hpc Hrv HJ Hid Ha0 Hn Hsp HE2 Hspw Hal Hneg Hbud Htp Htpw Hra Hraw.
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
{ eapply (cg_malloc B MR LAWS errno_low IMG HMA ALLOC_STACK (sp0 + o) [] Lc Ac (ms_mem ms) mdc Lc Ac (ms_regs ms) (ms_mem ms) mdc n HJ1 Hid Ha0 ltac:(lia)).
- rewrite Hra. exact Hraw.
- exact Hal16'.
- rewrite Hsp'. lia.
- rewrite Hsp'. lia.
- rewrite Htp. exact Htpw. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hr10 & Hres & Hkeep & Hhi).
exists L2, A2, regs2, mem2, md2, res. rewrite Hra. split; [reflexivity|]. split.
{ eapply (journal_sub B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ALLOC_STACK (sp0 + o) [] L2 A2 mem2 md2 HJ HJ2); [lia | lia |].
intros x (r & [] & _). }
split; [exact HJ2|]. split; [exact Hid2|]. split; [exact HP2|]. split; [exact Hr10|]. split.
{ destruct Hres as [Hz | (Hnz & Hm16 & (b1 & b2 & HB2 & HBc) & Wp)]; [left; exact Hz | right].
assert (Hin2 : In (res, n) (blocks L2 A2)) by (rewrite HB2; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range B MR LAWS L2 A2 mem2 md2 res n (proj1 HJ2) Hin2 ltac:(lia)) as (R0 & R1 & _).
split; [exact Hnz|]. split; [exact Hm16|]. split; [exists b1, b2; auto|]. split; [|lia].
intros Hold. destruct (Wp [(res, n)] 0 ltac:(left; reflexivity) ltac:(lia)) as [Hstk | [((xr & [] & _) & _) | (b & m & [<-|[]] & Hnot & _)]].
- lia.
- exact (Hnot Hold). }
split; [exact Hkeep|].
intros x Hx Hnx. apply Hhi; [exact Hx|]. rewrite Hsp'. exact Hnx.
Qed.
Lemma jmalloc_sub_g : malloc_realizes_g B MR -> errno_addr B + 4 <= alloc_ceiling ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc n (o : Z) spw tpw raw g,
st_ok segs E ss ms -> ss_pc ss = ms_malloc B -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
st_init_done Ac = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 n -> 0 < n < 2 ^ 62 ->
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
((res = 0 /\ blocks L2 A2 = blocks Lc Ac)
\/ (res <> 0 /\ res mod 16 = 0 /\
(exists b1 b2, blocks L2 A2 = b1 ++ (res, n) :: b2 /\ blocks Lc Ac = b1 ++ b2) /\
~ In (res, n) (blocks Lc Ac) /\ 4096 <= res /\ res + n <= alloc_ceiling)) /\
(forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m ->
mbyte segs mem2 (b + i) = mbyte segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 + o - ALLOC_STACK <= x < sp0 + o) ->
mbyte segs mem2 x = mbyte segs (ms_mem ms) x /\
(writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x)) /\
word_mem segs mem2 (ms_guard B) g).
Proof.
intros HMA errno_low E ss ms STK sp0 FP L A mem md Lc Ac mdc n o spw tpw raw g
HS Hpc Hrv HJ Hid Ha0 Hn Hsp HE2 Hspw Hal Hneg Hbud Htp Htpw Hra Hraw Hg.
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
{ eapply (cg_malloc_g HMA errno_low ALLOC_STACK (sp0 + o) [] Lc Ac (ms_mem ms) mdc Lc Ac (ms_regs ms) (ms_mem ms) mdc n g HJ1 Hid Ha0 ltac:(lia)).
- rewrite Hra. exact Hraw.
- exact Hal16'.
- rewrite Hsp'. lia.
- rewrite Hsp'. lia.
- rewrite Htp. exact Htpw.
- exact Hg. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hr10 & Hres & Hkeep & Hhi & Hg2).
exists L2, A2, regs2, mem2, md2, res. rewrite Hra. split; [reflexivity|]. split.
{ eapply (journal_sub B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ALLOC_STACK (sp0 + o) [] L2 A2 mem2 md2 HJ HJ2); [lia | lia |].
intros x (r & [] & _). }
split; [exact HJ2|]. split; [exact Hid2|]. split; [exact HP2|]. split; [exact Hr10|]. split.
{ destruct Hres as [Hz | (Hnz & Hm16 & (b1 & b2 & HB2 & HBc) & Wp)]; [left; exact Hz | right].
assert (Hin2 : In (res, n) (blocks L2 A2)) by (rewrite HB2; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range B MR LAWS L2 A2 mem2 md2 res n (proj1 HJ2) Hin2 ltac:(lia)) as (R0 & R1 & _).
split; [exact Hnz|]. split; [exact Hm16|]. split; [exists b1, b2; auto|]. split; [|lia].
intros Hold. destruct (Wp [(res, n)] 0 ltac:(left; reflexivity) ltac:(lia)) as [Hstk | [((xr & [] & _) & _) | (b & m & [<-|[]] & Hnot & _)]].
- lia.
- exact (Hnot Hold). }
split; [exact Hkeep|]. split; [|exact Hg2].
intros x Hx Hnx. apply Hhi; [exact Hx|]. rewrite Hsp'. exact Hnx.
Qed.
End e.
End c.
Ltac wr_normE :=
lazymatch goal with |- wr_okE ?B ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc =>
let rs' := eval vm_compute in rs in change (wr_okE B E rs' stk sp0 fp b0 bc) end.
Ltac jrun_ecall LAWS tblok HS HJ :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
lazymatch r with
| (?ss', RS_ecall) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs tbl FUEL ss = (ss', RS_ecall)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in
let IMG := lazymatch goal with IMG : img_laws _ _ |- _ => IMG end in
eapply (SR_run_J_ecall _ _ LAWS IMG _ tblok FUEL E ss ss' ms _ _ _ _ _ _ _ _ _ _ _ HS Hrun HJ);
clear Hrun;
[ | clear HS HJ;
try match type of ms with machine_state => clear ms | _ => idtac end;
let HF := fresh "HF" in let HG := fresh "HG" in
intros ms' HS HJ HF HG;
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
let rsv := eval vm_compute in rs in change (frame_of E1 rsv m1 m2) in HF end ]
| (_, ?st) => fail "jrun_ecall: the run does not stop at an ecall:" st
end
end
end.
Ltac jrunE LAWS tblok HS HJ :=
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
lazymatch st with
| RS_ecall => eapply (SR_run_JE_ecall _ _ LAWS IMG _ tblok FUEL E ss ss' ms _ _ _ _ _ _ _ _ _ _ _ HS Hrun HJ)
| _ => eapply (SR_run_JE _ _ LAWS IMG _ tblok FUEL E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HJ)
end;
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
Ltac jrunE_to LAWS tblok HS HJ stop :=
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
eapply (SR_run_to_JE _ _ LAWS IMG _ tblok FUEL stop E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HJ);
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
Ltac at_node_sr k :=
lazymatch goal with
| Hregs : regs_ok ?E ?sr _, Hmem : mem_ok _ _ _ ?rs, HG : facts_ok _ ?G
|- SR _ (mkCfg (mkst (regupd _ 10 ?RET) (v_addi (Z_to_bv 64 ?pc) 4) _ _) _) _ =>
k E (mkSS pc sr rs (@None sv) G) RET
end.
Ltac resume_sv_sr segs rv :=
at_node_sr ltac:(fun E ss RET =>
lazymatch goal with
| Hregs : regs_ok _ _ ?regs, Hmem : mem_ok _ _ ?mem _, HG : facts_ok _ _ |- _ =>
let H := fresh "HS" in
unshelve epose proof (st_ok_resume_sv segs E ss regs mem rv RET Hregs Hmem HG _) as H;
[ | clear Hregs Hmem HG; sym_norm H ]
end).
Ltac resume_atom_sr segs n f :=
at_node_sr ltac:(fun E ss RET =>
lazymatch goal with
| Hregs : regs_ok _ _ ?regs, Hmem : mem_ok _ _ ?mem _, HG : facts_ok _ _ |- _ =>
let H := fresh "HS" in
unshelve epose proof (st_ok_resume_atom segs n f E ss regs mem RET Hregs Hmem HG
ltac:(vm_compute; reflexivity) _ _ _) as H;
[ | | | clear Hregs Hmem HG; sym_norm H ]
end).
