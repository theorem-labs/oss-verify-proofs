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
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI06 YI08 YI0t YI0r.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Export YI0n.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI06.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section J.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis errno_low : errno_addr B + 4 <= alloc_ceiling.
Hypothesis IMG : img_laws B MR.
Context {SK : sink_head}.
Local Notation frame_saved := (YI0n.frame_saved B).
Local Notation segs := (ms_segs B) (only parsing).
Lemma ftok_of_wtok : forall STK sp0 FP bl0 p n,
wtok' STK sp0 FP bl0 (p, n) -> p + n <= alloc_ceiling -> alloc_ceiling + STK <= sp0 ->
ftok FP bl0 (p, n).
Proof.
intros STK sp0 FP bl0 p n HW Hpn Hsp Hin i Hi. cbn [fst snd] in *.
destruct (HW [(p, n)] i ltac:(left; reflexivity) Hi) as [Hs | [[Hf _] | (b & m & Hb & Hnb & _)]]; cbn [fst snd] in *.
- exfalso. lia.
- exact Hf.
- exfalso. destruct Hb as [Hb | []]. inversion Hb; subst. exact (Hnb Hin).
Qed.
Lemma wr_byte_of_wtok : forall STK sp0 FP bl0 blc p n a,
wtok' STK sp0 FP bl0 (p, n) -> In (p, n) blc -> p <= a < p + n -> wr_byte STK sp0 FP bl0 blc a.
Proof.
intros STK sp0 FP bl0 blc p n a HW Hin Ha. replace a with (p + (a - p)) by lia.
apply (HW blc (a - p) Hin). cbn [snd]. lia.
Qed.
Lemma jfree_tok : free_realizes B MR -> free_null_realizes B ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw,
st_ok segs E ss ms -> ss_pc ss = ms_free B -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc -> st_init_done Ac = true ->
(a = 0 \/ (In (a, n) (blocks Lc Ac) /\ ftok FP (blocks L A) (a, n))) ->
getr (ms_regs ms) 10 = Z_to_bv 64 a ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> 0 <= spc < 2 ^ 64 -> spc mod 16 = 0 ->
sp0 - STK <= spc - ALLOC_STACK -> spc <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SR segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved (ms_regs ms) regs2 /\
(a = 0 /\ blocks L2 A2 = blocks Lc Ac \/ a <> 0 /\ rm1 (a, n) (blocks Lc Ac) (blocks L2 A2)) /\
(forall b m i, In (b, m) (blocks L2 A2) -> 0 <= i < m ->
mbyte segs mem2 (b + i) = mbyte segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - ALLOC_STACK <= x < spc) ->
mbyte segs mem2 x = mbyte segs (ms_mem ms) x /\
(writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x))).
Proof.
intros HFR HFN E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw
HS Hpc Hrv HJ Hid Ha Ha0 Hsp Hspc Hal Hlo Hhi Htp Hra Hraw.
destruct (Z.eq_dec a 0) as [Hz | Hnz].
- subst a. destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
eapply SR_mono; [eapply (jfree_null B HFN); try eassumption|].
intros c' ->. exists Lc, Ac, (ms_regs ms), (ms_mem ms), mdc.
split; [reflexivity|]. split; [exact HJ|]. split; [exact Hid|]. split; [intros r Hr; reflexivity|].
split; [left; split; reflexivity|]. split; [intros; reflexivity|]. intros x _ _. split; [reflexivity | tauto].
- destruct Ha as [Hz | [Hin Htok]]; [lia|].
eapply SR_mono; [eapply (jfree_at B MR LAWS errno_low IMG HFR); try eassumption; exact Htok|].
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2 & Hid2).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|].
split; [exact HP2|].
split; [right; split; [exact Hnz | exact Hrm]|]. split; [exact Hkeep | exact Hhi2].
Qed.
Lemma journal_restart : forall STK sp0 FP L A mem md Lc Ac memc mdc FP',
journal B MR STK sp0 FP L A mem md Lc Ac memc mdc ->
journal B MR STK sp0 FP' Lc Ac memc mdc Lc Ac memc mdc.
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc FP' (HH & Hvm & Hhigh & Hblk & Hgone & Hst & Herr & Himg).
split; [exact HH|]. split; [apply os_step_refl|].
split; [intros a Ha Hna; split; [reflexivity | tauto]|].
split; [intros; reflexivity|]. split; [intros a n i H1 H2; exfalso; exact (H2 H1)|].
split; [exact Hst|]. split; [exact Herr | apply img_kept_refl].
Qed.
Lemma journal_blocks_kept : forall STK sp0 FP L A mem md L' A' mem' md',
journal B MR STK sp0 FP L A mem md L' A' mem' md' ->
forall a n i, In (a, n) (blocks L A) -> In (a, n) (blocks L' A') -> 0 <= i < n ->
~ inFP FP (a + i) -> mbyte segs mem' (a + i) = mbyte segs mem (a + i).
Proof. intros STK sp0 FP L A mem md L' A' mem' md' (_ & _ & _ & Hblk & _). exact Hblk. Qed.
Lemma journal_high_kept : forall STK sp0 FP L A mem md L' A' mem' md',
journal B MR STK sp0 FP L A mem md L' A' mem' md' ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a).
Proof. intros STK sp0 FP L A mem md L' A' mem' md' (_ & _ & Hhigh & _). exact Hhigh. Qed.
Lemma journal_img_kept : forall STK sp0 FP L A mem md L' A' mem' md',
journal B MR STK sp0 FP L A mem md L' A' mem' md' -> img_kept B FP mem mem'.
Proof. intros STK sp0 FP L A mem md L' A' mem' md' (_ & _ & _ & _ & _ & _ & _ & Himg). exact Himg. Qed.
Lemma journal_stack_ok : forall STK sp0 FP L A mem md L' A' mem' md',
journal B MR STK sp0 FP L A mem md L' A' mem' md' -> stack_ok B STK sp0 mem'.
Proof. intros STK sp0 FP L A mem md L' A' mem' md' (_ & _ & _ & _ & _ & Hst & _). exact Hst. Qed.
Lemma frame_saved_kept : forall regs0 m m' spe,
frame_saved regs0 m spe ->
(forall a, spe - 104 <= a < spe -> mbyte segs m' a = mbyte segs m a) ->
frame_saved regs0 m' spe.
Proof.
intros regs0 m m' spe H Hf r d Hin k Hk.
assert (Hd : 8 <= d <= 104).
{ cbv [SAVED In] in Hin. repeat (destruct Hin as [Hin|Hin]; [inversion Hin; subst; lia|]). destruct Hin. }
rewrite Hf by lia. apply (H r d Hin). exact Hk.
Qed.
Lemma frame_saved_of_region : forall E m regs0 spe cs lo hi wlo whi,
region_ok segs E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
bv_unsigned (ew E 2) = spe ->
(forall r d, In (r, d) SAVED -> exists e, In (mkChunk (- d) (CVal 8 e)) cs /\ sv_denot E e = getr regs0 r) ->
frame_saved regs0 m spe.
Proof.
intros E m regs0 spe cs lo hi wlo whi (_ & _ & _ & Hcs) H2 Hsv r d Hrd.
destruct (Hsv r d Hrd) as (e & Hin & He).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [r_base base_val] in Hc. rewrite H2 in Hc.
pose proof (bv_unsigned_in_range 64 (getr regs0 r)) as Rw. change (bv_modulus 64) with (2 ^ 64) in Rw.
apply val_mem_word_mem. replace (spe - d) with (spe + - d) by lia.
exact (val_of_chunk_ok segs E m spe (- d) 8%N e (bv_unsigned (getr regs0 r)) Hc
ltac:(rewrite He; symmetry; apply Z_to_bv_bv_unsigned) ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Lemma saved_chunks_ok : forall E m regs0 spe k,
(forall j, (j < 13)%nat -> ew E (k + j)%nat = nth j (saved_vals regs0) (Z_to_bv 64 0)) ->
frame_saved regs0 m spe ->
Forall (chunk_ok segs E m (spe - 208)) (saved_chunks k).
Proof.
intros E m regs0 spe k HE HF.
unfold saved_chunks. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([j d] & <- & Hjd).
cbn [fst snd].
apply in_combine_r in Hjd as Hd0. pose proof (in_combine_l _ _ _ _ Hjd) as Hj0. apply in_seq in Hj0.
assert (Hnth : nth_error (map snd SAVED) j = Some d /\ exists r, nth_error SAVED j = Some (r, d)).
{ clear - Hjd. cbv [SAVED map snd combine seq] in Hjd.
repeat (destruct Hjd as [Hjd|Hjd]; [inversion Hjd; subst; split; [reflexivity | eexists; reflexivity] |]). destruct Hjd. }
destruct Hnth as [Hnd (r & Hr)].
assert (Hin : In (r, d) SAVED) by (eapply nth_error_In; exact Hr).
pose proof (HF r d Hin) as W.
pose proof (bv_unsigned_in_range 64 (getr regs0 r)) as Rw. change (bv_modulus 64) with (2 ^ 64) in Rw.
eapply (chunk_ok_val segs E m (spe - 208) _ 8%N _ (bv_unsigned (getr regs0 r))).
- cbn [sv_denot]. rewrite Z.add_0_r, (HE j ltac:(lia)).
unfold saved_vals. erewrite (nth_error_nth _ _ _ (map_nth_error _ _ _ Hr)). cbn [fst]. rewrite Z_to_bv_bv_unsigned. reflexivity.
- cbn. lia.
- cbn. lia.
- replace (spe - 208 + (208 - d)) with (spe - d) by lia. apply val_mem_word_mem. exact W.
Qed.
End J.
End f.
