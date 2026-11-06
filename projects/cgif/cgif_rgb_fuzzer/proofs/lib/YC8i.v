(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC1b YC2u
YC4u YC4z YC52 YC53 YC51.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YC05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCbj YCas YCat YCau YCbh YCbk YC7e YC7j YCbl YC6e YCav YC7f YCaw YCax YCay YCaz YC7g YCbm YCb0 YCb1 YCbn YCbi YCbo YC1c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YC4h.
Ltac m_fact_of HS n H :=
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let fa := eval vm_compute in (f_atoms (ss_facts ssx)) in
let rec find l := lazymatch l with (n, ?af) :: _ => af | _ :: ?t => find t end in
let af := find fa in
pose proof (YC4h.st_ok_fact_In trasegs Ev ssx msx n af HS ltac:(cbn [f_atoms ss_facts In]; repeat (first [left; reflexivity | right]))) as H;
unfold afact_ok in H; cbn [af_lo af_hi af_al2] in H end.
Ltac m_run_kept HFr AG ZsPt Hceil Hslo FFS UN :=
pose proof (rg_kept_of_frame _ _ _ _ _ ZsPt HFr
ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hrr; revert Hrr; ga_evalE0 AG;
repeat match goal with H : bv_unsigned (ew _ 2) = _ |- _ => rewrite ?H end; intros Hrr; red;
clear - Hrr Hceil Hslo FFS; lia |]);
destruct Hin)) as UN.
Ltac m_obl_cfp HJx HE11 HE44 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal HFPapp :=
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 11 ?c)) ?len =>
lazymatch type of HE11 with _ = Z_to_bv 64 ?cfp =>
first [ rewrite (U_atom_off Ex 11 cfp c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE11 | lia | lia]
| rewrite (U_atom Ex 11 cfp); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE11 | lia] ];
eapply (obl_of_range trasegs _ _ Ex (SOff 44 0) _ len cfp 24);
[ let L := rnLAWS in eapply (range_addressable_entry_frame trasegs _ L); [exact HJx | exact Hfin | exact Hcid0 | exact Hflo | exact Hfhi | exact Hfal | exact HFPapp | exact HAR | exact HRA]
| rewrite (U_atom Ex 44 SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE44 | unfold SB; lia]
| lia | lia ] end end.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section ML.
Variable B : asyms.
Lemma m_aftok_mono : forall FP FP' bl0 b, (forall a, inFP FP a -> inFP FP' a) -> aftok FP bl0 b -> aftok FP' bl0 b.
Proof. intros FP FP' bl0 b Hs Ht Hin i Hi. apply Hs. exact (Ht Hin i Hi). Qed.
Lemma m_awr_mono : forall STK sp0 FP FP' bl0 blc ly own a, (forall x, inFP FP x -> inFP FP' x) ->
awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP' bl0 blc ly own a.
Proof.
intros STK sp0 FP FP' bl0 blc ly own a Hs [H | [[H1 H2] | [H | H]]]; [left; exact H | right; left; split; [apply Hs; exact H1 | exact H2] | right; right; left; exact H | right; right; right; exact H].
Qed.
Lemma m_fps_sub_fp : forall cx a, inFP (rgc_FPs cx) a -> inFP (rgc_FP cx) a.
Proof.
intros cx a (rg & [<- | []] & Hr). exists (c_r cx, c_r cx + req_size RGB_SIZE). split; [left; reflexivity | exact Hr].
Qed.
Hypothesis LAWS : AR_laws trasegs B.
Definition m_ZsP (F r : Z) : Z -> Prop := fun a => alloc_ceiling <= a \/ F <= a < F + 8192 \/ r <= a < r + 64.
Lemma m_blk_off_zs : forall ly S W m md b n r l fpos,
AR trasegs B ly S W m md -> Permutation (ablocks B ly S) ((r, RGB_SIZE) :: l) -> In (b, n) l -> In (7, fpos) (frames S) ->
forall a, b <= a < b + req_size n -> 0 <= a < 2 ^ 64 /\ ~ m_ZsP (frame_addr ly 7 fpos) r a.
Proof.
intros ly S W m md b n r l fpos HAR HP Hl Hfin a Ha.
assert (Hin : In (b, n) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HP | right; exact Hl]).
destruct (rga_blk_range B LAWS ly S _ _ _ b n HAR Hin) as (H4096 & _ & Hceil & _).
pose proof (sep_block_frame trasegs B LAWS ly S _ _ _ b n 7 fpos HAR Hin Hfin) as Dd.
unfold zdisjoint in Dd. cbn [fst snd] in Dd. change (fs_frame_bytes 7) with 8192 in Dd.
pose proof (rg_sep_head_in B LAWS ly S _ _ _ (r, RGB_SIZE) l (b, n) HAR HP Hl) as Dr.
unfold zdisjoint, block_rng in Dr. cbn [fst snd] in Dr. change (req_size RGB_SIZE) with 64 in Dr.
pose proof (asan_consts) as (C1 & _).
split; [lia|]. unfold m_ZsP. lia.
Qed.
Lemma m_awr_byte_callee : forall STK STK' sp sp' FP FP' (bl0 bl0' blc : list (Z * Z)) (lyq lyq' : alayout) own a,
awr_byte STK' sp' FP' bl0' blc lyq' [] a -> sp - STK <= sp' - STK' -> sp' <= sp ->
(forall x, inFP FP' x -> inFP FP x) -> (forall b, In b bl0 -> In b bl0') ->
awr_byte STK sp FP bl0 blc lyq own a.
Proof.
intros STK STK' sp sp' FP FP' bl0 bl0' blc lyq lyq' own a [H | [[Hf Hb] | [(b & n & Hin & Hn0 & Hb) | (c & p & Hin & _)]]] H1 H2 HFP Hsub.
- left. lia.
- right. left. split; [apply HFP; exact Hf | exact Hb].
- right. right. left. exists b, n. split; [exact Hin|]. split; [intros Hc; exact (Hn0 (Hsub _ Hc)) | exact Hb].
- destruct Hin.
Qed.
Definition rga_newblkF (cx : rgcx) (E : env) (a : nat) (b n : Z) : Prop :=
ew E a = Z_to_bv 64 b /\
aftok (rgc_FP cx) (ablocks B (c_ly cx) (c_S cx)) (b, n) /\
(forall blc lyq ownq i, In (b, n) blc -> 0 <= i < req_size n ->
awr_byte TRGBADD_STK (spZ (c_regs cx)) (rgc_FP cx) (ablocks B (c_ly cx) (c_S cx)) blc lyq ownq (b + i)).
Lemma rga_newblkF_of : forall cx E E' a b n, rga_newblk B cx E a b n -> ew E' a = ew E a -> rga_newblkF cx E' a b n.
Proof.
intros cx E E' a b n (R & T & A) He. split; [rewrite He; exact R|]. split.
- eapply m_aftok_mono; [|exact T]. apply m_fps_sub_fp.
- intros blc lyq ownq i Hb Hi. eapply m_awr_mono; [|exact (A blc lyq ownq i Hb Hi)]. apply m_fps_sub_fp.
Qed.
End ML.
End d.
