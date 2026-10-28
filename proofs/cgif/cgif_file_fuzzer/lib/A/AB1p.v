(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK0s YE06.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YE08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB15 AB14 AE20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YE05.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require AB1e AB1g AB19 AB17.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YK0c YK0e YK0f YK09 YA0c YA0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB12 AB1h.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YA0f YK0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB16 AB1i.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Local Instance asanreflect_fx : YK11.FPState := YK11.fx0.
Section b. Context {rc : YM05.RunCeil}.
Lemma kept_ok_of_regs_agree : forall (clob : list reg) regs regs',
(forall r, In r clob -> In (AX2.ridx r) APG.caller_saved) ->
regs_agree (fun r => In r clob) regs regs' -> APSXG.kept_ok regs regs'.
Proof. intros clob regs regs' Hsub Hag r Hr0 Hnin. apply Hag. intros Hin. apply Hnin. apply Hsub. exact Hin. Qed.
End b.
#[local] Ltac in_list := cbn [In]; repeat (first [left; (reflexivity || (apply bv_eq; reflexivity)) | right]).
#[local] Ltac clob_sub :=
let r := fresh "r" in let H := fresh "H" in
intros r H; cbn [In] in H;
repeat (destruct H as [<-|H]; [in_list|]); destruct H.
Section e. Context {rc : YM05.RunCeil}.
Lemma imemset_clob_sub : forall r, In r imemset_clob -> In (AX2.ridx r) APG.caller_saved.
Proof. unfold imemset_clob. clob_sub. Qed.
Lemma imemcpy_clob_sub : forall r, In r imemcpy_clob -> In (AX2.ridx r) APG.caller_saved.
Proof. unfold imemcpy_clob. clob_sub. Qed.
Lemma memisz_clob_sub : forall r, In r memisz_clob -> In (AX2.ridx r) APG.caller_saved.
Proof. unfold memisz_clob. clob_sub. Qed.
Lemma ms_clob_sub : forall r, In r ms_clob -> In (AX2.ridx r) APG.caller_saved.
Proof. unfold ms_clob. clob_sub. Qed.
Lemma kept_ok_of_keeps : forall regs regs', keeps regs regs' -> APSXG.kept_ok regs regs'.
Proof.
intros regs regs' Hk r Hr0 Hnin. apply Hk.
pose proof (AX2S.ridx_range r) as Hrr.
assert (Hr : AX2.ridx r <> 0%nat).
{ intros X. apply Hr0. rewrite (APSXG.reg_of_ridx r 0 X). apply bv_eq. reflexivity. }
unfold APG.caller_saved in Hnin. cbn [In] in Hnin.
assert (E : exists k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat /\ AX2.ridx r = k).
{ exists (AX2.ridx r). split; [|reflexivity]. cbn [In]. lia. }
destruct E as (k & Hink & Hrk). rewrite (APSXG.reg_of_ridx r k Hrk).
cbn [In] in Hink. unfold callee_kept.
repeat (destruct Hink as [<-|Hink]; [in_list|]). destruct Hink.
Qed.
Lemma segs_wr_of_forallb : forall segs,
forallb (fun seg => negb (seg_writable seg) || seg_readable seg)%bool segs = true -> APSXG.segs_wr_ok segs.
Proof.
intros segs H seg Hin Hw. pose proof (proj1 (forallb_forall _ _) H seg Hin) as Hs. cbn beta in Hs.
rewrite Hw in Hs. exact Hs.
Qed.
Lemma tfib_segs_wr : APSXG.segs_wr_ok TSEGS.
Proof. apply segs_wr_of_forallb. vm_compute. reflexivity. Qed.
Section f.
Variable SEGS : list Segment.
Lemma fill_spec_of_imemset : forall (entryw : word) (entry : Z),
Z_to_bv 64 entry = entryw ->
(forall mem0 (s c : word) n rom regs (ret : word),
(0 <= n)%Z -> (bv_unsigned s + n < 2 ^ 64)%Z ->
store_ok SEGS mem0 s (Z.to_nat n) = true ->
(align15 n s = 0%Z -> n <> 0%Z -> (bv_unsigned c < 256)%Z) ->
ret_ok ret -> getr regs 1%bv = ret ->
getr regs 10%bv = s -> getr regs 11%bv = c -> getr regs 12%bv = Z_to_bv 64 n ->
exists regs',
msteps SEGS (mkst regs entryw mem0 rom)
(mkst regs' ret (wbytes mem0 s (repeat (Z_to_bv 8 (bv_unsigned c)) (Z.to_nat n))) rom)
/\ regs_agree (fun r => In r imemset_clob) regs regs') ->
APSXG.fill_spec SEGS entry 256.
Proof.
intros entryw entry He SUM mem0 s c n regs ret Hn Hnw Hst Hc Hret R1 R10 R11 R12.
destruct (SUM mem0 s c n (seg_rom SEGS) regs ret Hn Hnw Hst ltac:(intros; exact Hc) Hret R1 R10 R11 R12) as (regs' & Hms & Hag).
exists regs'. rewrite He. split; [exact Hms|]. split.
- eapply kept_ok_of_regs_agree; [apply imemset_clob_sub | exact Hag].
- rewrite <- R10. apply Hag. unfold imemset_clob. cbn. intros [H|[H|[H|[]]]]; discriminate.
Qed.
Lemma fill_spec_of_memset : forall (entry : Z),
(forall mem0 (d cv ret : word) (n : Z) rom,
(0 <= n)%Z -> (bv_unsigned d + n < 2 ^ 64)%Z ->
store_ok SEGS mem0 d (Z.to_nat n) = true -> ret_ok ret ->
forall regs, getr regs 10%bv = d -> getr regs 11%bv = cv -> getr regs 12%bv = Z_to_bv 64 n -> getr regs 1%bv = ret ->
exists regs',
msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 rom)
(mkst regs' ret (wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n))) rom)
/\ getr regs' 10%bv = d /\ ms_agree regs regs') ->
APSXG.fill_spec SEGS entry AX2.two64.
Proof.
intros entry SUM mem0 s c n regs ret Hn Hnw Hst Hc Hret R1 R10 R11 R12.
destruct (SUM mem0 s c ret n (seg_rom SEGS) Hn Hnw Hst Hret regs R10 R11 R12 R1) as (regs' & Hms & H10 & Hag).
exists regs'. split; [exact Hms|]. split; [|exact H10].
eapply kept_ok_of_regs_agree; [apply ms_clob_sub | exact Hag].
Qed.
Lemma copy_spec_of_imemcpy : forall (entryw : word) (entry : Z),
Z_to_bv 64 entry = entryw ->
(forall mem0 (dst src : word) n bs rom regs (ret : word),
cpyH SEGS mem0 dst src n bs ->
ret_ok ret -> getr regs 1%bv = ret ->
getr regs 10%bv = dst -> getr regs 11%bv = src -> getr regs 12%bv = Z_to_bv 64 n ->
exists regs',
msteps SEGS (mkst regs entryw mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
/\ regs_agree (fun r => In r imemcpy_clob) regs regs') ->
APSXG.copy_spec SEGS entry.
Proof.
intros entryw entry He SUM mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
destruct (SUM mem0 dst src n bs (seg_rom SEGS) regs ret ltac:(constructor; assumption) Hret R1 R10 R11 R12) as (regs' & Hms & Hag).
exists regs'. rewrite He. split; [exact Hms|]. split.
- eapply kept_ok_of_regs_agree; [apply imemcpy_clob_sub | exact Hag].
- rewrite <- R10. apply Hag. unfold imemcpy_clob. cbn. intros [H|[H|[H|[H|[]]]]]; discriminate.
Qed.
Lemma miz_spec_of_summary : forall (entryw : word) (entry : Z),
Z_to_bv 64 entry = entryw ->
(forall mem (beg sp : word) N rom regs (ret : word),
(0 <= N <= 2 ^ 40)%Z ->
(bv_unsigned beg + N + 8 <= 2 ^ 64)%Z ->
(16 <= bv_unsigned sp)%Z ->
store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
(bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg)%Z ->
(forall a : word, (bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N)%Z ->
rdn SEGS mem a 1 = Some [Z_to_bv 8 0]) ->
ret_ok ret -> getr regs 1%bv = ret -> getr regs 2%bv = sp ->
getr regs 10%bv = beg -> getr regs 11%bv = Z_to_bv 64 N ->
exists regs',
msteps SEGS (mkst regs entryw mem rom)
(mkst regs' ret (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ret)) rom)
/\ regs_agree (fun r => In r memisz_clob) regs regs'
/\ getr regs' 10%bv = Z_to_bv 64 1 /\ getr regs' 2%bv = sp /\ getr regs' 1%bv = ret) ->
APSXG.miz_spec SEGS entry.
Proof.
intros entryw entry He SUM mem beg sp N regs ret HN Hnw Hsp Hst Hdisj Hz Hret R1 R2 R10 R11.
destruct (SUM mem beg sp N (seg_rom SEGS) regs ret HN Hnw Hsp Hst Hdisj Hz Hret R1 R2 R10 R11) as (regs' & Hms & Hag & H10 & _ & _).
exists regs'. rewrite He. split; [exact Hms|]. split; [|exact H10].
eapply kept_ok_of_regs_agree; [apply memisz_clob_sub | exact Hag].
Qed.
End f.
Lemma tfib_fill_spec_imemset : APSXG.fill_spec TSEGS (APG.x_imemset TFIB) 256.
Proof.
apply (fill_spec_of_imemset _ tfib_imemset_entry); [apply bv_eq; reflexivity|].
exact tfib_imemset.
Qed.
Lemma tfib_fill_spec_memset : APSXG.fill_spec TSEGS (APG.x_memset TFIB) AX2.two64.
Proof.
apply fill_spec_of_memset. intros mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1.
exact (AB1e.memset_summary mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1).
Qed.
Lemma tfib_copy_spec_imemcpy : APSXG.copy_spec TSEGS (APG.x_imemcpy TFIB).
Proof.
apply (copy_spec_of_imemcpy _ tfib_imemcpy_entry); [apply bv_eq; reflexivity|].
exact tfib_imemcpy.
Qed.
Lemma tfib_copy_spec_memcpy : APSXG.copy_spec TSEGS (APG.x_memcpy TFIB).
Proof.
intros mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
pose proof (u64_range dst) as Hdr.
assert (HOK : AB19.mcH mem0 dst src n bs) by (constructor; try assumption; lia).
destruct (AB17.ref_memcpy mem0 dst src n bs (seg_rom TSEGS) HOK regs ret Hret R1 R10 R11 R12) as (regs' & Hms & Hk).
exists regs'. split; [replace (Z_to_bv 64 (APG.x_memcpy TFIB)) with (0x97294%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
split; [apply kept_ok_of_keeps; exact Hk|].
rewrite <- R10. apply Hk. unfold callee_kept. in_list.
Qed.
Lemma tfib_miz_spec : APSXG.miz_spec TSEGS (APG.x_memiszero TFIB).
Proof.
apply (miz_spec_of_summary _ tfib_mem_is_zero_entry); [apply bv_eq; reflexivity|].
exact tfib_mem_is_zero.
Qed.
Lemma istrncpy_clob_sub : forall r, In r istrncpy_clob -> In (AX2.ridx r) APG.caller_saved.
Proof.
intros r H. unfold istrncpy_clob in H. cbn [In] in H.
repeat (destruct H as [<-|H]; [cbn; tauto|]). destruct H.
Qed.
Lemma tfib_istrncpy_spec : APSXG.istrncpy_spec TSEGS (APG.x_istrncpy TFIB) (APG.x_sealed TFIB).
Proof.
intros mem0 dst regs ret Hnone Hst Hnw Hdisj Hret R1 R10 R11 R12.
destruct (tfib_istrncpy_sealed mem0 dst (seg_rom TSEGS) regs ret Hnone Hst Hnw Hdisj Hret R1 R10 R11 R12)
as (regs' & Hms & Hag).
exists regs'. split; [|split].
- replace APSXG.SEALED_BYTES with strncpy_sealed_bytes by reflexivity.
replace (Z_to_bv 64 (APG.x_istrncpy TFIB)) with tfib_istrncpy_entry by (apply bv_eq; reflexivity). exact Hms.
- eapply kept_ok_of_regs_agree; [apply istrncpy_clob_sub | exact Hag].
- rewrite <- R10. apply Hag. unfold istrncpy_clob. cbn. intros [H|[H|[H|[H|[H|[]]]]]]; discriminate.
Qed.
Lemma tfib_popfree_spec' : popfree_spec TSEGS (APG.x_popfree TFIB).
Proof. exact tfib_popfree_spec. Qed.
Definition tfib_SUM_imemset  : APSXG.fill_spec TSEGS (APG.x_imemset TFIB) 256 := tfib_fill_spec_imemset.
Definition tfib_SUM_memset   : APSXG.fill_spec TSEGS (APG.x_memset TFIB) AX2.two64 := tfib_fill_spec_memset.
Definition tfib_SUM_imemcpy  : APSXG.copy_spec TSEGS (APG.x_imemcpy TFIB) := tfib_copy_spec_imemcpy.
Definition tfib_SUM_memcpy   : APSXG.copy_spec TSEGS (APG.x_memcpy TFIB) := tfib_copy_spec_memcpy.
Definition tfib_SUM_miz      : APSXG.miz_spec TSEGS (APG.x_memiszero TFIB) := tfib_miz_spec.
Definition tfib_SUM_istrncpy : APSXG.istrncpy_spec TSEGS (APG.x_istrncpy TFIB) (APG.x_sealed TFIB) := tfib_istrncpy_spec.
Definition tfib_SUM_popfree  : popfree_spec TSEGS (APG.x_popfree TFIB) := tfib_popfree_spec'.
End e.
