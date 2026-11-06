(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.json_c.json_object_fuzzer.images Require Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCoy QLPb QWTC QgpE Q3bI QU0c Q85Z Qo8J QG64 QqZL QBCP QJJu QiyH QWZn Q0qZ QsSk Qt8n QWtD QDlz QOTP Q1LT QEdo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.json_c.json_object_fuzzer.images.Asan.
Import QCoy QLPb.
Import QWTC QgpE Q3bI QU0c Q85Z.Mq1 Qo8J.Mq0 QG64.Mq3.
Import QqZL.Mq3.
Import QCoy.Mq1 QCoy.Mq0 QCoy.Mq2.
Import QBCP.Mq1.

Import QsSk Qt8n QWtD QqZL.Mq2 QDlz QOTP Q1LT.
Import QEdo.Mq3.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope Z_scope.

Lemma kept_ok_of_regs_agree : forall (clob : list reg) regs regs',
(forall r, In r clob -> In (AX2.ridx r) AP.caller_saved) ->
regs_agree (fun r => In r clob) regs regs' -> APSX.kept_ok regs regs'.
Proof. intros clob regs regs' Hsub Hag r Hr0 Hnin. apply Hag. intros Hin. apply Hnin. apply Hsub. exact Hin. Qed.

#[local] Ltac in_list := cbn [In]; repeat (first [left; (reflexivity || (apply bv_eq; reflexivity)) | right]).

#[local] Ltac clob_sub :=
let r := fresh "r" in let H := fresh "H" in
intros r H; cbn [In] in H;
repeat (destruct H as [<-|H]; [in_list|]); destruct H.

Lemma imemset_clob_sub : forall r, In r imemset_clob -> In (AX2.ridx r) AP.caller_saved.
Proof. unfold imemset_clob. clob_sub. Qed.
Lemma imemcpy_clob_sub : forall r, In r imemcpy_clob -> In (AX2.ridx r) AP.caller_saved.
Proof. unfold imemcpy_clob. clob_sub. Qed.
Lemma memisz_clob_sub : forall r, In r memisz_clob -> In (AX2.ridx r) AP.caller_saved.
Proof. unfold memisz_clob. clob_sub. Qed.
Lemma ms_clob_sub : forall r, In r ms_clob -> In (AX2.ridx r) AP.caller_saved.
Proof. unfold ms_clob. clob_sub. Qed.

Lemma kept_ok_of_keeps : forall regs regs', keeps regs regs' -> APSX.kept_ok regs regs'.
Proof.
intros regs regs' Hk r Hr0 Hnin. apply Hk.
pose proof (AX2S.ridx_range r) as Hrr.
assert (Hr : AX2.ridx r <> 0%nat).
{ intros X. apply Hr0. rewrite (APSX.reg_of_ridx r 0 X). apply bv_eq. reflexivity. }
unfold AP.caller_saved in Hnin. cbn [In] in Hnin.
assert (E : exists k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat /\ AX2.ridx r = k).
{ exists (AX2.ridx r). split; [|reflexivity]. cbn [In]. lia. }
destruct E as (k & Hink & Hrk). rewrite (APSX.reg_of_ridx r k Hrk).
cbn [In] in Hink. unfold callee_kept.
repeat (destruct Hink as [<-|Hink]; [in_list|]). destruct Hink.
Qed.

Lemma segs_wr_of_forallb : forall segs,
forallb (fun seg => negb (seg_writable seg) || seg_readable seg)%bool segs = true -> APSX.segs_wr_ok segs.
Proof.
intros segs H seg Hin Hw. pose proof (proj1 (forallb_forall _ _) H seg Hin) as Hs. cbn beta in Hs.
rewrite Hw in Hs. exact Hs.
Qed.

Lemma asan_segs_wr : APSX.segs_wr_ok JO6SEGS.
Proof. apply segs_wr_of_forallb. vm_compute. reflexivity. Qed.

Section Derive.
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
APSX.fill_spec SEGS entry 256.
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
APSX.fill_spec SEGS entry AX2.two64.
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
APSX.copy_spec SEGS entry.
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
APSX.miz_spec SEGS entry.
Proof.
intros entryw entry He SUM mem beg sp N regs ret HN Hnw Hsp Hst Hdisj Hz Hret R1 R2 R10 R11.
destruct (SUM mem beg sp N (seg_rom SEGS) regs ret HN Hnw Hsp Hst Hdisj Hz Hret R1 R2 R10 R11) as (regs' & Hms & Hag & H10 & _ & _).
exists regs'. rewrite He. split; [exact Hms|]. split; [|exact H10].
eapply kept_ok_of_regs_agree; [apply memisz_clob_sub | exact Hag].
Qed.
End Derive.

Lemma asan_fill_spec_imemset : APSX.fill_spec JO6SEGS (AP.x_imemset AJO6) 256.
Proof.
apply (fill_spec_of_imemset _ asan_imemset_entry); [apply bv_eq; reflexivity|].
exact asan_imemset.
Qed.

Lemma asan_fill_spec_memset : APSX.fill_spec JO6SEGS (AP.x_memset AJO6) AX2.two64.
Proof.
apply fill_spec_of_memset. intros mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1.
exact (QJJu.Mq0.memset_summary mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1).
Qed.

Lemma asan_copy_spec_imemcpy : APSX.copy_spec JO6SEGS (AP.x_imemcpy AJO6).
Proof.
apply (copy_spec_of_imemcpy _ asan_imemcpy_entry); [apply bv_eq; reflexivity|].
exact asan_imemcpy.
Qed.

Lemma asan_copy_spec_memcpy : APSX.copy_spec JO6SEGS (AP.x_memcpy AJO6).
Proof.
intros mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
pose proof (u64_range dst) as Hdr.
assert (HOK : QWZn.mcH mem0 dst src n bs) by (constructor; try assumption; lia).
destruct (Q0qZ.Mq1.ref_memcpy mem0 dst src n bs (seg_rom JO6SEGS) HOK regs ret Hret R1 R10 R11 R12) as (regs' & Hms & Hk).
exists regs'. split; [replace (Z_to_bv 64 (AP.x_memcpy AJO6)) with (0xdb34c%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
split; [apply kept_ok_of_keeps; exact Hk|].
rewrite <- R10. apply Hk. unfold callee_kept. in_list.
Qed.

Lemma asan_miz_spec : APSX.miz_spec JO6SEGS (AP.x_memiszero AJO6).
Proof.
apply (miz_spec_of_summary _ asan_mem_is_zero_entry); [apply bv_eq; reflexivity|].
exact asan_mem_is_zero.
Qed.

End Mq0.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyaF QXVi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.
Import QyaF QXVi.
Import QWTC QgpE Q3bI QU0c Q85Z.Mq1 Qo8J.Mq0 QG64.Mq3.
Import QqZL.Mq3.
Import QCoy.Mq8 QCoy.Mq7 QCoy.Mq9.
Import QBCP.Mq1.

Import QsSk Qt8n QWtD QqZL.Mq2 QDlz QOTP Q1LT.
Import QEdo.Mq3.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope Z_scope.

Lemma kept_ok_of_regs_agree : forall (clob : list reg) regs regs',
(forall r, In r clob -> In (AX2.ridx r) AP.caller_saved) ->
regs_agree (fun r => In r clob) regs regs' -> APSX.kept_ok regs regs'.
Proof. intros clob regs regs' Hsub Hag r Hr0 Hnin. apply Hag. intros Hin. apply Hnin. apply Hsub. exact Hin. Qed.

#[local] Ltac in_list := cbn [In]; repeat (first [left; (reflexivity || (apply bv_eq; reflexivity)) | right]).

#[local] Ltac clob_sub :=
let r := fresh "r" in let H := fresh "H" in
intros r H; cbn [In] in H;
repeat (destruct H as [<-|H]; [in_list|]); destruct H.

Lemma imemset_clob_sub : forall r, In r imemset_clob -> In (AX2.ridx r) AP.caller_saved.
Proof. unfold imemset_clob. clob_sub. Qed.
Lemma imemcpy_clob_sub : forall r, In r imemcpy_clob -> In (AX2.ridx r) AP.caller_saved.
Proof. unfold imemcpy_clob. clob_sub. Qed.
Lemma memisz_clob_sub : forall r, In r memisz_clob -> In (AX2.ridx r) AP.caller_saved.
Proof. unfold memisz_clob. clob_sub. Qed.
Lemma ms_clob_sub : forall r, In r ms_clob -> In (AX2.ridx r) AP.caller_saved.
Proof. unfold ms_clob. clob_sub. Qed.

Lemma kept_ok_of_keeps : forall regs regs', keeps regs regs' -> APSX.kept_ok regs regs'.
Proof.
intros regs regs' Hk r Hr0 Hnin. apply Hk.
pose proof (AX2S.ridx_range r) as Hrr.
assert (Hr : AX2.ridx r <> 0%nat).
{ intros X. apply Hr0. rewrite (APSX.reg_of_ridx r 0 X). apply bv_eq. reflexivity. }
unfold AP.caller_saved in Hnin. cbn [In] in Hnin.
assert (E : exists k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat /\ AX2.ridx r = k).
{ exists (AX2.ridx r). split; [|reflexivity]. cbn [In]. lia. }
destruct E as (k & Hink & Hrk). rewrite (APSX.reg_of_ridx r k Hrk).
cbn [In] in Hink. unfold callee_kept.
repeat (destruct Hink as [<-|Hink]; [in_list|]). destruct Hink.
Qed.

Lemma segs_wr_of_forallb : forall segs,
forallb (fun seg => negb (seg_writable seg) || seg_readable seg)%bool segs = true -> APSX.segs_wr_ok segs.
Proof.
intros segs H seg Hin Hw. pose proof (proj1 (forallb_forall _ _) H seg Hin) as Hs. cbn beta in Hs.
rewrite Hw in Hs. exact Hs.
Qed.

Lemma asan_segs_wr : APSX.segs_wr_ok JOB6SEGS.
Proof. apply segs_wr_of_forallb. vm_compute. reflexivity. Qed.

Section Derive.
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
APSX.fill_spec SEGS entry 256.
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
APSX.fill_spec SEGS entry AX2.two64.
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
APSX.copy_spec SEGS entry.
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
APSX.miz_spec SEGS entry.
Proof.
intros entryw entry He SUM mem beg sp N regs ret HN Hnw Hsp Hst Hdisj Hz Hret R1 R2 R10 R11.
destruct (SUM mem beg sp N (seg_rom SEGS) regs ret HN Hnw Hsp Hst Hdisj Hz Hret R1 R2 R10 R11) as (regs' & Hms & Hag & H10 & _ & _).
exists regs'. rewrite He. split; [exact Hms|]. split; [|exact H10].
eapply kept_ok_of_regs_agree; [apply memisz_clob_sub | exact Hag].
Qed.
End Derive.

Lemma asan_fill_spec_imemset : APSX.fill_spec JOB6SEGS (AP.x_imemset BJO6) 256.
Proof.
apply (fill_spec_of_imemset _ asan_imemset_entry); [apply bv_eq; reflexivity|].
exact asan_imemset.
Qed.

Lemma asan_fill_spec_memset : APSX.fill_spec JOB6SEGS (AP.x_memset BJO6) AX2.two64.
Proof.
apply fill_spec_of_memset. intros mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1.
exact (QJJu.Mq2.memset_summary mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1).
Qed.

Lemma asan_copy_spec_imemcpy : APSX.copy_spec JOB6SEGS (AP.x_imemcpy BJO6).
Proof.
apply (copy_spec_of_imemcpy _ asan_imemcpy_entry); [apply bv_eq; reflexivity|].
exact asan_imemcpy.
Qed.

Lemma asan_copy_spec_memcpy : APSX.copy_spec JOB6SEGS (AP.x_memcpy BJO6).
Proof.
intros mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
pose proof (u64_range dst) as Hdr.
assert (HOK : QWZn.Mq0.mcH mem0 dst src n bs) by (constructor; try assumption; lia).
destruct (Q0qZ.Mq6.ref_memcpy mem0 dst src n bs (seg_rom JOB6SEGS) HOK regs ret Hret R1 R10 R11 R12) as (regs' & Hms & Hk).
exists regs'. split; [replace (Z_to_bv 64 (AP.x_memcpy BJO6)) with (0xdda10%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
split; [apply kept_ok_of_keeps; exact Hk|].
rewrite <- R10. apply Hk. unfold callee_kept. in_list.
Qed.

Lemma asan_miz_spec : APSX.miz_spec JOB6SEGS (AP.x_memiszero BJO6).
Proof.
apply (miz_spec_of_summary _ asan_mem_is_zero_entry); [apply bv_eq; reflexivity|].
exact asan_mem_is_zero.
Qed.

End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgpE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgpE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3bI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3bI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU0c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QU0c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsSk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsSk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqZL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqZL.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6EJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6EJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo8J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo8J.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqZL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqZL.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEdo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEdo.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqZL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqZL.Mq3.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCoy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCoy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLPb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLPb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqQB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqQB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvfX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvfX.Mq0.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition sminv (w : Z) (z : Z) : Prop :=
0 <= z < 2 ^ 47 /\ forall i, 47 - w <= i <= 46 -> Z.testbit z i = true.

Lemma testbit_high_false : forall n z i, 0 <= n -> 0 <= z < 2 ^ n -> n <= i -> Z.testbit z i = false.
Proof.
intros n z i Hn Hz Hi.
destruct (Z.eq_dec z 0) as [->|Hnz]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|].
apply Z.log2_lt_pow2; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Hz)|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma lt_pow2_of_bits : forall n z, 0 <= n -> 0 <= z -> (forall i, n <= i -> Z.testbit z i = false) -> z < 2 ^ n.
Proof.
intros n z Hn Hz Hb.
destruct (Z.eq_dec z 0) as [->|Hnz]; [apply Z.pow_pos_nonneg; lia|].
destruct (Z.lt_ge_cases z (2 ^ n)) as [Hlt|Hge]; [exact Hlt|]. exfalso.
assert (Hl : n <= Z.log2 z) by (apply Z.log2_le_pow2; lia).
pose proof (Z.bit_log2 z ltac:(lia)) as Hbit. rewrite (Hb (Z.log2 z) Hl) in Hbit. discriminate.
Qed.

Lemma lor_lt_pow2 : forall n a b, 0 <= n -> 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
intros n a b Hn Ha Hb. split; [apply Z.lor_nonneg; lia|].
apply lt_pow2_of_bits; [lia | apply Z.lor_nonneg; lia |].
intros i Hi. rewrite Z.lor_spec. rewrite (testbit_high_false n a i), (testbit_high_false n b i) by lia. reflexivity.
Qed.

Lemma shiftr_lt : forall z k n, 0 <= z < 2 ^ n -> 0 <= k -> 0 <= Z.shiftr z k < 2 ^ n.
Proof.
intros z k n Hz Hk. rewrite Z.shiftr_div_pow2 by lia.
assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
split; [apply Z.div_pos; lia|].
apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Lemma sminv_start : forall x, 2 ^ 46 <= x < 2 ^ 47 -> sminv 1 x.
Proof.
intros x Hx. split; [lia|]. intros i Hi. replace i with 46 by lia.
apply Z.testbit_true; [lia|]. replace (x / 2 ^ 46) with 1; [reflexivity|].
apply Z.div_unique with (r := x - 2 ^ 46); [left; lia | lia].
Qed.

Lemma sminv_step : forall w k z, 0 <= k <= w -> w + k <= 47 -> sminv w z -> sminv (w + k) (Z.lor z (Z.shiftr z k)).
Proof.
intros w k z Hk Hwk [Hz Hb]. split.
- apply lor_lt_pow2; [lia | exact Hz | apply shiftr_lt; [exact Hz | lia]].
- intros i Hi. rewrite Z.lor_spec. destruct (Z.le_gt_cases (47 - w) i) as [Hhi|Hlo].
+ rewrite (Hb i) by lia. reflexivity.
+ rewrite Z.shiftr_spec by lia. rewrite (Hb (i + k)) by lia. apply orb_true_r.
Qed.

Lemma ones_of_bits : forall n z, 0 <= n -> 0 <= z < 2 ^ n -> (forall i, 0 <= i < n -> Z.testbit z i = true) -> z = 2 ^ n - 1.
Proof.
intros n z Hn Hz Hb. replace (2 ^ n - 1) with (Z.ones n) by (rewrite Z.ones_equiv; lia).
apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i n) as [Hl|Hh].
- rewrite (Hb i) by lia. symmetry. apply Z.ones_spec_low. lia.
- rewrite (testbit_high_false n z i) by lia. symmetry. apply Z.ones_spec_high. lia.
Qed.

Definition zsm (z k : Z) : Z := Z.lor z (Z.shiftr z k).
Definition zs5 (x : Z) : Z := zsm (zsm (zsm (zsm (zsm x 1) 2) 4) 8) 16.

Lemma zsm_lt47 : forall z k, 0 <= z < 2 ^ 47 -> 0 <= k -> 0 <= zsm z k < 2 ^ 47.
Proof. intros z k Hz Hk. unfold zsm. apply lor_lt_pow2; [lia | exact Hz | apply shiftr_lt; [exact Hz | lia]]. Qed.

Lemma zs5_inv : forall x, 2 ^ 46 <= x < 2 ^ 47 -> sminv 32 (zs5 x).
Proof.
intros x Hx. unfold zs5, zsm.
replace 32 with (16 + 16) by lia. apply sminv_step; [lia|lia|].
replace 16 with (8 + 8) at 1 by lia. apply sminv_step; [lia|lia|].
replace 8 with (4 + 4) at 1 by lia. apply sminv_step; [lia|lia|].
replace 4 with (2 + 2) at 1 by lia. apply sminv_step; [lia|lia|].
replace 2 with (1 + 1) at 1 by lia. apply sminv_step; [lia|lia|].
apply sminv_start. exact Hx.
Qed.

Lemma zs5_hi : forall x, 2 ^ 46 <= x < 2 ^ 47 -> Z.shiftr (zs5 x) 32 = 2 ^ 15 - 1.
Proof.
intros x Hx. destruct (zs5_inv x Hx) as [Hz Hb].
apply ones_of_bits; [lia | |].
- rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
change (2 ^ 32 * 2 ^ 15) with (2 ^ 47). lia.
- intros i Hi. rewrite Z.shiftr_spec by lia. apply Hb. lia.
Qed.

Lemma zs6_val : forall x, 2 ^ 46 <= x < 2 ^ 47 -> Z.lor (zs5 x) (Z.shiftr (zs5 x) 32) = 2 ^ 47 - 1.
Proof.
intros x Hx. destruct (zs5_inv x Hx) as [Hz Hb]. rewrite (zs5_hi x Hx).
apply ones_of_bits; [lia | |].
- apply lor_lt_pow2; lia.
- intros i Hi. rewrite Z.lor_spec. destruct (Z.lt_ge_cases i 15) as [Hl|Hh].
+ replace (2 ^ 15 - 1) with (Z.ones 15) by (rewrite Z.ones_equiv; lia). rewrite (Z.ones_spec_low 15 i) by lia. apply orb_true_r.
+ rewrite (Hb i) by lia. reflexivity.
Qed.

Definition wsm (a : word) (k : Z) : word := v_or a (v_srli a k).
Definition ws5 (x : word) : word := wsm (wsm (wsm (wsm (wsm x 1) 2) 4) 8) 16.

Lemma u_wsm : forall (a : word) k, 0 <= k -> bv_unsigned a < 2 ^ 47 -> bv_unsigned (wsm a k) = zsm (bv_unsigned a) k.
Proof.
intros a k Hk Ha. pose proof (u64_range a) as Ra. unfold wsm, v_or, v_srli, zsm.
pose proof (shiftr_lt (bv_unsigned a) k 47 ltac:(lia) Hk) as Hs.
rewrite (u_Z2bv (Z.shiftr (bv_unsigned a) k)) by lia.
pose proof (lor_lt_pow2 47 (bv_unsigned a) (Z.shiftr (bv_unsigned a) k) ltac:(lia) ltac:(lia) Hs) as Hl.
apply u_Z2bv; lia.
Qed.

Lemma u_ws5 : forall x : word, 2 ^ 46 <= bv_unsigned x < 2 ^ 47 -> bv_unsigned (ws5 x) = zs5 (bv_unsigned x).
Proof.
intros x Hx. unfold ws5, zs5.
pose proof (zsm_lt47 (bv_unsigned x) 1 ltac:(lia) ltac:(lia)) as H1.
pose proof (zsm_lt47 _ 2 H1 ltac:(lia)) as H2.
pose proof (zsm_lt47 _ 4 H2 ltac:(lia)) as H3.
pose proof (zsm_lt47 _ 8 H3 ltac:(lia)) as H4.
rewrite <- (u_wsm x 1) in H1, H2, H3, H4 |- * by lia.
rewrite <- (u_wsm (wsm x 1) 2) in H2, H3, H4 |- * by lia.
rewrite <- (u_wsm (wsm (wsm x 1) 2) 4) in H3, H4 |- * by lia.
rewrite <- (u_wsm (wsm (wsm (wsm x 1) 2) 4) 8) in H4 |- * by lia.
apply u_wsm; lia.
Qed.

Lemma smear_a5 : forall x : word, 2 ^ 46 <= bv_unsigned x < 2 ^ 47 -> v_srli (ws5 x) 32 = Z_to_bv 64 0x7fff.
Proof.
intros x Hx. unfold v_srli. rewrite (u_ws5 x Hx), (zs5_hi _ Hx). reflexivity.
Qed.

Lemma smear_a0 : forall x : word, 2 ^ 46 <= bv_unsigned x < 2 ^ 47 -> v_or (ws5 x) (v_srli (ws5 x) 32) = Z_to_bv 64 (2 ^ 47 - 1).
Proof.
intros x Hx. rewrite (smear_a5 x Hx). unfold v_or. rewrite (u_ws5 x Hx).
rewrite (u_Z2bv 0x7fff) by lia.
replace 0x7fff with (Z.shiftr (zs5 (bv_unsigned x)) 32) by (rewrite (zs5_hi _ Hx); reflexivity).
rewrite (zs6_val _ Hx). reflexivity.
Qed.

Definition smear_clob : list (bv 5) := [10; 11; 12; 13; 14; 15]%bv.

Open Scope bv_scope.

Definition smear_code (SEGS : list Segment) : Prop :=
fetch_word SEGS (0x765b8 : word) = Some W_765d0 /\
fetch_word SEGS (0x765bc : word) = Some W_765d4 /\
fetch_word SEGS (0x765c0 : word) = Some W_765d8 /\
fetch_word SEGS (0x765c4 : word) = Some W_765dc /\
fetch_word SEGS (0x765c8 : word) = Some W_765e0 /\
fetch_word SEGS (0x765cc : word) = Some W_765e4 /\
fetch_word SEGS (0x765d0 : word) = Some W_765e8 /\
fetch_word SEGS (0x765d4 : word) = Some W_765ec /\
fetch_word SEGS (0x765d8 : word) = Some W_765f0 /\
fetch_word SEGS (0x765dc : word) = Some W_765f4 /\
fetch_word SEGS (0x765e0 : word) = Some W_765f8 /\
fetch_word SEGS (0x765e4 : word) = Some W_765fc /\
fetch_word SEGS (0x765e8 : word) = Some W_76600 /\
fetch_word SEGS (0x765ec : word) = Some W_76604 /\
fetch_word SEGS (0x765f0 : word) = Some W_76608 /\
fetch_word SEGS (0x765f4 : word) = Some W_7660c /\
fetch_word SEGS (0x765f8 : word) = Some W_76610 /\
fetch_word SEGS (0x765fc : word) = Some W_76614 /\
fetch_word SEGS (0x76600 : word) = Some W_76618 /\
fetch_word SEGS (0x76604 : word) = Some W_7661c /\
fetch_word SEGS (0x76608 : word) = Some W_76620 /\
fetch_word SEGS (0x7660c : word) = Some W_76624 /\
fetch_word SEGS (0x76610 : word) = Some W_76628 /\
fetch_word SEGS (0x76614 : word) = Some W_7662c /\
fetch_word SEGS (0x76618 : word) = Some W_76630 /\
fetch_word SEGS (0x7661c : word) = Some W_76634 /\
fetch_word SEGS (0x76620 : word) = Some W_76638 /\
fetch_word SEGS (0x76624 : word) = Some W_7663c.

Lemma asegs_smear_code : smear_code JO6SEGS.
Proof.
unfold smear_code. repeat split;
first [ exact F_765d0 | exact F_765d4 | exact F_765d8 | exact F_765dc | exact F_765e0 | exact F_765e4 | exact F_765e8 | exact F_765ec | exact F_765f0 | exact F_765f4 | exact F_765f8 | exact F_765fc | exact F_76600 | exact F_76604 | exact F_76608 | exact F_7660c | exact F_76610 | exact F_76614 | exact F_76618 | exact F_7661c | exact F_76620 | exact F_76624 | exact F_76628 | exact F_7662c | exact F_76630 | exact F_76634 | exact F_76638 | exact F_7663c ].
Qed.

Lemma smear_run : forall SEGS, smear_code SEGS -> forall regs mem rom (x : word), getr regs 10 = x ->
exists regs', msteps SEGS (mkst regs (0x765b8 : word) mem rom) (mkst regs' (0x76628 : word) mem rom)
/\ getr regs' 10 = v_or (ws5 x) (v_srli (ws5 x) 32)
/\ getr regs' 11 = Z_to_bv 64 0x5555555555555555 /\ getr regs' 12 = Z_to_bv 64 0x3333333333333333
/\ getr regs' 13 = Z_to_bv 64 0x0f0f0f0f0f0f0f0f /\ getr regs' 14 = Z_to_bv 64 0x0101010101010101
/\ getr regs' 15 = v_srli (ws5 x) 32
/\ regs_agree (fun r => In r smear_clob) regs regs'.
Proof.
intros SEGS HCODE regs mem rom x H10. destruct HCODE as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27).
eexists. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
- an C0 D_765d0. an C1 D_765d4. an C2 D_765d8. an C3 D_765dc. an C4 D_765e0.
an C5 D_765e4. change (v_or x (v_srli x 1)) with (wsm x 1).
an C6 D_765e8. an C7 D_765ec. an C8 D_765f0. an C9 D_765f4.
an C10 D_765f8. an C11 D_765fc. change (v_or (wsm x 1) (v_srli (wsm x 1) 2)) with (wsm (wsm x 1) 2).
an C12 D_76600. an C13 D_76604. an C14 D_76608. an C15 D_7660c.
an C16 D_76610. an C17 D_76614. an C18 D_76618. an C19 D_7661c.
an C20 D_76620. an C21 D_76624. change (v_or (wsm (wsm x 1) 2) (v_srli (wsm (wsm x 1) 2) 4)) with (wsm (wsm (wsm x 1) 2) 4).
an C22 D_76628. an C23 D_7662c. change (v_or (wsm (wsm (wsm x 1) 2) 4) (v_srli (wsm (wsm (wsm x 1) 2) 4) 8)) with (wsm (wsm (wsm (wsm x 1) 2) 4) 8).
an C24 D_76630. an C25 D_76634. change (v_or (wsm (wsm (wsm (wsm x 1) 2) 4) 8) (v_srli (wsm (wsm (wsm (wsm x 1) 2) 4) 8) 16)) with (ws5 x).
an C26 D_76638. an C27 D_7663c.
apply mst_refl.
- gres. reflexivity.
- gres. reflexivity.
- gres. reflexivity.
- gres. reflexivity.
- gres. reflexivity.
- gres. reflexivity.
- unfold smear_clob. solve_regs_agree.
Qed.
Close Scope bv_scope.

Lemma know_byte_cov_vars : forall segs img b kn rb rk,
AP.kn_vars_lt b kn = true -> know_byte_cov segs img kn rb rk = true -> AP.expr_vars_lt b rb = true.
Proof.
intros segs img b kn rb rk. induction kn as [|K rest IH]; intros Hv H; [discriminate|].
cbn [AP.kn_vars_lt] in Hv. apply andb_prop in Hv as [HK Hrest].
cbn [know_byte_cov] in H. apply orb_prop in H as [H|H]; [|exact (IH Hrest H)].
assert (LIT : forall kb kk l, match rel_lit rb rk 1 kb kk l with RInside _ => true | _ => false end = true ->
AP.saddr_vars_lt b (SA kb kk) = true -> AP.expr_vars_lt b rb = true).
{ intros kb kk l Hr Hs. unfold rel_lit in Hr. destruct (expr_eqb rb kb) eqn:He; [|discriminate].
apply expr_eqb_eq in He. subst kb. exact Hs. }
destruct K as [[kb kk] w e|[kb kk] [l0| | | | | | |]|[kb kk] [l0| | | | | | |] kk2|lo hi|e m|e lo hi|[kb kk] n2|a1 n1 a2 n2|[kb kk] [l0| | | | | | |] c|[kb kk] [l0| | | | | | |]];
cbn [AP.kentry_vars_lt] in HK; try discriminate;
try (apply andb_prop in HK as [HK _]);
try (apply andb_prop in H as [_ H]; eapply LIT; [exact H | exact HK]);
try (eapply LIT; [exact H | exact HK]).

destruct img; [|discriminate]. cbn [andb] in H. destruct rb; try discriminate. reflexivity.
Qed.

Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable USP : Z.
Hypothesis NX0_ge : APS.nx0_ge nx0.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

#[local] Notation CSOK := (cs_ok SEGS A LIMIT USP SINV argH FS0) (only parsing).
#[local] Notation HID := (hid A USP argH) (only parsing).
#[local] Notation MR := (Mr A USP argH) (only parsing).

#[local] Ltac aps_fill :=
first [eassumption | exact (fun _ : nat => @None acs) | exact (fun _ _ _ => None) | exact (fun _ _ => None) | exact (fun _ => None)
| exact 0%nat | exact 0%Z | exact nx0 | exact LIMIT | exact USP].

Lemma w_cs_ok_agree : forall E E' cs R FULL model,
env_agree (nxt cs) E E' -> fresh_ok nx0 cs = true -> CSOK E cs R FULL model -> CSOK E' cs R FULL model.
Proof. intros. eapply cs_ok_agree; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_hid_agree : forall b E E' cs model,
env_agree b E E' -> (nx0 <= b)%nat -> pairs_vars_lt b (a_vis cs ++ a_ghost cs) = true ->
HID E' cs model = HID E cs model.
Proof. intros. eapply hid_agree; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_cs_ok_frame : forall E cs R FULL model ss' R' FULL' model',
CSOK E cs R FULL model -> same_but_materialized model model' -> MInv (allowA A E cs) model' ->
regs_ok E (s_regs ss') R' -> s_log ss' = [] ->
know_ok SEGS E (MR E cs model FULL') (s_know ss') ->
(forall a, HID E cs model a = true -> FULL' a = FULL a) ->
CSOK E (with_ss cs ss') R' FULL' model'.
Proof. intros. eapply cs_ok_frame; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_lazy_cover_cs : forall E cs R FULL model,
CSOK E cs R FULL model -> lazy_cover (HID E cs model) (m_vm_lazy model) (allowA A E cs).
Proof. intros. eapply lazy_cover_cs; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_A_wf_allowA : forall E cs, A_wf (allowA A E cs).
Proof. intros. eapply A_wf_allowA; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_H_off_segments_cs : forall E cs model, H_off_segments SEGS (HID E cs model).
Proof. intros. eapply H_off_segments_cs; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_fresh_ok_parts : forall cs, fresh_ok nx0 cs = true ->
AP.sr_vars_lt (nxt cs) (s_regs (a_ss cs)) = true /\ AP.kn_vars_lt (nxt cs) (kn cs) = true
/\ maps_vars_lt (nxt cs) (a_maps cs) = true /\ pairs_vars_lt (nxt cs) (a_vis cs ++ a_ghost cs) = true
/\ AP.expr_vars_lt (nxt cs) (a_brk cs) = true /\ fd_vars_lt (nxt cs) (a_fd cs) = true /\ (nx0 <= nxt cs)%nat.
Proof. intros. eapply fresh_ok_parts; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_reg_sound : forall E cs R FULL model n,
CSOK E cs R FULL model -> (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (reg cs n).
Proof. intros. eapply reg_sound; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma call_core_same : forall cs E R FULL model T (ret : Z) sr2 k' nx2 regs' MR',
CSOK E cs R FULL model ->
msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
(mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
regs_ok E sr2 regs' ->
know_ok SEGS E MR' k' ->
(forall R' FULL' model',
CSOK E (with_ss cs (mk_ss ret sr2 k' nx2)) R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS (cfg_of SEGS R' ret FULL' model') T) ->
srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) T.
Proof.
intros cs E R FULL model T ret sr2 k' nx2 regs' MR' HC Hms HR' HK' Hk.
set (H := HID E cs model).
unfold cfg_of.
apply (srz_msteps_restricted_T SEGS H
(w_H_off_segments_cs E cs model) SEGS_wx (allowA A E cs)
(mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)) (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) model T
(w_lazy_cover_cs E cs R FULL model HC)
(w_A_wf_allowA E cs)
(co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC)).
- rewrite restrict_mkst. exact Hms.
- intros model' Hinv' Hsame Hclean.
set (FULL' := munrestrict H FULL MR').
change (unrestrict H (ms_mem (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS))) (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)))
with (mkst regs' (Z_to_bv 64 ret) FULL' (seg_rom SEGS)).
apply (Hk regs' FULL' model').
+ eapply (w_cs_ok_frame E cs R FULL model _ regs' FULL' model' HC Hsame).
* exact Hinv'.
* exact HR'.
* reflexivity.
* cbn [s_know mk_ss]. unfold Mr.
fold H. unfold FULL'. rewrite (mrestrict_munrestrict_clean H FULL MR') by (intros a Ha; exact (Hclean a Ha)).
exact HK'.
* intros a Ha. unfold FULL', munrestrict. fold H in Ha. rewrite Ha. reflexivity.
+ apply (same_but_materialized_frame _ _ Hsame).
Qed.

Theorem joinv_sound : forall args, node1_stmt SEGS A nx0 LIMIT USP SINV argH FS0 always (fun cs => node_joinv SEGS nx0 cs args).
Proof.
intros args cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn. unfold node_joinv in Hn.
destruct args as [|b [|[n| | | | | | |] [|? ?]]]; try discriminate.
destruct (split_lit b) as [bb bo] eqn:Hsl.
destruct (fresh_ok nx0 cs && Z.ltb 0 n && Z.leb n 8 && know_bytes_cov SEGS true (kn cs) bb bo (Z.to_nat n))%bool eqn:Ht; [|discriminate].
apply andb_prop in Ht as [Ht Hcov]. apply andb_prop in Ht as [Ht Hn8]. apply andb_prop in Ht as [Hfresh Hn0].
apply Z.ltb_lt in Hn0. apply Z.leb_le in Hn8.
injection Hn as <-.
set (v := s_next (a_ss cs)).
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
destruct (know_bytes_cov_sound SEGS true E _ (kn cs) bb (Z.to_nat n) bo HK Hcov ltac:(lia)) as [Hfl Hpt].

assert (Hbs : exists bs, rdn SEGS (MR E cs model FULL) (adenot E (SA bb bo)) (Z.to_nat n) = Some bs /\ length bs = Z.to_nat n).
{ apply rdn_defined; rewrite (flat_u E _ _ Hfl); [destruct Hfl as (?&?&?&?); lia | exact Hpt]. }
destruct Hbs as (bs & Hrd & Hlen).
set (w := Z_to_bv 64 (bytes_le_to_Z bs)).
set (E' := ext1 E v w).
pose proof (ext1_agree E v w) as Hag. fold E' in Hag.
assert (Hag0 : env_agree nx0 E E') by (eapply env_agree_le; [exact Hag | exact Fle]).
assert (HC1 : CSOK E' cs R FULL model) by (eapply w_cs_ok_agree; [exact Hag | exact Hfresh | exact HC]).

assert (Hbb : AP.expr_vars_lt (nxt cs) bb = true).
{ destruct (Z.to_nat n) as [|n'] eqn:En; [lia|]. cbn [know_bytes_cov] in Hcov. apply andb_prop in Hcov as [Hc1 _].
eapply know_byte_cov_vars; [exact Fkn | exact Hc1]. }
assert (Had : adenot E' (SA bb bo) = adenot E (SA bb bo)).
{ unfold adenot. cbn [a_base a_off]. rewrite (edenot_agree' (nxt cs) E E' bb Hag Hbb). reflexivity. }
assert (HH : HID E' cs model = HID E cs model) by (eapply w_hid_agree; [exact Hag | exact Fle | exact Fallow]).
apply (Hk E' R FULL model (conj Hag0 Hag)); [|reflexivity].
eapply (w_cs_ok_frame E' cs R FULL model _ R FULL model HC1 (same_but_materialized_refl _) (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC1));
[exact (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC1) | reflexivity | | intros; reflexivity].
cbn [s_know mk_ss]. constructor.
-
cbn [kentry_ok]. split; [lia|]. split.
+ unfold flat, estart in *. cbn [a_base a_off] in *. rewrite <- (edenot_agree' (nxt cs) E E' bb Hag Hbb). exact Hfl.
+ unfold Mr. rewrite HH. fold (MR E cs model FULL). rewrite Had, Hrd. f_equal.
cbn [edenot]. unfold E'. rewrite ext1_at. unfold w, word_to_le_bytes.
pose proof (AX2S.bytes_le_to_Z_bound bs) as Bb. rewrite Hlen in Bb.
assert (2 ^ (8 * Z.of_nat (Z.to_nat n)) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
rewrite (u_Z2bv (bytes_le_to_Z bs)) by lia. rewrite <- Hlen. symmetry. apply Z_to_le_bytes_to_Z.
-
eapply know_ok_cutout; [exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC1) | intros; reflexivity].
Qed.

Hypothesis SMEAR : smear_code SEGS.

Theorem smear47_sound : node1_stmt SEGS A nx0 LIMIT USP SINV argH FS0 always (fun cs => node_smear47_at JO6_SMEAR cs []).
Proof.
intros cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn. unfold node_smear47_at, JO6_SMEAR in Hn. cbn [Z.add Pos.add Pos.succ] in Hn.
destruct (Z.eqb (pc cs) 0x765b8) eqn:Hpc; [|discriminate]. apply Z.eqb_eq in Hpc.
destruct (erange (kn cs) (reg cs 10)) as [[lo hi]|] eqn:Hr; [|discriminate].
destruct (Z.leb (2 ^ 46) lo && Z.ltb hi (2 ^ 47))%bool eqn:Hb; [|discriminate].
apply andb_prop in Hb as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
injection Hn as <-.
pose proof (erange_sound SEGS E _ (kn cs) (reg cs 10) lo hi (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) Hr) as Hx.
pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in R10 by (apply bv_eq; reflexivity).
destruct (smear_run SEGS SMEAR R (MR E cs model FULL) (seg_rom SEGS) (edenot E (reg cs 10)) R10) as (regs' & Hms & H10 & H11 & H12 & H13 & H14 & H15 & Hag).
rewrite (smear_a0 (edenot E (reg cs 10)) ltac:(lia)) in H10. rewrite (smear_a5 (edenot E (reg cs 10)) ltac:(lia)) in H15.
change (srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) T).
set (sr := s_regs (a_ss cs)).
set (sr2 := sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr 10 (ELit (2 ^ 47 - 1))) 11 (ELit 0x5555555555555555))
12 (ELit 0x3333333333333333)) 13 (ELit 0x0f0f0f0f0f0f0f0f)) 14 (ELit 0x0101010101010101)) 15 (ELit 0x7fff)).
eapply (call_core_same cs E R FULL model T 0x76628 sr2 (kn cs) (nxt cs) regs' (MR E cs model FULL) HC).
- rewrite Hpc. replace (Z_to_bv 64 0x765b8) with (0x765b8%bv : word) by (apply bv_eq; reflexivity).
replace (Z_to_bv 64 0x76628) with (0x76628%bv : word) by (apply bv_eq; reflexivity). exact Hms.
-
set (R6 := regupd (regupd (regupd (regupd (regupd (regupd R
(Z_to_bv 5 (Z.of_nat 10)) (Z_to_bv 64 (2 ^ 47 - 1))) (Z_to_bv 5 (Z.of_nat 11)) (Z_to_bv 64 0x5555555555555555))
(Z_to_bv 5 (Z.of_nat 12)) (Z_to_bv 64 0x3333333333333333)) (Z_to_bv 5 (Z.of_nat 13)) (Z_to_bv 64 0x0f0f0f0f0f0f0f0f))
(Z_to_bv 5 (Z.of_nat 14)) (Z_to_bv 64 0x0101010101010101)) (Z_to_bv 5 (Z.of_nat 15)) (Z_to_bv 64 0x7fff)).
assert (HR6 : regs_ok E sr2 R6).
{ unfold sr2, R6. do 6 (apply regs_ok_set_n; [| lia | reflexivity]). exact (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC). }
unfold R6 in HR6.
replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in HR6 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in HR6 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 (Z.of_nat 12)) with (12%bv : bv 5) in HR6 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 (Z.of_nat 13)) with (13%bv : bv 5) in HR6 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 (Z.of_nat 14)) with (14%bv : bv 5) in HR6 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 (Z.of_nat 15)) with (15%bv : bv 5) in HR6 by (apply bv_eq; reflexivity).
intros r. rewrite <- (HR6 r).
destruct (in_dec (@bv_eq_dec 5) r smear_clob) as [Hin|Hnin].
+ unfold smear_clob in Hin. cbn [In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; rewrite ?H10, ?H11, ?H12, ?H13, ?H14, ?H15; gres; reflexivity.
+ rewrite (Hag r Hnin).
assert (N10 : r <> 10%bv) by (intros ->; apply Hnin; unfold smear_clob; cbn; tauto).
assert (N11 : r <> 11%bv) by (intros ->; apply Hnin; unfold smear_clob; cbn; tauto).
assert (N12 : r <> 12%bv) by (intros ->; apply Hnin; unfold smear_clob; cbn; tauto).
assert (N13 : r <> 13%bv) by (intros ->; apply Hnin; unfold smear_clob; cbn; tauto).
assert (N14 : r <> 14%bv) by (intros ->; apply Hnin; unfold smear_clob; cbn; tauto).
assert (N15 : r <> 15%bv) by (intros ->; apply Hnin; unfold smear_clob; cbn; tauto).
rewrite !getr_other by assumption. reflexivity.
- exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC).
- intros R' FULL' model' HC' Hfs. apply (Hk E R' FULL' model' (conj (env_agree_refl _ _) (env_agree_refl _ _))); [exact HC' | exact Hfs].
Qed.

Theorem xnjo6_ext_sound_gen : ext_stmt SEGS A nx0 LIMIT USP (XNjo6 SEGS nx0) SINV argH FS0.
Proof.
intros id args. destruct id as [|[|[|id]]].
- intros cs cs' E R FULL model T HC _ Hn Hk. discriminate Hn.
- exact (joinv_sound args).
- destruct args as [|a r]; [exact smear47_sound|]. intros cs cs' E R FULL model T HC _ Hn Hk. discriminate Hn.
- intros cs cs' E R FULL model T HC _ Hn Hk. discriminate Hn.
Qed.
End Sound.

Theorem xnjo6_ext_sound : forall nx0 LIMIT USP SINV argH FS0,
APS.nx0_ge nx0 ->
wx_segs_nowrap JO6SEGS ->
(forall a : word, in_hull AJO6 (bv_unsigned a) = false -> find_segment JO6SEGS (bv_unsigned a) 1 = None) ->
hull_ok AJO6 ->
(forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a) ->
(forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a) ->
(forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M') ->
(forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M) ->
ext_stmt JO6SEGS AJO6 nx0 LIMIT USP (XNjo6 JO6SEGS nx0) SINV argH FS0.
Proof.
intros. eapply xnjo6_ext_sound_gen; try eassumption. exact asegs_smear_code.
Qed.
