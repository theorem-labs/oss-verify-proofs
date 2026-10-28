(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.simdjson.fuzz_dump.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import PropExec.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import SumsLib AsanIMemsetB AsanIMemcpyB AsanMemIsZeroB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import MemsetLib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require AsanMemsetB AsanMemset_codeB AsanMemcpyBaseB AsanMemcpyB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import AsanTablesB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import AsanPlanSoundSums.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation ASEGS := AsanUbsan.M.loaded_segments (only parsing).

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

Lemma asan_segs_wr : APSX.segs_wr_ok ASEGS.
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

Lemma asan_fill_spec_imemset : APSX.fill_spec ASEGS (AP.x_imemset ASAN_B) 256.
Proof.
  apply (fill_spec_of_imemset _ asan_imemset_entry); [apply bv_eq; reflexivity|].
  exact asan_imemset.
Qed.

Lemma asan_fill_spec_memset : APSX.fill_spec ASEGS (AP.x_memset ASAN_B) AX2.two64.
Proof.
  apply fill_spec_of_memset. intros mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1.
  exact (AsanMemsetB.memset_summary mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1).
Qed.

Lemma asan_copy_spec_imemcpy : APSX.copy_spec ASEGS (AP.x_imemcpy ASAN_B).
Proof.
  apply (copy_spec_of_imemcpy _ asan_imemcpy_entry); [apply bv_eq; reflexivity|].
  exact asan_imemcpy.
Qed.

Lemma asan_copy_spec_memcpy : APSX.copy_spec ASEGS (AP.x_memcpy ASAN_B).
Proof.
  intros mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
  pose proof (u64_range dst) as Hdr.
  assert (HOK : AsanMemcpyBaseB.mcH mem0 dst src n bs) by (constructor; try assumption; lia).
  destruct (AsanMemcpyB.ref_memcpy mem0 dst src n bs (seg_rom ASEGS) HOK regs ret Hret R1 R10 R11 R12) as (regs' & Hms & Hk).
  exists regs'. split; [replace (Z_to_bv 64 (AP.x_memcpy ASAN_B)) with (0x160884%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
  split; [apply kept_ok_of_keeps; exact Hk|].
  rewrite <- R10. apply Hk. unfold callee_kept. in_list.
Qed.

Lemma asan_miz_spec : APSX.miz_spec ASEGS (AP.x_memiszero ASAN_B).
Proof.
  apply (miz_spec_of_summary _ asan_mem_is_zero_entry); [apply bv_eq; reflexivity|].
  exact asan_mem_is_zero.
Qed.

