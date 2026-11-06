(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SumsLib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SumsLib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanSums2Code__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanIMemset AsanIMemcpy AsanMemIsZero AsanIStrncpy. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanSums2Code__Lib.AsanSumsCode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanSums2Code__Lib.AsanSums2Code OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanIMemset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanIMemcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanMemIsZero OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanIStrncpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Instance a3sums_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition a3_imemset_entry : word := 0x67a98.
Lemma a3_imemset_entry_eq : Z_to_bv 64 A_imemset = a3_imemset_entry.
Proof. apply bv_eq. reflexivity. Qed.
Lemma a3_imemset_code : code_at SEGS a3_imemset_entry 0 imemset_words.
Proof. unfold imemset_words. code_at_vm. Qed.

Theorem a3_imemset : forall mem0 (s c : word) n rom regs (ret : word),
  (0 <= n)%Z -> (bv_unsigned s + n < 2 ^ 64)%Z ->
  store_ok SEGS mem0 s (Z.to_nat n) = true ->
  (align15 n s = 0%Z -> n <> 0%Z -> (bv_unsigned c < 256)%Z) ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = s -> getr regs 11 = c -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 A_imemset) mem0 rom)
                (mkst regs' ret (wbytes mem0 s (repeat (Z_to_bv 8 (bv_unsigned c)) (Z.to_nat n))) rom)
    /\ regs_agree (fun r => In r imemset_clob) regs regs'.
Proof.
  intros mem0 s c n rom regs ret Hn Hnw Hok HC256.
  rewrite a3_imemset_entry_eq, <- (at_0 a3_imemset_entry).
  apply (imemset_run _ _ mem0 s c n rom a3_imemset_code Hn Hnw Hok HC256).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition a3_imemcpy_entry : word := 0x67a1c.
Lemma a3_imemcpy_entry_eq : Z_to_bv 64 A_imemcpy = a3_imemcpy_entry.
Proof. apply bv_eq. reflexivity. Qed.
Lemma a3_imemcpy_code : code_at SEGS a3_imemcpy_entry 0 imemcpy_words.
Proof. unfold imemcpy_words. code_at_vm. Qed.

Theorem a3_imemcpy : forall mem0 (dst src : word) n bs rom regs (ret : word),
  cpyH SEGS mem0 dst src n bs ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 A_imemcpy) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
    /\ regs_agree (fun r => In r imemcpy_clob) regs regs'.
Proof.
  intros mem0 dst src n bs rom regs ret HOK.
  rewrite a3_imemcpy_entry_eq, <- (at_0 a3_imemcpy_entry).
  apply (imemcpy_run _ _ mem0 dst src n bs rom a3_imemcpy_code HOK).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition a3_mem_is_zero_entry : word := 0x67fc8.
Lemma a3_mem_is_zero_entry_eq : Z_to_bv 64 A_mem_is_zero = a3_mem_is_zero_entry.
Proof. apply bv_eq. reflexivity. Qed.
Lemma a3_mem_is_zero_code : code_at SEGS a3_mem_is_zero_entry 0 memisz_words.
Proof. unfold memisz_words. code_at_vm. Qed.

Theorem a3_mem_is_zero : forall mem (beg sp : word) N rom regs (ret : word),
  (0 <= N <= 2 ^ 40)%Z ->
  (bv_unsigned beg + N + 8 <= 2 ^ 64)%Z ->
  (16 <= bv_unsigned sp)%Z ->
  store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
  (bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg)%Z ->
  (forall a : word, (bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N)%Z ->
     rdn SEGS mem a 1 = Some [Z_to_bv 8 0]) ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
  getr regs 10 = beg -> getr regs 11 = Z_to_bv 64 N ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 A_mem_is_zero) mem rom)
                (mkst regs' ret (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ret)) rom)
    /\ regs_agree (fun r => In r memisz_clob) regs regs'
    /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
  intros mem beg sp N rom regs ret.
  rewrite a3_mem_is_zero_entry_eq.
  apply (mem_is_zero_summary _ _ mem beg sp N rom regs ret a3_mem_is_zero_code).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition a3_istrncpy_entry : word := 0x67ec4.
Lemma a3_istrncpy_entry_eq : Z_to_bv 64 A_istrncpy = a3_istrncpy_entry.
Proof. apply bv_eq. reflexivity. Qed.
Definition a3_sealed_src : Z := 0x11854. (* [comment removed for export] *)

Lemma a3_istrncpy_code : code_at SEGS a3_istrncpy_entry 0 istrncpy_words.
Proof. unfold istrncpy_words. code_at_vm. Qed.

(* [comment removed for export] *)
Lemma a3_sealed_src_img : forall mem,
  (forall i, (a3_sealed_src <= i < a3_sealed_src + 9)%Z -> mem (Z_to_bv 64 i) = None) ->
  rdn SEGS mem (Z_to_bv 64 a3_sealed_src) 8 = Some sealed8
  /\ rdn SEGS mem (at_ (Z_to_bv 64 a3_sealed_src) 8) 1 = Some [Z_to_bv 8 0].
Proof.
  intros mem Hnone. unfold a3_sealed_src in *. split.
  - rewrite (rdn_ext _ 8 mem (fun _ => None)); [vm_compute; reflexivity | u_norm; cbn; lia |].
    intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hnone. revert Hx. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
  - rewrite (rdn_ext _ 1 mem (fun _ => None)); [vm_compute; reflexivity | rewrite at_u by (u_norm; lia); u_norm; cbn; lia |].
    intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hnone. revert Hx. rewrite at_u by (u_norm; lia). u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.

Theorem a3_istrncpy_sealed : forall mem0 (dst : word) rom regs (ret : word),
  (forall i, (a3_sealed_src <= i < a3_sealed_src + 9)%Z -> mem0 (Z_to_bv 64 i) = None) ->
  store_ok SEGS mem0 dst 4095%nat = true ->
  (bv_unsigned dst + 4095 < 2 ^ 64)%Z ->
  (bv_unsigned dst + 4095 <= a3_sealed_src \/ a3_sealed_src + 9 <= bv_unsigned dst)%Z ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = dst -> getr regs 11 = Z_to_bv 64 a3_sealed_src -> getr regs 12 = Z_to_bv 64 4095 ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 A_istrncpy) mem0 rom) (mkst regs' ret (wbytes mem0 dst strncpy_sealed_bytes) rom)
    /\ regs_agree (fun r => In r istrncpy_clob) regs regs'.
Proof.
  intros mem0 dst rom regs ret Hnone Hok Hnw Hdisj Hret H1 H10 H11 H12.
  destruct (a3_sealed_src_img mem0 Hnone) as [Hs Hn].
  rewrite a3_istrncpy_entry_eq, <- (at_0 a3_istrncpy_entry).
  apply (istrncpy_run _ _ mem0 dst (Z_to_bv 64 a3_sealed_src) rom a3_istrncpy_code Hs Hn); try assumption;
    unfold a3_sealed_src in *; u_norm; lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SumsLib.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanSums2Code__Lib.AsanSumsCode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanSums2Code__Lib.AsanSums2Code OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanIMemset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanIMemcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanMemIsZero OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanIStrncpy.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.TwB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Instance a3sums_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition a3_imemset_entry : word := 0x67b00.
Lemma a3_imemset_entry_eq : Z_to_bv 64 A_imemset = a3_imemset_entry.
Proof. apply bv_eq. reflexivity. Qed.
Lemma a3_imemset_code : code_at SEGS a3_imemset_entry 0 imemset_words.
Proof. unfold imemset_words. code_at_vm. Qed.

Theorem a3_imemset : forall mem0 (s c : word) n rom regs (ret : word),
  (0 <= n)%Z -> (bv_unsigned s + n < 2 ^ 64)%Z ->
  store_ok SEGS mem0 s (Z.to_nat n) = true ->
  (align15 n s = 0%Z -> n <> 0%Z -> (bv_unsigned c < 256)%Z) ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = s -> getr regs 11 = c -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 A_imemset) mem0 rom)
                (mkst regs' ret (wbytes mem0 s (repeat (Z_to_bv 8 (bv_unsigned c)) (Z.to_nat n))) rom)
    /\ regs_agree (fun r => In r imemset_clob) regs regs'.
Proof.
  intros mem0 s c n rom regs ret Hn Hnw Hok HC256.
  rewrite a3_imemset_entry_eq, <- (at_0 a3_imemset_entry).
  apply (imemset_run _ _ mem0 s c n rom a3_imemset_code Hn Hnw Hok HC256).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition a3_imemcpy_entry : word := 0x67a84.
Lemma a3_imemcpy_entry_eq : Z_to_bv 64 A_imemcpy = a3_imemcpy_entry.
Proof. apply bv_eq. reflexivity. Qed.
Lemma a3_imemcpy_code : code_at SEGS a3_imemcpy_entry 0 imemcpy_words.
Proof. unfold imemcpy_words. code_at_vm. Qed.

Theorem a3_imemcpy : forall mem0 (dst src : word) n bs rom regs (ret : word),
  cpyH SEGS mem0 dst src n bs ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 A_imemcpy) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
    /\ regs_agree (fun r => In r imemcpy_clob) regs regs'.
Proof.
  intros mem0 dst src n bs rom regs ret HOK.
  rewrite a3_imemcpy_entry_eq, <- (at_0 a3_imemcpy_entry).
  apply (imemcpy_run _ _ mem0 dst src n bs rom a3_imemcpy_code HOK).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition a3_mem_is_zero_entry : word := 0x68030.
Lemma a3_mem_is_zero_entry_eq : Z_to_bv 64 A_mem_is_zero = a3_mem_is_zero_entry.
Proof. apply bv_eq. reflexivity. Qed.
Lemma a3_mem_is_zero_code : code_at SEGS a3_mem_is_zero_entry 0 memisz_words.
Proof. unfold memisz_words. code_at_vm. Qed.

Theorem a3_mem_is_zero : forall mem (beg sp : word) N rom regs (ret : word),
  (0 <= N <= 2 ^ 40)%Z ->
  (bv_unsigned beg + N + 8 <= 2 ^ 64)%Z ->
  (16 <= bv_unsigned sp)%Z ->
  store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
  (bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg)%Z ->
  (forall a : word, (bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N)%Z ->
     rdn SEGS mem a 1 = Some [Z_to_bv 8 0]) ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
  getr regs 10 = beg -> getr regs 11 = Z_to_bv 64 N ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 A_mem_is_zero) mem rom)
                (mkst regs' ret (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ret)) rom)
    /\ regs_agree (fun r => In r memisz_clob) regs regs'
    /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
  intros mem beg sp N rom regs ret.
  rewrite a3_mem_is_zero_entry_eq.
  apply (mem_is_zero_summary _ _ mem beg sp N rom regs ret a3_mem_is_zero_code).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition a3_istrncpy_entry : word := 0x67f2c.
Lemma a3_istrncpy_entry_eq : Z_to_bv 64 A_istrncpy = a3_istrncpy_entry.
Proof. apply bv_eq. reflexivity. Qed.
Definition a3_sealed_src : Z := 0x11854. (* [comment removed for export] *)

Lemma a3_istrncpy_code : code_at SEGS a3_istrncpy_entry 0 istrncpy_words.
Proof. unfold istrncpy_words. code_at_vm. Qed.

(* [comment removed for export] *)
Lemma a3_sealed_src_img : forall mem,
  (forall i, (a3_sealed_src <= i < a3_sealed_src + 9)%Z -> mem (Z_to_bv 64 i) = None) ->
  rdn SEGS mem (Z_to_bv 64 a3_sealed_src) 8 = Some sealed8
  /\ rdn SEGS mem (at_ (Z_to_bv 64 a3_sealed_src) 8) 1 = Some [Z_to_bv 8 0].
Proof.
  intros mem Hnone. unfold a3_sealed_src in *. split.
  - rewrite (rdn_ext _ 8 mem (fun _ => None)); [vm_compute; reflexivity | u_norm; cbn; lia |].
    intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hnone. revert Hx. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
  - rewrite (rdn_ext _ 1 mem (fun _ => None)); [vm_compute; reflexivity | rewrite at_u by (u_norm; lia); u_norm; cbn; lia |].
    intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hnone. revert Hx. rewrite at_u by (u_norm; lia). u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.

Theorem a3_istrncpy_sealed : forall mem0 (dst : word) rom regs (ret : word),
  (forall i, (a3_sealed_src <= i < a3_sealed_src + 9)%Z -> mem0 (Z_to_bv 64 i) = None) ->
  store_ok SEGS mem0 dst 4095%nat = true ->
  (bv_unsigned dst + 4095 < 2 ^ 64)%Z ->
  (bv_unsigned dst + 4095 <= a3_sealed_src \/ a3_sealed_src + 9 <= bv_unsigned dst)%Z ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = dst -> getr regs 11 = Z_to_bv 64 a3_sealed_src -> getr regs 12 = Z_to_bv 64 4095 ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 A_istrncpy) mem0 rom) (mkst regs' ret (wbytes mem0 dst strncpy_sealed_bytes) rom)
    /\ regs_agree (fun r => In r istrncpy_clob) regs regs'.
Proof.
  intros mem0 dst rom regs ret Hnone Hok Hnw Hdisj Hret H1 H10 H11 H12.
  destruct (a3_sealed_src_img mem0 Hnone) as [Hs Hn].
  rewrite a3_istrncpy_entry_eq, <- (at_0 a3_istrncpy_entry).
  apply (istrncpy_run _ _ mem0 dst (Z_to_bv 64 a3_sealed_src) rom a3_istrncpy_code Hs Hn); try assumption;
    unfold a3_sealed_src in *; u_norm; lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End TwB.
(* [comment removed for export] *) Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
