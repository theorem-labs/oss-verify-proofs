(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainT9.v (commit 67fc7ef5787c2195464dbe4d4f7905278328dc0c, drain recycle tail; file sha256 c30137e54acf) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 1 image addresses moved by code-verified function pairs (1 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the SEED of the drain's EPILOGUE - YFgt.free_hyps (YFgt.v:62-69)
   for the tail at 0x33b00, where Recycle restores ra / s0 / s1 / s2 / s3 / s4 from its frame and returns
   (YFgt.segX's at_RETX, YFgt.v:106-111; the walk writes nothing, YFgt.WIN = False).  The six saved words are
   the ones Recycle's prologue wrote and no later walk touched: DoRecycle's changed set is
   [sp1 - DRSTACK_X, sp1 + 32) with sp1 = sp0 - 80, which stops at sp0 - 48, below the saved registers.
   rule 24: no function proved (kind: the seed of a segment already walked, YFgt.segX; the lane's reuse search
   is LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain`
   2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
   Additive: no existing file is touched. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0l YG0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AFeq AFex AFf2 AFfu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFfj.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFew AFff AFeu AFey AFgj AFgl AFh0 AFev AB13 AFgt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (vra vs0 vs1 vs2 vs3 vs4 : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let m := mrestrict (w_H W) mem0.
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Hra : YK0s.ret_ok (w64 vra).
Hypothesis Hsp : kHighMemBeg <= sp0 /\ sp0 + LFRAME <= kHighMemEnd.
Hypothesis Hal : sp0 mod 16 = 0.
Hypothesis Hvals : 0 <= vra < 2 ^ 64 /\ 0 <= vs0 < 2 ^ 64 /\ 0 <= vs1 < 2 ^ 64 /\ 0 <= vs2 < 2 ^ 64 /\ 0 <= vs3 < 2 ^ 64 /\ 0 <= vs4 < 2 ^ 64.
(* the six saved words still on Recycle's frame *)
Hypothesis V72 : val_mem tfibsegs m (sp0 + 72) 8 vra.
Hypothesis V64 : val_mem tfibsegs m (sp0 + 64) 8 vs0.
Hypothesis V56 : val_mem tfibsegs m (sp0 + 56) 8 vs1.
Hypothesis V48 : val_mem tfibsegs m (sp0 + 48) 8 vs2.
Hypothesis V40 : val_mem tfibsegs m (sp0 + 40) 8 vs3.
Hypothesis V32 : val_mem tfibsegs m (sp0 + 32) 8 vs4.

Local Notation E0 := (AFgt.E0 regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac r8 := change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia.
Lemma chunk_atom1 : forall base a (w : BinNums.N) k0 x, ew E0 k0 = w64 x -> 0 <= x < 2 ^ 64 ->
val_mem tfibsegs m (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m base (YP09.mkChunk a (CVal w (SOff k0 0))).
Proof.
intros base a w k0 x Hk0 Hr Hm Hx Hw. eapply chunk_ok_val; [| exact Hx | exact Hw | exact Hm].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
Qed.
Lemma Usp : 0 <= sp0 < 2 ^ 64.
Proof. unfold sp0. apply u64_range. Qed.

Lemma REG_ok : Forall (region_ok tfibsegs E0 m) AFgt.REG0.
Proof.
pose proof Usp as U. destruct Hsp as [S1 S2]. destruct Hvals as (R0 & R1 & R2 & R3 & R4 & R5).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite (AFgt.E2 regs0 vra vs0 vs1 vs2 vs3 vs4); reflexivity).
unfold AFgt.REG0, AFgt.R_STK.
apply Forall_cons; [|apply Forall_nil].
reg_intro. rewrite BV2. unfold kHighMemBeg, kHighMemEnd, LFRAME in *.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]].
- apply (chunk_atom1 _ _ 8 32%nat vra); [reflexivity | lia | exact V72 | r8 | cbn; lia].
- apply (chunk_atom1 _ _ 8 33%nat vs0); [reflexivity | lia | exact V64 | r8 | cbn; lia].
- apply (chunk_atom1 _ _ 8 34%nat vs1); [reflexivity | lia | exact V56 | r8 | cbn; lia].
- apply (chunk_atom1 _ _ 8 35%nat vs2); [reflexivity | lia | exact V48 | r8 | cbn; lia].
- apply (chunk_atom1 _ _ 8 36%nat vs3); [reflexivity | lia | exact V40 | r8 | cbn; lia].
- apply (chunk_atom1 _ _ 8 37%nat vs4); [reflexivity | lia | exact V32 | r8 | cbn; lia].
Qed.

Lemma PAIRS_ok : pairwise_disjoint E0 AFgt.REG0.
Proof. apply pairwise_disjoint_of_extents. cbn [AFgt.REG0 map]. cbn [zpairwise_disjoint zall_disjoint]. split; exact I. Qed.

Lemma FACTS_ok : atoms_ok E0 (f_atoms AFgt.FFX).
Proof.
pose proof Usp as U. destruct Hsp as [S1 S2]. destruct Hvals as (R0 & R1 & R2 & R3 & R4 & R5).
assert (AF : forall k0 Xv lo hi al, ew E0 k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
assert (E2' : ew E0 2 = w64 sp0) by (rewrite (AFgt.E2 regs0 vra vs0 vs1 vs2 vs3 vs4); unfold sp0, w64; symmetry; apply Z_to_bv_bv_unsigned).
cbn [AFgt.FFX f_atoms atoms_ok]. unfold kHighMemBeg, kHighMemEnd, LFRAME in *.
split. { apply (AF 2%nat sp0); [exact E2' | lia | lia | change (2 ^ 4) with 16; exact Hal | lia]. }
split. { apply (AF 32%nat vra); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (AF 33%nat vs0); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (AF 34%nat vs1); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (AF 35%nat vs2); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (AF 36%nat vs3); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split; [|exact I]. { apply (AF 37%nat vs4); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
Qed.

Lemma epi_seed : st_ok tfibsegs E0 AFgt.SS0
(restrict (w_H W) (mkst regs0 (w64 0x33b00) mem0 (seg_rom tfibsegs))).
Proof.
rewrite restrict_mkst_fx. unfold AFgt.SS0, AFgt.SR0, sr_set. cbn [bv_eqb]. unfold AFgt.E0, w64.
apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | intros XX; discriminate | cbn [sv_denot]; exact Htp].
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. exact REG_ok.
- exact PAIRS_ok.
- split; [exact FACTS_ok | split; exact I].
Qed.

Theorem epi_free_hyps : AFgt.free_hyps W regs0 mem0 vra vs0 vs1 vs2 vs3 vs4.
Proof.
constructor.
- exact Htp.
- exact Hra.
- exact Hsp.
- exact Hal.
- exact Hvals.
- exact epi_seed.
Qed.
End d.
End c.
