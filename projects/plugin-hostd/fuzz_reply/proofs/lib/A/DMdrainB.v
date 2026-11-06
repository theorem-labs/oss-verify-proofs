(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainB.v (commit fe876300d09, Quarantine::Drain walk set; file sha256 6906800fe2f2) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 1 image addresses moved by code-verified function pairs (1 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 2 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the SEED of the segment at 0x33a38 (Recycle after MergeBatches,
   DMseg_rj.v), i.e. DMseg_rj.free_hyps (DMseg_rj.v:78-84) in full, from the memory and register facts
   MergeBatches' return leaves (DMwalkIF.mb_post): the two lock bytes, the global list's count / first / bytes
   words, the temp list's count / last words on Recycle's frame, and the three saved registers s0 / s1 / s2.  The
   construction is DMdeq.SEED1_ok's (DMdeq.v:290-385) for this shell's three regions and five atoms.
   rule 24: no function proved (kind: the seed of a segment already walked, DMseg_rj.segR; the lane's reuse
   search is LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain`
   2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
   - [rj_seed]: st_ok at 0x33a38 over DMseg_rj.SS0;
   - [rj_free_hyps]: DMseg_rj.free_hyps, so DMseg_rj.segR applies.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFew AFff AFeu AFey AFgj AFgl AFh0 AFev AB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DMseg_rj.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variables (W : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte).
Variables (lcnt lfirst lbytes tcnt tlast : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let m := mrestrict (w_H W) mem0.
(* the registers MergeBatches returns unchanged (mb_pre's mb_s0 / mb_s1 / mb_s2 through mb_post's SREGSX) *)
Hypothesis Q8 : getr regs0 8 = w64 (A_QUAR + 160).
Hypothesis Q9 : getr regs0 9 = w64 kQuarantineMin.
Hypothesis Q18 : getr regs0 18 = w64 A_QUAR.
(* Recycle's sp (mb_pre's mb_sp / mb_sp_al) *)
Hypothesis Hsp : kHighMemBeg <= sp0 /\ sp0 + 32 <= kHighMemEnd.
Hypothesis Hal : sp0 mod 16 = 0.
(* the value ranges (DMdrainS.rj_Hl / rj_Ht) *)
Hypothesis Hl : 0 <= lcnt <= 2 ^ 40 /\ 0 <= lfirst < ASAN_CEIL /\ lfirst mod 8192 = 0 /\ 0 <= lbytes <= 2 ^ 31.
Hypothesis Ht : 0 <= tcnt <= 2 ^ 40 /\ 0 <= tlast < ASAN_CEIL /\ tlast mod 8192 = 0.
(* the cells mb_post leaves *)
Hypothesis VQW : val_mem tfibsegs m (A_QUAR + 152) 4 257.
Hypothesis VQS : val_mem tfibsegs m (A_QUAR + 160) 8 lcnt.
Hypothesis VQF : val_mem tfibsegs m (A_QUAR + 168) 8 lfirst.
Hypothesis VQB : val_mem tfibsegs m (A_QUAR + 184) 8 lbytes.
Hypothesis VT0 : val_mem tfibsegs m sp0 8 tcnt.
Hypothesis VT16 : val_mem tfibsegs m (sp0 + 16) 8 tlast.

Local Notation E0 := (DMseg_rj.E0 regs0 lcnt lfirst lbytes tcnt tlast).
Lemma E0r (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (DMseg_rj.Er regs0 lcnt lfirst lbytes tcnt tlast k r Hk). Qed.
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

Lemma REG_ok : Forall (region_ok tfibsegs E0 m) DMseg_rj.REG0.
Proof.
pose proof Usp as U. destruct Hsp as [S1 S2]. destruct Hl as (L1 & L2 & L3 & L4). destruct Ht as (T1 & T2 & T3).
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL in *.
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite (E0r 2 2%bv eq_refl); reflexivity).
unfold DMseg_rj.REG0, DMseg_rj.R_QW, DMseg_rj.R_LH, DMseg_rj.R_STK.
apply Forall_cons.
{ reg_intro. split; [unfold A_QUAR, A_ALLOCATOR, o_quar; lia|]. split; [unfold A_QUAR, A_ALLOCATOR, o_quar; lia|]. split.
  { intros o Ho. apply rw_writable. unfold A_QUAR, A_ALLOCATOR, o_quar in Ho. lia. }
  pose proof (proj1 (val_mem4_bytes _ _ _) VQW) as (W0 & W1 & W2 & W3).
  change (YO0f.le_byte 257 4 0) with 1 in W0. change (YO0f.le_byte 257 4 1) with 1 in W1.
  change (YO0f.le_byte 257 4 2) with 0 in W2. change (YO0f.le_byte 257 4 3) with 0 in W3.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | apply (proj2 (val_mem1_byte _ _ _)); rewrite Z.add_0_l; exact W0].
  - eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | apply (proj2 (val_mem1_byte _ _ _)); rewrite Z.add_0_l;
      replace (A_QUAR + 153) with (A_QUAR + 152 + 1) by lia; exact W1].
  - apply chunk_ok_zero_mb. intros i Hi. rewrite Z.add_0_l.
    assert (C : i = 0 \/ i = 1) by lia. destruct C as [-> | ->];
    [replace (A_QUAR + 154 + 0) with (A_QUAR + 152 + 2) by lia; exact W2 | replace (A_QUAR + 154 + 1) with (A_QUAR + 152 + 3) by lia; exact W3]. }
apply Forall_cons.
{ reg_intro. split; [unfold A_QUAR, A_ALLOCATOR, o_quar; lia|]. split; [unfold A_QUAR, A_ALLOCATOR, o_quar; lia|]. split.
  { intros o Ho. lia. }
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - apply (chunk_atom1 0 _ 8 32%nat lcnt); [reflexivity | lia | rewrite Z.add_0_l; exact VQS | r8 | cbn; lia].
  - apply (chunk_atom1 0 _ 8 33%nat lfirst); [reflexivity | lia | rewrite Z.add_0_l; exact VQF | r8 | cbn; lia].
  - apply (chunk_atom1 0 _ 8 34%nat lbytes); [reflexivity | lia | rewrite Z.add_0_l; exact VQB | r8 | cbn; lia]. }
apply Forall_cons; [|apply Forall_nil].
{ reg_intro. rewrite BV2. split; [lia|]. split; [lia|]. split.
  { intros o Ho. lia. }
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (chunk_atom1 _ _ 8 35%nat tcnt); [reflexivity | lia | rewrite Z.add_0_r; exact VT0 | r8 | cbn; lia].
  - apply (chunk_atom1 _ _ 8 36%nat tlast); [reflexivity | lia | exact VT16 | r8 | cbn; lia]. }
Qed.

Lemma PAIRS_ok : pairwise_disjoint E0 DMseg_rj.REG0.
Proof.
pose proof Usp as U. destruct Hsp as [S1 S2].
apply pairwise_disjoint_of_extents. unfold DMseg_rj.REG0, DMseg_rj.R_QW, DMseg_rj.R_LH, DMseg_rj.R_STK, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite (E0r 2 2%bv eq_refl). fold sp0.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. unfold A_QUAR, A_ALLOCATOR, o_quar.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
Qed.

Lemma FACTS_ok : atoms_ok E0 (f_atoms DMseg_rj.FFR).
Proof.
pose proof Usp as U. destruct Hsp as [S1 S2]. destruct Hl as (L1 & L2 & L3 & L4). destruct Ht as (T1 & T2 & T3).
assert (AF : forall k0 Xv lo hi al, ew E0 k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
assert (E2' : ew E0 2 = w64 sp0) by (rewrite (E0r 2 2%bv eq_refl); unfold sp0, w64; symmetry; apply Z_to_bv_bv_unsigned).
cbn [DMseg_rj.FFR f_atoms atoms_ok]. ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL in *.
split. { apply (AF 2%nat sp0); [exact E2' | | | |]. all: first [lia | change (2 ^ 4) with 16; exact Hal]. }
split. { apply (AF 32%nat lcnt); [reflexivity | | | |]. all: first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 33%nat lfirst); [reflexivity | | | |]. all: first [lia | change (2 ^ 13) with 8192; exact L3]. }
split. { apply (AF 34%nat lbytes); [reflexivity | | | |]. all: first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 35%nat tcnt); [reflexivity | | | |]. all: first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split; [|exact I]. { apply (AF 36%nat tlast); [reflexivity | | | |]. all: first [lia | change (2 ^ 13) with 8192; exact T3]. }
Qed.

Lemma rj_seed : st_ok tfibsegs E0 DMseg_rj.SS0 (restrict (w_H W) (mkst regs0 (w64 0x33a38) mem0 (seg_rom tfibsegs))).
Proof.
rewrite restrict_mkst_fx. unfold DMseg_rj.SS0, DMseg_rj.SR0, sr_set. cbn [bv_eqb]. unfold DMseg_rj.E0, w64.
apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros XX; discriminate | cbn [sv_denot]; exact Q8] | intros XX; discriminate | cbn [sv_denot]; exact Q9] | intros XX; discriminate | cbn [sv_denot]; exact Q18].
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. exact REG_ok.
- exact PAIRS_ok.
- split; [exact FACTS_ok | split; exact I].
Qed.

Theorem rj_free_hyps : DMseg_rj.free_hyps W regs0 mem0 lcnt lfirst lbytes tcnt tlast.
Proof.
constructor.
- exact Hsp.
- exact Hal.
- destruct Hl as (L1 & L2 & L3 & L4). splits; first [exact L3 | lia].
- destruct Ht as (T1 & T2 & T3). splits; first [exact T3 | lia].
- exact rj_seed.
Qed.
End d.
End c.
