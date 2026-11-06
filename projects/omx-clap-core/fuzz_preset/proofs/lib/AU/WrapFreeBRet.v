(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset image B (asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43; relocated from pin f8f98a95bc52 by alreloc c4338d099cfb8025), the
   RETURN SEGMENT of the free interceptor: ___interceptor_free's epilogue from Deallocate's return
   (+0x1a8, B 0x539d4, after its `jal asan_free` at +0x1a4; asan_free tail-jumps to Deallocate, so Deallocate returns
   here) to its `ret` (+0x1cc, B_INTERCEPTOR_FREE_PC_OFF_1CC) and the jump to the caller:
     addi sp, sp, 0x60; ld ra / s0 .. s5 at 0x7e8 .. 0x7b8 (sp); addi sp, sp, 0x7f0; ret.
   The ten instructions load and add only: the run reads the interceptor's seven saved registers in its frame at
   [sp + 2072, sp + 2128) (sp = Deallocate's entry sp = the caller's sp - 2128) and stores nothing.
   Ported BY STATEMENT from the tail of lib/Reusable/YFh1.v:336-370 segN (the same epilogue, run there from +0x194 on
   the NULL arm: srr_run_to_sh to B_INTERCEPTOR_FREE_PC_OFF_1CC, SRr_ret_at, the callee-saved cases), with a seed of
   its own at +0x1a8: one region over the saved registers, valued by seven atoms (32 .. 38) of the caller's
   registers, as lib/AU/DGh1.v:121-146 runs Deallocate's NULL arm from an abstract frame.
   Code read: the runtime decode table YB1t.tfibtbl_rtF. No Admitted / Axiom. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgCellsB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a YB1w YE3d YFeq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The seed at +0x1a8: the saved-register region based at sp (atom 2), not writable, its seven words the atoms 32
   (ra) .. 38 (s5); the stack pointer's range and alignment. *)
Definition RA_FREE : Z := B_INTERCEPTOR_FREE_PC + 0x1a8.
Definition RSV : YP09.region := YP09.mkRegion (Some 2%nat) 2072 2128 0 0
[ YP09.mkChunk 2072 (CVal 8 (SOff 38%nat 0)); YP09.mkChunk 2080 (CVal 8 (SOff 37%nat 0));
  YP09.mkChunk 2088 (CVal 8 (SOff 36%nat 0)); YP09.mkChunk 2096 (CVal 8 (SOff 35%nat 0));
  YP09.mkChunk 2104 (CVal 8 (SOff 34%nat 0)); YP09.mkChunk 2112 (CVal 8 (SOff 33%nat 0));
  YP09.mkChunk 2120 (CVal 8 (SOff 32%nat 0)) ].
Definition FFR : facts := mkFacts [(2%nat, mkAF kHighMemBeg kHighMemEnd 4)] [] [].
Definition SSR : sstate := mkSS RA_FREE sr_atoms [RSV] None FFR.

Section WK.
Variable W : world tfibsegs.
(* regs: the caller's registers at __wrap_free's entry; regs2 / mem2: the machine at Deallocate's return. *)
Variables (regs regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model).
Variable mat0 : list word.
Let spD : Z := bv_unsigned (getr regs2 2).
Let m0 := mrestrict (w_H W) mem2.
Hypothesis Hlo : kHighMemBeg <= spD.
Hypothesis Hhi : spD + 2128 <= kHighMemEnd.
Hypothesis Hal : spD mod 16 = 0.
Hypothesis Hra : YK0s.ret_ok (getr regs 1).
Hypothesis V1 : val_mem tfibsegs m0 (spD + 2120) 8 (bv_unsigned (getr regs 1)).
Hypothesis V8 : val_mem tfibsegs m0 (spD + 2112) 8 (bv_unsigned (getr regs 8)).
Hypothesis V9 : val_mem tfibsegs m0 (spD + 2104) 8 (bv_unsigned (getr regs 9)).
Hypothesis V18 : val_mem tfibsegs m0 (spD + 2096) 8 (bv_unsigned (getr regs 18)).
Hypothesis V19 : val_mem tfibsegs m0 (spD + 2088) 8 (bv_unsigned (getr regs 19)).
Hypothesis V20 : val_mem tfibsegs m0 (spD + 2080) 8 (bv_unsigned (getr regs 20)).
Hypothesis V21 : val_mem tfibsegs m0 (spD + 2072) 8 (bv_unsigned (getr regs 21)).
Definition XWr : list word :=
[ getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21 ].
Local Notation E0 := (Ereg regs2 XWr).
Let cfg0 : config := mkCfg (mkst regs2 (w64 RA_FREE) mem2 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md2) mat0 md2).

Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs2 r.
Proof. intros Hk. exact (ew_Ereg_nat regs2 XWr k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs2 2. Proof. exact (Er 2 2%bv eq_refl). Qed.

Lemma chunk_saved : forall a k (r : bv 5), ew E0 k = getr regs r ->
val_mem tfibsegs m0 (spD + a) 8 (bv_unsigned (getr regs r)) ->
YP09.chunk_ok tfibsegs E0 m0 spD (YP09.mkChunk a (CVal 8 (SOff k 0))).
Proof.
intros a k r Hk Hm. eapply chunk_ok_val; [| | | exact Hm].
- cbn [sv_denot]. rewrite Hk, ?Z.add_0_r. first [reflexivity | apply Z_to_bv_bv_unsigned | symmetry; apply Z_to_bv_bv_unsigned].
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply u64_range.
- lia.
Qed.

Lemma SEED_ok : st_ok tfibsegs E0 SSR (restrict (w_H W) (mkst regs2 (w64 RA_FREE) mem2 (seg_rom tfibsegs))).
Proof.
assert (Usp : 0 <= spD < 2 ^ 64) by (unfold spD; apply u64_range).
rewrite restrict_mkst_fx. unfold SSR, w64. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
unfold region_ok, RSV. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E2. fold spD.
split; [lia|]. split; [unfold kHighMemEnd in Hhi; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_saved 2072 38 21%bv); [reflexivity | exact V21] |].
apply Forall_cons; [apply (chunk_saved 2080 37 20%bv); [reflexivity | exact V20] |].
apply Forall_cons; [apply (chunk_saved 2088 36 19%bv); [reflexivity | exact V19] |].
apply Forall_cons; [apply (chunk_saved 2096 35 18%bv); [reflexivity | exact V18] |].
apply Forall_cons; [apply (chunk_saved 2104 34 9%bv); [reflexivity | exact V9] |].
apply Forall_cons; [apply (chunk_saved 2112 33 8%bv); [reflexivity | exact V8] |].
apply Forall_cons; [apply (chunk_saved 2120 32 1%bv); [reflexivity | exact V1] |].
apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. split; exact I.
- split; [|split; exact I]. cbn [FFR f_atoms atoms_ok]. split; [|exact I].
unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2. fold spD. change (2 ^ 4) with 16. unfold kHighMemBeg, kHighMemEnd in *. lia.
Qed.

(* The state at the caller's return: the saved registers restored, sp back at the caller's, gp, tp and s6 .. s11 as
   Deallocate left them, memory unchanged. *)
Definition at_RETF (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md2) mat md2) /\
getr regs' 1 = getr regs 1 /\ getr regs' 2 = w64 (spD + 2128) /\
getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\
getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\
getr regs' 3 = getr regs2 3 /\ getr regs' 4 = getr regs2 4 /\
(forall r : Z, 22 <= r <= 27 -> getr regs' (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) /\
(forall x : word, mem' x = mem2 x).

Lemma seg_ret : SRr tfibsegs W cfg0 at_RETF.
Proof.
pose proof Hwx_tfa as Hwx. pose proof SEED_ok as HS.
assert (Usp : 0 <= spD < 2 ^ 64) by (unfold spD; apply u64_range).
(* YFh1.v:336-351: the run to the `ret` at +0x1cc. *)
srr_run_to_sh tfibtbl_rtF_ok HS B_INTERCEPTOR_FREE_PC_OFF_1CC. clear HFr.
lazymatch type of HS with st_ok _ ?E _ (restrict _ ?msx) => rename msx into msR; set (En := E) in HS end.
assert (HEn : forall k, (k < aHAVf)%nat -> ew En k = ew E0 k) by (intros k _; subst En; reflexivity).
assert (FRR : forall y : word, ms_mem msR y = mem2 y).
{ intros y. apply HF. intros Hw. destruct (in_wrange_windows En _ _ Hw) as (b & lo & hi & Hin & Hr).
lazymatch type of Hin with In _ (windows ?rs) => let ws := eval vm_compute in (windows rs) in change (windows rs) with ws in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn [fst snd base_val] in Hr; lia |]).
destruct Hin. }
clear HF.
eapply (SRr_ret_at tfibsegs tfibtbl_rtF tfibtbl_rtF_ok Hwx W En); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|].
rreg HS (1%bv : bv 5) Q1.
exists (ms_regs msR), (ms_mem msR), mat'.
split. { rewrite Q1. subst En. change (ew (Ereg regs2 XWr) 32) with (getr regs 1). unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split. { rewrite Q1. subst En. first [reflexivity | (cbn; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned)]. }
split. { rreg HS (2%bv : bv 5) R; rewrite R. subst En. rewrite E2. unfold w64, spD. f_equal; lia. }
split. { rreg HS (8%bv : bv 5) R; rewrite R. subst En. first [reflexivity | (cbn; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned)]. }
split. { rreg HS (9%bv : bv 5) R; rewrite R. subst En. first [reflexivity | (cbn; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned)]. }
split. { rreg HS (18%bv : bv 5) R; rewrite R. subst En. first [reflexivity | (cbn; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned)]. }
split. { rreg HS (19%bv : bv 5) R; rewrite R. subst En. first [reflexivity | (cbn; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned)]. }
split. { rreg HS (20%bv : bv 5) R; rewrite R. subst En. first [reflexivity | (cbn; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned)]. }
split. { rreg HS (21%bv : bv 5) R; rewrite R. subst En. first [reflexivity | (cbn; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned)]. }
split. { rreg HS (3%bv : bv 5) R; rewrite R. subst En. apply Er. reflexivity. }
split. { rreg HS (4%bv : bv 5) R; rewrite R. subst En. apply Er. reflexivity. }
split. { intros r Hr. assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia. clear Hr.
repeat match type of Hr' with _ \/ _ => destruct Hr' as [Hr'|Hr'] end; subst r;
lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
let kb := eval vm_compute in (Z_to_bv 5 k : bv 5) in
let RR := fresh "RR" in rreg HS kb RR; change (Z_to_bv 5 k) with kb; rewrite RR; subst En; apply Er; reflexivity end. }
exact FRR.
Qed.
End WK.
End c.
