(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset image B (asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43; relocated from pin f8f98a95bc52 by alreloc c4338d099cfb8025), the
   RETURN SEGMENT of the malloc interceptor: Allocate's return address in asan_malloc (B 0x32674) to
   ___interceptor_malloc's `ret` (0x53b54) and the return to the caller, in its two arms:
   - a0 <> 0 (a block): asan_malloc's epilogue (0x32678-0x32684) and the interceptor's (0x53b30-0x53b54); no store;
   - a0 = 0 (PNull): SetErrnoToENOMEM (0x6d484; __errno_location 0x8f828 = tp - 0xa4) stores errno := 12, then the
     same epilogues.
   Code read: YB1q.tfibtbl_rtA. Ported BY STATEMENT from the donors' tails over cgif's ARm: the NULL arm's errno region
   and its check, lib/Reusable/YFjj.v:475-578 (PNULL, segR; errR of YFi4.v:105); the return at the interceptor's `ret`,
   lib/Reusable/YFh1.v:351-370 (SRr_ret_at, the callee-saved registers). The seeds below are the state at 0x32674 the
   call segment's invariant K_B (WrapMallocBM1.v) and Allocate's post leave: the two frames' saved words, the
   caller's register values as environment atoms 32..38 (ra, s0, s1, s2..s5), and, in the NULL arm, the writable
   16 bytes below the stack pointer (SetErrnoToENOMEM's frame) and errno. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a YB1w YE3d YFeq YB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The environment: the registers at Allocate's return and the caller's ra, s0, s1, s2, s3, s4, s5. *)
Definition XWr (regs : bvmap 5 word) : list word :=
[ getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21 ].
Definition Er2 (regs2 regs : bvmap 5 word) : env := Ereg regs2 (XWr regs).
(* asan_malloc's frame [sp, sp + 16): the interceptor's s0 (= the caller's sp, sp + 2144) and ra (0x53b30). *)
Definition RAF : YP09.region := YP09.mkRegion (Some 2%nat) 0 16 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 2 2144)); YP09.mkChunk 8 (CVal 8 (SLit 0x53b30))].
(* the interceptor's saved registers [sp + 2088, sp + 2144) = [caller sp - 56, caller sp). *)
Definition RSV : YP09.region := YP09.mkRegion (Some 2%nat) 2088 2144 0 0
[YP09.mkChunk 2088 (CVal 8 (SOff 38 0)); YP09.mkChunk 2096 (CVal 8 (SOff 37 0)); YP09.mkChunk 2104 (CVal 8 (SOff 36 0));
 YP09.mkChunk 2112 (CVal 8 (SOff 35 0)); YP09.mkChunk 2120 (CVal 8 (SOff 34 0)); YP09.mkChunk 2128 (CVal 8 (SOff 33 0));
 YP09.mkChunk 2136 (CVal 8 (SOff 32 0))].
(* SetErrnoToENOMEM's frame and errno (errR, YFi4.v:105; checked at YFjj.v:511-512), the NULL arm only. *)
Definition RWF : YP09.region := YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [].
Definition RER : YP09.region := YP09.mkRegion None TFIB_ERRNO (TFIB_ERRNO + 4) TFIB_ERRNO (TFIB_ERRNO + 4) [].
Definition FFR : facts := mkFacts [ (2%nat, mkAF (kHighMemBeg + ASTACK - 2144) (kHighMemEnd - 2144) 4) ] [] [].
Definition SSB : sstate := mkSS 0x32674 (sr_set sr_atoms 4%bv (SLit TFIB_TP)) [RAF; RSV] None FFR.
Definition SSN : sstate := mkSS 0x32674 (sr_set (sr_set sr_atoms 4%bv (SLit TFIB_TP)) 10%bv (SLit 0)) [RAF; RSV; RWF; RER] None FFR.

Section WK.
Variables (W2 : world tfibsegs) (regs2 regs : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) (mat2 : list word).
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation E := (Er2 regs2 regs).
Let m2 := mrestrict (w_H W2) mem2.
Hypothesis Hsp : kHighMemBeg + ASTACK <= sp0 <= kHighMemEnd /\ sp0 mod 16 = 0.
Hypothesis Hsp2 : getr regs2 2 = w64 (sp0 - 2144).
Hypothesis Htp2 : getr regs2 4 = w64 TFIB_TP.
Hypothesis VA0 : val_mem tfibsegs m2 (sp0 - 2144) 8 sp0.
Hypothesis VA1 : val_mem tfibsegs m2 (sp0 - 2136) 8 0x53b30.
Hypothesis V1 : val_mem tfibsegs m2 (sp0 - 8) 8 (bv_unsigned (getr regs 1)).
Hypothesis V8 : val_mem tfibsegs m2 (sp0 - 16) 8 (bv_unsigned (getr regs 8)).
Hypothesis V9 : val_mem tfibsegs m2 (sp0 - 24) 8 (bv_unsigned (getr regs 9)).
Hypothesis V18 : val_mem tfibsegs m2 (sp0 - 32) 8 (bv_unsigned (getr regs 18)).
Hypothesis V19 : val_mem tfibsegs m2 (sp0 - 40) 8 (bv_unsigned (getr regs 19)).
Hypothesis V20 : val_mem tfibsegs m2 (sp0 - 48) 8 (bv_unsigned (getr regs 20)).
Hypothesis V21 : val_mem tfibsegs m2 (sp0 - 56) 8 (bv_unsigned (getr regs 21)).

Lemma Esp : bv_unsigned (ew E 2) = sp0 - 2144.
Proof. unfold Er2. rewrite (ew_Ereg_nat regs2 (XWr regs) 2 2%bv eq_refl), Hsp2. unfold w64. apply unsigned_lit_small. unfold kHighMemBeg, kHighMemEnd, ASTACK in Hsp. lia. Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Lemma sp_range : 0x10007fff8000 <= sp0 - 2160 /\ sp0 <= 0x800000000000.
Proof. destruct Hsp as [[H1 H2] _]. unfold kHighMemBeg, kHighMemEnd, ASTACK in *. lia. Qed.
Ltac spc := pose proof sp_range; lia.
Lemma chunk_at : forall off (r : bv 5) j, nth j (XWr regs) (Z_to_bv 64 0) = getr regs r ->
val_mem tfibsegs m2 (sp0 - 2144 + off) 8 (bv_unsigned (getr regs r)) ->
YP09.chunk_ok tfibsegs E m2 (sp0 - 2144) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0))).
Proof.
intros off r j Hn Hm. eapply chunk_ok_val; [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply u64_range | cbn; lia | exact Hm].
cbn [sv_denot]. unfold Er2. rewrite (ew_Ereg_extra regs2 (XWr regs) j), Hn. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma RAF_ok : region_ok tfibsegs E m2 RAF.
Proof.
unfold region_ok, RAF; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]; replace (base_val E (Some 2%nat)) with (sp0 - 2144) by (cbn [base_val]; symmetry; exact Esp). split; [spc|]. split; [spc|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_ok_val tfibsegs _ _ _ 0 8 _ sp0); [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); spc | cbn; lia | rewrite Z.add_0_r; exact VA0].
cbn [sv_denot]. unfold Er2. rewrite (ew_Ereg_nat regs2 (XWr regs) 2 2%bv eq_refl), Hsp2. unfold w64.
rewrite unsigned_lit_small by spc. f_equal. lia.
- eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | replace (sp0 - 2144 + 8) with (sp0 - 2136) by lia; exact VA1].
Qed.
Lemma RSV_ok : region_ok tfibsegs E m2 RSV.
Proof.
unfold region_ok, RSV; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]; replace (base_val E (Some 2%nat)) with (sp0 - 2144) by (cbn [base_val]; symmetry; exact Esp). split; [spc|]. split; [spc|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_at 2088 21%bv 6); [reflexivity | replace (sp0 - 2144 + 2088) with (sp0 - 56) by lia; exact V21]|].
apply Forall_cons; [apply (chunk_at 2096 20%bv 5); [reflexivity | replace (sp0 - 2144 + 2096) with (sp0 - 48) by lia; exact V20]|].
apply Forall_cons; [apply (chunk_at 2104 19%bv 4); [reflexivity | replace (sp0 - 2144 + 2104) with (sp0 - 40) by lia; exact V19]|].
apply Forall_cons; [apply (chunk_at 2112 18%bv 3); [reflexivity | replace (sp0 - 2144 + 2112) with (sp0 - 32) by lia; exact V18]|].
apply Forall_cons; [apply (chunk_at 2120 9%bv 2); [reflexivity | replace (sp0 - 2144 + 2120) with (sp0 - 24) by lia; exact V9]|].
apply Forall_cons; [apply (chunk_at 2128 8%bv 1); [reflexivity | replace (sp0 - 2144 + 2128) with (sp0 - 16) by lia; exact V8]|].
apply Forall_cons; [apply (chunk_at 2136 1%bv 0); [reflexivity | replace (sp0 - 2144 + 2136) with (sp0 - 8) by lia; exact V1]|].
apply Forall_nil.
Qed.
Lemma FFR_ok : atoms_ok E (f_atoms FFR).
Proof.
cbn [FFR f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Esp.
destruct Hsp as (S1 & S2). split; [unfold kHighMemBeg, kHighMemEnd, ASTACK in *; lia|].
replace (sp0 - 2144) with (sp0 + (-134) * 16) by lia. rewrite Z_mod_plus_full. change (2 ^ 4) with 16. split; [exact S2 | lia].
Qed.

Lemma SEEDB_ok : st_ok tfibsegs E SSB (restrict (w_H W2) (mkst regs2 (w64 0x32674) mem2 (seg_rom tfibsegs))).
Proof.
rewrite restrict_mkst_fx. unfold SSB, Er2, w64. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate | cbn [sv_denot]; exact Htp2].
- vm_compute. reflexivity.
- apply Forall_cons; [exact RAF_ok|]. apply Forall_cons; [exact RSV_ok | apply Forall_nil].
- apply pairwise_disjoint_of_extents. unfold RAF, RSV, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
replace (base_val (Ereg regs2 (XWr regs)) (Some 2%nat)) with (sp0 - 2144) by (cbn [base_val]; symmetry; exact Esp).
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [exact FFR_ok | split; exact I].
Qed.

Hypothesis Hra : YK0s.ret_ok (getr regs 1).
(* The registers at the caller's return: sp and the six callee-saved registers the interceptor saved come back from
   its frame; gp, s6-s11 are Allocate's return registers; tp is the image's. *)
Definition RPOST (regs' : bvmap 5 word) : Prop :=
getr regs' 2 = getr regs 2 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\
getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\
getr regs' 3 = getr regs2 3 /\ getr regs' 4 = w64 TFIB_TP /\
(forall r : Z, 22 <= r <= 27 -> getr regs' (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
Ltac rr HS r := let R := fresh "R" in rreg HS r R; rewrite R.
Ltac rpost HS :=
unfold RPOST; split; [rr HS (2%bv : bv 5); rewrite Esp; replace (sp0 - 2144 + 2144) with sp0 by lia; unfold sp0; apply Z_to_bv_bv_unsigned|];
split; [rr HS (8%bv : bv 5); unfold Er2; exact (ew_Ereg_extra regs2 (XWr regs) 1)|];
split; [rr HS (9%bv : bv 5); unfold Er2; exact (ew_Ereg_extra regs2 (XWr regs) 2)|];
split; [rr HS (18%bv : bv 5); unfold Er2; exact (ew_Ereg_extra regs2 (XWr regs) 3)|];
split; [rr HS (19%bv : bv 5); unfold Er2; exact (ew_Ereg_extra regs2 (XWr regs) 4)|];
split; [rr HS (20%bv : bv 5); unfold Er2; exact (ew_Ereg_extra regs2 (XWr regs) 5)|];
split; [rr HS (21%bv : bv 5); unfold Er2; exact (ew_Ereg_extra regs2 (XWr regs) 6)|];
split; [rr HS (3%bv : bv 5); unfold Er2; exact (ew_Ereg_nat regs2 (XWr regs) 3 3%bv eq_refl)|];
split; [rr HS (4%bv : bv 5); reflexivity|];
let r := fresh "r" in let Hr := fresh "Hr" in let Hr' := fresh "Hr'" in
intros r Hr; assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia; clear Hr;
repeat match type of Hr' with _ \/ _ => destruct Hr' as [Hr'|Hr'] end; subst r;
lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
let kb := eval vm_compute in (Z_to_bv 5 k : bv 5) in
change (Z_to_bv 5 k) with kb; rr HS kb; unfold Er2; apply ew_Ereg_nat; reflexivity end.

(* The block arm: a0 <> 0. *)
Lemma retB : bv_unsigned (getr regs2 10) <> 0 ->
SRr tfibsegs W2 (mkCfg (mkst regs2 (w64 0x32674) mem2 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md2) mat2 md2))
(fun W' c' => W' = W2 /\ exists regs' mem' mat,
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md2) mat md2) /\
  RPOST regs' /\ getr regs' 10 = getr regs2 10 /\ (forall x, mem' x = mem2 x)).
Proof.
intros HNZ. pose proof Hwx_tfa as Hwx. pose proof SEEDB_ok as HS.
srr_branch_sh tfibtbl_rtA_ok HS.
- exfalso. apply HNZ. rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc. revert Hc. unfold U. cbn [sv_denot]. unfold Er2.
rewrite (ew_Ereg_nat regs2 (XWr regs) 10 10%bv eq_refl), ?Z.add_0_r, ?Z_to_bv_bv_unsigned. intros Hc. rewrite Hc. reflexivity.
- srr_run_to_sh tfibtbl_rtA_ok HS 0x53b54.
assert (FR : forall x, ms_mem ms x = mem2 x).
{ intros x. apply HF. intros Hw. destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hr).
lazymatch type of Hin with In _ (windows ?rs) => let ws := eval vm_compute in (windows rs) in change (windows rs) with ws in Hin end.
cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; lia|]). destruct Hin. }
eapply (SRr_ret_at tfibsegs tfibtbl_rtA tfibtbl_rtA_ok Hwx W2 E); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms), mat'.
split. { rreg HS (1%bv : bv 5) Q1. rewrite Q1. unfold Er2. pose proof (ew_Ereg_extra regs2 (XWr regs) 0) as X0. cbn [Nat.add nth XWr] in X0. rewrite X0.
pose proof Hra as Hr. unfold YK0s.ret_ok in Hr. rewrite Hr. reflexivity. }
split. { rpost HS. }
split. { rreg HS (10%bv : bv 5) R. rewrite R. unfold Er2. apply ew_Ereg_nat. reflexivity. }
exact FR.
Qed.

Hypothesis HA0 : getr regs2 10 = w64 0.
Hypothesis PRESW : forall a, sp0 - 2160 <= a < sp0 - 2144 -> apresent (w_H W2) mem2 a.
Lemma RWF_ok : region_ok tfibsegs E m2 RWF.
Proof.
apply (region_ok_stack tfibsegs E m2 2 (sp0 - 2144) (-16)); [exact Esp | spc | spc |].
intros a Ha. apply apresent_writable; [unfold TFIB_IMG_END; pose proof sp_range; lia | apply PRESW; lia].
Qed.
Lemma RER_ok : region_ok tfibsegs E m2 RER.
Proof.
unfold region_ok, RER; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold TFIB_ERRNO. split; [lia|]. split; [lia|]. split; [|apply Forall_nil]. intros o Ho. unfold writable_at. apply YB13.tfib_rw_window. rewrite unsigned_lit_small by lia. unfold B_SEG1_PAGE_HI, YImgTop.IMG_TOP_B. lia.
Qed.
Lemma SEEDN_ok : st_ok tfibsegs E SSN (restrict (w_H W2) (mkst regs2 (w64 0x32674) mem2 (seg_rom tfibsegs))).
Proof.
rewrite restrict_mkst_fx. unfold SSN, w64. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate | cbn [sv_denot]; exact Htp2] | intros X; discriminate | cbn [sv_denot]; exact HA0].
- vm_compute. reflexivity.
- apply Forall_cons; [exact RAF_ok|]. apply Forall_cons; [exact RSV_ok|]. apply Forall_cons; [exact RWF_ok|]. apply Forall_cons; [exact RER_ok | apply Forall_nil].
- apply pairwise_disjoint_of_extents. unfold RAF, RSV, RWF, RER, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
replace (base_val (Ereg regs2 (XWr regs)) (Some 2%nat)) with (sp0 - 2144) by (cbn [base_val]; symmetry; exact Esp).
cbn [base_val zpairwise_disjoint zall_disjoint]. unfold zdisj, TFIB_ERRNO. cbn [fst snd]. pose proof sp_range. repeat split; lia.
- split; [exact FFR_ok | split; exact I].
Qed.
(* The NULL arm: a0 = 0; SetErrnoToENOMEM stores errno := 12. *)
Lemma retN : SRr tfibsegs W2 (mkCfg (mkst regs2 (w64 0x32674) mem2 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md2) mat2 md2))
(fun W' c' => W' = W2 /\ exists regs' mem' mat,
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md2) mat md2) /\
  RPOST regs' /\ getr regs' 10 = w64 0 /\
  (forall x : word, ~ (sp0 - 2160 <= bv_unsigned x < sp0 - 2144) -> ~ (TFIB_ERRNO <= bv_unsigned x < TFIB_ERRNO + 4) -> mem' x = mem2 x) /\
  val_mem tfibsegs (mrestrict (w_H W2) mem') TFIB_ERRNO 4 12 /\
  (forall a, sp0 - 2160 <= a < sp0 - 2144 -> apresent (w_H W2) mem' a)).
Proof.
pose proof Hwx_tfa as Hwx. pose proof SEEDN_ok as HS.
srr_run_to_sh tfibtbl_rtA_ok HS 0x53b54.
assert (FR : forall x : word, ~ (sp0 - 2160 <= bv_unsigned x < sp0 - 2144) -> ~ (TFIB_ERRNO <= bv_unsigned x < TFIB_ERRNO + 4) -> ms_mem ms x = mem2 x).
{ intros x X1 X2. apply HF. intros Hw. destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hr).
lazymatch type of Hin with In _ (windows ?rs) => let ws := eval vm_compute in (windows rs) in change (windows rs) with ws in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hr; rewrite ?Esp in Hr; unfold TFIB_ERRNO in X2; lia|]). destruct Hin. }
eapply (SRr_ret_at tfibsegs tfibtbl_rtA tfibtbl_rtA_ok Hwx W2 E); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms), mat'.
split. { rreg HS (1%bv : bv 5) Q1. rewrite Q1. unfold Er2. pose proof (ew_Ereg_extra regs2 (XWr regs) 0) as X0. cbn [Nat.add nth XWr] in X0. rewrite X0.
pose proof Hra as Hr. unfold YK0s.ret_ok in Hr. rewrite Hr. reflexivity. }
split. { rpost HS. }
split. { rreg HS (10%bv : bv 5) R. rewrite R. reflexivity. }
split. { exact FR. }
split. { memv HS 3%nat 0%nat; [reflexivity | reflexivity | lia]. }
intros a Ha. eapply (st_ok_window_apresent_off (w_H W2) E _ _ 2 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite Esp; lia
| apply off_img_high; unfold TFIB_IMG_END; pose proof sp_range; lia ].
Qed.
End WK.
End c.

