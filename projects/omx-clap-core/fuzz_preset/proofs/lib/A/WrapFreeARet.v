(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/AU/WrapMallocBRetRun.v (origin/cold/h-rw-man-5-icpt fe4845c761b,
   image B's malloc return run) and moved to image A's free interceptor (asan, pin d83eb25dbf0d, twin f0d2e8d40c7e):
   the seed is the state at Deallocate's return 0x53854 (one frame: the interceptor's saved ra, s0, s1, s2..s5 at
   sp + 2072 .. sp + 2128 = the caller's sp - 56 .. sp, as environment atoms 32..38), the run is the epilogue
   0x53854-0x53878 over A's table tfibtbl_rtA (no store) and SRr_ret_at, as lib/A/AFh1.v:336-351 ends its walk.
   Added: wf_ret_A, field F2 wf_ret of h-mani-a8's Record wrap_free_walk_cf (lib/Reusable/YGcfMallocCompose.v:352-366)
   at segs := tfibsegs, atpD := 1, ARX := YGcfDIface.ARXs_cf B tfibsegs, K := K_A (lib/A/WrapFreeAK.v), from the run,
   DeallocG.dealloc_post_raw's raw frame and window (the caller's frame words and stack window are off Deallocate's
   window and errno, unowned by AR_laws_ok_cf's stack law, and below no freed block: YGcfBlockRange.block_user_range_cf)
   and AR_laws_ok_cf's frame law (memory unchanged, the model changes by materialization only). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/WrapFreeARet.v, with its module paths and addresses changed; 280 of its 522 lines of code are new or changed and 30 lines of the source are left out. *)
(* Theorem Labs, 2026-10: RELOCATED to the #102 pins (image A' = asan 1be0f53d96cb, twin bff8519bbe3e) from commit preset-tree-at-2026-10-29T17-46-55Z.tsv (sha256 7c0bbc66e4a5; internal record) (old-pin image A) by the relocation script, the internal file reloc_A2.py (named with its outputs in the commit that added this line): every code address moved by symbol + offset (the internal file reloc_A2.out), the walk's functions checked by bytecmp 1480ca2faea0 + a target pass (the internal file measure_A2.out); data addresses come by name from int102's A' tables; ARXs_cf / ARmcf follow preset-tree-at-2026-10-29T18-16-07Z.tsv (sha256 4c721de248fd; internal record) (xs_placed is ARmcf's field amc_xs_placed). *)
(* Modified by Theorem Labs, 2026-10: copied from lib/AU/WrapMallocBRetRun.v (commit fe4845c761b,
   image B's malloc return run) and moved to image A's free interceptor (asan, pin 1be0f53d96cb, twin bff8519bbe3e):
   the seed is the state at Deallocate's return 0x538e8 (one frame: the interceptor's saved ra, s0, s1, s2..s5 at
   sp + 2072 .. sp + 2128 = the caller's sp - 56 .. sp, as environment atoms 32..38), the run is the epilogue
   0x538e8-0x5390c over A's table tfibtbl_rtA (no store) and SRr_ret_at, as lib/A/AFh1.v:336-351 ends its walk.
   Added: wf_ret_gen, field F2 wf_ret of the Record wrap_free_walk_cf (lib/Reusable/YGcfMallocCompose.v)
   at segs := tfibsegs, atpD := 1, K := K_A (lib/A/WrapFreeAK.v) and any ARX with HXA / HXF, from the run,
   DeallocG.dealloc_post_raw's raw frame and window (the caller's frame words and stack window are off Deallocate's
   window and errno, unowned by AR_laws_ok_cf's stack law, and below no freed block: YGcfBlockRange.block_user_range_cf)
   and AR_laws_ok_cf's frame law (memory unchanged, the model changes by materialization only). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AE3d AFeq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcfBlockRange.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require AllocG DeallocG RGtop YGcfRmodel YAkMemnorm YGcfDIface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import WrapFreeAK.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* The environment: the registers at Deallocate's return, then the caller's ra, s0, s1, s2, s3, s4, s5 (atoms 32..38). *)
Definition wr_XW (regs : bvmap 5 word) : list word :=
[ getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21 ].
Definition wr_E (regs2 regs : bvmap 5 word) : env := Ereg regs2 (wr_XW regs).
(* The interceptor's saved registers [sp + 2072, sp + 2128) = [caller sp - 56, caller sp) (sd at 0x53744-0x5375c). *)
Definition wr_RSV : YP09.region := YP09.mkRegion (Some 2%nat) 2072 2128 0 0
[YP09.mkChunk 2072 (CVal 8 (SOff 38 0)); YP09.mkChunk 2080 (CVal 8 (SOff 37 0)); YP09.mkChunk 2088 (CVal 8 (SOff 36 0));
 YP09.mkChunk 2096 (CVal 8 (SOff 35 0)); YP09.mkChunk 2104 (CVal 8 (SOff 34 0)); YP09.mkChunk 2112 (CVal 8 (SOff 33 0));
 YP09.mkChunk 2120 (CVal 8 (SOff 32 0))].
Definition wr_FF : facts := mkFacts [ (2%nat, mkAF (kHighMemBeg + ASTACK - 2128) (kHighMemEnd - 2128) 4) ] [] [].
Definition wr_SS : sstate := mkSS 0x538e8 sr_atoms [wr_RSV] None wr_FF.

Section WK.
Variables (W2 : world tfibsegs) (regs2 regs : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model).
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Abbreviation E := (wr_E regs2 regs).
Let m2 := mrestrict (w_H W2) mem2.
Hypothesis Hsp : kHighMemBeg + ASTACK <= sp0 <= kHighMemEnd /\ sp0 mod 16 = 0.
Hypothesis Hsp2 : getr regs2 2 = w64 (sp0 - 2128).
Hypothesis V1 : val_mem tfibsegs m2 (sp0 - 8) 8 (bv_unsigned (getr regs 1)).
Hypothesis V8 : val_mem tfibsegs m2 (sp0 - 16) 8 (bv_unsigned (getr regs 8)).
Hypothesis V9 : val_mem tfibsegs m2 (sp0 - 24) 8 (bv_unsigned (getr regs 9)).
Hypothesis V18 : val_mem tfibsegs m2 (sp0 - 32) 8 (bv_unsigned (getr regs 18)).
Hypothesis V19 : val_mem tfibsegs m2 (sp0 - 40) 8 (bv_unsigned (getr regs 19)).
Hypothesis V20 : val_mem tfibsegs m2 (sp0 - 48) 8 (bv_unsigned (getr regs 20)).
Hypothesis V21 : val_mem tfibsegs m2 (sp0 - 56) 8 (bv_unsigned (getr regs 21)).

Lemma wr_Esp : bv_unsigned (ew E 2) = sp0 - 2128.
Proof. unfold wr_E. rewrite (ew_Ereg_nat regs2 (wr_XW regs) 2 2%bv eq_refl), Hsp2. unfold w64. apply unsigned_lit_small. unfold kHighMemBeg, kHighMemEnd, ASTACK in Hsp. lia. Qed.
Lemma wr_sp_range : 0x10007fff8000 <= sp0 - 2128 /\ sp0 <= 0x800000000000.
Proof. destruct Hsp as [[H1 H2] _]. unfold kHighMemBeg, kHighMemEnd, ASTACK in *. lia. Qed.
Ltac wr_spc := pose proof wr_sp_range; lia.
Lemma wr_chunk_at : forall off (r : bv 5) j, nth j (wr_XW regs) (Z_to_bv 64 0) = getr regs r ->
val_mem tfibsegs m2 (sp0 - 2128 + off) 8 (bv_unsigned (getr regs r)) ->
YP09.chunk_ok tfibsegs E m2 (sp0 - 2128) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0))).
Proof.
intros off r j Hn Hm. eapply chunk_ok_val; [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply u64_range | cbn; lia | exact Hm].
cbn [sv_denot]. unfold wr_E. rewrite (ew_Ereg_extra regs2 (wr_XW regs) j), Hn. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma wr_RSV_ok : region_ok tfibsegs E m2 wr_RSV.
Proof.
unfold region_ok, wr_RSV; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
replace (base_val E (Some 2%nat)) with (sp0 - 2128) by (cbn [base_val]; symmetry; exact wr_Esp).
split; [wr_spc|]. split; [wr_spc|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (wr_chunk_at 2072 21%bv 6); [reflexivity | replace (sp0 - 2128 + 2072) with (sp0 - 56) by lia; exact V21]|].
apply Forall_cons; [apply (wr_chunk_at 2080 20%bv 5); [reflexivity | replace (sp0 - 2128 + 2080) with (sp0 - 48) by lia; exact V20]|].
apply Forall_cons; [apply (wr_chunk_at 2088 19%bv 4); [reflexivity | replace (sp0 - 2128 + 2088) with (sp0 - 40) by lia; exact V19]|].
apply Forall_cons; [apply (wr_chunk_at 2096 18%bv 3); [reflexivity | replace (sp0 - 2128 + 2096) with (sp0 - 32) by lia; exact V18]|].
apply Forall_cons; [apply (wr_chunk_at 2104 9%bv 2); [reflexivity | replace (sp0 - 2128 + 2104) with (sp0 - 24) by lia; exact V9]|].
apply Forall_cons; [apply (wr_chunk_at 2112 8%bv 1); [reflexivity | replace (sp0 - 2128 + 2112) with (sp0 - 16) by lia; exact V8]|].
apply Forall_cons; [apply (wr_chunk_at 2120 1%bv 0); [reflexivity | replace (sp0 - 2128 + 2120) with (sp0 - 8) by lia; exact V1]|].
apply Forall_nil.
Qed.
Lemma wr_FF_ok : atoms_ok E (f_atoms wr_FF).
Proof.
cbn [wr_FF f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite wr_Esp.
destruct Hsp as (S1 & S2). split; [unfold kHighMemBeg, kHighMemEnd, ASTACK in *; lia|].
replace (sp0 - 2128) with (sp0 + (-133) * 16) by lia. rewrite Z_mod_plus_full. change (2 ^ 4) with 16. split; [exact S2 | lia].
Qed.
Lemma wr_SEED_ok : st_ok tfibsegs E wr_SS (restrict (w_H W2) (mkst regs2 (w64 0x538e8) mem2 (seg_rom tfibsegs))).
Proof.
rewrite restrict_mkst_fx. unfold wr_SS, wr_E, w64. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [exact wr_RSV_ok | apply Forall_nil].
- exact (conj I I).
- split; [exact wr_FF_ok | split; exact I].
Qed.

Hypothesis Hra : YK0s.ret_ok (getr regs 1).
(* The registers at the caller's return: sp and the seven words the interceptor saved come back from its frame; gp,
   tp and s6-s11 are the registers at Deallocate's return. *)
Definition wr_RPOST (regs' : bvmap 5 word) : Prop :=
getr regs' 2 = getr regs 2 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\
getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\
getr regs' 3 = getr regs2 3 /\ getr regs' 4 = getr regs2 4 /\
(forall r : Z, 22 <= r <= 27 -> getr regs' (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
Ltac wr_rr HS r := let R := fresh "R" in rreg HS r R; rewrite R.
Ltac wr_rpost HS :=
unfold wr_RPOST; split; [wr_rr HS (2%bv : bv 5); rewrite wr_Esp; replace (sp0 - 2128 + 2128) with sp0 by lia; unfold sp0; apply Z_to_bv_bv_unsigned|];
split; [wr_rr HS (8%bv : bv 5); unfold wr_E; exact (ew_Ereg_extra regs2 (wr_XW regs) 1)|];
split; [wr_rr HS (9%bv : bv 5); unfold wr_E; exact (ew_Ereg_extra regs2 (wr_XW regs) 2)|];
split; [wr_rr HS (18%bv : bv 5); unfold wr_E; exact (ew_Ereg_extra regs2 (wr_XW regs) 3)|];
split; [wr_rr HS (19%bv : bv 5); unfold wr_E; exact (ew_Ereg_extra regs2 (wr_XW regs) 4)|];
split; [wr_rr HS (20%bv : bv 5); unfold wr_E; exact (ew_Ereg_extra regs2 (wr_XW regs) 5)|];
split; [wr_rr HS (21%bv : bv 5); unfold wr_E; exact (ew_Ereg_extra regs2 (wr_XW regs) 6)|];
split; [wr_rr HS (3%bv : bv 5); unfold wr_E; exact (ew_Ereg_nat regs2 (wr_XW regs) 3 3%bv eq_refl)|];
split; [wr_rr HS (4%bv : bv 5); unfold wr_E; exact (ew_Ereg_nat regs2 (wr_XW regs) 4 4%bv eq_refl)|];
let r := fresh "r" in let Hr := fresh "Hr" in let Hr' := fresh "Hr'" in
intros r Hr; assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia; clear Hr;
repeat match type of Hr' with _ \/ _ => destruct Hr' as [Hr'|Hr'] end; subst r;
lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
let kb := eval vm_compute in (Z_to_bv 5 k : bv 5) in
change (Z_to_bv 5 k) with kb; wr_rr HS kb; unfold wr_E; apply ew_Ereg_nat; reflexivity end.

(* The epilogue 0x538e8-0x5390c (addi sp, sp, 0x60; ld ra, s0, s1, s2..s5; addi sp, sp, 0x7f0) and its `ret`. *)
Lemma wr_run : SRr tfibsegs W2 (mkCfg (mkst regs2 (w64 0x538e8) mem2 (seg_rom tfibsegs)) md2)
(fun W' c' => W' = W2 /\ exists regs' mem' mat,
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md2) mat md2) /\
  wr_RPOST regs' /\ (forall x, mem' x = mem2 x)).
Proof.
pose proof Hwx_tfa as Hwx. pose proof wr_SEED_ok as HS.
srr_run_to_sh tfibtbl_rtA_ok HS 0x5390c.
assert (FR : forall x, ms_mem ms x = mem2 x).
{ intros x. apply HF. intros Hw. destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hr).
lazymatch type of Hin with In _ (windows ?rs) => let ws := eval vm_compute in (windows rs) in change (windows rs) with ws in Hin end.
cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; lia|]). destruct Hin. }
eapply (SRr_ret_at tfibsegs tfibtbl_rtA tfibtbl_rtA_ok Hwx W2 E); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms), mat'.
split. { rreg HS (1%bv : bv 5) Q1. rewrite Q1. unfold wr_E. pose proof (ew_Ereg_extra regs2 (wr_XW regs) 0) as X0. cbn [Nat.add nth wr_XW] in X0. rewrite X0.
pose proof Hra as Hr. unfold YK0s.ret_ok in Hr. rewrite Hr. reflexivity. }
split. { wr_rpost HS. }
exact FR.
Qed.
End WK.

(* A byte read through two hidden sets: the same byte when neither hides the address and the raw bytes agree. *)
Lemma wr_mbyte_move : forall (H H' : word -> bool) (m m' : word -> option byte) a,
H (Z_to_bv 64 a) = false -> H' (Z_to_bv 64 a) = false -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
mbyte tfibsegs (mrestrict H' m') a = mbyte tfibsegs (mrestrict H m) a.
Proof. intros H H' m m' a E1 E2 E3. unfold mbyte, mrestrict. rewrite E1, E2, E3. reflexivity. Qed.

(* Field F2 wf_ret of the Record wrap_free_walk_cf (YGcfMallocCompose.v:352-366) at image A, for ANY call-site
   relation ARX that gives ARcf (HXA) and survives a view-equal memory and materialization (HXF) (the
   WrapMallocARetG.v method), so a change of the record's ARX re-instantiates it: segs := tfibsegs, atpD := 1, K := K_A. *)
Theorem wf_ret_gen : forall B, TfibSyms B -> forall ARX : YGcfMallocCompose.ARXh_t tfibsegs,
YGcfMallocCompose.ARX_ARcf tfibsegs B ARX ->
(forall Hp inst ly S W mem md mem' mat, ARX Hp inst ly S W mem md ->
  (forall a, aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  ARcf tfibsegs B ly S Hp W mem' (with_vm_backing (m_vm_lazy md) mat md) ->
  ARX Hp inst ly S W mem' (with_vm_backing (m_vm_lazy md) mat md)) ->
forall ly S Hp W regs mem md p n ch W1 inst so bp regsD memD mdD ly2 S2 W2 regs2 mem2 md2,
  fentry_cf tfibsegs B ly S Hp W regs mem md p n ch ->
  K_A ly S Hp W regs mem md p n ch W1 regsD memD mdD ->
  free_dpre_cf tfibsegs B 1 ARX Hp inst so bp ly (finit_cf S) W1 regsD memD mdD p n
    (ftr_cf B ly regs ch) ->
  free_dpost_cf tfibsegs B ARX Hp inst ly (finit_cf S) W1 regsD memD mdD
    (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly2 S2 W2 regs2 mem2 md2 ->
  qtight S2 ->
  (exists trc, apath (free_cf p (ftr_cf B ly regs ch) (finit_cf S)) trc (tt, S2) /\ gflag trc = true) ->
  SRr tfibsegs W2 (cfg_at tfibsegs (raZ regsD) regs2 mem2 md2)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
    ARX Hp inst ly2 S2 W' mem' md' /\ same_io md2 md' /\
    RGtop.rkeep tfibsegs B regs W2 mem2 W' mem' /\ RGtop.rwin tfibsegs regs W' mem' /\
    (YAkMemnorm.memnorm tfibsegs mem2 -> YAkMemnorm.memnorm tfibsegs mem') /\
    errno_kept_cf B mem2 mem').
Proof.
intros B TB ARX HXA HXF ly S Hp W regs mem md p n ch W1 inst so bp regsD memD mdD ly2 S2 W2 regs2 mem2 md2 ENT KK DPRE DPO _ _.
destruct ENT as (PRE & Hpn & _ & _ & _).
pose proof PRE as (HAR & Hra & Hal & Hlo & _ & Hhi & _).
destruct KK as (-> & D2 & D1 & D3 & D4 & DS & V1 & V8 & V9 & V18 & V19 & V20 & V21 & WIN).
destruct DPRE as (XD & _). pose proof (HXA _ _ _ _ _ _ _ XD) as HARD.
destruct DPO as (X2 & LLE & WLE & CS2 & _ & _ & FRR & PRD). pose proof (HXA _ _ _ _ _ _ _ X2) as HAR2.
destruct (AR_laws_ok_cf tfibsegs B) as [_ _ _ Lfr _ _ _ Lst _ _ _ _ _ _ _].
pose proof (amc_layout _ _ _ _ _ (proj1 HAR)) as LO.
pose proof (lo_top ly LO) as (_ & _ & _ & T4 & _ & _ & T7).
pose proof (lo_stk_ceil ly LO) as SC.
destruct LLE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & LL & LH & _).
unfold spZ, raZ, s0Z in Hal, Hlo, Hhi, WIN, D2, V1, V8, V9, V18, V19, V20, V21.
set (sp0 := bv_unsigned (getr regs 2)) in *.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (HSP : kHighMemBeg + ASTACK <= sp0 <= kHighMemEnd /\ sp0 mod 16 = 0)
  by (split; [clear - T7 Hlo Hhi T4; split; lia | exact Hal]).
assert (SD : bv_unsigned (getr regsD 2) = sp0 - 2128).
{ rewrite D2. change (bv_unsigned (Z_to_bv 64 (sp0 - 2128)) = sp0 - 2128). apply unsigned_lit_small.
  clear - HSP. unfold kHighMemBeg, kHighMemEnd, ASTACK in *. lia. }
assert (Ha64 : forall a, sp0 - ASTACK <= a < sp0 -> bv_unsigned (Z_to_bv 64 a) = a).
{ intros a Ha. apply unsigned_lit_small. clear - Ha HSP Usp. unfold kHighMemBeg, kHighMemEnd, ASTACK in *. lia. }
(* The caller's stack window off Deallocate's window keeps its raw bytes. *)
assert (KEEP : forall a, sp0 - ASTACK <= a < sp0 -> ~ (sp0 - 2128 - DeallocG.DFSTACK_G <= a < sp0 - 2128) ->
  mem2 (Z_to_bv 64 a) = memD (Z_to_bv 64 a)).
{ intros a Ha Hd. apply FRR; rewrite (Ha64 a Ha).
  - apply (Lst ly (finit_cf S) Hp W memD mdD a HARD). clear - Ha Hlo Hhi. lia.
  - apply (Lst ly2 S2 Hp W2 mem2 md2 a HAR2). rewrite LL, LH. clear - Ha Hlo Hhi. lia.
  - unfold ascratch, spZ. rewrite SD, (ts_errno B TB). intros [X|X]; [exact (Hd X)|].
    clear - X Ha HSP. unfold TFIB_ERRNO, kHighMemBeg, kHighMemEnd, ASTACK in *. lia.
  - cbv beta. intros (Hnp & X). destruct Hpn as [-> | Hin]; [exact (Hnp eq_refl)|].
    destruct (block_user_range_cf tfibsegs B ly S Hp W mem md p n HAR Hin) as (_ & [[_ L2] | [_ L2]]).
    + clear - X L2 Ha Hlo T7. unfold kLowShadowBeg, kHighMemBeg, ASTACK in *. lia.
    + clear - X L2 Ha Hlo SC. unfold ASTACK in *. lia. }
assert (OUT : forall a, sp0 - ASTACK <= a < sp0 -> ~ (sp0 - 2128 - DeallocG.DFSTACK_G <= a < sp0 - 2128) ->
  w_H W2 (Z_to_bv 64 a) = false /\ w_H W (Z_to_bv 64 a) = false /\ mem2 (Z_to_bv 64 a) = memD (Z_to_bv 64 a)).
{ intros a Ha Hd. destruct (WIN a Ha) as [Hh _]. split; [|split; [exact Hh | exact (KEEP a Ha Hd)]].
  destruct (w_H W2 (Z_to_bv 64 a)) eqn:EH; [|reflexivity]. rewrite (WLE _ EH) in Hh. discriminate. }
(* The caller's stack window is present after Deallocate. *)
assert (PRES2 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W2) mem2 a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2128 - DeallocG.DFSTACK_G)) as [A|A];
  [|destruct (Z_lt_le_dec a (sp0 - 2128)) as [A'|A']].
  - destruct (OUT a Ha ltac:(lia)) as (H2 & _ & M2). destruct (WIN a Ha) as [_ [b Hb]].
    split; [exact H2|]. exists b. rewrite M2. exact Hb.
  - apply PRD. unfold spZ. rewrite SD. lia.
  - destruct (OUT a Ha ltac:(lia)) as (H2 & _ & M2). destruct (WIN a Ha) as [_ [b Hb]].
    split; [exact H2|]. exists b. rewrite M2. exact Hb. }
(* The seven saved words, read at Deallocate's return. *)
assert (TV : forall a v, sp0 - 56 <= a -> a + 8 <= sp0 ->
  val_mem tfibsegs (mrestrict (w_H W) memD) a 8 v -> val_mem tfibsegs (mrestrict (w_H W2) mem2) a 8 v).
{ intros a v A1 A2 Hv k Hk. rewrite <- (Hv k Hk).
  assert (Hx : sp0 - ASTACK <= a + Z.of_nat k < sp0) by (clear - A1 A2 Hk; unfold ASTACK; lia).
  destruct (OUT (a + Z.of_nat k) Hx ltac:(clear - A1 A2 Hk; lia)) as (H2 & H1 & M).
  exact (wr_mbyte_move _ _ _ _ _ H1 H2 M). }
assert (V1' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 8) 8 (bv_unsigned (getr regs 1))) by (apply TV; [lia | lia | exact V1]).
assert (V8' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 16) 8 (bv_unsigned (getr regs 8))) by (apply TV; [lia | lia | exact V8]).
assert (V9' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 24) 8 (bv_unsigned (getr regs 9))) by (apply TV; [lia | lia | exact V9]).
assert (V18' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 32) 8 (bv_unsigned (getr regs 18))) by (apply TV; [lia | lia | exact V18]).
assert (V19' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 40) 8 (bv_unsigned (getr regs 19))) by (apply TV; [lia | lia | exact V19]).
assert (V20' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 48) 8 (bv_unsigned (getr regs 20))) by (apply TV; [lia | lia | exact V20]).
assert (V21' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 56) 8 (bv_unsigned (getr regs 21))) by (apply TV; [lia | lia | exact V21]).
(* sp at Deallocate's return: Deallocate keeps it (aregs_preserved regsD regs2). *)
assert (R2 : getr regs2 2 = w64 (sp0 - 2128)).
{ pose proof (CS2 2 ltac:(unfold acallee_saved; lia)) as C.
  replace (Z_to_bv 5 2) with (2%bv : bv 5) in C by (apply bv_eq; reflexivity). rewrite C. exact D2. }
replace (raZ regsD) with 0x538e8 by (unfold raZ; rewrite D1; reflexivity).
unfold cfg_at.
eapply SRr_mono; [exact (wr_run W2 regs2 regs mem2 md2 HSP R2 V1' V8' V9' V18' V19' V20' V21' Hra)|].
intros W' c' _ (-> & regs' & mem' & mat & -> & RP & FR).
exists regs', mem', (with_vm_backing (m_vm_lazy md2) mat md2).
destruct RP as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & P3 & P4 & P22).
split.
{ lazymatch goal with |- _ = mkCfg (mkst _ ?pc _ _) _ =>
    replace pc with (getr regs 1) by (unfold raZ; first [apply Z_to_bv_bv_unsigned | symmetry; apply Z_to_bv_bv_unsigned]) end.
  reflexivity. }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]].
  - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). exact P2.
  - replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P3, <- D3.
    pose proof (CS2 3 ltac:(unfold acallee_saved; lia)) as C.
    replace (Z_to_bv 5 3) with (3%bv : bv 5) in C by (apply bv_eq; reflexivity). exact C.
  - replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P4, <- D4.
    pose proof (CS2 4 ltac:(unfold acallee_saved; lia)) as C.
    replace (Z_to_bv 5 4) with (4%bv : bv 5) in C by (apply bv_eq; reflexivity). exact C.
  - replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). exact P8.
  - replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). exact P9.
  - assert (R : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ 22 <= r <= 27) by lia. clear Hr.
    destruct R as [->|[->|[->|[->|R]]]].
    + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). exact P18.
    + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). exact P19.
    + replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). exact P20.
    + replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). exact P21.
    + rewrite (P22 r R), (CS2 r ltac:(unfold acallee_saved; lia)). exact (DS r R). }
split.
{ apply (HXF Hp inst ly2 S2 W2 mem2 md2 mem' mat X2); [intros a; apply aview_same; apply FR|].
  apply (Lfr ly2 S2 Hp W2 mem2 md2 mem' (with_vm_backing (m_vm_lazy md2) mat md2) HAR2).
  - intros a _ _. apply aview_same. apply FR.
  - intros a Hv. rewrite (aview_same (w_H W2) mem2 mem' a (FR _)). exact Hv.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros a _ _. apply FR. }
split. { repeat split; reflexivity. }
split. { split; [intros a _ _; apply aview_same; apply FR | intros x _; apply FR]. }
split. { intros a Ha. apply (apresent_same (w_H W2) mem2 mem' a (FR _)). apply PRES2. exact Ha. }
split. { intros [M1 M2]. split; intros a b Hb; rewrite FR in Hb; [exact (M1 a b Hb) | exact (M2 a b Hb)]. }
intros i Hi. apply FR.
Qed.

(* The same field at the PRIMED Deallocate post YGcfRehidePost.dealloc_post_raw_rh (record wrap_free_walk_cf_rh's wfr_ret,
   lib/Reusable/YGcfMallocComposeRh.v): the hidden set grows only inside dead_shadow_new, which the caller's stack window
   (above kHighMemBeg) misses (YGcfRehidePost.dead_shadow_new_high). *)
Theorem wf_ret_gen_rh : forall B, TfibSyms B -> forall ARX : YGcfMallocCompose.ARXh_t tfibsegs,
YGcfMallocCompose.ARX_ARcf tfibsegs B ARX ->
(forall Hp inst ly S W mem md mem' mat, ARX Hp inst ly S W mem md ->
  (forall a, aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  ARcf tfibsegs B ly S Hp W mem' (with_vm_backing (m_vm_lazy md) mat md) ->
  ARX Hp inst ly S W mem' (with_vm_backing (m_vm_lazy md) mat md)) ->
forall ly S Hp W regs mem md p n ch W1 inst so bp regsD memD mdD ly2 S2 W2 regs2 mem2 md2,
  fentry_cf tfibsegs B ly S Hp W regs mem md p n ch ->
  K_A ly S Hp W regs mem md p n ch W1 regsD memD mdD ->
  free_dpre_cf tfibsegs B 1 ARX Hp inst so bp ly (finit_cf S) W1 regsD memD mdD p n
    (ftr_cf B ly regs ch) ->
  YGcfRehidePost.dealloc_post_raw_rh tfibsegs B (ARX Hp) (aowned B) inst ly (finit_cf S) W1 regsD memD mdD
    (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly2 S2 W2 regs2 mem2 md2 ->
  qtight S2 ->
  (exists trc, apath (free_cf p (ftr_cf B ly regs ch) (finit_cf S)) trc (tt, S2) /\ gflag trc = true) ->
  SRr tfibsegs W2 (cfg_at tfibsegs (raZ regsD) regs2 mem2 md2)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
    ARX Hp inst ly2 S2 W' mem' md' /\ same_io md2 md' /\
    RGtop.rkeep tfibsegs B regs W2 mem2 W' mem' /\ RGtop.rwin tfibsegs regs W' mem' /\
    errno_kept_cf B mem2 mem').
Proof.
intros B TB ARX HXA HXF ly S Hp W regs mem md p n ch W1 inst so bp regsD memD mdD ly2 S2 W2 regs2 mem2 md2 ENT KK DPRE DPO _ _.
destruct ENT as (PRE & Hpn & _ & _ & _).
pose proof PRE as (HAR & Hra & Hal & Hlo & _ & Hhi & _).
destruct KK as (-> & D2 & D1 & D3 & D4 & DS & V1 & V8 & V9 & V18 & V19 & V20 & V21 & WIN).
destruct DPRE as (XD & _). pose proof (HXA _ _ _ _ _ _ _ XD) as HARD.
destruct DPO as ((X2 & LLE & WLE & CS2 & _ & _ & PRD) & FRR). pose proof (HXA _ _ _ _ _ _ _ X2) as HAR2.
destruct (AR_laws_ok_cf tfibsegs B) as [_ _ _ Lfr _ _ _ Lst _ _ _ _ _ _ _].
pose proof (amc_layout _ _ _ _ _ (proj1 HAR)) as LO.
pose proof (lo_top ly LO) as (_ & _ & _ & T4 & _ & _ & T7).
pose proof (lo_stk_ceil ly LO) as SC.
destruct LLE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & LL & LH & _).
unfold spZ, raZ, s0Z in Hal, Hlo, Hhi, WIN, D2, V1, V8, V9, V18, V19, V20, V21.
set (sp0 := bv_unsigned (getr regs 2)) in *.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (HSP : kHighMemBeg + ASTACK <= sp0 <= kHighMemEnd /\ sp0 mod 16 = 0)
  by (split; [clear - T7 Hlo Hhi T4; split; lia | exact Hal]).
assert (SD : bv_unsigned (getr regsD 2) = sp0 - 2128).
{ rewrite D2. change (bv_unsigned (Z_to_bv 64 (sp0 - 2128)) = sp0 - 2128). apply unsigned_lit_small.
  clear - HSP. unfold kHighMemBeg, kHighMemEnd, ASTACK in *. lia. }
assert (Ha64 : forall a, sp0 - ASTACK <= a < sp0 -> bv_unsigned (Z_to_bv 64 a) = a).
{ intros a Ha. apply unsigned_lit_small. clear - Ha HSP Usp. unfold kHighMemBeg, kHighMemEnd, ASTACK in *. lia. }
(* The caller's stack window off Deallocate's window keeps its raw bytes. *)
assert (KEEP : forall a, sp0 - ASTACK <= a < sp0 -> ~ (sp0 - 2128 - DeallocG.DFSTACK_G <= a < sp0 - 2128) ->
  mem2 (Z_to_bv 64 a) = memD (Z_to_bv 64 a)).
{ intros a Ha Hd. apply FRR; rewrite (Ha64 a Ha).
  - apply (Lst ly (finit_cf S) Hp W memD mdD a HARD). clear - Ha Hlo Hhi. lia.
  - apply (Lst ly2 S2 Hp W2 mem2 md2 a HAR2). rewrite LL, LH. clear - Ha Hlo Hhi. lia.
  - unfold ascratch, spZ. rewrite SD, (ts_errno B TB). intros [X|X]; [exact (Hd X)|].
    clear - X Ha HSP. unfold TFIB_ERRNO, kHighMemBeg, kHighMemEnd, ASTACK in *. lia.
  - cbv beta. intros (Hnp & X). destruct Hpn as [-> | Hin]; [exact (Hnp eq_refl)|].
    destruct (block_user_range_cf tfibsegs B ly S Hp W mem md p n HAR Hin) as (_ & [[_ L2] | [_ L2]]).
    + clear - X L2 Ha Hlo T7. unfold kLowShadowBeg, kHighMemBeg, ASTACK in *. lia.
    + clear - X L2 Ha Hlo SC. unfold ASTACK in *. lia. }
assert (OUT : forall a, sp0 - ASTACK <= a < sp0 -> ~ (sp0 - 2128 - DeallocG.DFSTACK_G <= a < sp0 - 2128) ->
  w_H W2 (Z_to_bv 64 a) = false /\ w_H W (Z_to_bv 64 a) = false /\ mem2 (Z_to_bv 64 a) = memD (Z_to_bv 64 a)).
{ intros a Ha Hd. destruct (WIN a Ha) as [Hh _]. split; [|split; [exact Hh | exact (KEEP a Ha Hd)]].
  destruct (w_H W2 (Z_to_bv 64 a)) eqn:EH; [|reflexivity].
  destruct (WLE _ EH) as [EW|ED]; [rewrite EW in Hh; discriminate|]. exfalso.
  rewrite (Ha64 a Ha) in ED. apply (YGcfRehidePost.dead_shadow_new_high ly (finit_cf S) S2 a); [|exact ED].
  clear - Ha HSP. unfold ASTACK in *. lia. }
(* The caller's stack window is present after Deallocate. *)
assert (PRES2 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W2) mem2 a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2128 - DeallocG.DFSTACK_G)) as [A|A];
  [|destruct (Z_lt_le_dec a (sp0 - 2128)) as [A'|A']].
  - destruct (OUT a Ha ltac:(lia)) as (H2 & _ & M2). destruct (WIN a Ha) as [_ [b Hb]].
    split; [exact H2|]. exists b. rewrite M2. exact Hb.
  - apply PRD. unfold spZ. rewrite SD. lia.
  - destruct (OUT a Ha ltac:(lia)) as (H2 & _ & M2). destruct (WIN a Ha) as [_ [b Hb]].
    split; [exact H2|]. exists b. rewrite M2. exact Hb. }
(* The seven saved words, read at Deallocate's return. *)
assert (TV : forall a v, sp0 - 56 <= a -> a + 8 <= sp0 ->
  val_mem tfibsegs (mrestrict (w_H W) memD) a 8 v -> val_mem tfibsegs (mrestrict (w_H W2) mem2) a 8 v).
{ intros a v A1 A2 Hv k Hk. rewrite <- (Hv k Hk).
  assert (Hx : sp0 - ASTACK <= a + Z.of_nat k < sp0) by (clear - A1 A2 Hk; unfold ASTACK; lia).
  destruct (OUT (a + Z.of_nat k) Hx ltac:(clear - A1 A2 Hk; lia)) as (H2 & H1 & M).
  exact (wr_mbyte_move _ _ _ _ _ H1 H2 M). }
assert (V1' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 8) 8 (bv_unsigned (getr regs 1))) by (apply TV; [lia | lia | exact V1]).
assert (V8' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 16) 8 (bv_unsigned (getr regs 8))) by (apply TV; [lia | lia | exact V8]).
assert (V9' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 24) 8 (bv_unsigned (getr regs 9))) by (apply TV; [lia | lia | exact V9]).
assert (V18' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 32) 8 (bv_unsigned (getr regs 18))) by (apply TV; [lia | lia | exact V18]).
assert (V19' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 40) 8 (bv_unsigned (getr regs 19))) by (apply TV; [lia | lia | exact V19]).
assert (V20' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 48) 8 (bv_unsigned (getr regs 20))) by (apply TV; [lia | lia | exact V20]).
assert (V21' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 56) 8 (bv_unsigned (getr regs 21))) by (apply TV; [lia | lia | exact V21]).
(* sp at Deallocate's return: Deallocate keeps it (aregs_preserved regsD regs2). *)
assert (R2 : getr regs2 2 = w64 (sp0 - 2128)).
{ pose proof (CS2 2 ltac:(unfold acallee_saved; lia)) as C.
  replace (Z_to_bv 5 2) with (2%bv : bv 5) in C by (apply bv_eq; reflexivity). rewrite C. exact D2. }
replace (raZ regsD) with 0x538e8 by (unfold raZ; rewrite D1; reflexivity).
unfold cfg_at.
eapply SRr_mono; [exact (wr_run W2 regs2 regs mem2 md2 HSP R2 V1' V8' V9' V18' V19' V20' V21' Hra)|].
intros W' c' _ (-> & regs' & mem' & mat & -> & RP & FR).
exists regs', mem', (with_vm_backing (m_vm_lazy md2) mat md2).
destruct RP as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & P3 & P4 & P22).
split.
{ lazymatch goal with |- _ = mkCfg (mkst _ ?pc _ _) _ =>
    replace pc with (getr regs 1) by (unfold raZ; first [apply Z_to_bv_bv_unsigned | symmetry; apply Z_to_bv_bv_unsigned]) end.
  reflexivity. }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]].
  - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). exact P2.
  - replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P3, <- D3.
    pose proof (CS2 3 ltac:(unfold acallee_saved; lia)) as C.
    replace (Z_to_bv 5 3) with (3%bv : bv 5) in C by (apply bv_eq; reflexivity). exact C.
  - replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P4, <- D4.
    pose proof (CS2 4 ltac:(unfold acallee_saved; lia)) as C.
    replace (Z_to_bv 5 4) with (4%bv : bv 5) in C by (apply bv_eq; reflexivity). exact C.
  - replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). exact P8.
  - replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). exact P9.
  - assert (R : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ 22 <= r <= 27) by lia. clear Hr.
    destruct R as [->|[->|[->|[->|R]]]].
    + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). exact P18.
    + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). exact P19.
    + replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). exact P20.
    + replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). exact P21.
    + rewrite (P22 r R), (CS2 r ltac:(unfold acallee_saved; lia)). exact (DS r R). }
split.
{ apply (HXF Hp inst ly2 S2 W2 mem2 md2 mem' mat X2); [intros a; apply aview_same; apply FR|].
  apply (Lfr ly2 S2 Hp W2 mem2 md2 mem' (with_vm_backing (m_vm_lazy md2) mat md2) HAR2).
  - intros a _ _. apply aview_same. apply FR.
  - intros a Hv. rewrite (aview_same (w_H W2) mem2 mem' a (FR _)). exact Hv.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros a _ _. apply FR. }
split. { repeat split; reflexivity. }
split. { split; [intros a _ _; apply aview_same; apply FR | intros x _; apply FR]. }
split. { intros a Ha. apply (apresent_same (w_H W2) mem2 mem' a (FR _)). apply PRES2. exact Ha. }
intros i Hi. apply FR.
Qed.

(* The primed field WITH the memnorm keep (for the keep record at the primed post, YGcfMallocComposeKeep.v). *)
Theorem wf_ret_gen_keep_rh : forall B, TfibSyms B -> forall ARX : YGcfMallocCompose.ARXh_t tfibsegs,
YGcfMallocCompose.ARX_ARcf tfibsegs B ARX ->
(forall Hp inst ly S W mem md mem' mat, ARX Hp inst ly S W mem md ->
  (forall a, aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  ARcf tfibsegs B ly S Hp W mem' (with_vm_backing (m_vm_lazy md) mat md) ->
  ARX Hp inst ly S W mem' (with_vm_backing (m_vm_lazy md) mat md)) ->
forall ly S Hp W regs mem md p n ch W1 inst so bp regsD memD mdD ly2 S2 W2 regs2 mem2 md2,
  fentry_cf tfibsegs B ly S Hp W regs mem md p n ch ->
  K_A ly S Hp W regs mem md p n ch W1 regsD memD mdD ->
  free_dpre_cf tfibsegs B 1 ARX Hp inst so bp ly (finit_cf S) W1 regsD memD mdD p n
    (ftr_cf B ly regs ch) ->
  YGcfRehidePost.dealloc_post_raw_rh tfibsegs B (ARX Hp) (aowned B) inst ly (finit_cf S) W1 regsD memD mdD
    (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly2 S2 W2 regs2 mem2 md2 ->
  qtight S2 ->
  (exists trc, apath (free_cf p (ftr_cf B ly regs ch) (finit_cf S)) trc (tt, S2) /\ gflag trc = true) ->
  SRr tfibsegs W2 (cfg_at tfibsegs (raZ regsD) regs2 mem2 md2)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
    ARX Hp inst ly2 S2 W' mem' md' /\ same_io md2 md' /\
    RGtop.rkeep tfibsegs B regs W2 mem2 W' mem' /\ RGtop.rwin tfibsegs regs W' mem' /\
    (YAkMemnorm.memnorm tfibsegs mem2 -> YAkMemnorm.memnorm tfibsegs mem') /\
    errno_kept_cf B mem2 mem').
Proof.
intros B TB ARX HXA HXF ly S Hp W regs mem md p n ch W1 inst so bp regsD memD mdD ly2 S2 W2 regs2 mem2 md2 ENT KK DPRE DPO _ _.
destruct ENT as (PRE & Hpn & _ & _ & _).
pose proof PRE as (HAR & Hra & Hal & Hlo & _ & Hhi & _).
destruct KK as (-> & D2 & D1 & D3 & D4 & DS & V1 & V8 & V9 & V18 & V19 & V20 & V21 & WIN).
destruct DPRE as (XD & _). pose proof (HXA _ _ _ _ _ _ _ XD) as HARD.
destruct DPO as ((X2 & LLE & WLE & CS2 & _ & _ & PRD) & FRR). pose proof (HXA _ _ _ _ _ _ _ X2) as HAR2.
destruct (AR_laws_ok_cf tfibsegs B) as [_ _ _ Lfr _ _ _ Lst _ _ _ _ _ _ _].
pose proof (amc_layout _ _ _ _ _ (proj1 HAR)) as LO.
pose proof (lo_top ly LO) as (_ & _ & _ & T4 & _ & _ & T7).
pose proof (lo_stk_ceil ly LO) as SC.
destruct LLE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & LL & LH & _).
unfold spZ, raZ, s0Z in Hal, Hlo, Hhi, WIN, D2, V1, V8, V9, V18, V19, V20, V21.
set (sp0 := bv_unsigned (getr regs 2)) in *.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (HSP : kHighMemBeg + ASTACK <= sp0 <= kHighMemEnd /\ sp0 mod 16 = 0)
  by (split; [clear - T7 Hlo Hhi T4; split; lia | exact Hal]).
assert (SD : bv_unsigned (getr regsD 2) = sp0 - 2128).
{ rewrite D2. change (bv_unsigned (Z_to_bv 64 (sp0 - 2128)) = sp0 - 2128). apply unsigned_lit_small.
  clear - HSP. unfold kHighMemBeg, kHighMemEnd, ASTACK in *. lia. }
assert (Ha64 : forall a, sp0 - ASTACK <= a < sp0 -> bv_unsigned (Z_to_bv 64 a) = a).
{ intros a Ha. apply unsigned_lit_small. clear - Ha HSP Usp. unfold kHighMemBeg, kHighMemEnd, ASTACK in *. lia. }
(* The caller's stack window off Deallocate's window keeps its raw bytes. *)
assert (KEEP : forall a, sp0 - ASTACK <= a < sp0 -> ~ (sp0 - 2128 - DeallocG.DFSTACK_G <= a < sp0 - 2128) ->
  mem2 (Z_to_bv 64 a) = memD (Z_to_bv 64 a)).
{ intros a Ha Hd. apply FRR; rewrite (Ha64 a Ha).
  - apply (Lst ly (finit_cf S) Hp W memD mdD a HARD). clear - Ha Hlo Hhi. lia.
  - apply (Lst ly2 S2 Hp W2 mem2 md2 a HAR2). rewrite LL, LH. clear - Ha Hlo Hhi. lia.
  - unfold ascratch, spZ. rewrite SD, (ts_errno B TB). intros [X|X]; [exact (Hd X)|].
    clear - X Ha HSP. unfold TFIB_ERRNO, kHighMemBeg, kHighMemEnd, ASTACK in *. lia.
  - cbv beta. intros (Hnp & X). destruct Hpn as [-> | Hin]; [exact (Hnp eq_refl)|].
    destruct (block_user_range_cf tfibsegs B ly S Hp W mem md p n HAR Hin) as (_ & [[_ L2] | [_ L2]]).
    + clear - X L2 Ha Hlo T7. unfold kLowShadowBeg, kHighMemBeg, ASTACK in *. lia.
    + clear - X L2 Ha Hlo SC. unfold ASTACK in *. lia. }
assert (OUT : forall a, sp0 - ASTACK <= a < sp0 -> ~ (sp0 - 2128 - DeallocG.DFSTACK_G <= a < sp0 - 2128) ->
  w_H W2 (Z_to_bv 64 a) = false /\ w_H W (Z_to_bv 64 a) = false /\ mem2 (Z_to_bv 64 a) = memD (Z_to_bv 64 a)).
{ intros a Ha Hd. destruct (WIN a Ha) as [Hh _]. split; [|split; [exact Hh | exact (KEEP a Ha Hd)]].
  destruct (w_H W2 (Z_to_bv 64 a)) eqn:EH; [|reflexivity].
  destruct (WLE _ EH) as [EW|ED]; [rewrite EW in Hh; discriminate|]. exfalso.
  rewrite (Ha64 a Ha) in ED. apply (YGcfRehidePost.dead_shadow_new_high ly (finit_cf S) S2 a); [|exact ED].
  clear - Ha HSP. unfold ASTACK in *. lia. }
(* The caller's stack window is present after Deallocate. *)
assert (PRES2 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W2) mem2 a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2128 - DeallocG.DFSTACK_G)) as [A|A];
  [|destruct (Z_lt_le_dec a (sp0 - 2128)) as [A'|A']].
  - destruct (OUT a Ha ltac:(lia)) as (H2 & _ & M2). destruct (WIN a Ha) as [_ [b Hb]].
    split; [exact H2|]. exists b. rewrite M2. exact Hb.
  - apply PRD. unfold spZ. rewrite SD. lia.
  - destruct (OUT a Ha ltac:(lia)) as (H2 & _ & M2). destruct (WIN a Ha) as [_ [b Hb]].
    split; [exact H2|]. exists b. rewrite M2. exact Hb. }
(* The seven saved words, read at Deallocate's return. *)
assert (TV : forall a v, sp0 - 56 <= a -> a + 8 <= sp0 ->
  val_mem tfibsegs (mrestrict (w_H W) memD) a 8 v -> val_mem tfibsegs (mrestrict (w_H W2) mem2) a 8 v).
{ intros a v A1 A2 Hv k Hk. rewrite <- (Hv k Hk).
  assert (Hx : sp0 - ASTACK <= a + Z.of_nat k < sp0) by (clear - A1 A2 Hk; unfold ASTACK; lia).
  destruct (OUT (a + Z.of_nat k) Hx ltac:(clear - A1 A2 Hk; lia)) as (H2 & H1 & M).
  exact (wr_mbyte_move _ _ _ _ _ H1 H2 M). }
assert (V1' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 8) 8 (bv_unsigned (getr regs 1))) by (apply TV; [lia | lia | exact V1]).
assert (V8' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 16) 8 (bv_unsigned (getr regs 8))) by (apply TV; [lia | lia | exact V8]).
assert (V9' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 24) 8 (bv_unsigned (getr regs 9))) by (apply TV; [lia | lia | exact V9]).
assert (V18' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 32) 8 (bv_unsigned (getr regs 18))) by (apply TV; [lia | lia | exact V18]).
assert (V19' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 40) 8 (bv_unsigned (getr regs 19))) by (apply TV; [lia | lia | exact V19]).
assert (V20' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 48) 8 (bv_unsigned (getr regs 20))) by (apply TV; [lia | lia | exact V20]).
assert (V21' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 56) 8 (bv_unsigned (getr regs 21))) by (apply TV; [lia | lia | exact V21]).
(* sp at Deallocate's return: Deallocate keeps it (aregs_preserved regsD regs2). *)
assert (R2 : getr regs2 2 = w64 (sp0 - 2128)).
{ pose proof (CS2 2 ltac:(unfold acallee_saved; lia)) as C.
  replace (Z_to_bv 5 2) with (2%bv : bv 5) in C by (apply bv_eq; reflexivity). rewrite C. exact D2. }
replace (raZ regsD) with 0x538e8 by (unfold raZ; rewrite D1; reflexivity).
unfold cfg_at.
eapply SRr_mono; [exact (wr_run W2 regs2 regs mem2 md2 HSP R2 V1' V8' V9' V18' V19' V20' V21' Hra)|].
intros W' c' _ (-> & regs' & mem' & mat & -> & RP & FR).
exists regs', mem', (with_vm_backing (m_vm_lazy md2) mat md2).
destruct RP as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & P3 & P4 & P22).
split.
{ lazymatch goal with |- _ = mkCfg (mkst _ ?pc _ _) _ =>
    replace pc with (getr regs 1) by (unfold raZ; first [apply Z_to_bv_bv_unsigned | symmetry; apply Z_to_bv_bv_unsigned]) end.
  reflexivity. }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]].
  - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). exact P2.
  - replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P3, <- D3.
    pose proof (CS2 3 ltac:(unfold acallee_saved; lia)) as C.
    replace (Z_to_bv 5 3) with (3%bv : bv 5) in C by (apply bv_eq; reflexivity). exact C.
  - replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P4, <- D4.
    pose proof (CS2 4 ltac:(unfold acallee_saved; lia)) as C.
    replace (Z_to_bv 5 4) with (4%bv : bv 5) in C by (apply bv_eq; reflexivity). exact C.
  - replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). exact P8.
  - replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). exact P9.
  - assert (R : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ 22 <= r <= 27) by lia. clear Hr.
    destruct R as [->|[->|[->|[->|R]]]].
    + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). exact P18.
    + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). exact P19.
    + replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). exact P20.
    + replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). exact P21.
    + rewrite (P22 r R), (CS2 r ltac:(unfold acallee_saved; lia)). exact (DS r R). }
split.
{ apply (HXF Hp inst ly2 S2 W2 mem2 md2 mem' mat X2); [intros a; apply aview_same; apply FR|].
  apply (Lfr ly2 S2 Hp W2 mem2 md2 mem' (with_vm_backing (m_vm_lazy md2) mat md2) HAR2).
  - intros a _ _. apply aview_same. apply FR.
  - intros a Hv. rewrite (aview_same (w_H W2) mem2 mem' a (FR _)). exact Hv.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros a _ _. apply FR. }
split. { repeat split; reflexivity. }
split. { split; [intros a _ _; apply aview_same; apply FR | intros x _; apply FR]. }
split. { intros a Ha. apply (apresent_same (w_H W2) mem2 mem' a (FR _)). apply PRES2. exact Ha. }
split. { intros [M1 M2]. split; intros a b Hb; rewrite FR in Hb; [exact (M1 a b Hb) | exact (M2 a b Hb)]. }
intros i Hi. apply FR.
Qed.

End c.
