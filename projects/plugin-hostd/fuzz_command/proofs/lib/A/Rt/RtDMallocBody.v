(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AFeq.v, with its module paths changed; 405 of its 438 lines of code are new or changed and 214 lines of the source are left out. *)
(* The malloc interceptor's body ___interceptor_malloc 0x58b58 of plugin-hostd/fuzz_command's memory-checking image,
   lib/A/Rt/RtDDefs.v amalloc_body_realizes at 0x58b58 with the unwinder pc 0x58c20 and the window MALLOC_IN_STK,
   from the contract of __asan::asan_malloc 0x34528 (amalloc_inner_realizes) and the unwinder's call spec.
   The walk (lib/A/Rt/RtDMallocRun.v): the prologue (frame 2,128 bytes, ra/s0..s5 saved in [sp0-56, sp0)), the
   initialised test and GetMallocContextSize (record cells), the BufferedStackTrace at sp0-2128 (trace pointer
   sp0-2112, size and tag 0), GetCurrentPc = 0x58c20, then BufferedStackTrace::UnwindImpl 0x603d8 with this =
   sp0-2128, pc = 0x58c20, bp = s0 = sp0, request_fast = 1, max_depth = 30 (lib/A/Rt/RtDMallocUnw.v dm_unwind_any:
   cgif's spec when ly_bot < sp0, the walked bottom case otherwise; the trace it writes is inner_trace), then
   asan_malloc(n, &trace) at sp0-2128 (window MALLOC_ASAN_STK = MALLOC_IN_STK - 2,128), then the epilogue.
   The new block is below the stack (the model's malloc_post with AR_blocks_law), so the saved registers and the
   trace object outlive the inner call. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YN2j.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG07 YG0k YFfk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDDefs RtDMallocRun RtDMallocLeaf RtDMallocUnw.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AFl4.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Lemma dm_win_ss0 : forallb (fun t => win_eqb t (Some 2%nat, - 14208, 0) || (snd t <=? snd (fst t))) (windows (ss_mem DM_SS0)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma dm_win_1 : forallb (fun t => win_eqb t (Some 2%nat, - 64, 0) || (snd t <=? snd (fst t))) (windows (ss_mem DM_1)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma dm_win_2 : forallb (fun t => win_eqb t (Some 2%nat, - 64, 0) || (snd t <=? snd (fst t))) (windows (ss_mem DM_2)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma dm_u_atoms : ss_atoms_lt 64 DM_U = true /\ regions_wf dm_rsU = true /\ no_cdata dm_rsU = true /\ mem_atoms_lt 64 dm_rsU = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma dm_a_atoms : ss_atoms_lt 96 DM_A = true /\ regions_wf (ss_mem DM_A) = true /\ no_cdata (ss_mem DM_A) = true /\ mem_atoms_lt 96 (ss_mem DM_A) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma dm_1_eq : ss_after_call DM_U dm_rsU DM_HAV DM_RET1 = DM_1. Proof. reflexivity. Qed.
Lemma dm_2_eq : ss_after_call DM_A (ss_mem DM_A) DM_HAV2 DM_RET2 = DM_2. Proof. reflexivity. Qed.
Lemma dm_rsU_eq : dm_rsU = [YP09.mkRegion (Some 2%nat) (- 64) 0 (- 64) 0 (YP09.r_chunks (hd dm_stk dm_rsU))].
Proof. vm_compute. reflexivity. Qed.
Lemma dm_a_mem_eq : ss_mem DM_A = [YP09.mkRegion (Some 2%nat) (- 64) 0 (- 64) 0 (YP09.r_chunks dm_a_r0)].
Proof. vm_compute. reflexivity. Qed.
Lemma dm_r_mem0 : nth_error (ss_mem DM_R) 0 = Some dm_a_r0.
Proof. vm_compute. reflexivity. Qed.
Lemma dm_a_mem0 : nth_error (ss_mem DM_A) 0 = Some dm_a_r0.
Proof. vm_compute. reflexivity. Qed.
Lemma dm_a_r0_win : YP09.r_base dm_a_r0 = Some 2%nat /\ YP09.r_wlo dm_a_r0 = - 64 /\ YP09.r_whi dm_a_r0 = 0.
Proof. vm_compute. repeat split; reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* a register an atom (or an atom plus an offset, or a literal) in a symbolic state *)
Lemma dm_reg_off : forall H E ss ms (r : bv 5) k off,
st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff k off ->
getr (ms_regs ms) r = Z_to_bv 64 (bv_unsigned (ew E k) + off).
Proof. intros H E ss ms r k off HS Hr. rewrite (st_ok_reg_denot H E ss ms r HS), Hr. reflexivity. Qed.
Lemma dm_reg_atom : forall H E ss ms (r : bv 5) k,
st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff k 0 -> getr (ms_regs ms) r = ew E k.
Proof.
intros H E ss ms r k HS Hr. rewrite (dm_reg_off H E ss ms r k 0 HS Hr), Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.
Lemma dm_reg_lit : forall H E ss ms (r : bv 5) z,
st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z -> getr (ms_regs ms) r = Z_to_bv 64 z.
Proof. intros H E ss ms r z HS Hr. rewrite (st_ok_reg_denot H E ss ms r HS), Hr. reflexivity. Qed.

(* lib/A/AFl3.v chunk_val_at / memv *)
Lemma dm_chunk_val_at : forall (H : word -> bool) E ss ms i j r off (n : BinNums.N) e v a,
st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CVal n e)) ->
a = base_val E (YP09.r_base r) + off ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem tfibsegs (mrestrict H (ms_mem ms)) a (N.to_nat n) v.
Proof. intros H E ss ms i j r off n e v a HS Hi Hj -> He Hv Hn. eapply st_ok_chunk_val; eassumption. Qed.

Variable B : asyms.
Hypothesis TB : CmdBSyms B.
Hypothesis LAWS : AR_laws tfibsegs B.
(* the unwinder's call spec: dm_unwind_spec is the text of the chain's lib/A/AFl0.v tfib_unwind_spec, which
   lib/A/AFl4.v tfib_unwind_ok proves *)
Lemma U1 : dm_unwind_spec.
Proof. exact AFl4.tfib_unwind_ok. Qed.
(* asan_malloc with a trace its caller built *)
Hypothesis INNER : amalloc_inner_realizes tfibsegs B PC_asan_malloc.

Ltac memv HS i j :=
lazymatch goal with |- val_mem _ _ ?a ?n ?v =>
let nn := lazymatch n with 1%nat => constr:(1%N) | 2%nat => constr:(2%N) | 4%nat => constr:(4%N) | _ => constr:(8%N) end in
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
eapply (dm_chunk_val_at H E ss ms i j _ _ nn _ v a HS);
[ reflexivity | reflexivity | cbn [base_val YP09.r_base]
| | lazymatch goal with |- _ <= _ < ?p => let q := eval vm_compute in p in change p with q end
| cbn; lia ]
end
end.

Theorem cmd_amalloc_body : amalloc_body_realizes tfibsegs B PC_malloc_body DM_PC0.
Proof.
intros ly S W regs mem md n ch PRE Hn Hrange Hlive Htr.
destruct PRE as (HAR & Hreg & Hret & Hal & Hslo & Hshi & Hpres & Hgp & Htp & Hch & Hqm).
pose proof (am_layout B ly S _ (proj1 HAR)) as LY.
pose proof (img_cover_of_ledger ly S md (proj1 (proj2 HAR))) as IMG.
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd _ _ _ _ (proj1 HAR)); exact (ts_tsd B TB)).
pose proof (lo_top ly LY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof (lo_stk_ceil ly LY) as Lceil. unfold ASAN_CEIL in Lceil. pose proof alloc_ceiling_val as ACV.
unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi. unfold MALLOC_IN_STK in Hslo, Hpres.
pose proof (RtDMallocUnw.T_high ly LY) as (T1 & T2). pose proof (RtDMallocUnw.C_high ly LY) as (C1 & C2).
pose proof (RtDMallocUnw.TC_disj ly LY) as (_ & TD & CD).
unfold in_app, kThreadObjSize, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in T1, T2, C1, C2, TD.
rewrite (ts_tp B TB) in Htp.
set (Hd := w_H W) in *.
set (sp0 := spZ regs) in *.
pose proof (u64_range (getr regs 2%bv)) as Usp. fold sp0 in Usp.
destruct Hch as (Hra4096 & Hch).
(* ---- the entry state ---- *)
set (EE := AE2y.Env regs []).
assert (EEr : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEr 2%nat 2%bv eq_refl); reflexivity).
assert (HS0 : st_ok tfibsegs EE DM_SS0 (restrict Hd (mkst regs (Z_to_bv 64 DM_BODY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold DM_SS0, EE, AE2y.Env. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| exact (rodata_ok B TB dm_rodata ly S Hd mem (AE2y.Env regs []) (dm_rodata_chk ly) (proj1 HAR))].
unfold dm_stk, DM_WIN. apply (region_ok_stack tfibsegs _ _ 2 sp0 (- 14208)); [exact EE2 | lia | lia |].
intros a Ha. apply AF0x.apresent_writable; [unfold TFIB_IMG_END; lia|]. apply Hpres. lia.
- apply pairwise_disjoint_of_extents. unfold dm_stk, dm_rodata, ro_region, extent_of_region, DM_WIN.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. try change (Ereg regs []) with EE. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [exact I | split; exact I]. }
(* the facts the unwinder reads, at the entry *)
set (m0 := mrestrict Hd mem).
assert (V1 : val_mem tfibsegs m0 0xb1d98 1 1) by (apply (tfib_const_lookup B TB ly S Hd mem 0xb1d98 1 1 (proj1 HAR)); vm_compute; reflexivity).
assert (V2 : val_mem tfibsegs m0 0xb0920 1 1) by (apply (tfib_const_lookup B TB ly S Hd mem 0xb0920 1 1 (proj1 HAR)); vm_compute; reflexivity).
assert (V3 : val_mem tfibsegs m0 0xb0924 4 0) by (apply (tfib_const_lookup B TB ly S Hd mem 0xb0924 4 0 (proj1 HAR)); vm_compute; reflexivity).
assert (V11 : val_mem tfibsegs m0 0xa63d0 8 0x140b60) by (apply (tfib_const_lookup B TB ly S Hd mem 0xa63d0 8 0x140b60 (proj1 HAR)); vm_compute; reflexivity).
assert (V12 : val_mem tfibsegs m0 0x140b60 8 4096) by (apply (tfib_const_lookup B TB ly S Hd mem 0x140b60 8 4096 (proj1 HAR)); vm_compute; reflexivity).
assert (V4 : val_mem tfibsegs m0 (TFIB_TP - 88) 8 TFIB_TSD).
{ replace (TFIB_TP - 88) with (aeval B ly (ATp (-88))) by (cbn [aeval]; rewrite (ts_tp B TB); reflexivity).
replace TFIB_TSD with (aeval B ly (ATsd 0)) by (cbn [aeval]; rewrite HTSD; unfold TFIB_TSD; lia).
apply (tfib_const_lookup_sym B TB ly S Hd mem (ATp (-88)) 8 (ATsd 0) (proj1 HAR)). vm_compute. reflexivity. }
assert (V5 : val_mem tfibsegs m0 TFIB_TSD 8 (ly_C ly)).
{ replace TFIB_TSD with (aeval B ly (ATsd 0)) by (cbn [aeval]; rewrite HTSD; unfold TFIB_TSD; lia).
replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn [aeval]; lia).
apply (tfib_const_lookup_sym B TB ly S Hd mem (ATsd 0) 8 (AC 0) (proj1 HAR)). vm_compute. reflexivity. }
assert (V6 : val_mem tfibsegs m0 (ly_C ly + 152) 8 (ly_T ly)).
{ replace (ly_C ly + 152) with (aeval B ly (AC 152)) by (cbn [aeval]; lia).
replace (ly_T ly) with (aeval B ly (AT 0)) by (cbn [aeval]; lia).
apply (tfib_const_lookup_sym B TB ly S Hd mem (AC 152) 8 (AT 0) (proj1 HAR)). vm_compute. reflexivity. }
assert (V7 : val_mem tfibsegs m0 (ly_T ly + 40) 1 0).
{ replace (ly_T ly + 40) with (aeval B ly (AT 40)) by (cbn [aeval]; lia).
apply (tfib_const_lookup_sym B TB ly S Hd mem (AT 40) 1 (ANum 0) (proj1 HAR)). vm_compute. reflexivity. }
assert (V8 : val_mem tfibsegs m0 (ly_T ly + 8) 8 (ly_top ly)).
{ replace (ly_T ly + 8) with (aeval B ly (AT 8)) by (cbn [aeval]; lia).
replace (ly_top ly) with (aeval B ly (ATop 0)) by (cbn [aeval]; lia).
apply (tfib_const_lookup_sym B TB ly S Hd mem (AT 8) 8 (ATop 0) (proj1 HAR)). vm_compute. reflexivity. }
assert (V9 : val_mem tfibsegs m0 (ly_T ly + 16) 8 (ly_bot ly)).
{ replace (ly_T ly + 16) with (aeval B ly (AT 16)) by (cbn [aeval]; lia).
replace (ly_bot ly) with (aeval B ly (ATop (- kStackSpan))) by (cbn [aeval]; unfold ly_bot; lia).
apply (tfib_const_lookup_sym B TB ly S Hd mem (AT 16) 8 (ATop (- kStackSpan)) (proj1 HAR)). vm_compute. reflexivity. }
assert (V10 : val_mem tfibsegs m0 (ly_T ly + t_unwinding) 1 0).
{ replace (ly_T ly + t_unwinding) with (aeval B ly (AT t_unwinding)) by reflexivity.
apply (cell_holds_val_mem B ly Hd mem (AT t_unwinding) 1 (ANum 0)).
apply (proj1 (Forall_forall _ _) (am_cells B ly S _ (proj1 HAR))).
unfold acells. do 8 (apply in_or_app; right). left. reflexivity. }
assert (P10 : apresent Hd mem (ly_T ly + t_unwinding)).
{ assert (TZ : zone3 (ly_T ly) kThreadObjSize).
{ pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD. destruct HD as (_ & _ & D3 & _).
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail D3))))))) as X.
exact (zone3_intro ly (ly_T ly) kThreadObjSize IMG ltac:(unfold kThreadObjSize; lia) (RtDMallocUnw.T_high ly LY) X). }
eapply mbyte_off_apresent; [exact (zone3_off_img (ly_T ly) kThreadObjSize (ly_T ly + t_unwinding) TZ ltac:(unfold t_unwinding, kThreadObjSize; lia))|].
rewrite <- (Z.add_0_r (ly_T ly + t_unwinding)). exact (V10 0%nat ltac:(lia)). }
(* ---- the prefix: 0x58b58 to the unwinder call ---- *)
apply (amreal_SRr_pre tfibsegs _ W (cfg_at tfibsegs PC_malloc_body regs mem md) _
(fun W' c' => amreal tfibsegs (malloc n (inner_trace ly DM_PC0 regs ch) S) W' c' (malloc_leaf_w tfibsegs B MALLOC_IN_STK ly S W regs mem md n)));
[| intros W' c' _ HX; exact HX].
eapply SRr_bind; [exact (dm_phase W EE DM_SS0 DM_U (mkst regs (Z_to_bv 64 DM_BODY) mem (seg_rom tfibsegs)) md DM_UNWIND HS0 dm_run_u)|].
cbv beta. intros W1 c1 _ (-> & msU & matU & -> & HSU & HFU & _).
set (mdU := with_vm_backing (m_vm_lazy md) matU md) in *.
assert (SBMU : same_but_materialized md mdU) by exact (with_vm_backing_same md matU). clearbody mdU.
cbn [ms_mem mkst] in HFU.
assert (MEQU : forall x : word, ~ (sp0 - 14208 <= bv_unsigned x < sp0) -> ms_mem msU x = mem x).
{ intros x Hx. apply HFU. intros Hin. apply Hx.
pose proof (in_wrange_single_b EE (ss_mem DM_SS0) (bv_unsigned x) 2 (- 14208) 0 sp0 dm_win_ss0 EE2 Hin). lia. }
pose proof dm_u_shape as (UPC & URV & UR1 & UR2 & UR4 & UR8 & UR9 & UR10 & UR11 & UR12 & UR13 & UR14 & UR15).
pose proof (st_ok_restrict_mkst tfibsegs Hd EE DM_U msU HSU URV) as UShape. rewrite UPC in UShape.
assert (SPU : bv_unsigned (getr (ms_regs msU) 2%bv) = sp0 - 2128).
{ rewrite (dm_reg_off Hd EE DM_U msU 2%bv 2 (- DM_FRAME) HSU UR2), EE2. apply unsigned_lit_small. unfold DM_FRAME. lia. }
assert (PRU : forall a, sp0 - 14208 <= a < sp0 -> apresent Hd (ms_mem msU) a).
{ intros a Ha. pose proof dm_u_r0_shape as (B0 & L0 & H0 & WL0 & WH0 & _).
apply (AF0x.st_ok_window_apresent Hd EE DM_U msU 0 dm_u_r0 a HSU dm_u_mem0); [| unfold TFIB_IMG_END; lia].
rewrite B0, WL0, WH0. cbn [base_val]. rewrite EE2. unfold DM_WIN. lia. }
(* transfer of the read-only facts to the memory at the call *)
assert (OUT : forall a k v, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 -> (a + Z.of_nat k <= sp0 - 14208 \/ sp0 <= a) ->
val_mem tfibsegs m0 a k v -> val_mem tfibsegs (mrestrict Hd (ms_mem msU)) a k v).
{ intros a k v Ha Hk Ho Hv. exact (dm_val_mem_out Hd mem (ms_mem msU) (sp0 - 14208) sp0 a k v MEQU Ha Hk Ho Hv). }
assert (TOUT : forall o, 0 <= o -> o + 8 <= 4096 -> ly_T ly + o + 8 <= sp0 - 14208 \/ sp0 <= ly_T ly + o) by (intros; lia).
(* ---- the unwinder call ---- *)
set (TRACE := if sp0 <=? ly_bot ly then [DM_PC0] else if sp0 + 16 <? ly_top ly
then unwind_of_chain DM_PC0 ((sp0, raZ regs, s0Z regs) :: ch) else [DM_PC0]).
assert (ETR : TRACE = inner_trace ly DM_PC0 regs ch) by reflexivity.
assert (UNW : SRr tfibsegs W (mkCfg (mkst (ms_regs msU) (Z_to_bv 64 DM_UNW_PC) (ms_mem msU) (seg_rom tfibsegs)) mdU)
(dm_unw_post W (ms_regs msU) (ms_mem msU) mdU (sp0 - 2128) sp0 TRACE)).
{ apply (dm_unwind_any U1 W ly (ms_regs msU) (ms_mem msU) mdU (sp0 - 2128) DM_PC0 sp0 (raZ regs) (s0Z regs) ch LY IMG).
- rewrite (dm_reg_off Hd EE DM_U msU 10%bv 2 (- DM_FRAME) HSU UR10), EE2. unfold DM_FRAME; f_equal; lia.
- exact (dm_reg_lit Hd EE DM_U msU 11%bv DM_PC0 HSU UR11).
- rewrite (dm_reg_off Hd EE DM_U msU 12%bv 2 0 HSU UR12), EE2; f_equal; lia.
- exact (dm_reg_lit Hd EE DM_U msU 13%bv 0 HSU UR13).
- exact (dm_reg_lit Hd EE DM_U msU 14%bv 1 HSU UR14).
- exact (dm_reg_lit Hd EE DM_U msU 15%bv 30 HSU UR15).
- rewrite (dm_reg_atom Hd EE DM_U msU 4%bv 4 HSU UR4), (EEr 4%nat 4%bv eq_refl). exact Htp.
- rewrite (dm_reg_lit Hd EE DM_U msU 1%bv DM_RET1 HSU UR1). apply ret_ok_even. reflexivity.
- unfold DM_PC0. lia.
- apply OUT; [lia | cbn; lia | cbn; lia | exact V1].
- apply OUT; [lia | cbn; lia | cbn; lia | exact V2].
- apply OUT; [lia | cbn; lia | cbn; lia | exact V3].
- apply OUT; [unfold TFIB_TP; lia | cbn; unfold TFIB_TP; lia | cbn; unfold TFIB_TP; lia | exact V4].
- apply OUT; [unfold TFIB_TSD; lia | cbn; unfold TFIB_TSD; lia | cbn; unfold TFIB_TSD; lia | exact V5].
- apply OUT; [lia | cbn; lia | cbn; lia | exact V6].
- apply OUT; [lia | cbn; lia | cbn; lia | exact V7].
- apply OUT; [lia | cbn; lia | cbn; lia | exact V8].
- apply OUT; [lia | cbn; lia | cbn; lia | exact V9].
- apply OUT; [unfold t_unwinding; lia | cbn; unfold t_unwinding; lia | cbn; unfold t_unwinding; lia | exact V10].
- apply (apresent_same Hd mem (ms_mem msU)); [| exact P10]. apply MEQU. rewrite unsigned_lit_small by (unfold t_unwinding; lia). unfold t_unwinding. lia.
- apply OUT; [lia | cbn; lia | cbn; lia | exact V11].
- apply OUT; [lia | cbn; lia | cbn; lia | exact V12].
- rewrite SPU. replace (sp0 - 2128) with (sp0 + (-133) * 16) by lia. rewrite Z_mod_plus_full. exact Hal.
- rewrite SPU. unfold DM_UNW_STK. lia.
- intros a Ha. rewrite SPU in Ha. apply PRU. unfold DM_UNW_STK in Ha. lia.
- replace (sp0 - 2128) with (sp0 + (-266) * 8) by lia. rewrite Z_mod_plus_full.
apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 16); [exists 2; reflexivity|]. apply Znumtheory.Zmod_divide; [lia | exact Hal].
- lia.
- rewrite SPU. right. lia.
- intros a Ha. apply PRU. unfold DM_BST in Ha. lia.
- unfold DM_BST. lia.
- rewrite SPU. lia.
- exact Hshi.
- apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 16); [exists 2; reflexivity|]. apply Znumtheory.Zmod_divide; [lia | exact Hal].
- apply val_mem_rdword; [apply u64_range|]. memv HSU 0%nat 11%nat;
[rewrite EE2; lia
| cbn [sv_denot]; rewrite (EEr 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity | apply u64_range].
- apply val_mem_rdword; [apply u64_range|]. memv HSU 0%nat 10%nat;
[rewrite EE2; lia
| cbn [sv_denot]; rewrite (EEr 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity | apply u64_range].
- exact Hra4096.
- unfold frame0_ok in Hch. fold sp0 in Hch.
destruct (sp0 + 16 <? ly_top ly) eqn:Hf0; [|exact Hch].
destruct (bad_next sp0 (ly_top ly) (s0Z regs)) eqn:Hb; [exact Hch|].
destruct Hch as [H16 Hfp]. split; [exact H16|].
unfold bad_next in Hb. apply Bool.orb_false_iff in Hb as [Hb _]. apply Bool.orb_false_iff in Hb as [Hb1 Hb2].
apply Z.leb_gt in Hb2.
eapply AF0x.fpchain_ext2; [exact Hfp | lia |].
intros a va Ha1 Ha2 Hva. eapply AF0x.rdword_ext; [|exact Hva]. intros i Hi. apply aview_same.
apply MEQU. rewrite unsigned_lit_small by lia. lia. }
rewrite UShape. eapply SRr_bind; [exact UNW|].
clear UNW. intros W2 c2 _ (-> & regs' & mem' & mat' & -> & URP & UFR & UPR & USZ & UFRM & UTOP).
rewrite (dm_reg_lit Hd EE DM_U msU 1%bv DM_RET1 HSU UR1).
assert (MEQ' : forall z : word, ~ (sp0 - 2272 <= bv_unsigned z < sp0 - 64) -> mem' z = (ms_mem msU) z).
{ intros z Hz. apply UFR; try rewrite SPU; unfold DM_UNW_STK, DM_BST; lia. }
(* ---- after the unwinder: the saved registers, sp0 - 64 .. sp0 ---- *)
pose proof (st_ok_after_call tfibsegs DM_HAV EE DM_U (restrict Hd msU) regs' (mrestrict Hd mem') dm_rsU DM_RET1 HSU URV
(proj1 dm_u_atoms) (proj1 (proj2 dm_u_atoms)) (proj1 (proj2 (proj2 dm_u_atoms))) (proj2 (proj2 (proj2 dm_u_atoms)))
dm_submem_u UR1 URP) as HS1.
lazymatch type of HS1 with ?P -> _ => assert (KEPT : P) end.
{ rewrite dm_rsU_eq. apply Forall_cons; [| apply Forall_nil].
apply (dm_kept_of_eq EE Hd (ms_mem msU) mem' 2 (- 64) 0 (- 64) 0 _ sp0 (sp0 - 2272) (sp0 - 64) EE2 MEQ'); lia. }
specialize (HS1 KEPT). clear KEPT. rewrite dm_1_eq in HS1. rewrite <- (restrict_mkst_fx Hd) in HS1.
set (E1 := havoc EE DM_HAV (map (getr regs') CLOB)) in *.
assert (E1o : forall k, (k < 64)%nat -> ew E1 k = ew EE k) by (intros k Hk; exact (ew_havoc_old EE DM_HAV (map (getr regs') CLOB) k Hk)).
assert (E12 : bv_unsigned (ew E1 2) = sp0) by (rewrite (E1o 2%nat ltac:(lia)); exact EE2).
(* ---- to the call of asan_malloc ---- *)
eapply SRr_bind; [exact (dm_phase W E1 DM_1 DM_A (mkst regs' (Z_to_bv 64 DM_RET1) mem' (seg_rom tfibsegs))
(with_vm_backing (m_vm_lazy mdU) mat' mdU) DM_ASAN HS1 dm_run_a)|].
cbv beta. intros W3 c3 _ (-> & msA & matA & -> & HSA & HFA & _).
rewrite wvb_collapse.
set (mdA := with_vm_backing (m_vm_lazy mdU) matA mdU) in *.
assert (SBMA : same_but_materialized md mdA) by exact (same_but_materialized_trans md mdU mdA SBMU (with_vm_backing_same mdU matA)).
clearbody mdA. cbn [ms_mem mkst] in HFA.
assert (MEQA : forall x : word, ~ (sp0 - 64 <= bv_unsigned x < sp0) -> ms_mem msA x = mem' x).
{ intros x Hx. apply HFA. intros Hin. apply Hx.
pose proof (in_wrange_single_b E1 (ss_mem DM_1) (bv_unsigned x) 2 (- 64) 0 sp0 dm_win_1 E12 Hin). lia. }
pose proof dm_a_shape as (APC & ARV & AM & AB & AL & AH & AWL & AWH & AR1 & AR2 & AR3 & AR4 & AR10 & AR11).
pose proof (st_ok_restrict_mkst tfibsegs Hd E1 DM_A msA HSA ARV) as AShape. rewrite APC in AShape.
(* the memory at the call against the entry's *)
assert (MEQA0 : forall x : word, ~ (sp0 - 14208 <= bv_unsigned x < sp0) -> (ms_mem msA) x = mem x).
{ intros x Hx. rewrite MEQA by lia. rewrite MEQ' by lia. apply MEQU. exact Hx. }
assert (PRA : forall a, sp0 - 14208 <= a < sp0 -> apresent Hd (ms_mem msA) a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 64)) as [Hlo|Hhi].
- apply (apresent_same Hd mem' (ms_mem msA) a); [apply MEQA; rewrite unsigned_lit_small by lia; lia|].
apply UPR. apply PRU. exact Ha.
- apply (AF0x.st_ok_window_apresent Hd E1 DM_A msA 0 dm_a_r0 a HSA dm_a_mem0); [| unfold TFIB_IMG_END; lia].
rewrite AB, AWL, AWH. cbn [base_val]. rewrite E12. unfold DM_KEEP. lia. }
assert (SPA : bv_unsigned (getr (ms_regs msA) 2%bv) = sp0 - 2128).
{ rewrite (dm_reg_off Hd E1 DM_A msA 2%bv 2 (- DM_FRAME) HSA AR2), E12. apply unsigned_lit_small. unfold DM_FRAME. lia. }
(* the trace object at sp0 - 2128 *)
assert (TRB : forall x, In x TRACE -> 0 <= x < 2 ^ 64).
{ rewrite ETR. apply dm_trace_bound; [unfold DM_PC0; lia|].
unfold frame0_ok in Hch. fold sp0 in Hch. destruct (sp0 + 16 <? ly_top ly); [|subst ch; constructor].
destruct (bad_next sp0 (ly_top ly) (s0Z regs)); [subst ch; constructor|].
exact (dm_fpchain_bound Hd mem _ _ ch (proj2 Hch)). }
assert (TRL : (length TRACE <= kUnwindMax)%nat).
{ rewrite ETR. unfold inner_trace. destruct (spZ regs <=? ly_bot ly); [cbn; unfold kUnwindMax; lia | apply call_trace_len]. }
unfold kUnwindMax in TRL.
assert (OBJ0 : val_mem tfibsegs (mrestrict Hd (ms_mem msU)) (sp0 - 2128) 8 (sp0 - 2112)).
{ memv HSU 0%nat 2%nat; [rewrite EE2; lia
| cbn [sv_denot]; rewrite EE2; try (f_equal; lia) | lia]. }
assert (OBJ1 : val_mem tfibsegs (mrestrict Hd (ms_mem msU)) (sp0 - 2120) 8 0).
{ memv HSU 0%nat 1%nat; [rewrite EE2; lia | reflexivity | lia]. }
(* bytes of the trace object the unwinder did not write: the call leaves them as they were *)
assert (UKEEP : forall a k v, sp0 - 2128 <= a -> a + Z.of_nat k <= sp0 - 2120 \/ (sp0 - 2116 <= a /\ a + Z.of_nat k <= sp0 - 2112) ->
val_mem tfibsegs (mrestrict Hd (ms_mem msU)) a k v -> val_mem tfibsegs (mrestrict Hd mem') a k v).
{ intros a k v Ha Hk Hv. apply (val_mem_frame Hd (ms_mem msU) mem' a k v); [|exact Hv].
intros j Hj. apply UFR; try rewrite SPU; rewrite unsigned_lit_small by lia; unfold DM_UNW_STK, DM_BST; lia. }
assert (AKEEP : forall a k v, 0 <= a -> a + Z.of_nat k <= sp0 - 64 ->
val_mem tfibsegs (mrestrict Hd mem') a k v -> val_mem tfibsegs (mrestrict Hd (ms_mem msA)) a k v).
{ intros a k v Ha Hk Hv. exact (dm_val_mem_out Hd mem' (ms_mem msA) (sp0 - 64) sp0 a k v MEQA Ha ltac:(lia) ltac:(lia) Hv). }
assert (ATR : astrace_at tfibsegs W (ms_mem msA) (sp0 - 2128) TRACE).
{ split; [|split; [|split]].
- apply val_mem_rdword; [lia|]. replace (sp0 - 2128 + 16) with (sp0 - 2112) by lia.
apply AKEEP; [lia | cbn; lia|]. apply UKEEP; [lia | cbn; lia | exact OBJ0].
- apply dm_rd32_of_val_mem. apply AKEEP; [lia | cbn; lia | exact USZ].
- apply dm_rd32_of_val_mem.
assert (Z4 : val_mem tfibsegs (mrestrict Hd (ms_mem msU)) (sp0 - 2128 + 12) 4 0).
{ intros k Hk. replace (sp0 - 2128 + 12 + Z.of_nat k) with (sp0 - 2120 + Z.of_nat (4 + k)) by lia.
rewrite (OBJ1 (4 + k)%nat ltac:(lia)).
assert (LB0 : forall w j, le_byte 0 w j = 0).
{ intros w j. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. }
rewrite !LB0. reflexivity. }
apply AKEEP; [lia | cbn; lia|]. apply UKEEP; [lia | cbn; lia | exact Z4].
- intros i Hi. apply val_mem_rdword; [apply TRB; apply nth_In; exact Hi|].
apply AKEEP; [lia | cbn; lia | exact (UFRM i Hi)]. }
(* ---- asan_malloc ---- *)
assert (HARA : AR tfibsegs B ly S W (ms_mem msA) mdA).
{ destruct (same_but_materialized_frame md mdA SBMA) as (_ & V1m & V2m & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V3m).
apply (al_frame _ _ LAWS ly S W mem md (ms_mem msA) mdA HAR).
- intros a Ha Ho. apply aview_same. apply MEQA0. rewrite unsigned_lit_small by lia. intros Hs.
exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(lia) Ho).
- intros a Hv. fold Hd in Hv |- *. rewrite (AE2y.aview_mod _ (ms_mem msA) a). rewrite (AE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 14208)) as [L1|L1];
[rewrite (aview_same Hd mem (ms_mem msA) a'); [exact Hv | apply MEQA0; rewrite unsigned_lit_small by lia; lia]|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply aview_some_of_apresent; apply PRA; lia|].
rewrite (aview_same Hd mem (ms_mem msA) a'); [exact Hv | apply MEQA0; rewrite unsigned_lit_small by lia; lia].
- exact V1m.
- exact V2m.
- exact V3m.
- exact (AE2y.hs_kept_win Hd mem mem (ms_mem msA) (sp0 - 14208) sp0 (sp0 - 14208) sp0 MEQA0 Hpres ltac:(lia) ltac:(lia)). }
assert (G3A : getr (ms_regs msA) 3%bv = w64 (as_gp B))
by (rewrite (dm_reg_atom Hd E1 DM_A msA 3%bv 3 HSA AR3), (E1o 3%nat ltac:(lia)), (EEr 3%nat 3%bv eq_refl); exact Hgp).
assert (G4A : getr (ms_regs msA) 4%bv = w64 (as_tp B))
by (rewrite (dm_reg_atom Hd E1 DM_A msA 4%bv 4 HSA AR4), (E1o 4%nat ltac:(lia)), (EEr 4%nat 4%bv eq_refl), (ts_tp B TB); exact Htp).
assert (G10A : getr (ms_regs msA) 10%bv = w64 n)
by (rewrite (dm_reg_atom Hd E1 DM_A msA 10%bv 10 HSA AR10), (E1o 10%nat ltac:(lia)), (EEr 10%nat 10%bv eq_refl); exact Hn).
assert (G11A : getr (ms_regs msA) 11%bv = w64 (sp0 - 2128)).
{ rewrite (dm_reg_off Hd E1 DM_A msA 11%bv 2 (- DM_FRAME) HSA AR11), E12. unfold w64, DM_FRAME; f_equal; lia. }
assert (TRU : In TRACE (as_universe B) \/ st_nev S < EV_MAX) by (rewrite ETR; exact Htr).
assert (TRA : tr_admit (as_universe B) S TRACE)
by (destruct TRU as [X|X]; [left; exact X | right; split; [unfold kUnwindMax; lia | exact X]]).
assert (SPA' : spZ (ms_regs msA) = sp0 - 2128) by exact SPA.
pose proof (INNER ly S W (ms_regs msA) (ms_mem msA) mdA n (sp0 - 2128) TRACE HARA Hreg
ltac:(rewrite (dm_reg_lit Hd E1 DM_A msA 1%bv DM_RET2 HSA AR1); apply ret_ok_even; reflexivity)
ltac:(rewrite SPA'; replace (sp0 - 2128) with (sp0 + (-133) * 16) by lia; rewrite Z_mod_plus_full; exact Hal)
ltac:(rewrite SPA'; unfold MALLOC_ASAN_STK; lia)
ltac:(rewrite SPA'; lia)
ltac:(intros a Ha; rewrite SPA' in Ha; unfold MALLOC_ASAN_STK in Ha; apply PRA; lia)
G3A G4A Hqm G10A G11A ltac:(rewrite SPA'; lia)
ltac:(replace (sp0 - 2128) with (sp0 + (-266) * 8) by lia; rewrite Z_mod_plus_full;
apply Znumtheory.Zdivide_mod; apply (Z.divide_trans _ 16); [exists 2; reflexivity|]; apply Znumtheory.Zmod_divide; [lia | exact Hal])
ltac:(lia) ATR ltac:(rewrite ETR; apply dm_trace_len1) ltac:(unfold kUnwindMax; lia)
Hrange Hlive TRU) as HIN.
pose proof (dm_malloc_apost (as_universe B) S n TRACE (am_universe B ly S _ (proj1 HAR)) (am_wf B ly S _ (proj1 HAR)) Hreg Hrange Hlive TRA) as HPB.
pose proof (amreal_apost tfibsegs _ _ W _ _ HPB HIN) as HIN2. clear HIN.
rewrite AShape. apply SRr_ret. rewrite <- ETR.
change (mkCfg (mkst (ms_regs msA) (Z_to_bv 64 DM_ASAN) (ms_mem msA) (seg_rom tfibsegs)) mdA) with (cfg_at tfibsegs PC_asan_malloc (ms_regs msA) (ms_mem msA) mdA).
apply (dm_amreal_then_SRr _ W _ _ _ HIN2).
(* ---- after asan_malloc: the epilogue ---- *)
intros r W4 c4 [HB (ly' & regs'' & mem'' & md'' & -> & (HAR'' & Hle & Hwle & Hrp & Hio & Hfr & Hp) & H10 & Hqt)].
pose proof Hle as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
assert (STK : forall a, ly_stk_lo ly <= a < ly_stk_hi ly ->
~ (fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)).
{ intros a Ha [Hnn Hin]. pose proof (dm_blocks_below B LAWS ly' (snd r) W4 mem'' md'' (fst r) n HAR'' (HB Hnn)) as X.
rewrite Elo in X. lia. }
assert (VIEW : forall a, sp0 - 2128 <= a < sp0 -> aview tfibsegs (w_H W4) mem'' a = aview tfibsegs Hd (ms_mem msA) a).
{ intros a Ha. apply Hfr; [lia | exact (al_stack _ _ LAWS ly S W (ms_mem msA) mdA a HARA ltac:(lia))
| apply (al_stack _ _ LAWS ly' (snd r) W4 mem'' md'' a HAR''); rewrite Elo, Ehi; lia
| unfold ascratch; rewrite (ts_errno B TB), SPA'; unfold TFIB_ERRNO, MALLOC_ASAN_STK; intros [X|X]; lia
| apply STK; lia]. }
assert (PR4 : forall a, sp0 - 2128 <= a < sp0 -> apresent (w_H W4) mem'' a).
{ intros a Ha. apply (dm_apresent_hi Hd (w_H W4) (ms_mem msA) mem'' a); [unfold TFIB_IMG_END; lia | apply VIEW; exact Ha | apply PRA; lia]. }
unfold cfg_at, raZ. rewrite (dm_reg_lit Hd E1 DM_A msA 1%bv DM_RET2 HSA AR1), unsigned_lit_small by (unfold DM_RET2; lia).
pose proof (st_ok_after_call tfibsegs DM_HAV2 E1 DM_A (restrict Hd msA) regs'' (mrestrict (w_H W4) mem'') (ss_mem DM_A) DM_RET2 HSA ARV
(proj1 dm_a_atoms) (proj1 (proj2 dm_a_atoms)) (proj1 (proj2 (proj2 dm_a_atoms))) (proj2 (proj2 (proj2 dm_a_atoms)))
(submem_refl _) AR1 ltac:(intros q Hq; exact (Hrp q Hq))) as HS2.
lazymatch type of HS2 with ?P -> _ => assert (KEPT : P) end.
{ rewrite dm_a_mem_eq. apply Forall_cons; [| apply Forall_nil].
apply (dm_kept_of_view E1 Hd (w_H W4) (ms_mem msA) mem'' 2 (- 64) 0 (- 64) 0 _ sp0 E12).
- intros a Ha. apply VIEW. lia.
- intros a Ha. split; [unfold TFIB_IMG_END; lia | apply PR4; lia]. }
specialize (HS2 KEPT). clear KEPT. rewrite dm_2_eq in HS2. rewrite <- (restrict_mkst_fx (w_H W4)) in HS2.
set (E2 := havoc E1 DM_HAV2 (map (getr regs'') CLOB)) in *.
assert (E2o : forall k, (k < 64)%nat -> ew E2 k = ew EE k).
{ intros k Hk. transitivity (ew E1 k); [exact (ew_havoc_old E1 DM_HAV2 (map (getr regs'') CLOB) k ltac:(unfold DM_HAV2; lia)) | apply E1o; exact Hk]. }
assert (E22 : bv_unsigned (ew E2 2) = sp0) by (rewrite (E2o 2%nat ltac:(lia)); exact EE2).
eapply SRr_bind; [exact (dm_phase W4 E2 DM_2 DM_R (mkst regs'' (Z_to_bv 64 DM_RET2) mem'' (seg_rom tfibsegs)) md'' DM_EXIT HS2 dm_run_r)|].
cbv beta. intros W5 c5 _ (-> & msR & matR & -> & HSR & HFR & _).
cbn [ms_mem mkst] in HFR.
assert (MEQR : forall x : word, ~ (sp0 - 64 <= bv_unsigned x < sp0) -> ms_mem msR x = mem'' x).
{ intros x Hx. apply HFR. intros Hin. apply Hx.
pose proof (in_wrange_single_b E2 (ss_mem DM_2) (bv_unsigned x) 2 (- 64) 0 sp0 dm_win_2 E22 Hin). lia. }
pose proof dm_r_shape as (RPC & RRV & RM & RR1 & _).
apply (SRr_ret_at tfibsegs tfibtbl_rtA tfibtbl_rtA_ok AF0x.Hwx_tfa W4 E2 DM_R msR _ _ HSR RRV); [rewrite RPC; exact dm_ret_word|].
intros matF. rewrite wvb_collapse.
assert (GR : forall (q : bv 5) k, Z.of_nat k = bv_unsigned q -> (k < 32)%nat -> sr_get (ss_regs DM_R) q = SOff k 0 ->
getr (ms_regs msR) q = getr regs q).
{ intros q k Hk Hk32 Hq. rewrite (dm_reg_atom (w_H W4) E2 DM_R msR q k HSR Hq), (E2o k ltac:(lia)). exact (EEr k q Hk). }
assert (PRR : forall a, sp0 - 64 <= a < sp0 -> apresent (w_H W4) (ms_mem msR) a).
{ intros a Ha. apply (AF0x.st_ok_window_apresent (w_H W4) E2 DM_R msR 0 dm_a_r0 a HSR dm_r_mem0); [| unfold TFIB_IMG_END; lia].
rewrite (proj1 dm_a_r0_win), (proj1 (proj2 dm_a_r0_win)), (proj2 (proj2 dm_a_r0_win)). cbn [base_val]. rewrite E22. lia. }
exists ly', (ms_regs msR), (ms_mem msR), (with_vm_backing (m_vm_lazy md'') matF md'').
split.
{ unfold cfg_at. f_equal. f_equal. rewrite (GR 1%bv 1%nat eq_refl ltac:(apply Nat.ltb_lt; reflexivity) RR1).
unfold YK0s.ret_ok in Hret. rewrite Hret. unfold w64, raZ. symmetry. apply Z_to_bv_bv_unsigned. }
split; [|split].
- split.
{ destruct (same_but_materialized_frame md'' _ (with_vm_backing_same md'' matF)) as (_ & V1m & V2m & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V3m).
apply (al_frame _ _ LAWS ly' (snd r) W4 mem'' md'' (ms_mem msR) _ HAR'').
- intros a Ha Ho. apply aview_same. apply MEQR. rewrite unsigned_lit_small by lia. intros Hs.
exact (al_stack _ _ LAWS ly' (snd r) W4 mem'' md'' a HAR'' ltac:(rewrite Elo, Ehi; lia) Ho).
- intros a Hv. rewrite (AE2y.aview_mod _ (ms_mem msR) a). rewrite (AE2y.aview_mod _ mem'' a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 64)) as [L1|L1];
[rewrite (aview_same (w_H W4) mem'' (ms_mem msR) a'); [exact Hv | apply MEQR; rewrite unsigned_lit_small by lia; lia]|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply aview_some_of_apresent; apply PRR; lia|].
rewrite (aview_same (w_H W4) mem'' (ms_mem msR) a'); [exact Hv | apply MEQR; rewrite unsigned_lit_small by lia; lia].
- exact V1m.
- exact V2m.
- exact V3m.
- exact (AE2y.hs_kept_win (w_H W4) mem'' mem'' (ms_mem msR) (sp0 - 64) sp0 (sp0 - 64) sp0 MEQR (fun a Ha => PR4 a ltac:(lia)) ltac:(lia) ltac:(lia)). }
split; [exact Hle|]. split; [exact Hwle|].
split.
{ intros q Hq. unfold acallee_saved in Hq.
assert (Q : q = 2 \/ q = 3 \/ q = 4 \/ q = 8 \/ q = 9 \/ q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
destruct Q as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
lazymatch goal with |- getr _ (Z_to_bv 5 ?z) = _ =>
apply (GR (Z_to_bv 5 z) (Z.to_nat z) ltac:(vm_compute; reflexivity) ltac:(apply Nat.ltb_lt; reflexivity)); vm_compute; reflexivity end. }
split.
{ apply (dm_same_io_trans md md'' _); [| exact (dm_same_io_sbm md'' _ (with_vm_backing_same md'' matF))].
exact (dm_same_io_trans md mdA md'' (dm_same_io_sbm md mdA SBMA) Hio). }
split.
{ intros a Ha Ho Ho' Hs HE.
assert (Hout : ~ (sp0 - 14208 <= a < sp0)) by (intros X; apply Hs; left; change (spZ regs) with sp0; unfold MALLOC_IN_STK; lia).
rewrite (aview_same (w_H W4) mem'' (ms_mem msR) a) by (apply MEQR; rewrite unsigned_lit_small by lia; lia).
rewrite (Hfr a Ha Ho Ho'); [ | | exact HE].
- apply aview_same. apply MEQA0. rewrite unsigned_lit_small by lia. exact Hout.
- unfold ascratch. rewrite SPA'. intros [X|X]; apply Hs; [left | right; exact X]. change (spZ regs) with sp0.
unfold MALLOC_ASAN_STK in X. unfold MALLOC_IN_STK. lia. }
intros a Ha. change (spZ regs) with sp0 in Ha. unfold MALLOC_IN_STK in Ha.
destruct (Z_lt_le_dec a (sp0 - 64)) as [L1|L1]; [|apply PRR; lia].
apply (apresent_same (w_H W4) mem'' (ms_mem msR) a); [apply MEQR; rewrite unsigned_lit_small by lia; lia|].
destruct (Z_lt_le_dec a (sp0 - 2128)) as [L2|L2]; [|apply PR4; lia].
apply Hp. rewrite SPA'. unfold MALLOC_ASAN_STK. lia.
- pose proof dm_r_shape as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R10).
rewrite (dm_reg_atom (w_H W4) E2 DM_R msR 10%bv 100 HSR R10).
exact (eq_trans (ew_havoc_new E1 DM_HAV2 (map (getr regs'') CLOB) 4 (ew E1 100) ltac:(rewrite length_map; apply Nat.ltb_lt; reflexivity)) H10).
- exact Hqt.
Qed.

End b.
