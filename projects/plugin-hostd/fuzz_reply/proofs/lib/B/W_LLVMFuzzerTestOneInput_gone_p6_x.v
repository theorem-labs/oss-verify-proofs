(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC twin of ARM_gone's phase p6 on image B (lib/B/W_LLVMFuzzerTestOneInput_gone_p6.v,
   a Theorem Labs lane's, fee5272ac13 / 4118c28f01e: check_shape_done, the fake frame's re-poison and the latch, GCSD to
   INV_K), for the conversion of ARM_gone to the cut invariants of lib/B/W_LLVMFuzzerTestOneInput_cut_x.v.
   _gone_p6.v is not edited.
   - CITED from _gone_p6.v: its AR-free names (the run states, g6_fp_low and its lemmas, the kept lemmas, ...), with the
     Section variables they were generalized over;
   - RESTATED over ARx at the ghost list []: B's Section g6c, the walk of check_shape_done with the kept post
     (g6_csdk_spec_x, g6_csd_entry_x, g6_pb_csdk_x; W1Verify's check_bounded conversion: the callee's journal
     W_journal_x's gx form at G = [], post cut_x's aleafx_post_x); and, merged per item with SmallX's image-A twin
     lib/A/W_LLVMFuzzerTestOneInput_gone_p6_x.v (95a5de32ab2), the transport kit g6k (g6_blk_x .. g6_amodel_kept_x) and
     the phase lemma gp6_csd_latch_x (its end state is cut_x's INV_K_x).
   Section hypotheses beyond cut_x's header: _gone.v's TL verbatim, BLKN and HPST (the generic relation's facts, as on
   image A).  Every ghost list is [] (cut_x's HP0). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface YCe5x YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_kit_xb W_journal_x W_frame_x W_contract_x W_sites_x W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_img_x.
(* W_LLVMFuzzerTestOneInput_gone_p6.v's own imports, AFTER the generic kit's: the converted proofs see the names they were written against *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require ListRep RelayRunT drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone_tk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base_x W_LLVMFuzzerTestOneInput_gone_tk_x W_LLVMFuzzerTestOneInput_gone_p6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* the zify flag as W_LLVMFuzzerTestOneInput_gone_p6.v's proofs see it (true: its imports' last setting), whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* @@ B-ONLY-HDR Local_Notation LLVMF_STK *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* ================================================================== check_shape_done, with the kept clause *)
(* @@ SECTION g6c *)
Section g6c.
(* @@ MERGED Context ctx:fx *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* @@ B-ONLY-HDR #[local]_Notation SEGS *)
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PB_fr).
(* @@ MERGED #[local]_Notation VAL *)
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
(* @@ MERGED #[local]_Notation BASE *)
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* @@ MERGED Variable B *)
Variable B : asyms.
(* @@ AX-ONLY Variable ARx *)
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* @@ AX-ONLY Context ctx:hl *)
Context {hl : Z}.
(* @@ RESOLVED Hypothesis LAWS *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* OWED: kit _x twin of al_blocks' last conjunct (AR's 0 <= n < MALLOC_MAX, YG0d.v:441; ARx_blocks_law has no size
   conjunct).  The text is W_kit_x.v's BLKN (_gone_tk_x.v's). *)
(* @@ RESTATED-LOCAL Let RUN *)
(* the callee's own journal is W_journal_x's gx form at G = [] (W1Verify's check_bounded conversion) *)
Let HG0 : gx_ok SEGS B [] := gx_ok_nil SEGS B.
Let RUN := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS [] HG0 0 [].
(* @@ RESTATED-LOCAL Let BR *)
Let BR := paj_branch (PI := PB_fr).
(* @@ B-ONLY-HDR Let RET *)
Let RET := paj_ret_at (PL := PL_fr) (PI := PB_fr).
(* W_contract.v's csd_spec with aleafx_post for aleaf_post: the same premises, the post with the kept clause *)
(* @@ CONVERTED Definition g6_csdk_spec *)
Definition g6_csdk_spec_x (pc : Z) : Prop :=
  forall W ly S regs mem md ch n,
  afn_pre_x SEGS B ARx CSD_STK ly S [] W regs mem md ch ->
  getr regs 10 = w64 n -> 0 <= n < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_nout) 8 n ->
  SRr SEGS W (cfg_at SEGS pc regs mem md) (aleafx_post_x B PST ARx CSD_STK regs ly S [] W mem md (fun a => a = w64 n)).
(* lib/B/W_check_shape_done.v's entry state, verbatim but for the names *)
(* @@ CONVERTED Lemma g6_csd_entry *)
Lemma g6_csd_entry_x : forall W ly S regs mem md ch n,
afn_pre_x SEGS B ARx CSD_STK ly S [] W regs mem md ch ->
getr regs 10 = w64 n -> 0 <= n < 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_nout) 8 n ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (g6_csd_extra n))) ss_g6csd
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_fr_check_shape_done)) mem (seg_rom SEGS)))
/\ sh_ok SEGS g6_Bx g6_csd_SH (Eimg (Ereg regs (g6_csd_extra n))) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md ch n HPRE H10 Rn Mn.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CSD_STK = 16) by reflexivity.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (g6_csd_extra n))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Eno : ew E A_g_nout = Z_to_bv 64 (VAL A_g_nout)) by (subst E; apply Eimg_img; unfold A_g_nout, A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HnoR. change (A_OBJ 12) with A_g_nout in HnoR.
pose proof (pa_val_range A_g_nout) as HnoV.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_g6csd. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold g6_csd_regions, stack_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB A_g_nout (VAL A_g_nout) Eno) by (pose proof (pa_val_range A_g_nout); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL A_g_nout) 0 8 (SOff 32 0) n);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact Mn.
+ apply pairwise_disjoint_of_extents. unfold g6_csd_regions, stack_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB A_g_nout (VAL A_g_nout) Eno) by (pose proof (pa_val_range A_g_nout); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HnoR. clear.
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [g6_csd_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, E33, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 Rn. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, g6_csd_SH. constructor.
Qed.
(* the walk's regions: only the stack region has a writable window, so a byte outside the frame is outside
   every region's window (A's g6_nowr) *)
(* @@ B-ONLY-HDR Ltac g6_nowr *)
Ltac g6_nowr :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr); vm_compute in Hin;
repeat (destruct Hin as [<- | Hin];
 [cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
  repeat match goal with Hu : bv_unsigned (ew _ 2) = _ |- _ => rewrite Hu in Hr end;
  first [lia | match goal with Hno : ~ _ |- _ => apply Hno; unfold CSD_STK in *; lia end] |]);
destruct Hin.
(* @@ CONVERTED Theorem g6_pb_csdk *)
Theorem g6_pb_csdk_x : g6_csdk_spec_x (BASE + AF_fr_check_shape_done).
Proof.
intros W ly S regs mem md ch n HPRE H10 Rn Mn.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (g6_csd_entry_x W ly S regs mem md ch n HPRE H10 Rn Mn) as [HS SHOK].
assert (HJ : ajournal_gx_x SEGS B PST ARx [] 0 [] CSD_STK (spZ regs) [] ly S [] W mem md [] ly S [] W mem md 0)
  by (apply ajournal_gx_nil_x; exact (ajournal_x_init SEGS B PST ARx CSD_STK [] ly S [] W regs mem md ch HPRE)).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
remember (Eimg (Ereg regs (g6_csd_extra n))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (g6_csd_extra n)) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_fr_check_shape_done)) with (Z_to_bv 64 (BASE + AF_fr_check_shape_done)).
paj_run_tok_x RUN HS HJ SHOK g6_Bspan. { apply awr_ok_x_of0; awr_ok_tac. exact Usp. }
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CSD_STK <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a Ha Hno; apply (aview_kept_out E _ (w_H W) mem (ms_mem ms) HFr a Ha); g6_nowr).
psrr_branch_tok RUN BR HS SHOK g6_Bspan.
-
(* the abort arm: a0 <> g_nout, which the premise refutes *)
exfalso. rewrite branch_ne_U, (U_atom E 10 n E10), (U_atom E 32 n E32) in Hc by lia.
cbn [negb] in Hc. apply (proj1 (Bool.negb_true_iff _)) in Hc. apply (proj1 (Z.eqb_neq _ _)) in Hc.
exact (Hc eq_refl).
-
paj_run_tok_x RUN HS HJ SHOK g6_Bspan. { apply awr_ok_x_of0; awr_ok_tac. exact Usp. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CSD_STK <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a)
  by (intros a Ha Hno;
      match goal with H : frame_of ?Ev _ (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)) |- _ =>
        rewrite (aview_kept_out Ev _ (w_H W) (ms_mem ms) (ms_mem ms0) H a Ha) by g6_nowr end;
      apply KEEP0; assumption).
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold aleafx_post_x.
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [|split; [|split; [|split]]].
+ cbn [ms_mem]. apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs). exact HJ.
+ eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (g6_csd_extra n) HS); [exact HAE | vm_compute; reflexivity].
+ intros a Ha. cbn [ms_mem]. pres_chain.
+ cbn [ms_mem]. intros a Ha Hno. split; [exact (KEEP1 a Ha Hno)|].
  apply writable_kept. intros Hp. pres_chain.
+ cbn [ms_regs]. rewrite R10, E10. reflexivity.
Qed.
(* @@ END g6c *)
End g6c.

(* ================================================================== the transport kit
   The base's _gone_tk.v (B's latch kit, gk_), with each range of a cut fact also wholly below kLowMemEnd or wholly at
   or above kHighMemBeg (g6_lo, A's g6k): every shadow byte lies in [kLowMemEnd, kHighMemBeg), so the kept bytes the
   kit asks for (g6_app) exclude the fake frame's shadow, which the re-poison writes. *)
(* @@ SECTION g6k *)
Section g6k.
(* @@ MERGED Context ctx:fx *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* @@ MERGED Local_Notation segs *)
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
(* @@ MERGED Variable B *)
Variable B : asyms.
(* @@ AX-ONLY Variable PST *)
Variable PST : list (Z * Z).
(* @@ AX-ONLY Variable ARx *)
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
(* @@ AX-ONLY Context ctx:hl *)
Context {hl : Z}.
(* @@ MERGED Hypothesis LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx hl.
(* OWED: kit _x twin of al_blocks' last conjunct (AR's 0 <= n < MALLOC_MAX, YG0d.v:441; ARx_blocks_law has no size
   conjunct).  The text is W_kit_x.v's BLKN (_gone_tk_x.v's). *)
(* @@ UNANCHORED Hypothesis BLKN *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* @@ UNANCHORED Local_Notation AR0 *)
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
(* _gone_p6.v's AR-free names that take this Section's B *)
(* @@ B-ONLY-HDR Ltac g6_low *)
Ltac g6_low :=
  cbn [fst snd gfp]; unfold g6_CEIL8, kLowMemEnd, kHighMemBeg in *;
  cbn [fr_globals_b rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *;
  pose proof g6_ceil_lo; lia.
(* @@ MERGED Lemma g6_blk *)
Lemma g6_blk_x : forall ly S (W : world segs) mem md p n,
  AR0 ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n /\
  (p + req_size n <= kLowMemEnd \/ kHighMemBeg <= p).
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (al0_blocks B ARx LAWS BLKN ly S W mem md p n HAR Hin) as (_ & H1 & H2 & Happ & _ & _ & H3).
  pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2].
  unfold in_app, kLowShadowBeg in Happ.
  split; [lia|]. split; [lia|]. split; [lia|]. unfold kLowMemEnd. lia.
Qed.

(* ---- struct list ---- *)
(* @@ RESOLVED Lemma g6_alist *)
Lemma g6_alist_x : forall ly S (W : world segs) mem md LA l lines,
  AR0 ly S W mem md -> alist_at B ly S W mem LA l lines -> 0 <= LA -> LA + 16 <= kLowMemEnd ->
  g6_fp_low (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HL0 HL1.
  pose proof g6_ceil_lo as HCL.
  assert (HREC : g6_fp_low (map (fun r => gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0]))) (hl_recs l))
                 /\ (forall b, In b (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l)) ->
                       In b (ablocks B ly S))).
  { rewrite Forall_forall in H9. split.
    - rewrite g6_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (x & <- & Hx).
      destruct (H9 x Hx) as (K1 & _). destruct (g6_blk_x ly S W mem md _ _ HAR K1) as (P1 & P2 & P3 & P4).
      unfold g6_lo. cbn [gfp fst snd]. rewrite gk_bzs_len, length_app. cbn [length].
      unfold g6_CEIL8 in *. lia.
    - intros b Hb. apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (H9 x Hx)). }
  destruct HREC as [HR1 HR2].
  unfold alist_fp, alist_blks. split.
  - apply g6_fp_low_cons; [cbn; lia | cbn; unfold g6_CEIL8, kLowMemEnd in *; lia | cbn; left; lia |].
    apply g6_fp_low_app; [|exact HR1].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply g6_fp_low_nil|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    destruct (g6_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4).
    apply g6_fp_low_cons; [cbn; lia | | | apply g6_fp_low_nil];
      cbn [gfp fst snd]; rewrite gk_bzs_len, length_app, gk_concat_len;
      unfold hl_n in Hj; unfold AREC in *; unfold g6_CEIL8 in *; lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [|exact (HR2 b Hb)].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|].
    destruct Hb as [<- | []]. exact Hin.
Qed.
(* ---- struct source ---- *)
(* @@ RESOLVED Lemma g6_asrc *)
Lemma g6_asrc_x : forall ly S (W : world segs) mem md HA h,
  AR0 ly S W mem md -> asrc_at B ly S W mem HA h -> 0 <= HA -> HA + ASRC <= kLowMemEnd ->
  g6_fp_low (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md HA h HAR HS HL0 HL1.
  pose proof g6_ceil_lo as HCL.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  destruct (g6_alist_x ly S W mem md (HA + 16) (hs_pending h) false HAR Hpend ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [A1 A2].
  destruct (g6_alist_x ly S W mem md (HA + 64) (hs_expected h) true HAR Hexp ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [E1 E2].
  destruct (g6_alist_x ly S W mem md (HA + 80) (hs_held h) true HAR Hheld ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [H1 H2].
  destruct (g6_blk_x ly S W mem md _ _ HAR Hpb) as (P1 & P2 & P3 & P4).
  unfold asrc_fp, asrc_blks. split.
  - apply g6_fp_low_cons; [cbn; lia | cbn; unfold ASRC, g6_CEIL8, kLowMemEnd in *; lia | cbn; left; exact HL1 |].
    apply g6_fp_low_cons.
    + cbn [gfp fst]. lia.
    + cbn [gfp snd]. rewrite gk_bzs_len, Hpj. unfold APARTIAL, g6_CEIL8 in *. lia.
    + cbn [gfp fst snd]. rewrite gk_bzs_len, Hpj. unfold APARTIAL in *. lia.
    + apply g6_fp_low_app; [exact A1|]. apply g6_fp_low_app; [exact E1 | exact H1].
  - intros b [<- | Hb]; [exact Hpb|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (A2 b Hb)|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (E2 b Hb) | exact (H2 b Hb)].
Qed.

(* ---- one source_t of the relay's table ---- *)
(* @@ RESOLVED Lemma g6_aentry *)
Lemma g6_aentry_x : forall ly S (W : world segs) mem md e,
  AR0 ly S W mem md -> aentry_ok B ly S W mem e ->
  g6_fp_low (aentry_fp e) /\ (forall b, In b (aentry_blks e) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md e HAR (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  pose proof g6_ceil_lo as HCL.
  assert (HK : g6_fp_low (map (fun k => gfp (gestures_end_b_c.key_addr k)
                  (bzs (gestures_end_b_c.key_text k ++ [Z_to_bv 8 0]))) (re_keys e))
               /\ (forall b, In b (map (fun k => (gestures_end_b_c.key_addr k,
                     Z.of_nat (length (gestures_end_b_c.key_text k)) + 1)) (re_keys e)) ->
                     In b (ablocks B ly S))).
  { rewrite Forall_forall in K15. split.
    - rewrite g6_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (k & <- & Hk).
      destruct (K15 k Hk) as (M1 & _).
      destruct (g6_blk_x ly S W mem md _ _ HAR M1) as (P1 & P2 & P3 & P4).
      unfold g6_lo. cbn [gfp fst snd]. rewrite gk_bzs_len, length_app. cbn [length].
      unfold g6_CEIL8 in *. lia.
    - intros b Hb. apply in_map_iff in Hb as (k & <- & Hk). exact (proj1 (K15 k Hk)). }
  destruct HK as [HK1 HK2]. unfold aentry_fp, aentry_blks. split.
  - apply g6_fp_low_app.
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply g6_fp_low_nil|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
      destruct (g6_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4).
      apply g6_fp_low_cons; [cbn; lia | | | apply g6_fp_low_nil];
        cbn [gfp fst snd]; rewrite gk_bzs_len, length_app; unfold g6_CEIL8 in *; lia.
    + apply g6_fp_low_cons; [| | |exact HK1].
      * cbn [gfp fst]. destruct K12 as [(Hz & _) | (Hz & Hin & _)]; [lia|].
        destruct (g6_blk_x ly S W mem md _ _ HAR Hin) as (P1 & _). lia.
      * cbn [gfp snd]. rewrite gk_bzs_len, gk_key_ptrs_len.
        destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
        { rewrite Hz, Hks. cbn [length]. unfold g6_CEIL8. lia. }
        destruct (g6_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4).
        unfold re_nheld in Hk1. unfold g6_CEIL8 in *. lia.
      * cbn [gfp fst snd]. rewrite gk_bzs_len, gk_key_ptrs_len.
        destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
        { rewrite Hz, Hks. cbn [length]. left. unfold kLowMemEnd. lia. }
        destruct (g6_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4).
        unfold re_nheld in Hk1. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hb|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + apply in_app_or in Hb as [Hb | Hb]; [|exact (HK2 b Hb)].
      destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [destruct Hb|].
      destruct K12 as [(Hz0 & _) | (_ & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- the relay's table, at fuzz_reply.asan-ubsan's globals (fr_globals_b, the cut's fr_RG) ---- *)
(* @@ RESOLVED Lemma g6_arelay *)
Lemma g6_arelay_x : forall ly S (W : world segs) mem md G es,
  AR0 ly S W mem md -> arelay_at B fr_globals_b ly S W mem G es ->
  g6_fp_low (arelay_fp fr_globals_b G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md G es HAR (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
  destruct (g6_blk_x ly S W mem md _ _ HAR R8) as (P1 & P2 & P3 & P4).
  assert (HE : g6_fp_low (concat (map aentry_fp es))
               /\ (forall b, In b (concat (map aentry_blks es)) -> In b (ablocks B ly S))).
  { rewrite Forall_forall in R10. split.
    - rewrite g6_fp_low_forall. intros r Hr. apply in_concat in Hr as (f & Hf & Hr).
      apply in_map_iff in Hf as (e & <- & He).
      destruct (g6_aentry_x ly S W mem md e HAR (R10 e He)) as [F1 _].
      rewrite g6_fp_low_forall in F1. exact (F1 r Hr).
    - intros b Hb. apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
      destruct (g6_aentry_x ly S W mem md e HAR (R10 e He)) as [_ F2]. exact (F2 b Hb). }
  destruct HE as [HE1 HE2]. unfold arelay_fp, arelay_blks. split.
  - apply g6_fp_low_cons; [g6_low | g6_low | g6_low |].
    apply g6_fp_low_cons; [g6_low | g6_low | g6_low |].
    apply g6_fp_low_cons; [g6_low | g6_low | g6_low |].
    apply g6_fp_low_cons; [cbn; lia | cbn [fst snd]; unfold ATABLE, g6_CEIL8 in *; lia
                          | cbn [fst snd]; unfold ATABLE in *; lia | exact HE1].
  - intros b [<- | Hb]; [exact R8 | exact (HE2 b Hb)].
Qed.

(* ---- the controller's stream ---- *)
(* @@ RESOLVED Lemma g6_aout *)
Lemma g6_aout_x : forall ly S (W : world segs) mem md c O mx no cap out,
  AR0 ly S W mem md -> aout_at B fr_globals_b ly S W mem c O mx no cap out ->
  0 <= as_errno B -> as_errno B + 4 <= kLowMemEnd ->
  g6_fp_low (aout_fp B fr_globals_b cap out) /\ (forall b, In b (aout_blks cap out) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md c O mx no cap out HAR HO HE0 HE1.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & Hblk).
  unfold aout_fp, aout_blks. split.
  - do 9 (apply g6_fp_low_cons; [g6_low | g6_low | g6_low |]).
    destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [apply g6_fp_low_nil|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & junk & Hj & Hg)]; [lia|].
    destruct (g6_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4).
    apply g6_fp_low_cons; [cbn; lia | cbn; unfold g6_CEIL8 in *; lia | cbn; lia | apply g6_fp_low_nil].
  - intros b Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.
(* @@ RESOLVED Lemma g6_amodel_kept *)
Lemma g6_amodel_kept_x : forall ly S (W : world segs) mem md (W' : world segs) mem' m,
  AR0 ly S W mem md -> amodel_at B ly S W mem m ->
  0 <= as_errno B -> as_errno B + 4 <= kLowMemEnd ->
  (forall a, g6_app a -> abyte_kept W mem W' mem' a) ->
  amodel_at B ly S W' mem' m.
Proof.
  intros ly S W mem md W' mem' m HAR (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10) HE0 HE1 KEEP.
  split; [exact M1|]. split.
  { intros i Hi. specialize (M2 i Hi). unfold aslot in *.
    assert (HB0 : 0 <= rg_s fr_RG + ASRC * Z.of_nat i) by (unfold fr_RG; cbn; unfold ASRC; lia).
    assert (HB1 : rg_s fr_RG + ASRC * Z.of_nat i + ASRC <= kLowMemEnd)
      by (unfold fr_RG, kLowMemEnd; cbn; unfold ASRC; lia).
    destruct (nth i (lm_hs m) None) as [h|].
    - destruct (g6_asrc_x ly S W mem md _ h HAR M2 HB0 HB1) as [F1 F2].
      exact (asrc_at_kept B ly S W mem ly S W' mem' _ h M2 (g6_akept_of_low _ _ _ _ _ KEEP F1) F2).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply (g6_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx.
        apply (g6_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia. }
  split.
  { destruct (g6_arelay_x ly S W mem md (lm_G m) (lm_es m) HAR M3) as [F1 F2].
    exact (arelay_at_kept B fr_RG ly S W mem ly S W' mem' _ _ M3
             (g6_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { destruct (g6_aout_x ly S W mem md _ _ _ _ _ _ HAR M4 HE0 HE1) as [F1 F2].
    exact (aout_at_kept B fr_RG ly S W mem ly S W' mem' _ _ _ _ _ _ M4
             (g6_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { apply (agone_at_kept fr_RG W mem W' mem' _ M5).
    apply g6_akept_rng; [exact KEEP | cbn; lia | unfold kLowMemEnd; cbn; lia]. }
  split.
  { apply (alock_at_kept fr_RG W mem W' mem' _ M6).
    apply g6_akept_rng; [exact KEEP | cbn; lia | unfold kLowMemEnd; cbn; lia]. }
  split.
  { apply (awake_at_kept fr_RG W mem W' mem' M7).
    apply g6_akept_rng; [exact KEEP | cbn; lia | unfold kLowMemEnd; cbn; lia]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. apply KEEP.
    unfold g6_app, AG_NFD, g6_CEIL8, kLowMemEnd in *. pose proof g6_ceil_lo. cbn in Hx. lia. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply KEEP.
    unfold g6_app, AG_NFD, g6_CEIL8, kLowMemEnd in *. pose proof g6_ceil_lo. lia. }
  destruct M10 as (M10 & M11 & (lst & M12) & M13).
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. apply KEEP.
    unfold g6_app, AG_THREAD_UP, g6_CEIL8, kLowMemEnd in *. pose proof g6_ceil_lo. cbn in Hx. lia. }
  split.
  { exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx. apply KEEP.
    unfold g6_app, AG_LISTEN, g6_CEIL8, kLowMemEnd in *. pose proof g6_ceil_lo. cbn in Hx. lia. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply KEEP.
  unfold g6_app, AG_LISTEN, g6_CEIL8, kLowMemEnd in *. pose proof g6_ceil_lo. lia.
Qed.
(* ---- the input block, the read-only image, the jump table ---- *)
(* @@ RESOLVED Lemma g6_ainput_kept *)
Lemma g6_ainput_kept_x : forall cx ly S (W : world segs) mem md (W' : world segs) mem',
  AR0 ly S W mem md -> ainput_at B cx ly S W mem ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  (forall a, g6_app a -> abyte_kept W mem W' mem' a) ->
  ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S W mem md W' mem' HAR (I1 & I2) Hlen KEEP.
  split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
  intros x Hx. rewrite length_map in Hx. rewrite Hlen in Hx. apply KEEP.
  destruct I1 as [(Hn & Hp) | (Hn & Hin)]; [lia|].
  destruct (g6_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4).
  unfold g6_app, g6_CEIL8. lia.
Qed.
(* @@ END g6k *)
End g6k.

(* ================================================================== the phase *)
(* @@ SECTION gp6 *)
Section gp6.
(* @@ MERGED Context ctx:fx *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* @@ MERGED #[local]_Notation segs *)
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
(* @@ MERGED Variable B *)
Variable B : asyms.
(* @@ MERGED Variable MT *)
Variable MT : ameter_ops.
(* @@ MERGED Variables XM_LIB *)
Variables XM_LIB : Z -> Z.
(* @@ MERGED Variables RLO *)
Variables RLO RHI : Z.
(* @@ MERGED Variable fr_live_pre *)
Variable fr_live_pre : astate -> Prop.
(* @@ AX-ONLY Variables LIBROOM *)
Variables LIBROOM NP : astate -> Prop.
(* @@ MERGED Variable G_fr *)
Variable G_fr : list (Z * Z).
(* @@ MERGED Variable fr_FP *)
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
(* @@ MERGED Hypothesis LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx hl.
(* OWED: kit _x twin of al_blocks' last conjunct (AR's 0 <= n < MALLOC_MAX, YG0d.v:441; ARx_blocks_law has no size
   conjunct).  The text is W_kit_x.v's BLKN (_gone_tk_x.v's). *)
(* @@ AX-ONLY Hypothesis HP0 *)
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
(* @@ MERGED Hypothesis HG *)
Hypothesis HG : gx_ok segs B G_fr.
(* @@ AX-ONLY Variable LSx *)
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
(* @@ RESOLVED Variable RINV *)
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* the allocator instance (W_kit.v): its api_env (pal_env) puts errno's 4 bytes below kLowMemEnd *)
(* @@ RESOLVED Hypothesis TL *)
Hypothesis TL : @PALib _ _ PB_fr B.
(* @@ MERGED #[local]_Notation VAL *)
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
(* @@ MERGED #[local]_Notation BASE *)
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).

(* a callee-saved register across the call (the latch's lt_pres) *)
(* @@ RESOLVED Ltac g6_cs *)
Ltac g6_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
(* the registers the cut point names that neither run writes and the call keeps (B: the runs write a0, s4, s7, s8,
   s9, s10) *)
(* @@ UNANCHORED Hypothesis BLKN *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* the image is off PST (add_x's HPST): the callee journal's image clause takes it; trivial at PST = [] *)
(* @@ UNANCHORED Hypothesis HPST *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.
(* @@ UNANCHORED Local_Notation AR0 *)
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
(* @@ UNANCHORED Local_Notation AJ0 *)
Local Notation AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
(* @@ UNANCHORED Local_Notation AJi0 *)
Local Notation AJi0 STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_x segs B PST ARx STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
(* @@ UNANCHORED Local_Notation AFN0 *)
Local Notation AFN0 STK ly S W regs mem md ch := (afn_pre_x segs B ARx STK ly S [] W regs mem md ch).
(* @@ UNANCHORED Local_Notation LFB0 *)
Local Notation LFB0 cx := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx []).
(* a ghost list read off an ARx fact, or off a journal's last state, is [] *)
(* @@ UNANCHORED Ltac hp0a *)
Ltac hp0a H := let E := fresh "EHp" in pose proof (HP0 _ _ _ _ _ _ H) as E;
  lazymatch type of E with ?h = [] => subst h end.
(* @@ UNANCHORED Ltac hp0g *)
Ltac hp0g HJ := let H := fresh "HARg" in
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H; hp0a H; clear H.
(* _gone_p6.v's AR-free definition over this Section's B (_gone_p6.v:527 g6_kcls), cited *)
(* @@ CONFLICT Theorem gp6_csd_latch *)
Theorem gp6_csd_latch_x : forall cx t m mc W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  GCSD_x B NP G_fr fr_FP PST ARx LSx RINV cx t m mc W c ->
  SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx [] t).
Proof.
  intros cx t m mc W c HB HC.
  pose (RUNTOP := SRr_run_to_pi_AJX0_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr).
  destruct HC as (regs & mem & md & ly & S & kk & fpos & -> &
    ((HJ & HGF & HFLAG & S16 & S144 & S88 & HIN & HRV & HJT) & HMOD & HSEP & HNP) &
    HLS & HRI & Hk & Hkq & Ht & S208 & AW192 & S24 & (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4)).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx [(1, fpos)] ly S W mem md kk
    fpos HB HJ eq_refl) as NUMS.
  cbv zeta in NUMS.
  destruct NUMS as (Hsp16 & Hsp0 & HF32 & HFb & HFF4 & HFFc & HFFapp & Hfrs & HAR).
  pose proof HB as (HAI0 & HPRE0).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  assert (HFlo : g6_CEIL8 + 32000 <= lf_F cx) by (unfold g6_CEIL8, LLVMF_STK in *; lia).
  assert (HF46 : 2 ^ 46 <= lf_F cx /\ lf_F cx + 320 <= 2 ^ 47) by (unfold LLVMF_STK in *; lia).
  assert (HFF8 : 0 <= frame_addr ly 1 fpos / 8 /\ frame_addr ly 1 fpos / 8 + 16 <= 2 ^ 44)
    by (split; [apply Z.div_pos; lia | lia]).
  (* at = |O| = g_nout (aout_at), the value check_shape_done compares a0 with *)
  pose proof HMOD as (_ & _ & _ & HOUT & _).
  pose proof HOUT as (_ & _ & Mno & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & Hblk).
  assert (Hn : 0 <= Z.of_nat (length (lm_O mc)) < 2 ^ 64).
  { destruct Hblk as [(Hc0 & _ & Hno) | (Hcp & Hno & Hin & _)]; [lia|].
    destruct (g6_blk_x B ARx LAWS BLKN ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4). lia. }
  assert (Mno' : val_mem segs (mrestrict (w_H W) mem) (VAL A_g_nout) 8 (Z.of_nat (length (lm_O mc)))).
  { replace (VAL A_g_nout) with (rg_nout fr_RG) by (vm_compute; reflexivity). exact Mno. }
  (* in.p = c_p + kq, the value s4 reloads *)
  assert (HP : 0 <= c_p cx + gn_kq cx m < 2 ^ 64).
  { pose proof HIN as ([(Hn0 & Hp0) | (Hn0 & Hin)] & _).
    - rewrite Hp0. unfold YCfn.A_EMPTY. lia.
    - destruct (g6_blk_x B ARx LAWS BLKN ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4). lia. }
  assert (HT : 0 <= t < 2 ^ 64) by (unfold OPS_MAX in *; lia).
  (* ---- 0x84c84-0x84c88: ld a0,208(s1); jal check_shape_done ---- *)
  pose proof (g6_entry1 W regs mem (lf_F cx) (Z.of_nat (length (lm_O mc))) (proj1 HF46) (proj2 HF46) HF32 R2 R9
    S208 Hn) as HS.
  remember (Eimg (Ereg regs (g6_extra1 (Z.of_nat (length (lm_O mc)))))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E32 : ew E 32 = Z_to_bv 64 (Z.of_nat (length (lm_O mc))))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (HAE : env_agree 32 (Ereg regs (g6_extra1 (Z.of_nat (length (lm_O mc))))) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_csd)) with (Z_to_bv 64 (BASE + AF_gn_csd)).
  paj_run_to_sh_x RUNTOP HS HJ AF_fr_check_shape_done.
  { intros a (r & Hin & Hr). vm_compute in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
  lazymatch goal with H : mem_grows _ _ |- _ => rename H into HGR1 end.
  cbn [ms_mem mkst] in HF, HFr, HGR1.
  lazymatch type of HF with frame_of ?E0 ?rs ?m0 ?m1 =>
    pose proof (frame_of_read_only E0 rs m0 m1 ltac:(vm_compute; reflexivity) HF) as Em1 end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ g6_saved HS HAE ltac:(vm_compute; reflexivity)) as KR1.
  cbn [ms_regs restrict] in KR1.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. rewrite E32 in Q10.
  pmkst HS. rewrite Em1 in *.
  clear HF HFr HGR1.
  rename ms into ms1, mat into mat1.
  set (mdc := with_vm_backing (m_vm_lazy md) mat1 md) in *.
  assert (Hsp1 : spZ (ms_regs ms1) = lf_F cx).
  { unfold spZ. rewrite (KR1 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
  pose proof HGF as (HSV & HFW & G32 & G40 & G48 & G56 & G64 & G72 & G80 & G96 & G104 & G120 & G128 & G136 & G152 &
    G184 & GFF0 & GFF8 & GFF16 & GFFW & GSH & GSHW).
  destruct (gn_afn_pre_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx HG LSx RINV cx ly S fpos kk W mem mdc (ms_regs ms1)
    CSD_STK HB HJ HSV Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR1 3%bv ltac:(cbv; tauto)). exact R3. }
  { rewrite (KR1 4%bv ltac:(cbv; tauto)). exact R4. }
  { rewrite (KR1 8%bv ltac:(cbv; tauto)). exact R8. }
  { unfold CSD_STK. lia. }
  { unfold CSD_STK, LLVMF_STK. lia. }
  eapply SRr_bind.
  { exact (g6_pb_csdk_x B PST ARx LAWS W ly S (ms_regs ms1) mem mdc ch (Z.of_nat (length (lm_O mc))) HPREc Q10 Hn Mno'). }
  intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & HPR2 & HK2 & HA02).
  rewrite Hsp1 in HJc, HK2. unfold CSD_STK in HK2.
  (* check_shape_done's journal inside this function's (B's latch walk, lf_seg_latch) *)
  assert (HJc' : AJ0 G_fr 0 [] CSD_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0).
  { refine (ajournal_gx_G_mono_x segs B PST ARx [] G_fr 0 [] CSD_STK (lf_F cx) [] ly S [] W mem mdc [] ly S [] W2 mem2 md2 0 _ HJc).
    intros a Ha. exfalso. exact (inG_nil a Ha). }
  pose proof (ajournal_gx_sub_x segs B PST ARx LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem mdc kk
     CSD_STK (lf_F cx) 0 [] [] [] ly S [] W2 mem2 md2 0 HJ HJc'
     ltac:(unfold CSD_STK, LLVMF_STK in *; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
  cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
  clear HJc HJc'.
  (* the cells the tail reads, kept across the call *)
  assert (KCh : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W2 mem2 a) by (intros a Ha; apply HK2; lia).
  assert (M16 : sv8 W2 mem2 (lf_F cx + 16) (c_p cx + gn_kq cx m))
    by (apply (gk_sv8_kept W W2 mem mem2); [intros x Hx; apply KCh; lia | exact S16]).
  assert (M24 : sv8 W2 mem2 (lf_F cx + 24) HI_G_NOUT)
    by (apply (gk_sv8_kept W W2 mem mem2); [intros x Hx; apply KCh; lia | exact S24]).
  assert (M88 : sv8 W2 mem2 (lf_F cx + 88) t)
    by (apply (gk_sv8_kept W W2 mem mem2); [intros x Hx; apply KCh; lia | exact S88]).
  assert (M96 : sv8 W2 mem2 (lf_F cx + 96) (SB + frame_addr ly 1 fpos / 8))
    by (apply (gk_sv8_kept W W2 mem mem2); [intros x Hx; apply KCh; lia | exact G96]).
  assert (AWsh : awr W2 mem2 (SB + frame_addr ly 1 fpos / 8) 16).
  { apply (akept_awr W mem W2 mem2); [|exact GSHW]. intros x Hx.
    apply HK2; unfold SB, g6_CEIL8 in *; lia. }
  assert (R9b : getr regs2 9 = w64 (lf_F cx)).
  { rewrite (g6_pres (ms_regs ms1) regs2 9%bv HP2 ltac:(g6_cs)). rewrite (KR1 9%bv ltac:(cbv; tauto)). exact R9. }
  (* ---- 0x84c8c-0x84dac: the re-poison of prefix[48], s4, s10, s9, s7, and the jump to the latch ---- *)
  rewrite Q1. change (Z_to_bv 64 (BASE + 10568)) with (Z_to_bv 64 (BASE + AF_g6_ret)).
  pose proof (g6_entry2 W2 regs2 mem2 (lf_F cx) (c_p cx + gn_kq cx m) (frame_addr ly 1 fpos) t
    (proj1 HF46) (proj2 HF46) HF32 R9b ltac:(lia) ltac:(lia) HP HT M16 M24 M88 M96 AWsh) as HS2.
  remember (Eimg (Ereg regs2 (g6_extra2 (c_p cx + gn_kq cx m) (SB + frame_addr ly 1 fpos / 8) t))) as E2 eqn:HE2.
  assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
  assert (E2_32 : ew E2 32 = Z_to_bv 64 (c_p cx + gn_kq cx m))
    by (subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  assert (E2_33 : ew E2 33 = Z_to_bv 64 (SB + frame_addr ly 1 fpos / 8))
    by (subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
  assert (E2_34 : ew E2 34 = Z_to_bv 64 t)
    by (subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
  assert (U2_33 : bv_unsigned (ew E2 33) = SB + frame_addr ly 1 fpos / 8)
    by (rewrite E2_33; apply unsigned_lit_small; unfold SB; lia).
  assert (HAE2 : env_agree 32 (Ereg regs2 (g6_extra2 (c_p cx + gn_kq cx m) (SB + frame_addr ly 1 fpos / 8) t)) E2)
    by (rewrite HE2; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE2.
  paj_run_to_sh_x RUNTOP HS2 HJ2 AF_LLVM_latch.
  { (* the six stores hit the shadow of the fake frame the function owns *)
    intros a (r & Hin & Hr). vm_compute in Hin.
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [lia|].
    rewrite U2_33 in Hr. right; right; right.
    exists 1, fpos. split; [left; reflexivity|]. right. unfold in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd].
    change (fs_frame_bytes 1 / 8) with 16. unfold SB in Hr. lia. }
  lazymatch goal with H : mem_grows _ _ |- _ => rename H into HGR2 end.
  cbn [ms_mem mkst] in HF, HFr, HGR2.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 _ g6_saved HS2 HAE2 ltac:(vm_compute; reflexivity)) as KR2.
  cbn [ms_regs restrict] in KR2.
  prreg HS2 (20%bv : bv 5) Q20. prreg HS2 (23%bv : bv 5) Q23. prreg HS2 (24%bv : bv 5) Q24.
  prreg HS2 (25%bv : bv 5) Q25. prreg HS2 (26%bv : bv 5) Q26.
  rewrite ?E2_32 in Q20. rewrite ?E2_33 in Q24. rewrite ?E2_34 in Q25.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS2 eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
  pmkst HS2.
  (* the six shadow bytes now hold 0xf8, and are still writable *)
  assert (NEW : forall i, 4 <= i < 10 ->
      mbyte segs (arm W2 (ms_mem ms)) (SB + frame_addr ly 1 fpos / 8 + i) = Some (Z_to_bv 8 248) /\
      writable_at segs (arm W2 (ms_mem ms)) (SB + frame_addr ly 1 fpos / 8 + i)).
  { destruct RG1 as (_ & _ & RW & RC).
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in RW, RC. rewrite U2_33 in RW, RC.
    intros i Hi. split; [|exact (RW i Hi)].
    rewrite Forall_forall in RC.
    assert (Hi6 : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) by lia.
    unfold arm.
    destruct Hi6 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      (lazymatch goal with |- mbyte _ _ (_ + ?o) = _ =>
         destruct (RC (YP09.mkChunk o (CVal 1 (SLit 18446744073709551608)))
                    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) 0 ltac:(cbn; lia))
           as (bb & Hcb & Hmb) end;
       cbn [YP09.c_off YP09.c_val YP09.cbyte sv_denot] in Hcb, Hmb; rewrite Z.add_0_r in Hmb; rewrite Hmb;
       injection Hcb as <-; f_equal; apply bv_eq; vm_compute; reflexivity). }
  (* every other byte is kept from the cut point: the call keeps all but its 16-byte frame below F, the
     re-poison writes only the six shadow bytes *)
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx - 16 <= a < lf_F cx) ->
      ~ (SB + frame_addr ly 1 fpos / 8 + 4 <= a < SB + frame_addr ly 1 fpos / 8 + 10) ->
      abyte_kept W mem W2 (ms_mem ms) a).
  { intros a Ha Hn1 Hn2. destruct (HK2 a Ha Hn1) as [V1 Wr1]. split.
    - rewrite <- V1. apply (aview_kept_out E2 _ (w_H W2) mem2 (ms_mem ms) HFr a Ha).
      intros (r & Hin & Hr). vm_compute in Hin.
      destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [lia|].
      rewrite U2_33 in Hr. exact (Hn2 Hr).
    - intros Hw. apply (writable_kept (w_H W2) mem2 (ms_mem ms) a);
        [intros Hp; exact (apresent_grows _ _ _ _ HGR2 Hp) | exact (Wr1 Hw)]. }
  assert (KAPP : forall a, g6_app a -> abyte_kept W mem W2 (ms_mem ms) a).
  { intros a (Ha1 & Ha2). apply KALL; unfold g6_CEIL8, SB, kLowMemEnd, kHighMemBeg in *; lia. }
  (* the cut's facts at the latch *)
  assert (HGF2 : gframe cx fake_shadow (frame_addr ly 1 fpos) W2 (ms_mem ms))
    by exact (g6_gframe_carry cx (frame_addr ly 1 fpos) W W2 mem (ms_mem ms) HGF KALL NEW HFlo
                ltac:(lia) ltac:(lia) HFFapp HFFc).
  pose proof (aframe_of_gframe cx (frame_addr ly 1 fpos) W2 (ms_mem ms) HGF2) as HFR2.
  pose proof (g6_amodel_kept_x B ARx LAWS BLKN ly S W mem md W2 (ms_mem ms) mc HAR HMOD HE0 HE1 KAPP) as HMOD2.
  pose proof (g6_ainput_kept_x B ARx LAWS BLKN cx ly S W mem md W2 (ms_mem ms) HAR HIN (eq_sym HlenP) KAPP) as HIN2.
  pose proof (g6_rom_kept W W2 mem (ms_mem ms) HRV KAPP) as HRV2.
  pose proof (g6_jt_kept W W2 mem (ms_mem ms) HJT KAPP) as HJT2.
  assert (HFLAG2 : sv8 W2 (ms_mem ms) (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos)).
  { apply (gk_sv8_kept W W2 mem (ms_mem ms)); [|exact HFLAG].
    intros x Hx. apply KAPP. unfold g6_app, g6_CEIL8, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd in *. lia. }
  assert (S144' : sv8 W2 (ms_mem ms) (lf_F cx + 144) (c_n cx - gn_kq cx m)).
  { apply (gk_sv8_kept W W2 mem (ms_mem ms)); [|exact S144].
    intros x Hx. apply KALL; unfold SB in *; lia. }
  (* the registers: the call keeps the callee-saved ones, the two runs write a0, s4, s7, s8, s9, s10 only *)
  assert (RR : forall r : bv 5, In r g6_saved -> getr (ms_regs ms) r = getr regs r).
  { intros r Hr. rewrite (KR2 r Hr). rewrite <- (KR1 r Hr).
    unfold g6_saved in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [apply (g6_pres _ _ _ HP2); g6_cs |]). destruct Hr. }
  apply SRr_ret.
  lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
  split; [reflexivity|]. split; [exact HJT2|].
  exists [(1, fpos)], ly, S, [], kk, mc, fpos.
  split; [exact HJ2|]. split; [reflexivity|]. split; [exact HFR2|]. split; [exact HFLAG2|].
  split; [exact HMOD2|]. split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP|].
  split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
  split.
  { split; [rewrite (RR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (RR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (RR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite (RR 18%bv ltac:(cbv; tauto)); exact R18|].
    split; [rewrite (RR 19%bv ltac:(cbv; tauto)); exact R19|].
    split; [exact Q23|].
    split; [exact Q24|].
    split; [exact Q26|].
    split; [rewrite (RR 27%bv ltac:(cbv; tauto)); exact R27|].
    split; [rewrite (RR 3%bv ltac:(cbv; tauto)); exact R3|].
    rewrite (RR 4%bv ltac:(cbv; tauto)); exact R4. }
  split; [exact Q25|].
  split; [exact Ht|].
  split; [rewrite Q20, Hk; reflexivity|].
  split; [rewrite Hk; exact S144'|].
  rewrite Hk. exact Hkq.
Qed.
(* @@ END gp6 *)
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the R twins of this phase over the R cut points of
   W_LLVMFuzzerTestOneInput_gone_base_x.v (Section gR), as SRrG walks with the G runs.  Strict text above
   unchanged. ---- *)
Section gp6R.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Local Notation AJ0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0R STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_xR segs B PST ARx R STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).



Theorem gp6_csd_latch_xR : forall cx t m mc W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  GCSD_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m mc W c ->
  YA0nH.SRrG segs R W c (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] t).
Proof.
  intros cx t m mc W c HB HC.
  pose (RUNTOP := SRrG_run_to_pi_AJX0_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr R).
  destruct HC as (regs & mem & md & ly & S & kk & fpos & -> &
    ((HJ & HGF & HFLAG & S16 & S144 & S88 & HIN & HRV & HJT) & HMOD & HSEP & HNP) &
    HLS & HRI & Hk & Hkq & Ht & S208 & AW192 & S24 & (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4)).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly S W mem md kk
    fpos HB HJ eq_refl) as NUMS.
  cbv zeta in NUMS.
  destruct NUMS as (Hsp16 & Hsp0 & HF32 & HFb & HFF4 & HFFc & HFFapp & Hfrs & HAR).
  pose proof HB as (HAI0 & HPRE0).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  assert (HFlo : g6_CEIL8 + 32000 <= lf_F cx) by (unfold g6_CEIL8, LLVMF_STK in *; lia).
  assert (HF46 : 2 ^ 46 <= lf_F cx /\ lf_F cx + 320 <= 2 ^ 47) by (unfold LLVMF_STK in *; lia).
  assert (HFF8 : 0 <= frame_addr ly 1 fpos / 8 /\ frame_addr ly 1 fpos / 8 + 16 <= 2 ^ 44)
    by (split; [apply Z.div_pos; lia | lia]).
  (* at = |O| = g_nout (aout_at), the value check_shape_done compares a0 with *)
  pose proof HMOD as (_ & _ & _ & HOUT & _).
  pose proof HOUT as (_ & _ & Mno & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & Hblk).
  assert (Hn : 0 <= Z.of_nat (length (lm_O mc)) < 2 ^ 64).
  { destruct Hblk as [(Hc0 & _ & Hno) | (Hcp & Hno & Hin & _)]; [lia|].
    destruct (g6_blk_x B ARx LAWS BLKN ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4). lia. }
  assert (Mno' : val_mem segs (mrestrict (w_H W) mem) (VAL A_g_nout) 8 (Z.of_nat (length (lm_O mc)))).
  { replace (VAL A_g_nout) with (rg_nout fr_RG) by (vm_compute; reflexivity). exact Mno. }
  (* in.p = c_p + kq, the value s4 reloads *)
  assert (HP : 0 <= c_p cx + gn_kq cx m < 2 ^ 64).
  { pose proof HIN as ([(Hn0 & Hp0) | (Hn0 & Hin)] & _).
    - rewrite Hp0. unfold YCfn.A_EMPTY. lia.
    - destruct (g6_blk_x B ARx LAWS BLKN ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4). lia. }
  assert (HT : 0 <= t < 2 ^ 64) by (unfold OPS_MAX in *; lia).
  (* ---- 0x84c84-0x84c88: ld a0,208(s1); jal check_shape_done ---- *)
  pose proof (g6_entry1 W regs mem (lf_F cx) (Z.of_nat (length (lm_O mc))) (proj1 HF46) (proj2 HF46) HF32 R2 R9
    S208 Hn) as HS.
  remember (Eimg (Ereg regs (g6_extra1 (Z.of_nat (length (lm_O mc)))))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E32 : ew E 32 = Z_to_bv 64 (Z.of_nat (length (lm_O mc))))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (HAE : env_agree 32 (Ereg regs (g6_extra1 (Z.of_nat (length (lm_O mc))))) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_csd)) with (Z_to_bv 64 (BASE + AF_gn_csd)).
  paj_run_to_sh_x RUNTOP HS HJ AF_fr_check_shape_done.
  { intros a (r & Hin & Hr). vm_compute in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
  lazymatch goal with H : mem_grows _ _ |- _ => rename H into HGR1 end.
  cbn [ms_mem mkst] in HF, HFr, HGR1.
  lazymatch type of HF with frame_of ?E0 ?rs ?m0 ?m1 =>
    pose proof (frame_of_read_only E0 rs m0 m1 ltac:(vm_compute; reflexivity) HF) as Em1 end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ g6_saved HS HAE ltac:(vm_compute; reflexivity)) as KR1.
  cbn [ms_regs restrict] in KR1.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. rewrite E32 in Q10.
  pmkst HS. rewrite Em1 in *.
  clear HF HFr HGR1.
  rename ms into ms1, mat into mat1.
  set (mdc := with_vm_backing (m_vm_lazy md) mat1 md) in *.
  assert (Hsp1 : spZ (ms_regs ms1) = lf_F cx).
  { unfold spZ. rewrite (KR1 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
  pose proof HGF as (HSV & HFW & G32 & G40 & G48 & G56 & G64 & G72 & G80 & G96 & G104 & G120 & G128 & G136 & G152 &
    G184 & GFF0 & GFF8 & GFF16 & GFFW & GSH & GSHW).
  destruct (gn_afn_pre_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx HG LSx RINV R cx ly S fpos kk W mem mdc (ms_regs ms1)
    CSD_STK HB HJ HSV Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR1 3%bv ltac:(cbv; tauto)). exact R3. }
  { rewrite (KR1 4%bv ltac:(cbv; tauto)). exact R4. }
  { rewrite (KR1 8%bv ltac:(cbv; tauto)). exact R8. }
  { unfold CSD_STK. lia. }
  { unfold CSD_STK, LLVMF_STK. lia. }
  eapply (YA0nH.SRrG_bind _ R R_trans).
  { apply (YA0nH.SRr_SRrG _ R WLE_R); exact (g6_pb_csdk_x B PST ARx LAWS W ly S (ms_regs ms1) mem mdc ch (Z.of_nat (length (lm_O mc))) HPREc Q10 Hn Mno'). }
  intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & HPR2 & HK2 & HA02).
  rewrite Hsp1 in HJc, HK2. unfold CSD_STK in HK2.
  (* check_shape_done's journal inside this function's (B's latch walk, lf_seg_latch) *)
  assert (HJc' : AJ0R G_fr 0 [] CSD_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0).
  { refine (ajournal_gx_G_mono_xR segs B PST ARx [] G_fr 0 [] CSD_STK (lf_F cx) [] ly S [] W mem mdc [] ly S [] W2 mem2 md2 0 _ (ajournal_gx_xR_mono segs B PST ARx (@wle segs) R WLE_R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc)).
    intros a Ha. exfalso. exact (inG_nil a Ha). }
  pose proof (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem mdc kk
     CSD_STK (lf_F cx) 0 [] [] [] ly S [] W2 mem2 md2 0 HJ HJc'
     ltac:(unfold CSD_STK, LLVMF_STK in *; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
  cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
  clear HJc HJc'.
  (* the cells the tail reads, kept across the call *)
  assert (KCh : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W2 mem2 a) by (intros a Ha; apply HK2; lia).
  assert (M16 : sv8 W2 mem2 (lf_F cx + 16) (c_p cx + gn_kq cx m))
    by (apply (gk_sv8_kept W W2 mem mem2); [intros x Hx; apply KCh; lia | exact S16]).
  assert (M24 : sv8 W2 mem2 (lf_F cx + 24) HI_G_NOUT)
    by (apply (gk_sv8_kept W W2 mem mem2); [intros x Hx; apply KCh; lia | exact S24]).
  assert (M88 : sv8 W2 mem2 (lf_F cx + 88) t)
    by (apply (gk_sv8_kept W W2 mem mem2); [intros x Hx; apply KCh; lia | exact S88]).
  assert (M96 : sv8 W2 mem2 (lf_F cx + 96) (SB + frame_addr ly 1 fpos / 8))
    by (apply (gk_sv8_kept W W2 mem mem2); [intros x Hx; apply KCh; lia | exact G96]).
  assert (AWsh : awr W2 mem2 (SB + frame_addr ly 1 fpos / 8) 16).
  { apply (akept_awr W mem W2 mem2); [|exact GSHW]. intros x Hx.
    apply HK2; unfold SB, g6_CEIL8 in *; lia. }
  assert (R9b : getr regs2 9 = w64 (lf_F cx)).
  { rewrite (g6_pres (ms_regs ms1) regs2 9%bv HP2 ltac:(g6_cs)). rewrite (KR1 9%bv ltac:(cbv; tauto)). exact R9. }
  (* ---- 0x84c8c-0x84dac: the re-poison of prefix[48], s4, s10, s9, s7, and the jump to the latch ---- *)
  rewrite Q1. change (Z_to_bv 64 (BASE + 10568)) with (Z_to_bv 64 (BASE + AF_g6_ret)).
  pose proof (g6_entry2 W2 regs2 mem2 (lf_F cx) (c_p cx + gn_kq cx m) (frame_addr ly 1 fpos) t
    (proj1 HF46) (proj2 HF46) HF32 R9b ltac:(lia) ltac:(lia) HP HT M16 M24 M88 M96 AWsh) as HS2.
  remember (Eimg (Ereg regs2 (g6_extra2 (c_p cx + gn_kq cx m) (SB + frame_addr ly 1 fpos / 8) t))) as E2 eqn:HE2.
  assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
  assert (E2_32 : ew E2 32 = Z_to_bv 64 (c_p cx + gn_kq cx m))
    by (subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  assert (E2_33 : ew E2 33 = Z_to_bv 64 (SB + frame_addr ly 1 fpos / 8))
    by (subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
  assert (E2_34 : ew E2 34 = Z_to_bv 64 t)
    by (subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
  assert (U2_33 : bv_unsigned (ew E2 33) = SB + frame_addr ly 1 fpos / 8)
    by (rewrite E2_33; apply unsigned_lit_small; unfold SB; lia).
  assert (HAE2 : env_agree 32 (Ereg regs2 (g6_extra2 (c_p cx + gn_kq cx m) (SB + frame_addr ly 1 fpos / 8) t)) E2)
    by (rewrite HE2; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE2.
  paj_run_to_sh_x RUNTOP HS2 HJ2 AF_LLVM_latch.
  { (* the six stores hit the shadow of the fake frame the function owns *)
    intros a (r & Hin & Hr). vm_compute in Hin.
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [lia|].
    rewrite U2_33 in Hr. right; right; right.
    exists 1, fpos. split; [left; reflexivity|]. right. unfold in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd].
    change (fs_frame_bytes 1 / 8) with 16. unfold SB in Hr. lia. }
  lazymatch goal with H : mem_grows _ _ |- _ => rename H into HGR2 end.
  cbn [ms_mem mkst] in HF, HFr, HGR2.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 _ g6_saved HS2 HAE2 ltac:(vm_compute; reflexivity)) as KR2.
  cbn [ms_regs restrict] in KR2.
  prreg HS2 (20%bv : bv 5) Q20. prreg HS2 (23%bv : bv 5) Q23. prreg HS2 (24%bv : bv 5) Q24.
  prreg HS2 (25%bv : bv 5) Q25. prreg HS2 (26%bv : bv 5) Q26.
  rewrite ?E2_32 in Q20. rewrite ?E2_33 in Q24. rewrite ?E2_34 in Q25.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS2 eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
  pmkst HS2.
  (* the six shadow bytes now hold 0xf8, and are still writable *)
  assert (NEW : forall i, 4 <= i < 10 ->
      mbyte segs (arm W2 (ms_mem ms)) (SB + frame_addr ly 1 fpos / 8 + i) = Some (Z_to_bv 8 248) /\
      writable_at segs (arm W2 (ms_mem ms)) (SB + frame_addr ly 1 fpos / 8 + i)).
  { destruct RG1 as (_ & _ & RW & RC).
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in RW, RC. rewrite U2_33 in RW, RC.
    intros i Hi. split; [|exact (RW i Hi)].
    rewrite Forall_forall in RC.
    assert (Hi6 : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) by lia.
    unfold arm.
    destruct Hi6 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      (lazymatch goal with |- mbyte _ _ (_ + ?o) = _ =>
         destruct (RC (YP09.mkChunk o (CVal 1 (SLit 18446744073709551608)))
                    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) 0 ltac:(cbn; lia))
           as (bb & Hcb & Hmb) end;
       cbn [YP09.c_off YP09.c_val YP09.cbyte sv_denot] in Hcb, Hmb; rewrite Z.add_0_r in Hmb; rewrite Hmb;
       injection Hcb as <-; f_equal; apply bv_eq; vm_compute; reflexivity). }
  (* every other byte is kept from the cut point: the call keeps all but its 16-byte frame below F, the
     re-poison writes only the six shadow bytes *)
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx - 16 <= a < lf_F cx) ->
      ~ (SB + frame_addr ly 1 fpos / 8 + 4 <= a < SB + frame_addr ly 1 fpos / 8 + 10) ->
      abyte_kept W mem W2 (ms_mem ms) a).
  { intros a Ha Hn1 Hn2. destruct (HK2 a Ha Hn1) as [V1 Wr1]. split.
    - rewrite <- V1. apply (aview_kept_out E2 _ (w_H W2) mem2 (ms_mem ms) HFr a Ha).
      intros (r & Hin & Hr). vm_compute in Hin.
      destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [lia|].
      rewrite U2_33 in Hr. exact (Hn2 Hr).
    - intros Hw. apply (writable_kept (w_H W2) mem2 (ms_mem ms) a);
        [intros Hp; exact (apresent_grows _ _ _ _ HGR2 Hp) | exact (Wr1 Hw)]. }
  assert (KAPP : forall a, g6_app a -> abyte_kept W mem W2 (ms_mem ms) a).
  { intros a (Ha1 & Ha2). apply KALL; unfold g6_CEIL8, SB, kLowMemEnd, kHighMemBeg in *; lia. }
  (* the cut's facts at the latch *)
  assert (HGF2 : gframe cx fake_shadow (frame_addr ly 1 fpos) W2 (ms_mem ms))
    by exact (g6_gframe_carry cx (frame_addr ly 1 fpos) W W2 mem (ms_mem ms) HGF KALL NEW HFlo
                ltac:(lia) ltac:(lia) HFFapp HFFc).
  pose proof (aframe_of_gframe cx (frame_addr ly 1 fpos) W2 (ms_mem ms) HGF2) as HFR2.
  pose proof (g6_amodel_kept_x B ARx LAWS BLKN ly S W mem md W2 (ms_mem ms) mc HAR HMOD HE0 HE1 KAPP) as HMOD2.
  pose proof (g6_ainput_kept_x B ARx LAWS BLKN cx ly S W mem md W2 (ms_mem ms) HAR HIN (eq_sym HlenP) KAPP) as HIN2.
  pose proof (g6_rom_kept W W2 mem (ms_mem ms) HRV KAPP) as HRV2.
  pose proof (g6_jt_kept W W2 mem (ms_mem ms) HJT KAPP) as HJT2.
  assert (HFLAG2 : sv8 W2 (ms_mem ms) (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos)).
  { apply (gk_sv8_kept W W2 mem (ms_mem ms)); [|exact HFLAG].
    intros x Hx. apply KAPP. unfold g6_app, g6_CEIL8, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd in *. lia. }
  assert (S144' : sv8 W2 (ms_mem ms) (lf_F cx + 144) (c_n cx - gn_kq cx m)).
  { apply (gk_sv8_kept W W2 mem (ms_mem ms)); [|exact S144].
    intros x Hx. apply KALL; unfold SB in *; lia. }
  (* the registers: the call keeps the callee-saved ones, the two runs write a0, s4, s7, s8, s9, s10 only *)
  assert (RR : forall r : bv 5, In r g6_saved -> getr (ms_regs ms) r = getr regs r).
  { intros r Hr. rewrite (KR2 r Hr). rewrite <- (KR1 r Hr).
    unfold g6_saved in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [apply (g6_pres _ _ _ HP2); g6_cs |]). destruct Hr. }
  apply (YA0nH.SRrG_ret _ R R_refl).
  lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
  split; [reflexivity|]. split; [exact HJT2|].
  exists [(1, fpos)], ly, S, [], kk, mc, fpos.
  split; [exact HJ2|]. split; [reflexivity|]. split; [exact HFR2|]. split; [exact HFLAG2|].
  split; [exact HMOD2|]. split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP|].
  split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
  split.
  { split; [rewrite (RR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (RR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (RR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite (RR 18%bv ltac:(cbv; tauto)); exact R18|].
    split; [rewrite (RR 19%bv ltac:(cbv; tauto)); exact R19|].
    split; [exact Q23|].
    split; [exact Q24|].
    split; [exact Q26|].
    split; [rewrite (RR 27%bv ltac:(cbv; tauto)); exact R27|].
    split; [rewrite (RR 3%bv ltac:(cbv; tauto)); exact R3|].
    rewrite (RR 4%bv ltac:(cbv; tauto)); exact R4. }
  split; [exact Q25|].
  split; [exact Ht|].
  split; [rewrite Q20, Hk; reflexivity|].
  split; [rewrite Hk; exact S144'|].
  rewrite Hk. exact Hkq.
Qed.

End gp6R.

End gp6.

