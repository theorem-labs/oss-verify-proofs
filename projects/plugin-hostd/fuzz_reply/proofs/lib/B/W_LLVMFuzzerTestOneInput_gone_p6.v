(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_gone of the ASan+UBSan walk of fuzz_reply's LLVMFuzzerTestOneInput on image B,
   PHASE 6: from GCSD at 0x84c84 to INV_K at the latch 0x84804 (fuzz_reply.c:654 and the arm's tail).  The image-B port
   of lib/A/W_LLVMFuzzerTestOneInput_gone_p6.v (a working branch 32b23a20c3e), at B's addresses,
   registers and frame (the objdump of the pinned binary fuzz_reply.asan-ubsan),
   over the base lib/B/W_LLVMFuzzerTestOneInput_gone_base.v (85b530db754):
     0x84c84  ld a0,208(s1); jal check_shape_done      a0 = at = |O|, the value of g_nout (the abort is not reached)
     0x84c8c  ld s8,96(s1); li a0,-8; sb a0,4..9(s8)    prefix[48]'s six shadow bytes go back to 0xf8
     0x84cac  ld s4,16(s1); ld s10,24(s1); j 84da4      in.p, HI_G_NOUT
     0x84da4  ld s9,88(s1); li s7,1; j 84804            t, s7 = 1
   What this file proves besides the phase:
   - g6_pb_csdk: check_shape_done (0x85a5c) WALKED INLINE, with W_contract.v's aleafx_post (the kept clause: every
     byte outside its own 16-byte frame keeps its view and its writability), by the walk of lib/B/W_check_shape_done.v
     (10 instructions, B's listing) with the KEEP part of A's g6_pb_csdk.  Callee walked inline: the kit post (csd_spec,
     aleaf_post) lacks the outside-frame-kept clause, so errno's view, which amodel_at's aout_at reads (W_rep.v:186),
     would not be carried across the call;
   - the transport kit of the base's _gone_tk.v (gk_), with each range of a cut fact also wholly below kLowMemEnd or
     wholly at or above kHighMemBeg (g6_lo, A's g6k): every shadow byte lies in [kLowMemEnd, kHighMemBeg), so the kept
     bytes the kit asks for (g6_app) exclude the fake frame's shadow, which the re-poison writes;
   - g6_gframe_carry: the base's gframe with prefix[48] unpoisoned (fake_shadow_open), carried across the call and the
     re-poison, is the frame with the shadow poisoned again (fake_shadow), i.e. the cut's aframe_at (aframe_of_gframe).
   Section hypotheses beyond the cut's Section w context: TL : PALib B (the allocator instance, W_kit.v), for its
   api_env (as_errno B + 4 <= kLowMemEnd: errno is not one of the six shadow bytes). *)
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
(* The sink-instance guard (MERGE.md (sha256 0694aca87ccd; internal record) rule 3): every sink argument is passed with @ or from the Context *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the program interface's stack budget, from the generated lib/B/YCfn.v, as the cut names it *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* ================================================================== check_shape_done, with the kept clause *)
Section g6c.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PB_fr).
Let RET := paj_ret_at (PL := PL_fr) (PI := PB_fr).
(* W_contract.v's csd_spec with aleafx_post for aleaf_post: the same premises, the post with the kept clause *)
Definition g6_csdk_spec (pc : Z) : Prop :=
  forall W ly S regs mem md ch n,
  afn_pre SEGS B CSD_STK ly S W regs mem md ch ->
  getr regs 10 = w64 n -> 0 <= n < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_nout) 8 n ->
  SRr SEGS W (cfg_at SEGS pc regs mem md) (aleafx_post B CSD_STK regs ly S W mem md (fun a => a = w64 n)).
(* lib/B/W_check_shape_done.v's entry state, verbatim but for the names *)
Definition g6_Bx : sv := SOff 33 0.
Definition g6_csd_regions : smem :=
[ stack_region CSD_STK;
YP09.mkRegion (Some A_g_nout) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))] ].
Definition g6_csd_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF 0 (2 ^ 64 - 1) 0); (33%nat, mkAF SB SB 0) ] [] [].
Definition ss_g6csd : sstate := mkSS AF_fr_check_shape_done sr_atoms g6_csd_regions None g6_csd_facts.
Definition g6_csd_SH : list shent := [].
Definition g6_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition g6_csd_extra (n : Z) : list word := map (Z_to_bv 64) [n; SB].
Lemma g6_csd_entry : forall W ly S regs mem md ch n,
afn_pre SEGS B CSD_STK ly S W regs mem md ch ->
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
Ltac g6_nowr :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr); vm_compute in Hin;
repeat (destruct Hin as [<- | Hin];
 [cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
  repeat match goal with Hu : bv_unsigned (ew _ 2) = _ |- _ => rewrite Hu in Hr end;
  first [lia | match goal with Hno : ~ _ |- _ => apply Hno; unfold CSD_STK in *; lia end] |]);
destruct Hin.
Theorem g6_pb_csdk : g6_csdk_spec (BASE + AF_fr_check_shape_done).
Proof.
intros W ly S regs mem md ch n HPRE H10 Rn Mn.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (g6_csd_entry W ly S regs mem md ch n HPRE H10 Rn Mn) as [HS SHOK].
pose proof (ajournal_init SEGS B CSD_STK [] ly S W regs mem md ch HPRE) as HJ.
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
paj_run_tok RUN HS HJ SHOK g6_Bspan. { awr_ok_tac. exact Usp. }
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
paj_run_tok RUN HS HJ SHOK g6_Bspan. { awr_ok_tac. exact Usp. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CSD_STK <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a)
  by (intros a Ha Hno;
      match goal with H : frame_of ?Ev _ (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)) |- _ =>
        rewrite (aview_kept_out Ev _ (w_H W) (ms_mem ms) (ms_mem ms0) H a Ha) by g6_nowr end;
      apply KEEP0; assumption).
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold aleafx_post.
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [|split; [|split; [|split]]].
+ cbn [ms_mem]. apply ajournal_gx_nil. apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJ.
+ eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (g6_csd_extra n) HS); [exact HAE | vm_compute; reflexivity].
+ intros a Ha. cbn [ms_mem]. pres_chain.
+ cbn [ms_mem]. intros a Ha Hno. split; [exact (KEEP1 a Ha Hno)|].
  apply writable_kept. intros Hp. pres_chain.
+ cbn [ms_regs]. rewrite R10, E10. reflexivity.
Qed.
End g6c.

(* ================================================================== the transport kit
   The base's _gone_tk.v (B's latch kit, gk_), with each range of a cut fact also wholly below kLowMemEnd or wholly at
   or above kHighMemBeg (g6_lo, A's g6k): every shadow byte lies in [kLowMemEnd, kHighMemBeg), so the kept bytes the
   kit asks for (g6_app) exclude the fake frame's shadow, which the re-poison writes. *)
Section g6k.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

Definition g6_CEIL8 : Z := alloc_ceiling + 8.
Definition g6_lo (r : Z * Z) : Prop :=
  0 <= fst r /\ snd r <= g6_CEIL8 /\ (snd r <= kLowMemEnd \/ kHighMemBeg <= fst r).
Definition g6_fp_low (fp : list (Z * Z)) : Prop := Forall g6_lo fp.
Definition g6_app (a : Z) : Prop := 0 <= a < g6_CEIL8 /\ (a < kLowMemEnd \/ kHighMemBeg <= a).
Lemma g6_ceil_lo : 0x7fff7f800000 <= alloc_ceiling.
Proof. pose proof asan_consts as (C1 & _). lia. Qed.
Ltac g6_low :=
  cbn [fst snd gfp]; unfold g6_CEIL8, kLowMemEnd, kHighMemBeg in *;
  cbn [fr_globals_b rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *;
  pose proof g6_ceil_lo; lia.
Lemma g6_fp_low_nil : g6_fp_low []. Proof. constructor. Qed.
Lemma g6_fp_low_cons : forall r fp, 0 <= fst r -> snd r <= g6_CEIL8 ->
  (snd r <= kLowMemEnd \/ kHighMemBeg <= fst r) -> g6_fp_low fp -> g6_fp_low (r :: fp).
Proof. intros r fp H1 H2 H3 H4. constructor; [split; [exact H1 | split; [exact H2 | exact H3]] | exact H4]. Qed.
Lemma g6_fp_low_app : forall f1 f2, g6_fp_low f1 -> g6_fp_low f2 -> g6_fp_low (f1 ++ f2).
Proof. intros f1 f2 H1 H2. apply Forall_app. split; assumption. Qed.
Lemma g6_fp_low_forall : forall fp, g6_fp_low fp <-> (forall r, In r fp -> g6_lo r).
Proof. intros fp. unfold g6_fp_low. apply Forall_forall. Qed.
Lemma g6_akept_of_low : forall (W : world segs) mem (W' : world segs) mem' fp,
  (forall a, g6_app a -> abyte_kept W mem W' mem' a) -> g6_fp_low fp -> akept W mem W' mem' fp.
Proof.
  intros W mem W' mem' fp HK Hl r Hr a Ha. rewrite g6_fp_low_forall in Hl.
  destruct (Hl r Hr) as (H1 & H2 & H3). apply HK. unfold g6_app. lia.
Qed.

(* a live block is wholly in low or wholly in high memory (AR_blocks_law's in_app) *)
Lemma g6_blk : forall ly S (W : world segs) mem md p n,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n /\
  (p + req_size n <= kLowMemEnd \/ kHighMemBeg <= p).
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H1 & H2 & Happ & _ & _ & H3).
  pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2].
  unfold in_app, kLowShadowBeg in Happ.
  split; [lia|]. split; [lia|]. split; [lia|]. unfold kLowMemEnd. lia.
Qed.

(* ---- struct list ---- *)
Lemma g6_alist : forall ly S (W : world segs) mem md LA l lines,
  AR segs B ly S W mem md -> alist_at B ly S W mem LA l lines -> 0 <= LA -> LA + 16 <= kLowMemEnd ->
  g6_fp_low (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HL0 HL1.
  pose proof g6_ceil_lo as HCL.
  assert (HREC : g6_fp_low (map (fun r => gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0]))) (hl_recs l))
                 /\ (forall b, In b (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l)) ->
                       In b (ablocks B ly S))).
  { rewrite Forall_forall in H9. split.
    - rewrite g6_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (x & <- & Hx).
      destruct (H9 x Hx) as (K1 & _). destruct (g6_blk ly S W mem md _ _ HAR K1) as (P1 & P2 & P3 & P4).
      unfold g6_lo. cbn [gfp fst snd]. rewrite gk_bzs_len, length_app. cbn [length].
      unfold g6_CEIL8 in *. lia.
    - intros b Hb. apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (H9 x Hx)). }
  destruct HREC as [HR1 HR2].
  unfold alist_fp, alist_blks. split.
  - apply g6_fp_low_cons; [cbn; lia | cbn; unfold g6_CEIL8, kLowMemEnd in *; lia | cbn; left; lia |].
    apply g6_fp_low_app; [|exact HR1].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply g6_fp_low_nil|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    destruct (g6_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4).
    apply g6_fp_low_cons; [cbn; lia | | | apply g6_fp_low_nil];
      cbn [gfp fst snd]; rewrite gk_bzs_len, length_app, gk_concat_len;
      unfold hl_n in Hj; unfold AREC in *; unfold g6_CEIL8 in *; lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [|exact (HR2 b Hb)].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|].
    destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- struct source ---- *)
Lemma g6_asrc : forall ly S (W : world segs) mem md HA h,
  AR segs B ly S W mem md -> asrc_at B ly S W mem HA h -> 0 <= HA -> HA + ASRC <= kLowMemEnd ->
  g6_fp_low (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md HA h HAR HS HL0 HL1.
  pose proof g6_ceil_lo as HCL.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  destruct (g6_alist ly S W mem md (HA + 16) (hs_pending h) false HAR Hpend ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [A1 A2].
  destruct (g6_alist ly S W mem md (HA + 64) (hs_expected h) true HAR Hexp ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [E1 E2].
  destruct (g6_alist ly S W mem md (HA + 80) (hs_held h) true HAR Hheld ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [H1 H2].
  destruct (g6_blk ly S W mem md _ _ HAR Hpb) as (P1 & P2 & P3 & P4).
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
Lemma g6_aentry : forall ly S (W : world segs) mem md e,
  AR segs B ly S W mem md -> aentry_ok B ly S W mem e ->
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
      destruct (g6_blk ly S W mem md _ _ HAR M1) as (P1 & P2 & P3 & P4).
      unfold g6_lo. cbn [gfp fst snd]. rewrite gk_bzs_len, length_app. cbn [length].
      unfold g6_CEIL8 in *. lia.
    - intros b Hb. apply in_map_iff in Hb as (k & <- & Hk). exact (proj1 (K15 k Hk)). }
  destruct HK as [HK1 HK2]. unfold aentry_fp, aentry_blks. split.
  - apply g6_fp_low_app.
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply g6_fp_low_nil|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
      destruct (g6_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4).
      apply g6_fp_low_cons; [cbn; lia | | | apply g6_fp_low_nil];
        cbn [gfp fst snd]; rewrite gk_bzs_len, length_app; unfold g6_CEIL8 in *; lia.
    + apply g6_fp_low_cons; [| | |exact HK1].
      * cbn [gfp fst]. destruct K12 as [(Hz & _) | (Hz & Hin & _)]; [lia|].
        destruct (g6_blk ly S W mem md _ _ HAR Hin) as (P1 & _). lia.
      * cbn [gfp snd]. rewrite gk_bzs_len, gk_key_ptrs_len.
        destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
        { rewrite Hz, Hks. cbn [length]. unfold g6_CEIL8. lia. }
        destruct (g6_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4).
        unfold re_nheld in Hk1. unfold g6_CEIL8 in *. lia.
      * cbn [gfp fst snd]. rewrite gk_bzs_len, gk_key_ptrs_len.
        destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
        { rewrite Hz, Hks. cbn [length]. left. unfold kLowMemEnd. lia. }
        destruct (g6_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4).
        unfold re_nheld in Hk1. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hb|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + apply in_app_or in Hb as [Hb | Hb]; [|exact (HK2 b Hb)].
      destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [destruct Hb|].
      destruct K12 as [(Hz0 & _) | (_ & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- the relay's table, at fuzz_reply.asan-ubsan's globals (fr_globals_b, the cut's fr_RG) ---- *)
Lemma g6_arelay : forall ly S (W : world segs) mem md G es,
  AR segs B ly S W mem md -> arelay_at B fr_globals_b ly S W mem G es ->
  g6_fp_low (arelay_fp fr_globals_b G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md G es HAR (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
  destruct (g6_blk ly S W mem md _ _ HAR R8) as (P1 & P2 & P3 & P4).
  assert (HE : g6_fp_low (concat (map aentry_fp es))
               /\ (forall b, In b (concat (map aentry_blks es)) -> In b (ablocks B ly S))).
  { rewrite Forall_forall in R10. split.
    - rewrite g6_fp_low_forall. intros r Hr. apply in_concat in Hr as (f & Hf & Hr).
      apply in_map_iff in Hf as (e & <- & He).
      destruct (g6_aentry ly S W mem md e HAR (R10 e He)) as [F1 _].
      rewrite g6_fp_low_forall in F1. exact (F1 r Hr).
    - intros b Hb. apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
      destruct (g6_aentry ly S W mem md e HAR (R10 e He)) as [_ F2]. exact (F2 b Hb). }
  destruct HE as [HE1 HE2]. unfold arelay_fp, arelay_blks. split.
  - apply g6_fp_low_cons; [g6_low | g6_low | g6_low |].
    apply g6_fp_low_cons; [g6_low | g6_low | g6_low |].
    apply g6_fp_low_cons; [g6_low | g6_low | g6_low |].
    apply g6_fp_low_cons; [cbn; lia | cbn [fst snd]; unfold ATABLE, g6_CEIL8 in *; lia
                          | cbn [fst snd]; unfold ATABLE in *; lia | exact HE1].
  - intros b [<- | Hb]; [exact R8 | exact (HE2 b Hb)].
Qed.

(* ---- the controller's stream ---- *)
Lemma g6_aout : forall ly S (W : world segs) mem md c O mx no cap out,
  AR segs B ly S W mem md -> aout_at B fr_globals_b ly S W mem c O mx no cap out ->
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
    destruct (g6_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4).
    apply g6_fp_low_cons; [cbn; lia | cbn; unfold g6_CEIL8 in *; lia | cbn; lia | apply g6_fp_low_nil].
  - intros b Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.

Lemma g6_akept_rng : forall (W W' : world segs) mem mem' lo hi,
  (forall a, g6_app a -> abyte_kept W mem W' mem' a) -> 0 <= lo -> hi <= kLowMemEnd ->
  akept W mem W' mem' [(lo, hi)].
Proof.
  intros W W' mem mem' lo hi HK H1 H2. apply g6_akept_of_low; [exact HK|].
  apply g6_fp_low_cons;
    [cbn; lia | cbn; unfold g6_CEIL8, kLowMemEnd in *; pose proof g6_ceil_lo; lia | cbn; left; exact H2
    | apply g6_fp_low_nil].
Qed.
Lemma g6_akept_of_rng : forall (W W' : world segs) mem mem' lo hi,
  (forall a, g6_app a -> abyte_kept W mem W' mem' a) -> 0 <= lo -> hi <= kLowMemEnd ->
  forall x, lo <= x < hi -> abyte_kept W mem W' mem' x.
Proof.
  intros W W' mem mem' lo hi HK H1 H2 x Hx. apply HK.
  unfold g6_app, g6_CEIL8, kLowMemEnd in *. pose proof g6_ceil_lo. lia.
Qed.
(* ---- the model ---- *)
Lemma g6_amodel_kept : forall ly S (W : world segs) mem md (W' : world segs) mem' m,
  AR segs B ly S W mem md -> amodel_at B ly S W mem m ->
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
    - destruct (g6_asrc ly S W mem md _ h HAR M2 HB0 HB1) as [F1 F2].
      exact (asrc_at_kept B ly S W mem ly S W' mem' _ h M2 (g6_akept_of_low _ _ _ _ _ KEEP F1) F2).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply (g6_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx.
        apply (g6_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia. }
  split.
  { destruct (g6_arelay ly S W mem md (lm_G m) (lm_es m) HAR M3) as [F1 F2].
    exact (arelay_at_kept B fr_RG ly S W mem ly S W' mem' _ _ M3
             (g6_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { destruct (g6_aout ly S W mem md _ _ _ _ _ _ HAR M4 HE0 HE1) as [F1 F2].
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
Lemma g6_ainput_kept : forall cx ly S (W : world segs) mem md (W' : world segs) mem',
  AR segs B ly S W mem md -> ainput_at B cx ly S W mem ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  (forall a, g6_app a -> abyte_kept W mem W' mem' a) ->
  ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S W mem md W' mem' HAR (I1 & I2) Hlen KEEP.
  split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
  intros x Hx. rewrite length_map in Hx. rewrite Hlen in Hx. apply KEEP.
  destruct I1 as [(Hn & Hp) | (Hn & Hin)]; [lia|].
  destruct (g6_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4).
  unfold g6_app, g6_CEIL8. lia.
Qed.
Lemma g6_rom_kept : forall (W W' : world segs) mem mem',
  rom_view segs W mem -> (forall a, g6_app a -> abyte_kept W mem W' mem' a) ->
  rom_view segs W' mem'.
Proof.
  intros W W' mem mem' HR KEEP a Ha. rewrite <- (HR a Ha).
  assert (Hin : in_img segs a) by (destruct Ha as (sg & H1 & _ & H3); exists sg; split; assumption).
  pose proof (pa_segs_low a Hin) as Hlow. pose proof g6_ceil_lo.
  exact (proj1 (KEEP a ltac:(unfold g6_app, g6_CEIL8, kLowMemEnd in *; lia))).
Qed.
Lemma g6_jt_kept : forall (W W' : world segs) mem mem',
  jt_rom W mem -> (forall a, g6_app a -> abyte_kept W mem W' mem' a) -> jt_rom W' mem'.
Proof.
  intros W W' mem mem' HJ KEEP i Hi. apply (akept_vm W mem); [|exact (HJ i Hi)].
  intros x Hx. apply KEEP. unfold g6_app, fr_jtab, g6_CEIL8, kLowMemEnd in *. pose proof g6_ceil_lo. cbn in Hx. lia.
Qed.

(* ---- the frame, across the call and the re-poison ---- *)
(* the fake frame's shadow: bytes 4..9 (prefix[48]) now 0xf8, the other ten kept *)
Lemma g6_shadow_close : forall (W W' : world segs) mem mem' a,
  garr8 segs (arm W mem) a fake_shadow_open ->
  (forall i, 0 <= i < 16 -> ~ (4 <= i < 10) -> abyte_kept W mem W' mem' (a + i)) ->
  (forall i, 4 <= i < 10 -> mbyte segs (arm W' mem') (a + i) = Some (Z_to_bv 8 248)) ->
  garr8 segs (arm W' mem') a fake_shadow.
Proof.
  intros W W' mem mem' a HGa HK HN j Hj. cbn [length fake_shadow] in Hj.
  assert (Hc : (4 <= j < 10)%nat \/ ~ (4 <= j < 10)%nat) by lia.
  destruct Hc as [Hc | Hc].
  - assert (Ev : nth j fake_shadow 0 = 248).
    { unfold fake_shadow. do 10 (destruct j as [|j]; [cbn [nth]; first [reflexivity | lia] |]). lia. }
    rewrite Ev. split; [|lia].
    intros k Hk. assert (Ek : k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
    rewrite (HN (Z.of_nat j) ltac:(lia)). vm_compute. reflexivity.
  - assert (Ev : nth j fake_shadow 0 = nth j fake_shadow_open 0).
    { unfold fake_shadow, fake_shadow_open.
      do 16 (destruct j as [|j]; [cbn [nth]; first [reflexivity | lia] |]). lia. }
    destruct (HGa j ltac:(cbn [length fake_shadow_open]; lia)) as [Hv Hr].
    rewrite Ev. split; [|exact Hr].
    apply (akept_vm W mem W' mem'); [|exact Hv]. intros x Hx.
    replace x with (a + Z.of_nat j) by lia. apply HK; lia.
Qed.
(* the base's gframe (B: no `full` flag; 14 slots above F, the fake frame's three header words, its window, its
   shadow and the shadow's window) *)
Lemma g6_gframe_carry : forall cx FF (W W' : world segs) mem mem',
  gframe cx fake_shadow_open FF W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx - 16 <= a < lf_F cx) -> ~ (SB + FF / 8 + 4 <= a < SB + FF / 8 + 10) ->
     abyte_kept W mem W' mem' a) ->
  (forall i, 4 <= i < 10 -> mbyte segs (arm W' mem') (SB + FF / 8 + i) = Some (Z_to_bv 8 248) /\
     writable_at segs (arm W' mem') (SB + FF / 8 + i)) ->
  g6_CEIL8 + 32000 <= lf_F cx -> lf_F cx + 320 <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  in_app FF 128 -> FF + 128 <= alloc_ceiling ->
  gframe cx fake_shadow FF W' mem'.
Proof.
  intros cx FF W W' mem mem'
    (H1 & H2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 &
     A20 & A21 & A22) HK HN HFlo HF1 HF2 Happ HFFc.
  pose proof g6_ceil_lo as HCL. pose proof asan_consts as (C1 & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  unfold g6_CEIL8 in HFlo.
  assert (HF8 : 0 <= FF / 8 /\ FF / 8 + 16 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | lia]).
  assert (KH : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W' mem' a)
    by (intros a Ha; apply HK; [lia | lia | unfold SB; lia]).
  assert (KF : forall a, FF <= a < FF + 128 -> abyte_kept W mem W' mem' a)
    by (intros a Ha; apply HK; [lia | lia | unfold SB; lia]).
  assert (KS : forall i, 0 <= i < 16 -> ~ (4 <= i < 10) -> abyte_kept W mem W' mem' (SB + FF / 8 + i))
    by (intros i Hi Hn; apply HK; [unfold SB; lia | unfold SB; lia | lia]).
  split.
  { intros o r Hin. apply (gk_sv8_kept W W' mem mem'); [|exact (H1 o r Hin)].
    intros x Hx. apply KH.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
    lia. }
  split.
  { apply (akept_awr W mem); [|exact H2]. intros x Hx. apply KH. lia. }
  do 14 (split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | assumption]|]).
  do 3 (split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KF; lia | assumption]|]).
  split; [apply (akept_awr W mem); [intros x Hx; apply KF; lia | exact A20]|].
  split.
  { exact (g6_shadow_close W W' mem mem' (SB + FF / 8) A21 KS (fun i Hi => proj1 (HN i Hi))). }
  intros i Hi.
  destruct (Z_lt_le_dec i 4) as [Hl | Hl]; [exact (proj2 (KS i ltac:(lia) ltac:(lia)) (A22 i Hi))|].
  destruct (Z_lt_le_dec i 10) as [Hl2 | Hl2]; [exact (proj2 (HN i ltac:(lia)))|].
  exact (proj2 (KS i ltac:(lia) ltac:(lia)) (A22 i Hi)).
Qed.
End g6k.

(* ================================================================== the phase *)
Section gp6.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* the allocator instance (W_kit.v): its api_env (pal_env) puts errno's 4 bytes below kLowMemEnd *)
Hypothesis TL : @PALib _ _ PB_fr B.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).

(* a callee-saved register across the call (the latch's lt_pres) *)
Lemma g6_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac g6_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
(* the registers the cut point names that neither run writes and the call keeps (B: the runs write a0, s4, s7, s8,
   s9, s10) *)
Definition g6_saved : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 27]%bv.

(* 0x84c84: `ld a0,208(s1)` reads at out of the frame cell F+208 *)
Definition g6_atR : YP09.region :=
  YP09.mkRegion (Some 9%nat) 208 216 0 0 [YP09.mkChunk 208 (CVal 8 (SOff 32 0))].
Definition g6_facts1 : facts :=
  mkFacts [ (2%nat, mkAF (2^46) (2^47) 5); (9%nat, mkAF (2^46) (2^47) 5); (32%nat, mkAF 0 (2 ^ 64 - 1) 0) ] [] [].
Definition ss_g6a : sstate := mkSS AF_gn_csd sr_atoms [g6_atR] None g6_facts1.
Definition g6_extra1 (A : Z) : list word := map (Z_to_bv 64) [A].
Lemma g6_entry1 : forall (W : world segs) regs mem (F A : Z),
  2 ^ 46 <= F -> F + 320 <= 2 ^ 47 -> F mod 32 = 0 ->
  getr regs 2 = w64 F -> getr regs 9 = w64 F ->
  sv8 W mem (F + 208) A -> 0 <= A < 2 ^ 64 ->
  st_ok_pi segs VAL (Eimg (Ereg regs (g6_extra1 A))) ss_g6a
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gn_csd)) mem (seg_rom segs))).
Proof.
  intros W regs mem F A HFlo HFhi HF32 R2 R9 Mat HA.
  pose proof pa_B_ok as HBASE.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (g6_extra1 A))).
  assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E9 : ew E 9 = getr regs 9) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 A) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (Usp : bv_unsigned (ew E 2) = F) by (rewrite E2, R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9, R9; apply unsigned_lit_small; lia).
  unfold ss_g6a. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, g6_atR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ F 208 8 (SOff 32 0) A);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mat].
  - cbn [pairwise_disjoint all_disjoint]. repeat split.
  - split; [|split; [exact I | exact I]].
    cbn [g6_facts1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, U9, E32, unsigned_lit_small by lia.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; lia.
Qed.

(* 0x84c8c, back from check_shape_done: s8 = F+96 (the fake frame's shadow), the six stores `sb a0,4..9(s8)` (the
   shadow region's window [4, 10)), s4 = F+16 (in.p), s10 = F+24 (HI_G_NOUT), then 0x84da4: s9 = F+88 (t) *)
Definition AF_g6_ret : Z := 0x2948.
Definition g6_frR : YP09.region :=
  YP09.mkRegion (Some 9%nat) 16 104 0 0
    [YP09.mkChunk 16 (CVal 8 (SOff 32 0)); YP09.mkChunk 24 (CVal 8 (SLit HI_G_NOUT));
     YP09.mkChunk 88 (CVal 8 (SOff 34 0)); YP09.mkChunk 96 (CVal 8 (SOff 33 0))].
Definition g6_shR : YP09.region := YP09.mkRegion (Some 33%nat) 4 10 4 10 [].
Definition g6_facts2 : facts :=
  mkFacts [ (9%nat, mkAF (2^46) (2^47) 5); (32%nat, mkAF 0 (2 ^ 64 - 1) 0);
            (33%nat, mkAF SB (SB + 2 ^ 44) 0); (34%nat, mkAF 0 (2 ^ 64 - 1) 0) ] [] [].
Definition ss_g6b : sstate := mkSS AF_g6_ret sr_atoms [g6_frR; g6_shR] None g6_facts2.
Definition g6_extra2 (P SH T : Z) : list word := map (Z_to_bv 64) [P; SH; T].
Lemma g6_entry2 : forall (W : world segs) regs mem (F P FF T : Z),
  2 ^ 46 <= F -> F + 320 <= 2 ^ 47 -> F mod 32 = 0 -> getr regs 9 = w64 F ->
  0 <= FF -> FF + 128 <= 2 ^ 47 -> 0 <= P < 2 ^ 64 -> 0 <= T < 2 ^ 64 ->
  sv8 W mem (F + 16) P -> sv8 W mem (F + 24) HI_G_NOUT -> sv8 W mem (F + 88) T ->
  sv8 W mem (F + 96) (SB + FF / 8) ->
  awr W mem (SB + FF / 8) 16 ->
  st_ok_pi segs VAL (Eimg (Ereg regs (g6_extra2 P (SB + FF / 8) T))) ss_g6b
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_g6_ret)) mem (seg_rom segs))).
Proof.
  intros W regs mem F P FF T HFlo HFhi HF32 R9 HFF0 HFF1 HP HT M16 M24 M88 M96 AW.
  pose proof pa_B_ok as HBASE.
  assert (HF8 : 0 <= FF / 8 /\ FF / 8 + 16 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | lia]).
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (g6_extra2 P (SB + FF / 8) T))).
  assert (E9 : ew E 9 = getr regs 9) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 P) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (SB + FF / 8))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 T) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9, R9; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = P) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = SB + FF / 8) by (rewrite E33; apply unsigned_lit_small; unfold SB; lia).
  assert (U34 : bv_unsigned (ew E 34) = T) by (rewrite E34; apply unsigned_lit_small; lia).
  unfold ss_g6b. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold region_ok, g6_frR.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
      * apply (chunk_ok_val segs E _ F 16 8 (SOff 32 0) P);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M16].
      * apply (chunk_ok_val segs E _ F 24 8 (SLit HI_G_NOUT) HI_G_NOUT);
          [reflexivity | unfold HI_G_NOUT; zside | zside | exact M24].
      * apply (chunk_ok_val segs E _ F 88 8 (SOff 34 0) T);
          [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M88].
      * apply (chunk_ok_val segs E _ F 96 8 (SOff 33 0) (SB + FF / 8));
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside
          | exact M96].
    + unfold region_ok, g6_shR.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U33. split; [unfold SB; lia|]. split; [unfold SB; lia|].
      split; [intros o Ho; exact (AW o ltac:(lia)) | constructor].
  - apply pairwise_disjoint_of_extents. unfold g6_frR, g6_shR, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U33.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold SB. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [g6_facts2 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U32, U33, U34.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB.
    repeat match goal with |- _ /\ _ => split end; lia.
Qed.

Theorem gp6_csd_latch : forall cx t m mc W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> GCSD B G_fr fr_FP LS RINV cx t m mc W c ->
  SRr segs W c (INV_K B G_fr fr_FP LS RINV cx t).
Proof.
  intros cx t m mc W c HB HC.
  pose (RUNTOP := SRr_run_to_pi_AJX0 (PL := PL_fr) (PI := PB_fr) B LAWS G_fr).
  destruct HC as (regs & mem & md & ly & S & kk & fpos & -> &
    ((HJ & HGF & HFLAG & S16 & S144 & S88 & HIN & HRV & HJT) & HMOD & HSEP) &
    HLS & HRI & Hk & Hkq & Ht & S208 & AW192 & S24 & (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4)).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx [(1, fpos)] ly S W mem md kk fpos HB HJ eq_refl)
    as NUMS.
  cbv zeta in NUMS.
  destruct NUMS as (Hsp16 & Hsp0 & HF32 & HFb & HFF4 & HFFc & HFFapp & Hfrs & HAR).
  pose proof HB as (HAI0 & HPRE0).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf in HPRE0; tauto).
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
    destruct (g6_blk B LAWS ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4). lia. }
  assert (Mno' : val_mem segs (mrestrict (w_H W) mem) (VAL A_g_nout) 8 (Z.of_nat (length (lm_O mc)))).
  { replace (VAL A_g_nout) with (rg_nout fr_RG) by (vm_compute; reflexivity). exact Mno. }
  (* in.p = c_p + kq, the value s4 reloads *)
  assert (HP : 0 <= c_p cx + gn_kq cx m < 2 ^ 64).
  { pose proof HIN as ([(Hn0 & Hp0) | (Hn0 & Hin)] & _).
    - rewrite Hp0. unfold YCfn.A_EMPTY. lia.
    - destruct (g6_blk B LAWS ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4). lia. }
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
  paj_run_to_shx RUNTOP HS HJ AF_fr_check_shape_done.
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
  destruct (gn_afn_pre B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP HG LS RINV cx ly S fpos kk W mem mdc (ms_regs ms1)
    CSD_STK HB HJ HSV Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR1 3%bv ltac:(cbv; tauto)). exact R3. }
  { rewrite (KR1 4%bv ltac:(cbv; tauto)). exact R4. }
  { rewrite (KR1 8%bv ltac:(cbv; tauto)). exact R8. }
  { unfold CSD_STK. lia. }
  { unfold CSD_STK, LLVMF_STK. lia. }
  eapply SRr_bind.
  { exact (g6_pb_csdk B LAWS W ly S (ms_regs ms1) mem mdc ch (Z.of_nat (length (lm_O mc))) HPREc Q10 Hn Mno'). }
  intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & HPR2 & HK2 & HA02).
  rewrite Hsp1 in HJc, HK2. unfold CSD_STK in HK2.
  (* check_shape_done's journal inside this function's (B's latch walk, lf_seg_latch) *)
  assert (HJc' : ajournal_gx segs B G_fr 0 [] CSD_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0).
  { refine (ajournal_gx_G_mono segs B [] G_fr 0 [] CSD_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0 _ HJc).
    intros a Ha. exfalso. exact (inG_nil a Ha). }
  pose proof (ajournal_gx_sub segs B LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem mdc kk
     CSD_STK (lf_F cx) 0 [] [] [] ly S W2 mem2 md2 0 HJ HJc'
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
  paj_run_to_shx RUNTOP HS2 HJ2 AF_LLVM_latch.
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
  pose proof (g6_amodel_kept B LAWS ly S W mem md W2 (ms_mem ms) mc HAR HMOD HE0 HE1 KAPP) as HMOD2.
  pose proof (g6_ainput_kept B LAWS cx ly S W mem md W2 (ms_mem ms) HAR HIN (eq_sym HlenP) KAPP) as HIN2.
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
  exists [(1, fpos)], ly, S, kk, mc, fpos.
  split; [exact HJ2|]. split; [reflexivity|]. split; [exact HFR2|]. split; [exact HFLAG2|].
  split; [exact HMOD2|]. split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP|].
  split; [exact HLS|]. split; [exact HRI|].
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

End gp6.
