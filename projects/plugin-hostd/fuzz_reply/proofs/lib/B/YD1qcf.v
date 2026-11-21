(* Hand port by a Theorem Labs lane (2026-10-29, a Theorem Labs lane's DRIVER_CF_B): A1's raw generator copy of this file
   with CfDriver's hand edits to lib/A/AD1qcf.v (generator run out-DRV2 ->)
   three-way merged on; YCegcf -> YCeg as CfDriver's A edit (ACegcf -> ACeg), Reusable YC5d as A2's YD1w_cf, A1's
   two cf-suffix defects fixed, AStkUp -> RelocB-2's YStkUp, AD29cf -> YD29cf. No image-A literal. *)
(* copied from cgif_file lib/A/YD1q.v by rules r1,r2,r6,rC, generator c03cd3ee83e0f39cd4fe9d090fe9d53155314a0005789c623a860de97ecb6274 *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YD1q.v, with its module paths changed, and its fuzz_reply.asan-ubsan addresses relocated from cgif_file_fuzzer.asan-ubsan (3 numerals; per-numeral report). *)
(* Modified by Theorem Labs, 2026-10: the library shape is fuzz_reply's checksum_shape (lib/ZTraceSpec.v), not cgif's ff_lib_shape: ff_unl_has_nil / ff_libk_has_nil become checksum_libk_has_nil, and the ff_lib_shape files (YI17, YI0a, YO08) are not imported (as lib/A/AD1q.v). *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revision's launch (CONFIG_RSEQ-sized auxv, execfn, group id, launch premises); the input-owned, top-anchored launch stack; the start-up certificate per CONFIG_RSEQ flag with states computed in the build); internal commit ids in comments replaced by public commits or removed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB12 YB1h YB01r YB1n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0f YG00 YG01 YG0n YG0d YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0f YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YF0m YCeg YD1vcf YD1wcf YD1xcf YD1icf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCfn YD1pcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YD1g YD2i YD2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0d2cf YG0dcf YGcfNames YG01cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD1w_cf YD1mcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyStartWitB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YG0dcfR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
Lemma checksum_libk_has_nil : forall pl fs K, (forall l, K l []) -> @LIBK checksum_shape pl fs K [].
Proof. intros pl fs K HK. cbn. apply HK. Qed.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance checksum_shape.
Section b.
Context {ci : YGcfNames.CfImg} {cp : YGcfNames.CfParams}.
 Context {rc : YM05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
(* the cf allocator's non-primary room between the driver's allocator calls, with its three laws (A/AD1w_cf.v) *)
Variable NP : astate -> Prop.
Hypothesis NPI : iface_room_np_init NP.
Hypothesis NPS : iface_room_np_step NP.
Hypothesis NPT : iface_room_np_tail NP.
Hypothesis AMALLOC : amalloc_realizes_cf tfibsegs B.
Hypothesis AFREE : YG0dcfR.afree_realizes_cf_rh tfibsegs B.
Hypothesis AICPY : aintrin_realizes_cf tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : YD1icf.aread_check_stmt B.
Variables (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z).
(* the run count (at MT_sec: a Theorem Labs lane's nsec_cf), its run bound and its per-call step bound (B/YD1mcf.v; KF-COUNT #7) *)
Variables (NS : astate -> Z) (NRUN XNMAX : Z).
(* the meter's room at each call (A/AD1mcf.v MT_PRE) *)
Hypothesis MT_PRE : forall S n, Wf_cf (as_universe B) S -> qtight S -> blocks_bytes S <= DRV_LIVE -> NP S -> NS S + XNMAX <= NRUN ->
  0 <= n < 2 ^ 26 -> mo_ok MT S (XM_LIB n).
(* the meter's step bounds the run count's step and one call's step is at most XNMAX (B/YD1mcf.v); the count's step
   at the driver's own mallocs and frees (B/CfRBridgeRulesB.v's texts at NS); and its room at the start state
   init_state for the driver's mallocs before the loop and the loop's at most 4 calls (B/YD1pcf.v, B/YD2dcf.v
   NS_START) *)
Hypothesis NS_MO : forall S S' n, mo_le MT S S' (XN_LIB n) -> NS S' <= NS S + XN_LIB n.
Hypothesis XN_BND : forall n, 0 <= n < 2 ^ 26 -> 0 <= XN_LIB n <= XNMAX.
Hypothesis HULL_NS : forall S, NS S <= NRUN -> cf_hull_ok S.
Hypothesis nsec_malloc_cf : forall n tr s,
  YGcfXs.cfx_ipost (YG00cf.malloc_cf n tr s) (fun r => NS (snd r) <= NS s + (if from_primary n then 0 else 1)).
Hypothesis nsec_free_cf : forall p tr s, YGcfXs.cfx_ipost (YG00cf.free_cf p tr s) (fun r => NS (snd r) <= NS s).
Hypothesis NS_START : NS init_state + 12 + 4 * XNMAX <= NRUN.
Hypothesis RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a.
(* field round 3 (Part A): the image fact behind drv_pre's RELRO bytes (B/YD1pcf.v RO, B/YD1vcf.v relro_ok) *)
Hypothesis RO : relro_ok.
(* fuzz_reply's cf program interface at every FP state (B/YD1w_cf.v), its room at preset's LIB_ROOM (B/YD1mcf.v), at
   the world relation wle' tfibsegs RZ_cf (route R: the library run can free, B/YD1pcf.v Rcf) *)
Hypothesis LIBX : fr_lib_contract_drv_allR B MT XM_LIB XN_LIB RLO RHI LIBROOM_fr NP (YA0nH.wle' tfibsegs YGcfRehidePost.RZ_cf).
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis PF1 : printf_first_tfa B xst.
Hypothesis PFN : printf_next_tfa B xst.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis ESTI : est_img_tfa est.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis FWS : fwrite_site_tfa B est.
Hypothesis RFS : refused_site_tfa B est.
Hypothesis FPO : fprintf_s_site_tfa B est 0x1d745 (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est 0x1d75a (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est 0x15886 (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS : exit_site_tfa B est xst.
(* field rounds 2 and 3: the cf driver's start witnesses (at the start-up hand-off, B/ReplyStartWitB.v), the unit's three
   image rows and the pf cells' ownership (B/YD1pcf.v HSTART / HSTART_ARO / HSTART_PF / HROWS / HPFO) *)
Hypothesis HSTART : ReplyStartWitB.start_cells_ho_t B.
Hypothesis HSTART_ARO : start_aro_ho_t B.
Hypothesis HSTART_PF : ReplyStartWitB.start_pf_ho_t B.
Hypothesis HROWS : YGcfImgRows.EXH_OFF_t /\ YG0ncf.errb_obj_owned_t B /\ YG0ncf.errb_ial_apart_t B.
Hypothesis HPFO : YG0ncf.pf_cells_owned_t B.
Definition drv_mainX_stmt : Prop :=
forall (sp : word) (rdraw : EntryDraw) (brk mbase : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
(FULL : word -> option byte) (model : Model) (SINV : env -> (word -> option byte) -> Prop),
valid_sp sp -> valid_brk TSEGS brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
HS_tfib_r (rseq_z (kb_rseq (in_kernel inp))) h = Some ch ->
(forall E' M, SINV E' M -> uE E' e_sp0 = YA02.TOP sp + 8388608) ->
cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp) SINV
(YA02.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp)
  (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp)
  (in_execfn inp) (in_sigpipe_default inp)) (in_fs inp) E ch R FULL model ->
(forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 sp rdraw brk (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp)
  (in_uid inp) (in_gid inp) (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp)
  (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)) n) ->
(forall a, YA02.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp)
  (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp)
  (in_execfn inp) (in_sigpipe_default inp) E a = true ->
FULL a = wrap_mem inp mbase TPH (Z_to_bv 64 (Z.of_N AsanUbsan.M.init_pc)) sp rdraw a) ->
srealizes TSEGS (cfg_of TSEGS R (pc ch) FULL model) (CLOSEDX inp).
Lemma DRV_MAINX : drv_mainX_stmt.
Proof.
  exact (tfib_drv_main B HB NP NPI NPS NPT AMALLOC AFREE AICPY ARDCHK MT XM_LIB XN_LIB RLO RHI NS NRUN XNMAX MT_PRE NS_MO
    XN_BND HULL_NS nsec_malloc_cf nsec_free_cf NS_START RO_IN RO (LIBX _) xst XFR PF1 PFN
    est ESTI ESTF FWS RFS FPO FPR FPU EXS HSTART HSTART_ARO HSTART_PF HROWS HPFO).
Qed.
Theorem tfib_srealizesX : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk mb rdraw) inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw YA02.LIMIT inp) (SPECX inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hlau Hceil.
pose proof Hinp as (Hva & Hve & _ & _ & _ & [Huid _] & Hnof & Hsig & Hhw & Hab & Hmmu & _ & Hvl & Hcr & Hspt & Hkern).
destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw ab mmu urnd tmp kern execfn cr spd spt].
cbn [in_argv in_envp in_uid in_hwcap in_nofile in_abort_terminal in_va_size in_channel_reader in_sigpipe_terminal in_kernel]
in Hva, Hve, Hfit, Huid, Hhw, Hnof, Hab, Hmmu, Hcr, Hspt, Hkern.
subst ab mmu cr spt.
rewrite Hkern in Hinp, Hsig, Hvl, Hlau |- *.
change (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp (recorded_kernel kern) execfn true spd false)
with (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd) in *.
apply (srz_conseq TSEGS _ (CLOSEDX (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd)));
[| apply t_eq_sym; apply specx_closedx_eq].
apply (tfib_startup_T1 sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd
Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hnof Hsig Hvl Hlau
(CLOSEDX (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd)) (CLOSEDX_has_nil _)).
intros h c Hok.
destruct (HS_ok_open h sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd
(fs_seed_tmp fs tmp) c Hok) as (ch & E & R & FULL & model & Hch & -> & HC & HE & HM & _).
assert (SP0 : forall E' M, YA02.SINV0 TSEGS TPH sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp
kern execfn spd AsanUbsan.M.init_pc E' M -> uE E' e_sp0 = YA02.TOP sp + 8388608).
{ intros E' M HSv. eapply YA02.SINV0_sp0; try eassumption. Unshelve. all: first [assumption | exact TSEGS | exact TFIB]. }
exact (DRV_MAINX sp rdraw brk mb (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd)
h ch E R FULL model _ Hsp Hbrk Hfit Hinp Hlau Hceil Hch SP0 HC HE HM).
Qed.
End d.
End b.
