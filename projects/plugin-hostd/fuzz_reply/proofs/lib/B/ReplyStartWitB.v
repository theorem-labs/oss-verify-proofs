(* Image B's start witnesses of the cf conversion at init (Reusable/YGcfNilInit.v ARcf_nil_init), which the cf driver
   (B/YD1pcf.v tfib_drv_main) names as HSTART / HSTART_PF:
   - start_cells_ho_t / start_pf_ho_t: the two premises' statements, generic in the CfImg, at the start-up hand-off:
     for every hand-off state h of YB01.v with cs_ok, at a world W whose hidden set is the hand-off's (YD2i.H1) and
     the start-up memory FULL, the start witness YG0ncf.start_cells_cf (given AR at init_state) and
     YG0ncf.start_pf_cf hold. They read the hand-off because the error buffer's five cells and Printf's two cells are
     not const cells of AR (the walks write them);
   - start_cells_B: start_cells_ho_t at CfImg_B, from B/ReplyImg_startcells.v start_exh_B (the 31 exhausted bytes, from
     AR) and start_errb_B (the error buffer's five cells, from the hand-off), put in the layer's form by
     B/YGcfInstBase.v exh_cell_cf_init / errb_cells_cf_init;
   - start_pf_B: start_pf_ho_t at CfImg_B, from B/ReplyImg_startcells.v start_pf_cells_B.
   The image rows are B/ReplyImgRowsB.v exh_off_B and errb_obj_owned_B (used directly at the instance).
   rule 24: no function proved (kind: start-up fact). *)
(* Modified by Theorem Labs, 2026-10-30 (a Theorem Labs lane M, CfInstHit): the start witness reads the hand-off
   (start_cells_ho_t), and start_pf_ho_t / start_pf_B are new (field round 3). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YP09 YK00 YK04 YA0i YA0n YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB12 YB1h YB13 YB01r.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0r YG0b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YD1h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD1g YD2i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0d YI04 YI00 YE00 YA0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YB1v YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05 YK04 YA0n YG00 YG01 YG0f YG0v YG0n YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YF0m YF0x CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0ncf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l ReplyImg_startcells YGcfInstBase.
Import ListNotations.
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Open Scope Z_scope.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
(* HSTART's statement: the start witness of the two machine cells at the hand-off world, given AR there.
   LPS 727298f3: over the start of B/YD1q.v's drv_mainX_stmt (YB01r's hand-off state of the run's own CONFIG_RSEQ
   flag, the invariant abstract with SINV_sp0, the mmap base and the launch premise), as A/AD1pcf.v's handoff_cov (B/YD1pcf.v). *)
#[local] Notation ARGH sp rdraw inp := (YA02.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp)
  (in_uid inp) (in_gid inp) (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp)
  (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)).
Definition start_cells_ho_t (B : asyms) : Prop :=
  forall (sp : word) (rdraw : EntryDraw) (brk mbase : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env)
    (R : bvmap 5 word) (FULL : word -> option byte) (model : Model) (SINV : env -> (word -> option byte) -> Prop)
    (ly : alayout) (W : world TSEGS) (md : Model),
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
  HS_tfib_r (rseq_z (kb_rseq (in_kernel inp))) h = Some ch ->
  (forall E' M, SINV E' M -> uE E' e_sp0 = YA02.TOP sp + 8388608) ->
  cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp) SINV (ARGH sp rdraw inp) (in_fs inp) E ch R FULL model ->
  w_H W = YD2i.H1 sp rdraw inp ch E model ->
  AR TSEGS B ly YG00.init_state W FULL md ->
  start_cells_cf TSEGS B ly YG00.init_state W FULL.
(* HSTART_PF's statement: the start witness of Printf's two image cells at the hand-off world. *)
Definition start_pf_ho_t (B : asyms) : Prop :=
  forall (sp : word) (rdraw : EntryDraw) (brk mbase : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env)
    (R : bvmap 5 word) (FULL : word -> option byte) (model : Model) (SINV : env -> (word -> option byte) -> Prop)
    (ly : alayout) (W : world TSEGS),
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
  HS_tfib_r (rseq_z (kb_rseq (in_kernel inp))) h = Some ch ->
  (forall E' M, SINV E' M -> uE E' e_sp0 = YA02.TOP sp + 8388608) ->
  cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp) SINV (ARGH sp rdraw inp) (in_fs inp) E ch R FULL model ->
  w_H W = YD2i.H1 sp rdraw inp ch E model ->
  start_pf_cf TSEGS B ly W FULL.
End g.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* B/ReplyImg_startcells.v's Section e lemmas at these proofs' names, whatever subset each one takes: the
   specializations are written in each proof, where the names are bound (an Ltac body naming [sp] here, where no
   [sp] is bound, is refused). *)

Theorem start_cells_B : start_cells_ho_t (ci := CfImg_B) TfibB.
Proof.
intros sp rdraw brk mbase inp h ch E R FULL model SINV ly W md Hsp Hva Hve Hfit Hinp Hlau Hch SP0 HC HW HAR W' HW'. split.
- apply exh_cell_cf_init. intros c Hc. exact (start_exh_B TfibB ly YG00.init_state W FULL md HAR W' HW' c Hc).
- pose proof (@start_errb_B) as F.
  try specialize (F fx); try specialize (F sp); try specialize (F rdraw); try specialize (F brk);
  try specialize (F inp); try specialize (F Hsp); try specialize (F Hva); try specialize (F h); try specialize (F ch);
  try specialize (F E); try specialize (F R); try specialize (F FULL); try specialize (F model); try specialize (F Hch);
  try specialize (F SINV); try specialize (F SP0); try specialize (F HC); try specialize (F W); try specialize (F HW).
  specialize (F TfibB ly W' HW').
  rewrite Forall_forall in F. unfold errb_start_cells_B in F.
  apply errb_cells_cf_init; apply F; apply in_map_iff;
    [exists 0 | exists 16 | exists 32 | exists 40 | exists 48];
    (split; [first [reflexivity | f_equal; f_equal; lia] | cbn; tauto]).
Qed.

Theorem start_pf_B : start_pf_ho_t (ci := CfImg_B) TfibB.
Proof.
intros sp rdraw brk mbase inp h ch E R FULL model SINV ly W Hsp Hva Hve Hfit Hinp Hlau Hch SP0 HC HW W' HW'.
pose proof (@start_pf_cells_B) as F.
try specialize (F fx); try specialize (F sp); try specialize (F rdraw); try specialize (F brk);
  try specialize (F inp); try specialize (F Hsp); try specialize (F Hva); try specialize (F h); try specialize (F ch);
  try specialize (F E); try specialize (F R); try specialize (F FULL); try specialize (F model); try specialize (F Hch);
  try specialize (F SINV); try specialize (F SP0); try specialize (F HC); try specialize (F W); try specialize (F HW).
exact (F TfibB ly W' HW').
Qed.
End s.
