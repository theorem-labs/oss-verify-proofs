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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB12 YB1h YB13 YB01.
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
(* HSTART's statement: the start witness of the two machine cells at the hand-off world, given AR there. *)
Definition start_cells_ho_t (B : asyms) : Prop :=
  forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env)
    (R : bvmap 5 word) (FULL : word -> option byte) (model : Model) (ly : alayout) (W : world TSEGS) (md : Model),
  valid_sp sp -> valid_argv (in_argv inp) -> HS_tfib h = Some ch ->
  cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp)
    (YA02.SINV0 TSEGS TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
  w_H W = YD2i.H1 sp rdraw inp ch E model ->
  AR TSEGS B ly YG00.init_state W FULL md ->
  start_cells_cf TSEGS B ly YG00.init_state W FULL.
(* HSTART_PF's statement: the start witness of Printf's two image cells at the hand-off world. *)
Definition start_pf_ho_t (B : asyms) : Prop :=
  forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env)
    (R : bvmap 5 word) (FULL : word -> option byte) (model : Model) (ly : alayout) (W : world TSEGS),
  valid_sp sp -> valid_argv (in_argv inp) -> HS_tfib h = Some ch ->
  cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp)
    (YA02.SINV0 TSEGS TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
  w_H W = YD2i.H1 sp rdraw inp ch E model ->
  start_pf_cf TSEGS B ly W FULL.
End g.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem start_cells_B : start_cells_ho_t (ci := CfImg_B) TfibB.
Proof.
intros sp rdraw brk inp h ch E R FULL model ly W md Hsp Hva Hch HC HW HAR W' HW'. split.
- apply exh_cell_cf_init. intros c Hc. exact (start_exh_B TfibB ly YG00.init_state W FULL md HAR W' HW' c Hc).
- pose proof (start_errb_B sp rdraw brk inp Hsp Hva h ch E R FULL model Hch HC W HW TfibB ly W' HW') as F.
  rewrite Forall_forall in F. unfold errb_start_cells_B in F.
  apply errb_cells_cf_init; apply F; apply in_map_iff;
    [exists 0 | exists 16 | exists 32 | exists 40 | exists 48];
    (split; [first [reflexivity | f_equal; f_equal; lia] | cbn; tauto]).
Qed.

Theorem start_pf_B : start_pf_ho_t (ci := CfImg_B) TfibB.
Proof.
intros sp rdraw brk inp h ch E R FULL model ly W Hsp Hva Hch HC HW W' HW'.
exact (start_pf_cells_B sp rdraw brk inp Hsp Hva h ch E R FULL model Hch HC W HW TfibB ly W' HW').
Qed.
End s.
