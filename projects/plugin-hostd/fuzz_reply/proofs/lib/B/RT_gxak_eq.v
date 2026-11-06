(* Image B twin of lib/A/RT_gxak_eq.v at 2c1f180a413 (sha256 9be41bcf007f; internal record): module paths lib.A -> lib.B; image-generic, no numeral. *) (* The keep-FP twin (lib/CJ/RL/{GK,GXK,GXAK}, provenance/keepfx/README.md) against the released GXA vocabulary, one
   lemma for each twin name that the keep-fx chain (RT_gxa_inst_k.v, RT_pf_*_k.v) uses in place of a released name.

   VERBATIM COPIES (the twin's text is the released text; the lemma is `reflexivity`, so a drift of either side breaks
   THIS file's build and not a consumer's): vf_guard, vsnprintf_ready, vf_ready_a, vf_snf_guard, snf_out_ready,
   pc_guard, args_ok, arg_ok, va_area, OUT_snf, OUTFP_snf, GLOBALS_TOP, VF_DEPTH, K_SN_WRITE, snf_file,
   PROGAT_CODE_vfprintf, PROGAT_CODE_vsnprintf, VSN_DEPTH.  The RT_pf_*_k.v proofs rewrite with these where a
   statement of one side meets a premise of the other.

   STRENGTHENED BY THE TWIN (keepfx.patch items 1-4: the post keeps the FP state, the frm0 premise is gone), so the
   lemma is the implication twin -> released, not an equality: pop_arg_post / pop_arg_contract,
   pop_arg_x_post / pop_arg_x_contract, vfprintf_snf_post / vfprintf_guarded_stmt, vsnprintf_x_post /
   vsnprintf_x_stmt.  A post implication takes the released statement's `frm0 fc` where the released post asks
   `frm0 fc'`.

   Every lemma is stated for all instances: no two instances are compared here. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require Import SFModel Arr ITree Nodes PropExec MState Mem Exec Frame Cells Step FP.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require Import RStep.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G.G_pop_arg.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GK.G_pop_arg.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_pop_arg_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXK.G_pop_arg_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_printf_core_common.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXK.G_printf_core_common.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_vfprintf_snf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXK.G_vfprintf_snf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.VfprintfCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXAK.VfprintfCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_printf_core_common.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXAK.G_printf_core_common.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_printf_snfsink.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXAK.G_printf_snfsink.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_vfprintf_snf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXAK.G_vfprintf_snf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_vsnprintf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXAK.G_vsnprintf.
Import ListNotations.
Open Scope Z_scope.
Local Abbreviation mem := (word -> option byte).

Module GPA := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G.G_pop_arg.
Module GPAK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GK.G_pop_arg.
Module GPX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_pop_arg_x.
Module GPXK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXK.G_pop_arg_x.
Module GIF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module GIFK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXK.G_printf_core_common.G_printf_iface.
Module GVF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_vfprintf_snf.
Module GVFK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXK.G_vfprintf_snf.
Module VFC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.VfprintfCall.
Module VFCK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXAK.VfprintfCall.
Module AIF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
Module AIFK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXAK.G_printf_core_common.G_printf_iface.
Module ASK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_printf_snfsink.
Module ASKK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXAK.G_printf_snfsink.
Module AVF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_vfprintf_snf.
Module AVFK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXAK.G_vfprintf_snf.
Module GVS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_vsnprintf.
Module GVSK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXAK.G_vsnprintf.

(* ======================= verbatim copies: equal by reflexivity ======================= *)

(* GXAK/VfprintfCall.v *)
Lemma vf_guard_eq : VFCK.vf_guard = VFC.vf_guard.
Proof. reflexivity. Qed.

Lemma vsnprintf_ready_eq : @VFCK.vsnprintf_ready = @VFC.vsnprintf_ready.
Proof. reflexivity. Qed.

(* GXAK/G_vfprintf_snf.v: the guard of the closed vfprintf body (RT_pf_chain_k.v fr_vfb_k) and its parts *)
Lemma vf_ready_a_eq : @AVFK.vf_ready_a = @AVF.vf_ready_a.
Proof. reflexivity. Qed.

Lemma vf_snf_guard_eq : @AVFK.vf_snf_guard = @AVF.vf_snf_guard.
Proof. reflexivity. Qed.

(* GXAK/G_printf_snfsink.v *)
Lemma snf_out_ready_eq : @ASKK.snf_out_ready = @ASK.snf_out_ready.
Proof. reflexivity. Qed.

(* GXAK/G_printf_core_common.v, module G_printf_iface *)
Lemma pc_guard_eq : @AIFK.pc_guard = @AIF.pc_guard.
Proof. reflexivity. Qed.

(* GXK/G_printf_core_common.v, module G_printf_iface *)
Lemma args_ok_eq : @GIFK.args_ok = @GIF.args_ok.
Proof. reflexivity. Qed.

Lemma arg_ok_eq : @GIFK.arg_ok = @GIF.arg_ok.
Proof. reflexivity. Qed.

Lemma OUT_snf_eq : GIFK.OUT_snf = GIF.OUT_snf.
Proof. reflexivity. Qed.

Lemma OUTFP_snf_eq : GIFK.OUTFP_snf = GIF.OUTFP_snf.
Proof. reflexivity. Qed.

Lemma GLOBALS_TOP_eq : @GIFK.GLOBALS_TOP = @GIF.GLOBALS_TOP.
Proof. reflexivity. Qed.

Lemma VF_DEPTH_eq : GIFK.VF_DEPTH = GIF.VF_DEPTH.
Proof. reflexivity. Qed.

Lemma K_SN_WRITE_eq : GIFK.K_SN_WRITE = GIF.K_SN_WRITE.
Proof. reflexivity. Qed.

(* GXK/G_vfprintf_snf.v *)
Lemma snf_file_eq : @GVFK.snf_file = @GVF.snf_file.
Proof. reflexivity. Qed.

Lemma PROGAT_CODE_vfprintf_eq : GVFK.PROGAT_CODE_vfprintf = GVF.PROGAT_CODE_vfprintf.
Proof. reflexivity. Qed.

(* GXAK/G_vsnprintf.v *)
Lemma PROGAT_CODE_vsnprintf_eq : GVSK.PROGAT_CODE_vsnprintf = GVS.PROGAT_CODE_vsnprintf.
Proof. reflexivity. Qed.

Lemma VSN_DEPTH_eq : GVSK.VSN_DEPTH = GVS.VSN_DEPTH.
Proof. reflexivity. Qed.

(* GK/G_pop_arg.v *)
Lemma va_area_eq : @GPAK.va_area = @GPA.va_area.
Proof. reflexivity. Qed.

(* ======================= strengthened by the twin: twin -> released ======================= *)

Section Img.
Context {IMG : RImg}.

(* GK/G_pop_arg.v: Ft = F for every type but T_DBL, which keeps the released clause *)
Lemma pop_arg_post_x : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ARG AP VA slots i ty slot y m ms,
  @GPAK.pop_arg_post IMG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ARG AP VA slots i ty slot y m ms ->
  @GPA.pop_arg_post IMG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ARG AP VA slots i ty slot y m ms.
Proof.
  intros until ms. unfold GPAK.pop_arg_post, GPA.pop_arg_post. cbv beta.
  intros (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & Ft & m' & E & MU & WM & MI & ST
          & APC & ARGC & VAA & FP).
  exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, Ft, m'.
  split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact APC|]. split; [exact ARGC|]. split; [exact VAA|].
  revert FP. lazymatch goal with |- (if ?c then _ else _) -> _ => destruct c end.
  - intros FP. exact FP.
  - intros ->. intros k _. reflexivity.
Qed.

Lemma pop_arg_contract_x : @GPAK.pop_arg_contract IMG -> @GPA.pop_arg_contract IMG.
Proof.
  intros K. unfold GPA.pop_arg_contract. intros until y. intros.
  eapply evt_mono.
  - apply (K ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m VA slots i ty slot x y); assumption.
  - intros ms P. eapply pop_arg_post_x. exact P.
Qed.

(* GXK/G_pop_arg_x.v: Ft = F *)
Lemma pop_arg_x_post_x : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ARG AP VA slots i slot y m ms,
  @GPXK.pop_arg_x_post IMG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ARG AP VA slots i slot y m ms ->
  @GPX.pop_arg_x_post IMG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ARG AP VA slots i slot y m ms.
Proof.
  intros until ms. unfold GPXK.pop_arg_x_post, GPX.pop_arg_x_post. cbv beta.
  intros (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & Ft & m' & E & MU & WM & MI & ST
          & APC & ARGC & VAA & ->).
  exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F, m'.
  split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact APC|]. split; [exact ARGC|]. split; [exact VAA|].
  intros k _. reflexivity.
Qed.

Lemma pop_arg_x_contract_x : @GPXK.pop_arg_x_contract IMG -> @GPX.pop_arg_x_contract IMG.
Proof.
  intros K. unfold GPX.pop_arg_x_contract. intros until y. intros.
  eapply evt_mono.
  - apply (K ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m VA slots i ty slot x y); assumption.
  - intros ms P. eapply pop_arg_x_post_x. exact P.
Qed.

(* GXK/G_vfprintf_snf.v: Ft = F /\ fc' = fc in place of frm0 fc' /\ (every f-register except f10 kept) *)
Lemma vfprintf_snf_post_x : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp CK D N dn junkd r o lo canary
    m ms,
  frm0 fc ->
  @GVFK.vfprintf_snf_post IMG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp CK D N dn junkd r o lo canary m ms ->
  @GVF.vfprintf_snf_post IMG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D N dn junkd r o lo canary m ms.
Proof.
  intros until ms. intros FR. unfold GVFK.vfprintf_snf_post, GVF.vfprintf_snf_post. cbv beta.
  intros (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & Ft & fc' & fjunk & m' & E & MU & WM & MI
          & -> & -> & REST).
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F, fc, fjunk, m'.
  split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FR|].
  split; [intros k _; reflexivity | exact REST].
Qed.

(* GXAK/VfprintfCall.v: no frm0 premise, the post above *)
Lemma vfprintf_guarded_stmt_x : forall vf : VFC.vf_guard,
  @VFCK.vfprintf_guarded_stmt IMG vf -> @VFC.vfprintf_guarded_stmt IMG vf.
Proof.
  intros vf K. unfold VFC.vfprintf_guarded_stmt. intros until o. cbv zeta. intros.
  pose proof (K ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m Fp CK D N OM bufp A VA dn junkd fmt slots args lo canary r o) as K'.
  cbv zeta in K'.
  match goal with FR : frm0 fc |- _ =>
    eapply evt_mono; [ apply K'; assumption | intros ms P; eapply vfprintf_snf_post_x; [exact FR | exact P] ]
  end.
Qed.

(* GXAK/G_vsnprintf.v: Ft = F /\ fc' = fc in place of frm0 fc' /\ (every f-register except f10 kept) *)
Lemma vsnprintf_x_post_x : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D dn txt r lo canary m ms,
  frm0 fc ->
  @GVSK.vsnprintf_x_post IMG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D dn txt r lo canary m ms ->
  @GVS.vsnprintf_x_post IMG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn txt r lo canary m ms.
Proof.
  intros until ms. intros FR. unfold GVSK.vsnprintf_x_post, GVS.vsnprintf_x_post. cbv beta.
  intros (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & Ft & fc' & m' & E & MU & WM & MI
          & -> & -> & REST).
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F, fc, m'.
  split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FR|].
  split; [intros k _; reflexivity | exact REST].
Qed.

(* GXAK/G_vsnprintf.v: no frm0 premise, the post above *)
Lemma vsnprintf_x_stmt_x : forall (set_ready : mem -> Z -> Z -> Z -> Prop) (vf : VFC.vf_guard),
  @GVSK.vsnprintf_x_stmt IMG set_ready vf -> @GVS.vsnprintf_x_stmt IMG set_ready vf.
Proof.
  intros set_ready vf K. unfold GVS.vsnprintf_x_stmt. intros until o. cbv zeta. intros.
  pose proof (K ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m D n A VA dn junkd fmt slots args lo canary r o) as K'.
  cbv zeta in K'.
  match goal with FR : frm0 fc |- _ =>
    eapply evt_mono; [ apply K'; assumption | intros ms P; eapply vsnprintf_x_post_x; [exact FR | exact P] ]
  end.
Qed.

End Img.
