(* Modified by Theorem Labs, 2026-10: adapted from lib/A/GrantTop.v for image B (fuzz_grant.asan-ubsan). *)
(* The closing file of libreac/fuzz_grant's ASan+UBSan build (image B, fuzz_grant.asan-ubsan, bin sha256
   fde52226dc48): the two statements `Statements.asan_ubsan_agrees` and `Statements.asan_ubsan_halts`, with no
   hypothesis left. This file proves no function: it composes the walks (each proved on its branch) and the B core.

   The chain, each link proved in its owner's file:
     GrantBClose.tb_LLVMFuzzerTestOneInput_holds_B  (lib/B/Prog/GrantBClose.v) -- image B's entry contract, composed
       bottom-up from the proved walks of lib/B/Prog, over the runtime and image facts RT_* / IMG_* and three facts of
       the runtime record, each a Section hypothesis there;
     GrantBTFIB.grant_TFIB_TB_of_lib               (lib/B/Prog/GrantBTFIB.v) -- the driver and the start-up over that
       contract, giving GrantTFIBB.TFIB_TB, over the same facts and the B core's statements, each a Section variable
       or hypothesis there;
     AsanUbsanTop.grant_asan_ubsan_agrees_of_tfib / grant_asan_ubsan_halts_of_tfib (lib/B/AsanUbsanTop.v) -- the two
       statements from TFIB_TB.

   Every Section variable and hypothesis of GrantBTFIB.v is instantiated here at image B's concrete runtime record
   GrantB (lib/B/YD2l.v:16) and image instance PI_grant (lib/B/Prog/GrantImg.v:152), and discharged by a theorem:
     B, tfib_K_B, xst_B, est_B          GrantB, YE2k.tfib_K, YD1k.xst, YD1k.est (the B core's values)
     the statement forms <A form>_B     the B core's relocated definitions (YF0m GrantSyms, YD1i, YD1w, YD1x)
     RT_* / IMG_* / H_*_B               lib/B/GrantBCloseInst.v grantB_* (the B twin of lib/A/Prog/GrantClose.v)
     H_tfib_AIL                          YD1u.tfib_AIL                 (A: AD1u.v:43)
     H_GrantB_syms                       YD2l.GrantB_syms              (A: AD2l.v:73)
     H_tfib_AICPY / H_tfib_ARDCHK        YD2m.tfib_AICPY / tfib_ARDCHK (A: AD2m.v:17 / :22)
     H_tfib_xst_frame                    YD1k.tfib_xst_frame           (A: AD1k.v:133)
     H_tfib_printf_first / _next         YD1o.tfib_printf_first / _next (A: AD1o.v:244 / :280)
     H_tfib_est_img / _frame             YD1k.tfib_est_img / _frame    (A: AD1k.v:114 / :116)
     H_tfib_fwrite_site / _refused_site  YD1k.tfib_fwrite_site / tfib_refused_site (A: AD1k.v:282 / :323)
     H_tfib_fprintf_*_site               YD1l.tfib_fprintf_open_site / _rderr_site / _usage_site (A: AD1l.v:147-157)
     H_tfib_exit_site                    YD1j.tfib_exit_site           (A: AD1j.v:123)
     H_tfib_srealizesX                   YD1q.tfib_srealizesX          (A: AD1q.v:170, Section d)
   (AF0w.v / AF0q.v's malloc and free realizers, A's AGrantT.v:43-44, are GrantBTFIB.v's RT_MALLOC / RT_FREE at fx0:
   GrantBCloseInst.v grantB_MALLOC / grantB_FREE, from YF0w.tfib_amalloc_realizes / YF0q.afree_realizes_closed.)

   THE SINK INSTANCE IS EXPLICIT (image A's rule, lib/A/GrantTop.v). lib/B/AsanUbsanTop.v loads lib/A/AsanTop.v, which
   loads the plain build's lib/Reusable/YI5b.v (`#[global] Instance src0_sink_head`, the PLAIN build's output head) and
   lib/Reusable/YI5c.v (`src0_sink`). Both hints are removed below; image B's own head is GrantBClose.grantB_sink_head
   (ofl_head 0x5f9008), and every part named here that takes SK is stated at it (GrantBClose.v and GrantBTFIB.v name
   `(SK := grantB_sink_head)`; the B core's YE2k.tfib_sink_head is the same record, ofl_head 0x5f9008).
   `sk_probe_is_asan_ubsan` shows what a bare `sink_head` resolves to here. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_grant Require Statements.
From OSSVerify.libreac.fuzz_grant.images Require AsanUbsan.
(* The import block of lib/B/Prog/GrantBTFIB.v, whose Section b this file instantiates, and the B core's files. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YN3g.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YE00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YE01 YC5d YCbp.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaStep PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require Import GrantShape.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame GrantRo GrantImg GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YB1v YF0m YD2l.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require
YE2k YD1u YD1i YD1k YD1o YD1l YD1j YD2m YD1w YD1x YD1q YCfn YCeg.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require GrantTFIBB AsanUbsanTop GrantBCloseInst.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require GrantBClose GrantBTFIB.
Import ListNotations.
Open Scope Z_scope.

(* The guard: the plain build's sink hints are out of the way, so no `{SK}` of a walk or of a contract can be filled
   with the plain build's head. *)
#[local] Remove Hints YI5b.src0_sink_head : typeclass_instances.
#[local] Remove Hints YI5c.src0_sink : typeclass_instances.
#[local] Existing Instance GrantBClose.grantB_sink_head.

(* What a bare `sink_head` resolves to in this file: image B's own head. *)
Definition sk_probe : YI16.sink_head := _.
Lemma sk_probe_is_asan_ubsan : sk_probe = GrantBClose.grantB_sink_head.
Proof. reflexivity. Qed.

(* The machine parameters the B core's driver statements are stated at (GrantBTFIB.v:307-308). *)
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance grant_shape.

(* ---- the B core's facts, each at GrantB, in the form GrantBTFIB.v's Section b takes it ------------------------- *)
(* H_tfib_AIL: the sink's laws at image B (A: AD1u.v:43). *)
Lemma grantB_tfib_AIL : asink_img_laws (SK := GrantBClose.grantB_sink_head) GrantTFIBB.grantsegsB0 GrantB YE2k.tfib_K.
Proof. exact (YD1u.tfib_AIL GrantB GrantB_syms). Qed.

(* H_tfib_AICPY / H_tfib_ARDCHK: the memcpy wrapper and the read interceptor's check (A: AD2m.v:17, :22). *)
Lemma grantB_tfib_AICPY : forall rc : YM05.RunCeil,
  aintrin_realizes (fx := YK11.fx0) (rc := rc) GrantTFIBB.grantsegsB0 GrantB OCpy (pc_wrap_memcpy (as_code GrantB)).
Proof. intros rc. exact (YD2m.tfib_AICPY GrantB GrantB_syms). Qed.
Lemma grantB_tfib_ARDCHK : forall rc : YM05.RunCeil, YD1i.aread_check_stmt (fx := YK11.fx0) (rc := rc) GrantB.
Proof. intros rc. exact (YD2m.tfib_ARDCHK GrantB GrantB_syms). Qed.

(* H_tfib_printf_first / _next (A: AD1o.v:244, :280). *)
Lemma grantB_tfib_printf_first : forall rc : YM05.RunCeil,
  YD1w.printf_first_tfa (fx := YK11.fx0) (rc := rc) GrantB YD1k.xst.
Proof. intros rc. exact (YD1o.tfib_printf_first GrantB GrantB_syms GrantBCloseInst.grantB_LAWS GrantB_syms). Qed.
Lemma grantB_tfib_printf_next : forall rc : YM05.RunCeil,
  YD1w.printf_next_tfa (fx := YK11.fx0) (rc := rc) GrantB YD1k.xst.
Proof. intros rc. exact (YD1o.tfib_printf_next GrantB GrantB_syms GrantBCloseInst.grantB_LAWS GrantB_syms). Qed.

(* H_tfib_fwrite_site / H_tfib_refused_site (A: AD1k.v:282, :323). *)
Lemma grantB_tfib_fwrite_site : forall rc : YM05.RunCeil,
  YD1x.fwrite_site_tfa (fx := YK11.fx0) (rc := rc) GrantB YD1k.est.
Proof. intros rc. exact (YD1k.tfib_fwrite_site GrantB GrantB_syms GrantBCloseInst.grantB_LAWS). Qed.
Lemma grantB_tfib_refused_site : forall rc : YM05.RunCeil,
  YD1x.refused_site_tfa (fx := YK11.fx0) (rc := rc) GrantB YD1k.est.
Proof. intros rc. exact (YD1k.tfib_refused_site GrantB GrantB_syms GrantBCloseInst.grantB_LAWS GrantB_syms). Qed.

(* H_tfib_fprintf_*_site: the three fprintf sites at image B's format strings 0x1d6e7, 0x1d6fc, 0x1583c
   (A: AD1l.v:147, :152, :157). *)
Lemma grantB_tfib_fprintf_open_site : forall rc : YM05.RunCeil,
  YD1x.fprintf_s_site_tfa (fx := YK11.fx0) (rc := rc) GrantB YD1k.est GrantBTFIB.FMT_OPEN_B
    (YO05.strB "cli: cannot open "%string) YO05.nlB.
Proof. intros rc. exact (YD1l.tfib_fprintf_open_site GrantB GrantB_syms GrantBCloseInst.grantB_LAWS GrantB_syms). Qed.
Lemma grantB_tfib_fprintf_rderr_site : forall rc : YM05.RunCeil,
  YD1x.fprintf_s_site_tfa (fx := YK11.fx0) (rc := rc) GrantB YD1k.est GrantBTFIB.FMT_RDERR_B
    (YO05.strB "cli: read error on "%string) YO05.nlB.
Proof. intros rc. exact (YD1l.tfib_fprintf_rderr_site GrantB GrantB_syms GrantBCloseInst.grantB_LAWS GrantB_syms). Qed.
Lemma grantB_tfib_fprintf_usage_site : forall rc : YM05.RunCeil,
  YD1x.fprintf_s_site_tfa (fx := YK11.fx0) (rc := rc) GrantB YD1k.est GrantBTFIB.FMT_USAGE_B
    (YO05.strB "usage: "%string) (YO05.strB " INPUT"%string ++ YO05.nlB).
Proof. intros rc. exact (YD1l.tfib_fprintf_usage_site GrantB GrantB_syms GrantBCloseInst.grantB_LAWS GrantB_syms). Qed.

(* H_tfib_exit_site: the exit path, with the module destructor and __do_fini inside its proof (A: AD1j.v:123). *)
Lemma grantB_tfib_exit_site : forall rc : YM05.RunCeil,
  YD1x.exit_site_tfa (fx := YK11.fx0) (rc := rc) GrantB YD1k.est YD1k.xst.
Proof. intros rc. exact (YD1j.tfib_exit_site GrantB GrantB_syms GrantBCloseInst.grantB_LAWS). Qed.

(* H_tfib_srealizesX: the driver and the start-up over the slot, at every run ceiling (A: AD1q.v:170, Section d).
   GrantBTFIB.v's slot tfib_lib_contract_x_allB at YE2k.tfib_K is the B core's YCfn.tfib_lib_contract_x_all (the same
   numbers: entry 0x80a3c, return 0x80938, empty buffer 0x5d7fe0, stack 32768, events 2000, live 2 ^ 33), and
   GrantBTFIB.v's in_ro_tfa_B is YCeg.in_ro_tfa; both by conversion. *)
Lemma grantB_tfib_srealizesX : forall (rc : YM05.RunCeil),
  GrantSyms GrantB ->
  amalloc_realizes (fx := YK11.fx0) (rc := rc) GrantTFIBB.grantsegsB0 GrantB ->
  afree_realizes (fx := YK11.fx0) (rc := rc) GrantTFIBB.grantsegsB0 GrantB ->
  aintrin_realizes (fx := YK11.fx0) (rc := rc) GrantTFIBB.grantsegsB0 GrantB OCpy (pc_wrap_memcpy (as_code GrantB)) ->
  YD1i.aread_check_stmt (fx := YK11.fx0) (rc := rc) GrantB ->
  forall (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z),
  (forall S m, mo_ok MT S m) ->
  (forall a, RLO <= a < RHI -> GrantBTFIB.in_ro_tfa_B a) ->
  GrantBTFIB.tfib_lib_contract_x_allB (rc := rc) (LS := grant_shape) YE2k.tfib_K GrantB MT XM_LIB XN_LIB RLO RHI ->
  forall xst : nat -> (word -> bool) -> (word -> option byte) -> Prop,
  YD1w.xst_frame_tfa xst -> YD1w.printf_first_tfa (fx := YK11.fx0) (rc := rc) GrantB xst ->
  YD1w.printf_next_tfa (fx := YK11.fx0) (rc := rc) GrantB xst ->
  forall est : (word -> bool) -> (word -> option byte) -> Prop,
  YD1x.est_img_tfa est -> YD1x.est_frame_tfa est ->
  YD1x.fwrite_site_tfa (fx := YK11.fx0) (rc := rc) GrantB est -> YD1x.refused_site_tfa (fx := YK11.fx0) (rc := rc) GrantB est ->
  YD1x.fprintf_s_site_tfa (fx := YK11.fx0) (rc := rc) GrantB est GrantBTFIB.FMT_OPEN_B (YO05.strB "cli: cannot open "%string) YO05.nlB ->
  YD1x.fprintf_s_site_tfa (fx := YK11.fx0) (rc := rc) GrantB est GrantBTFIB.FMT_RDERR_B (YO05.strB "cli: read error on "%string) YO05.nlB ->
  YD1x.fprintf_s_site_tfa (fx := YK11.fx0) (rc := rc) GrantB est GrantBTFIB.FMT_USAGE_B (YO05.strB "usage: "%string)
    (YO05.strB " INPUT"%string ++ YO05.nlB) ->
  YD1x.exit_site_tfa (fx := YK11.fx0) (rc := rc) GrantB est xst ->
  forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
  valid_sp sp -> valid_brk GrantTFIBB.grantsegsB0 brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  @YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
  srealizes GrantTFIBB.grantsegsB0
    (init_config GrantTFIBB.grantsegsB0 AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mb rdraw target_alloc_limit inp)
    (SPECX inp).
Proof.
intros rc HB AM AF AI ARD MT XM XN RLO RHI MTF ROIN LIBX xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS.
exact (@YD1q.tfib_srealizesX rc GrantB HB AM AF AI ARD MT XM XN RLO RHI MTF ROIN LIBX xst XFR PF1 PFN est ESTI ESTF
  FWS RFS FPO FPR FPU EXS).
Qed.

(* ---- the chain, with no hypothesis -------------------------------------------------------------------------------- *)
(* A Section that declares no variable: `Print Assumptions` inside it would list any Section variable in scope, and
   `About` / `Check` after its `End` would show any that became an argument. *)
Section asan_ubsan.

(* TFIB_TB (lib/B/GrantTFIBB.v:19): GrantBTFIB.v's grant_TFIB_TB_of_lib, every Section variable and hypothesis of it
   instantiated at GrantB and discharged by the theorem named in this file's header. *)
Theorem grant_TFIB_TB_of_parts_B : GrantTFIBB.TFIB_TB.
Proof.
eapply (GrantBTFIB.grant_TFIB_TB_of_lib GrantB YE2k.tfib_K YD1k.xst YD1k.est GrantSyms
  (fun fx rc B => YD1i.aread_check_stmt (fx := fx) (rc := rc) B)
  YD1w.xst_frame_tfa
  (fun fx rc B xst => YD1w.printf_first_tfa (fx := fx) (rc := rc) B xst)
  (fun fx rc B xst => YD1w.printf_next_tfa (fx := fx) (rc := rc) B xst)
  YD1x.est_img_tfa YD1x.est_frame_tfa
  (fun fx rc B est => YD1x.fwrite_site_tfa (fx := fx) (rc := rc) B est)
  (fun fx rc B est fmt l1 l2 => YD1x.fprintf_s_site_tfa (fx := fx) (rc := rc) B est fmt l1 l2)
  (fun fx rc B est => YD1x.refused_site_tfa (fx := fx) (rc := rc) B est)
  (fun fx rc B est xst => YD1x.exit_site_tfa (fx := fx) (rc := rc) B est xst)).
all: first
  [ exact (fun rc => GrantBCloseInst.grantB_PALIB (rc := rc))
  | exact (fun rc => GrantBCloseInst.grantB_PALIBF (rc := rc))
  | exact GrantBCloseInst.grantB_ML
  | exact GrantBCloseInst.grantB_SMP
  | exact (fun rc => GrantBCloseInst.grantB_ASF (rc := rc))
  | exact (fun rc => GrantBCloseInst.grantB_FFL (rc := rc))
  | exact (fun rc => GrantBCloseInst.grantB_TP_FS (rc := rc))
  | exact (fun rc fx => GrantBCloseInst.grantB_MALLOC (fx := fx) (rc := rc))
  | exact (fun rc fx => GrantBCloseInst.grantB_FREE (fx := fx) (rc := rc))
  | exact (fun rc fx => GrantBCloseInst.grantB_MEMCPY (fx := fx) (rc := rc))
  | exact (fun rc fx => GrantBCloseInst.grantB_MEMSET (fx := fx) (rc := rc))
  | exact (fun rc fx => GrantBCloseInst.grantB_BCMP (fx := fx) (rc := rc))
  | exact (fun rc fx => GrantBCloseInst.grantB_SM0 (fx := fx) (rc := rc))
  | exact (fun rc fx => GrantBCloseInst.grantB_SM1 (fx := fx) (rc := rc))
  | exact (fun rc fx => GrantBCloseInst.grantB_SM2 (fx := fx) (rc := rc))
  | exact (fun rc fx => GrantBCloseInst.grantB_SM4 (fx := fx) (rc := rc))
  | exact (fun rc fx => GrantBCloseInst.grantB_SM6 (fx := fx) (rc := rc))
  | exact (fun rc fx => GrantBCloseInst.grantB_SF6 (fx := fx) (rc := rc))
  | exact (fun rc fx => GrantBCloseInst.grantB_SS00 (fx := fx) (rc := rc))
  | exact (fun rc fx => GrantBCloseInst.grantB_SSF5 (fx := fx) (rc := rc))
  | exact (fun rc fx => GrantBCloseInst.grantB_SSF8 (fx := fx) (rc := rc))
  | exact (fun rc => GrantBCloseInst.grantB_IMGSH (rc := rc))
  | exact (fun rc => GrantBCloseInst.grantB_GLOBS (rc := rc))
  | exact (fun rc => GrantBCloseInst.grantB_IMG_CTRL_ROW (rc := rc))
  | exact (fun rc => GrantBCloseInst.grantB_IMG_CTRL_ROW_FIN (rc := rc))
  | exact (fun rc => GrantBCloseInst.grantB_IMG_CTRL_LAY_JT (rc := rc))
  | exact (fun rc => GrantBCloseInst.grantB_IMG_CTRL_STAMP_TM (rc := rc))
  | exact (fun rc => GrantBCloseInst.grantB_IMG_BGS_ROWS (rc := rc))
  | exact (fun rc => GrantBCloseInst.grantB_IMG_reac_ctrl_parse (rc := rc))
  | exact (fun rc => GrantBCloseInst.grantB_IMG_check_groupa (rc := rc))
  | exact (fun rc => GrantBCloseInst.grantB_IMG_LLVMF_SWEEP (rc := rc))
  | exact (fun rc => GrantBCloseInst.grantB_IMG_NEXT_DIV3 (rc := rc))
  | exact GrantBCloseInst.grantB_universe
  | exact GrantBCloseInst.grantB_malloc_ra0
  | exact GrantBCloseInst.grantB_free_ra0
  | exact grantB_tfib_AIL
  | exact GrantB_syms
  | exact grantB_tfib_AICPY
  | exact grantB_tfib_ARDCHK
  | exact YD1k.tfib_xst_frame
  | exact grantB_tfib_printf_first
  | exact grantB_tfib_printf_next
  | exact YD1k.tfib_est_img
  | exact YD1k.tfib_est_frame
  | exact grantB_tfib_fwrite_site
  | exact grantB_tfib_refused_site
  | exact grantB_tfib_fprintf_open_site
  | exact grantB_tfib_fprintf_rderr_site
  | exact grantB_tfib_fprintf_usage_site
  | exact grantB_tfib_exit_site
  | exact grantB_tfib_srealizesX ].
Qed.

(* The two statements of libreac/fuzz_grant's ASan+UBSan build (lib/B/AsanUbsanTop.v:30 and :46). *)
Theorem grant_asan_ubsan_agrees_of_parts : Statements.asan_ubsan_agrees.
Proof. exact (AsanUbsanTop.grant_asan_ubsan_agrees_of_tfib grant_TFIB_TB_of_parts_B). Qed.
Theorem grant_asan_ubsan_halts_of_parts : Statements.asan_ubsan_halts.
Proof. exact (AsanUbsanTop.grant_asan_ubsan_halts_of_tfib grant_TFIB_TB_of_parts_B). Qed.

End asan_ubsan.
