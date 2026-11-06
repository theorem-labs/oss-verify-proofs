(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_disco.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02 YA00 YB12 YB1h YB01
YB1n YG0f YG00 YG01 YG0n YF0m YP0m YP09 YP0l YP08 YP03 YN3q YK04 YA0i YA0n YA0o YA0p
YB1v YD1h YD1g YD1f YD2i YDiscoWorldH8 YD1t YG0d YD1v YD1w YD2a YD26 YD22 YD1z YD2g
YD2c YD2d YD29 YD2e YD1r YD1x YD27 YCfl YD1i YD1n YG05 YG0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC5d YCfn YCeg YE2k YD1u YD1m YD2k.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YFrm0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
Lemma wr_has_nil : forall ch bs T, wr ch bs T [].
Proof. intros. unfold wr. apply t_emit_has_nil. Qed.
Lemma diag_has_nil : forall m fs, diag m fs [].
Proof. intros. unfold diag. apply wr_has_nil. Qed.
Lemma t_alt2_has_nil_l : forall A B, A [] -> t_alt2 A B [].
Proof. intros A B H. left. exact H. Qed.
#[local] Existing Instance YK11.fx0.
(* The start-up FP state has rounding mode 0 (fcsr = 0): the first call of the program part meets the
   contract's frm0 guard; later calls get it from the previous call's post. *)
Lemma frm0_fx0 : YFrm0.frm0 (@YK11.fp_csr YK11.fx0).
Proof. vm_compute. reflexivity. Qed.
Section b. Context {rc : YM05.RunCeil} {LS : lib_shape}.
Section c.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Let ARL : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let ML : model_laws (as_universe B) := model_laws_ok (as_universe B) (ts_universe B HB).
Hypothesis AMALLOC : amalloc_realizes tfibsegs B.
Hypothesis AFREE : forall fq : YK11.FPState, afree_realizes (fx := fq) tfibsegs B.
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : aread_check_stmt B.
Variables (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z).
Hypothesis MT_FREE : forall S m, mo_ok MT S m.
Hypothesis RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a.
Hypothesis LIBC : forall fq : YK11.FPState, YFrm0.frm0 (@YK11.fp_csr fq) -> tfib_lib_contract_x (fx := fq) B MT XM_LIB XN_LIB RLO RHI.
Let MSITE : malloc_site_tfa B := tfib_malloc_site B ML AMALLOC.
Let RCHK : read_check_tfa B := tfib_read_check B ARDCHK.
Let MCPY : memcpy_site_tfa B := tfib_memcpy_site B AICPY.
Let FREEa : forall fq : YK11.FPState, free_site_tfa (fx := fq) B := fun fq => tfib_free_site (fx := fq) B ML (AFREE fq).
Let FREENa : forall fq : YK11.FPState, free_null_site_tfa (fx := fq) B := fun fq => tfib_free_null_site (fx := fq) B ML (AFREE fq).
Let LIBa : forall fq : YK11.FPState, YFrm0.frm0 (@YK11.fp_csr fq) -> lib_site_x (fx := fq) B := fun fq HF => tfib_lib_site_x (fx := fq) B MT XM_LIB XN_LIB RLO RHI MT_FREE RO_IN (LIBC fq HF).
Let FREE : free_site_tfa B := FREEa _.
Let FREEN : free_null_site_tfa B := FREENa _.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis PF1 : forall fq : YK11.FPState, printf_first_tfa (fx := fq) B xst.
Hypothesis PFN : forall fq : YK11.FPState, printf_next_tfa (fx := fq) B xst.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis ESTI : est_img_tfa est.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis FWS : fwrite_site_tfa B est.
Hypothesis RFS : refused_site_tfa B est.
Hypothesis FPO : fprintf_s_site_tfa B est 0x1d868 (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est 0x1d87d (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est 0x1583b (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS : forall fq : YK11.FPState, exit_site_tfa (fx := fq) B est xst.
Let RDERR : rderr_leaf_tfa B := tfib_rderr_leaf B HB ARL xst est XFR ESTF FPR (EXS _).
Let REFUSED : refused_leaf_tfa B := tfib_refused_leaf B HB ARL xst est XFR ESTF RFS (EXS _).
Let SHORT : short_leaf_tfa B := tfib_short_leaf B HB ARL ML xst est XFR ESTF FWS (EXS _) FREE.
Let OVERRUN : overrun_leaf_tfa B := tfib_overrun_leaf B HB ARL ML xst est XFR ESTF FWS (EXS _) FREE.
Let EXITLa : forall fq : YK11.FPState, exit_leaf_tfa (fx := fq) B xst := fun fq => tfib_exit_leaf (fx := fq) B HB ARL xst est XFR ESTI ESTF (EXS fq).
Let EXITL : exit_leaf_tfa B xst := EXITLa _.
Let HCO : cannot_open_tfa B := tfib_cannot_open B HB ARL xst est XFR ESTF FPO (EXS _).
Let LOOPL : loop_L_x B xst := tfib_loop_L B HB ARL ML xst LIBa PF1 PFN FREEa FREENa EXITLa XFR frm0_fx0.
Let RUNQM : run_QM_tfa B := tfib_run_QM B HB ARL ML MSITE MCPY FREE xst EXITL XFR LOOPL.
Let RUNQ : run_Q_tfa B := tfib_run_Q B HB ARL xst LOOPL RUNQM.
Let POSTP : post_P_tfa B := tfib_post_P B HB ARL RUNQ.
Let HDR : hdr_tfa B := tfib_hdr B HB ARL SHORT OVERRUN POSTP.
Let RDD : rd0_dir_tfa B := tfib_rd0_dir B HB ARL RDERR.
Let RDF : rd0_file_tfa B := tfib_rd0_file B HB ARL ML MSITE RCHK MCPY FREE REFUSED HDR.
Let HFILE : file_arm_tfa B := tfib_file_arm B HB ARL ML MSITE RDF.
Let HDIR : dir_arm_tfa B := tfib_dir_arm B HB ARL ML MSITE RDD.
Theorem tfib_drv_main : forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
(FULL : word -> option byte) (model : Model),
valid_sp sp -> valid_brk TSEGS brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
HS_tfib h = Some ch ->
cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp)
(YA02.SINV0 TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
(forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) n) ->
(forall a, YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E a = true ->
FULL a = wrap_mem TPH sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw a) ->
srealizes TSEGS (cfg_of TSEGS R (pc ch) FULL model) (CLOSEDX inp).
Proof.
intros sp rdraw brk inp h ch E R FULL model Hsp Hbrk Hfit (Hva & Hve & Hvfs & _) Hceil Hch HC HE HM.
pose (H8 := YDiscoWorldH8.H1_H8 sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC).
pose proof (tfib_main_entry sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC HE HM (sliver_allowed sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC Hceil) H8) as (Hpc & HST & HAI & Hfs & Hfds & _).
set (ly := YD1g.ly0 ch E model).
assert (HAR : AR TSEGS B ly init_state (W1 sp rdraw inp Hsp Hva ch E model H8) FULL model) by (eapply (tfib_AR B HB); eassumption).
assert (HTOP : YD1v.top_ok (bv_unsigned sp) ly) by (eapply tfib_top_ok; eassumption).
assert (HFI : FINV ly (w_H (W1 sp rdraw inp Hsp Hva ch E model H8)) FULL) by exact (tfib_finv_handoff sp rdraw brk inp Hsp Hva h ch E R FULL model Hch HC).
rewrite Hpc. change (cfg_of TSEGS R TFIB_MAIN FULL model) with (mkCfg (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom tfibsegs)) model).
change TSEGS with tfibsegs in HST, HAI, HAR |- *. unfold CLOSEDX.
destruct (Nat.eq_dec (length (in_argv inp)) 2) as [Hlen|Hlen].
- assert (Hargv : exists a0 p, in_argv inp = [a0; p]).
{ clear -Hlen. destruct (in_argv inp) as [|a0 [|p [|x r]]]; try (cbn in Hlen; lia). exists a0, p. reflexivity. }
destruct Hargv as (a0 & p & Hargv).
destruct (HST true ltac:(unfold two_ok; rewrite Hargv; cbn; lia)) as [HS HR].
replace (CLOSEDX_args (in_argv inp) (in_fs inp)) with (CLOSEDX_args [a0; p] (in_fs inp)) by (rewrite Hargv; reflexivity).
exact (tfib_arm_argv2 B HB ARL HCO HFILE HDIR sp inp (xwE E R) (xdE inp)
(W1 sp rdraw inp Hsp Hva ch E model H8) (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom tfibsegs)) model ly a0 p
Hargv Hsp Hva Hve Hfit Hvfs HS HR HAI HAR HTOP HFI Hfs Hfds).
- destruct (HST false I) as [HS HR].
replace (CLOSEDX_args (in_argv inp) (in_fs inp)) with (diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
2:{ clear -Hlen. unfold CLOSEDX_args. destruct (in_argv inp) as [|x [|y [|z r]]]; try reflexivity. cbn in Hlen. lia. }
exact (tfib_usage B HB ARL xst est XFR ESTF FPU (EXS _) sp inp (xwE E R) (xdE inp) (W1 sp rdraw inp Hsp Hva ch E model H8) (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom tfibsegs))
model ly Hsp Hva Hve Hfit Hlen HS HR HAI HAR HTOP Hfs Hfds).
Qed.
End c.
End b.
