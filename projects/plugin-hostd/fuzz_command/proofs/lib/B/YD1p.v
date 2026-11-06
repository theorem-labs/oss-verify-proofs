(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1p.v, with its module paths changed, names TfibSyms -> CmdBSyms and its addresses moved to plugin-hostd/fuzz_command's ASan build; the program contract is taken at every call index j with fuzz_command's GI_cmdA (lib/A/Prog/CmdGlob.v) and at every float state, since a call may return in another one (C3's pass 5b), so the sites the loop reaches after a call (the contract, printf, free, exit) are hypotheses for all float states; main's entry gives the arms frm0 (fx0's fcsr is 0) and stk_top (AD1v.v): [sp, sp + 24) from argc/argv in the entry state, and [sp + 24, stack top) from the hand-off's argH0 equation with wrap_mem_present (the kernel maps the entry stack to the page boundary above its image) where argH0 holds, from StartStkAuxG.stk_aux_present (the hole states' auxv and AT_RANDOM words) where it does not; the start-up certificate's hole states come from class StartData (A/CmdStartCert.v) and its checks from classes TfibHolesChk, TfibHolesIf, EntryCheckAll, TfibHolesChkB, TfibHolesImgsh, FinvCheckAll, TfibHolesStkAux and TfibAvis8 (A/CmdWorldH8.v), Section hypotheses until plugin-hostd/fuzz_command's certificate is generated; the entry world W1 takes A/CmdWorldH8.v's H1_H8 for the world field w_H8. *)
(* Modified by Theorem Labs, 2026-10: copied from this harness's lib/A/AD1p.v (the twin of cgif_file_fuzzer's lib/YD1p.v), with its module paths changed (lib/A to lib/B, image Asan to AsanUbsan) and its addresses moved to plugin-hostd/fuzz_command's ASan+UBSan build. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.plugin_hostd.fuzz_command.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02 YA00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB12 YB1h CmdStartCertB StartStkAuxG.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0f YG00 YG01 YG0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP09 YP0l YP08 YP03 YN3q YK04 YA0i YA0n YA0o YA0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YD1h.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YD1d YD1g YD1f YD2i YD1t YCmdWorldH8.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YD1v YD1w YD2a YD26 YD22 YD1z YD2g YD2c YD2d YD29 YD2e YD1r YD1x YD27 YD1i YD1n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn YCeg YE2k YD1u YD1m YD2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
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
Lemma hdr_stk_present : forall E (m : word -> option byte) rs usp,
mem_ok tfibsegs E m rs -> In (YP08.R_hdr true) rs -> bv_unsigned (ew E 0) = usp -> sp_window_lo <= usp -> usp + 24 <= 2 ^ 64 ->
forall a, usp <= a < usp + 24 -> m (Z_to_bv 64 a) <> None.
Proof.
intros E m rs usp (_ & HR & _) Hin E0 Ulo Uhi a Ha. unfold sp_window_lo in Ulo.
pose proof (proj1 (Forall_forall _ _) HR _ Hin) as Hr.
assert (Hc : exists c, In c (r_chunks (YP08.R_hdr true)) /\ YP09.c_off c <= a - usp < YP09.c_off c + YP09.c_len c).
{ destruct (Z.lt_ge_cases (a - usp) 8) as [H1|H1]; [|destruct (Z.lt_ge_cases (a - usp) 16) as [H2|H2]].
- eexists. split; [left; reflexivity | cbn; lia].
- eexists. split; [right; left; reflexivity | cbn; lia].
- eexists. split; [right; right; left; reflexivity | cbn; lia]. }
destruct Hc as (c & Hc & Hoff).
destruct (region_ok_chunk tfibsegs E m _ c Hr Hc (a - usp - YP09.c_off c) ltac:(lia)) as (b & _ & Hb).
assert (Hbase : base_val E (r_base (YP08.R_hdr true)) = usp) by (rewrite <- E0; reflexivity).
rewrite Hbase in Hb. replace (usp + YP09.c_off c + (a - usp - YP09.c_off c)) with a in Hb by lia.
unfold mbyte in Hb. rewrite (YF0x.seg_rom_none_high a) in Hb by (unfold YF0x.TFIB_IMG_END; lia).
destruct (m (Z_to_bv 64 a)); [discriminate | discriminate Hb].
Qed.
(* Every byte of the kernel's entry stack, from the entry sp up to the page boundary above its image,
   is mapped in the exec state: the image is build_stack_bytes followed by the slack that fills the page
   (LPS Run.v entry_stack_image / entry_stack_image_top, StackLayout.v stack_to_mem). *)
Lemma wrap_mem_present : forall ph (sp : word) argv envp (uid hw : word) rnd a,
valid_sp sp -> entry_stack_fits sp argv envp ->
bv_unsigned sp <= a < entry_page_top sp (build_stack_bytes ph sp argv envp uid hw rnd) ->
wrap_mem ph sp argv envp uid hw rnd (Z_to_bv 64 a) <> None.
Proof.
intros ph sp argv envp uid hw rnd a Hsp Hfit Ha.
pose proof (entry_page_top_within_window ph sp argv envp uid hw rnd Hfit) as HW.
pose proof Hsp as (Ulo & Uhi & _). unfold sp_window_lo, sp_window_hi in *.
assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
pose proof (entry_stack_image_top ph sp argv envp uid hw rnd) as HT.
rewrite (wrap_above_sp ph sp argv envp (Z_to_bv 64 a) uid hw rnd) by (rewrite YK00.u64_lit by lia; lia).
unfold stack_to_mem. rewrite YK00.u64_lit by lia.
destruct (Z.leb_spec (bv_unsigned sp) a) as [_|Hgt]; [| lia].
destruct (Z.ltb_spec (a - bv_unsigned sp) (Z.of_nat (length (entry_stack_image ph sp argv envp uid hw rnd)))) as [_|Hge]; [| lia].
apply (proj2 (nth_error_Some _ _)). lia.
Qed.
(* The driver's stack top (YD1v.TOPF, the page boundary ly_top of YD1g.ly0) is at or below that boundary. *)
Lemma TOPF_le_page_top : forall ph (sp : word) argv envp (uid hw : word) rnd,
YD1v.TOPF (bv_unsigned sp) <= entry_page_top sp (build_stack_bytes ph sp argv envp uid hw rnd).
Proof.
intros ph sp argv envp uid hw rnd. unfold YD1v.TOPF, entry_page_top, page_round_up_Z, page_size, entry_block_top.
pose proof (Z.div_le_mono (bv_unsigned sp - 160 + 4095)
(bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp argv envp uid hw rnd)) + 4096 - 1) 4096 ltac:(lia) ltac:(lia)). lia.
Qed.
#[local] Existing Instance YK11.fx0.
Section b. Context {rc : YM05.RunCeil} {LS : lib_shape}.
Context {SD : StartData} {HCK : TfibHolesChk} {HIF : TfibHolesIf} {ECA : EntryCheckAll} {HCB : TfibHolesChkB} {HIS : TfibHolesImgsh} {FCA : FinvCheckAll}.
Context {HSA : TfibHolesStkAux} {HAV : TfibAvis8}.
Lemma W1_high_visible : forall sp rdraw inp (Hsp : valid_sp sp) (Hva : valid_argv (in_argv inp)) ch E model H8 (a : word),
YA02.TOP sp <= bv_unsigned a -> w_H (W1 sp rdraw inp Hsp Hva ch E model H8) a = false.
Proof.
intros sp rdraw inp Hsp Hva ch E model H8 a Ha. cbn [w_H W1]. unfold YD2i.H1. cbv beta.
destruct (YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E a) eqn:Hg.
- cbn [negb]. rewrite andb_false_r. reflexivity.
- rewrite YA0j.ho_hid_high; [reflexivity | exact Ha | exact Hg].
Qed.
Section c.
Variable B : asyms.
Hypothesis HB : CmdBSyms B.
Let ARL : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let ML : model_laws (as_universe B) := model_laws_ok (as_universe B) (ts_universe B HB).
Hypothesis AMALLOC : amalloc_realizes tfibsegs B.
Hypothesis AFREE : forall (fy : YK11.FPState), afree_realizes (fx := fy) tfibsegs B.
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : aread_check_stmt B.
Variables (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z).
Hypothesis MT_FREE : forall S m, mo_ok MT S m.
Hypothesis RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a.
Hypothesis LIBC : forall (fy : YK11.FPState) (j : nat), tfib_lib_contract_x (fx := fy) B MT XM_LIB XN_LIB RLO RHI GI_cmdA j.
Let MSITE : malloc_site_tfa B := tfib_malloc_site B ML AMALLOC.
Let RCHK : read_check_tfa B := tfib_read_check B ARDCHK.
Let MCPY : memcpy_site_tfa B := tfib_memcpy_site B AICPY.
Let FREEa (fy : YK11.FPState) : free_site_tfa (fx := fy) B := tfib_free_site B ML (AFREE fy).
Let FREENa (fy : YK11.FPState) : free_null_site_tfa (fx := fy) B := tfib_free_null_site B ML (AFREE fy).
Let FREE : free_site_tfa B := FREEa _.
Let FREEN : free_null_site_tfa B := FREENa _.
Let LIBa (fy : YK11.FPState) : lib_site_x (fx := fy) B := tfib_lib_site_x B MT XM_LIB XN_LIB RLO RHI MT_FREE RO_IN (LIBC fy).
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis PF1 : forall (fy : YK11.FPState), printf_first_tfa (fx := fy) B xst.
Hypothesis PFN : forall (fy : YK11.FPState), printf_next_tfa (fx := fy) B xst.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis ESTI : est_img_tfa est.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis FWS : fwrite_site_tfa B est.
Hypothesis RFS : refused_site_tfa B est.
Hypothesis FPO : fprintf_s_site_tfa B est 0x1d922 (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est 0x1d937 (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est 0x158f2 (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS : forall (fy : YK11.FPState), exit_site_tfa (fx := fy) B est xst.
Let RDERR : rderr_leaf_tfa B := tfib_rderr_leaf B HB ARL xst est XFR ESTF FPR (EXS _).
Let REFUSED : refused_leaf_tfa B := tfib_refused_leaf B HB ARL xst est XFR ESTF RFS (EXS _).
Let SHORT : short_leaf_tfa B := tfib_short_leaf B HB ARL ML xst est XFR ESTF FWS (EXS _) FREE.
Let OVERRUN : overrun_leaf_tfa B := tfib_overrun_leaf B HB ARL ML xst est XFR ESTF FWS (EXS _) FREE.
Let EXITLa (fy : YK11.FPState) : exit_leaf_tfa (fx := fy) B xst := tfib_exit_leaf B HB ARL xst est XFR ESTI ESTF (EXS fy).
Let EXITL : exit_leaf_tfa B xst := EXITLa _.
Let HCO : cannot_open_tfa B := tfib_cannot_open B HB ARL xst est XFR ESTF FPO (EXS _).
Let LOOPL : loop_L_x B xst := tfib_loop_L B HB ARL ML xst LIBa PF1 PFN FREEa FREENa EXITLa XFR.
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
pose (H8 := YCmdWorldH8.H1_H8 sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC).
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
(* the stack from the entry sp to the stack top is present: argc, argv[0], argv[1] from the entry state's R_hdr;
   above them every byte is either an argH0 byte (the hand-off pins it to wrap_mem, which maps the whole entry
   stack up to its page boundary) or one of the certificate's known auxv / AT_RANDOM words *)
assert (HTK : stk_top (bv_unsigned sp) (mrestrict (w_H (W1 sp rdraw inp Hsp Hva ch E model H8)) FULL)).
{ pose proof (st_ok_mem_ok tfibsegs _ _ _ HS) as HMEM. cbn [restrict ms_mem ss_main ss_mem] in HMEM.
pose proof Hsp as (Ulo & Uhi & _).
pose proof (TOPF_le_page_top TPH sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw) as HPT.
intros a Ha Ha2. destruct (Z.lt_ge_cases a (bv_unsigned sp + 24)) as [Hl|Hl].
- apply (hdr_stk_present _ _ (smem_main true) (bv_unsigned sp) HMEM);
[unfold smem_main; right; left; reflexivity | reflexivity | exact Ulo | unfold sp_window_hi in Uhi; lia | lia].
- unfold mrestrict. rewrite W1_high_visible by (rewrite YK00.u64_lit by (unfold sp_window_lo in Ulo; lia); unfold YA02.TOP; lia).
destruct (YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E (Z_to_bv 64 a)) eqn:Hg.
* rewrite (HM (Z_to_bv 64 a) Hg).
apply (wrap_mem_present TPH sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw a Hsp Hfit). lia.
* assert (HFC : (bv_unsigned sp + 8 * Z.of_nat (length (in_argv inp)) + 8 * Z.of_nat (length (in_envp inp)) + 24 <= bv_unsigned (Z_to_bv 64 a)
< bv_unsigned sp + 8 * Z.of_nat (length (in_argv inp)) + 8 * Z.of_nat (length (in_envp inp)) + 184)
\/ (bv_unsigned sp + Z.of_nat (length (build_stack_bytes TPH sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw)) - 16 <= bv_unsigned (Z_to_bv 64 a)
< bv_unsigned sp + Z.of_nat (length (build_stack_bytes TPH sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw)))).
{ (* the section variables argH0_false_cases does not read are filled with the run's own values *)
apply (YA02.argH0_false_cases TSEGS TFIB TPH sp rdraw brk brk (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp)
(in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_nofile inp) (in_stdin inp) (in_fs inp) Hva Hve E (Z_to_bv 64 a));
[rewrite YK00.u64_lit by (unfold sp_window_lo in Ulo; lia); lia | exact Hg]. }
rewrite YK00.u64_lit in HFC by (unfold sp_window_lo in Ulo; lia).
pose proof (proj1 (forallb_forall _ _) tfib_holes_stkaux_c ch (HS_tfib_In h ch Hch)) as Hchk.
exact (stk_aux_present sp rdraw brk inp ch E R FULL model Hsp Hva Hve Hfit Hchk HC a HFC). }
replace (CLOSEDX_args (in_argv inp) (in_fs inp)) with (CLOSEDX_args [a0; p] (in_fs inp)) by (rewrite Hargv; reflexivity).
exact (tfib_arm_argv2 B HB ARL HCO HFILE HDIR sp inp (xwE E R) (xdE inp)
(W1 sp rdraw inp Hsp Hva ch E model H8) (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom tfibsegs)) model ly a0 p
Hargv Hsp Hva Hve Hfit Hvfs HS HR HTK ltac:(unfold YD1v.frm0; vm_compute; reflexivity) HAI HAR HTOP HFI Hfs Hfds).
- destruct (HST false I) as [HS HR].
replace (CLOSEDX_args (in_argv inp) (in_fs inp)) with (diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
2:{ clear -Hlen. unfold CLOSEDX_args. destruct (in_argv inp) as [|x [|y [|z r]]]; try reflexivity. cbn in Hlen. lia. }
exact (tfib_usage B HB ARL xst est XFR ESTF FPU (EXS _) sp inp (xwE E R) (xdE inp) (W1 sp rdraw inp Hsp Hva ch E model H8) (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom tfibsegs))
model ly Hsp Hva Hve Hfit Hlen HS HR HAI HAR HTOP Hfs Hfds).
Qed.
End c.
End b.
