(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1p.v, with its module paths changed, names TfibSyms -> CmdBSyms and its addresses moved to plugin-hostd/fuzz_command's ASan build; the program contract is taken at every call index j with fuzz_command's GI_cmdA (lib/A/Prog/CmdGlob.v) and at every float state, since a call may return in another one (C3's pass 5b), so the sites the loop reaches after a call (the contract, printf, free, exit) are hypotheses for all float states; main's entry gives the arms frm0 (fx0's fcsr is 0) and stk_top (AD1v.v): [sp, sp + 24) from argc/argv in the entry state, and [sp + 24, stack top) from the hand-off's argH0 equation with wrap_mem_present (the kernel maps the entry stack to the page boundary above its image) where argH0 holds, from StartStkAuxG.stk_aux_present (the hole states' auxv and AT_RANDOM words) where it does not; the start-up certificate's hole states come from class StartData (A/CmdStartCert.v) and its checks from classes TfibHolesChk, TfibHolesIf, EntryCheckAll, TfibHolesChkB, TfibHolesImgsh, FinvCheckAll, TfibHolesStkAux and TfibAvis8 (A/CmdWorldH8.v), Section hypotheses until plugin-hostd/fuzz_command's certificate is generated; the entry world W1 takes A/CmdWorldH8.v's H1_H8 for the world field w_H8. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3, merging libreac/fuzz_boxreg's port of its copy of this file: the hand-off state is the one of the run's own CONFIG_RSEQ flag (HS_tfib_r) and the computed checks run over both flags' states, the stack invariant is abstract, the entry stack is laid out from the stack VMA's end and the launch premises (valid_launch, entry_launch_ok_va, valid_input) are carried; this unit's own stk_top and frm0 premises are kept The stack's presence at main (stk_top) is read from argH0 up to the stack VMA's end and from the hand-off state's knowledge of the auxv and the AT_RANDOM bytes; the model's channel reader that fdchan asks for beside the descriptor, carried from the hand-off's cs_ok (its co_rdr field, proved at the launch). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.plugin_hostd.fuzz_command.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02 YA00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB12 AB1h CmdStartCert StartStkAuxG.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0f YG00 YG01 YG0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP09 YP0l YP08 YP03 YN3q YK04 YA0i YA0n YA0o YA0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YD1h.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AD1d AD1g AD1f AD2i AD1t CmdWorldH8.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AD1v AD1w AD2a AD26 AD22 AD1z AD2g AD2c AD2d AD29 AD2e AD1r AD1x AD27 AD1i AD1n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import ACfn ACeg AE2k AD1u AD1m AD2k.
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
unfold mbyte in Hb. rewrite (AF0x.seg_rom_none_high a) in Hb by (unfold AF0x.TFIB_IMG_END; lia).
destruct (m (Z_to_bv 64 a)); [discriminate | discriminate Hb].
Qed.
(* Every byte of the kernel's entry stack, from the entry sp up to the top of the stack VMA, is mapped in the exec
   state: the image is the launch's entry_stack_image, which runs from sp to the VMA's end (LPS Common/PropExec.v
   wrap_above_sp and length_entry_stack_image_launch). *)
Lemma wrap_mem_present : forall inp mbase ph entry (sp : word) rdraw a,
bv_unsigned sp <= a < bv_unsigned sp + Z.of_nat (length (entry_stack_image inp mbase ph entry sp rdraw)) -> a < 2 ^ 64 ->
wrap_mem inp mbase ph entry sp rdraw (Z_to_bv 64 a) <> None.
Proof.
intros inp mbase ph entry sp rdraw a Ha Ha64. pose proof (u64_range sp).
rewrite (wrap_above_sp inp mbase ph entry sp rdraw (Z_to_bv 64 a)) by (rewrite YK00.u64_lit by lia; lia).
unfold stack_to_mem. rewrite YK00.u64_lit by lia.
replace (bv_unsigned sp <=? a) with true by (symmetry; apply Z.leb_le; lia).
cbv zeta.
replace (a - bv_unsigned sp <? Z.of_nat (length (entry_stack_image inp mbase ph entry sp rdraw))) with true
by (symmetry; apply Z.ltb_lt; lia).
intros Hn. apply nth_error_None in Hn. lia.
Qed.
(* The driver's stack top (AD1v.TOPF, the page boundary ly_top of AD1g.ly0) is at or below the top of the stack VMA,
   a page boundary above the entry sp (LPS Run.v valid_stack_top_va). *)
Lemma TOPF_le_top : forall (usp utop : Z), usp <= utop -> utop mod 4096 = 0 -> AD1v.TOPF usp <= utop.
Proof.
intros usp utop H1 H2. unfold AD1v.TOPF.
pose proof (Z.div_mod (usp - 160 + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (usp - 160 + 4095) 4096 ltac:(lia)).
pose proof (Z.div_mod utop 4096 ltac:(lia)). lia.
Qed.
#[local] Existing Instance YK11.fx0.
Section b. Context {rc : YM05.RunCeil} {LS : lib_shape}.
Context {SD : StartData} {HCK : TfibHolesChk} {HIF : TfibHolesIf} {ECA : EntryCheckAll} {HCB : TfibHolesChkB} {HIS : TfibHolesImgsh} {FCA : FinvCheckAll}.
Context {HSA : TfibHolesStkAux} {HAV : TfibAvis8}.
Lemma W1_high_visible : forall sp rdraw inp (Hsp : valid_sp sp) (Hva : valid_argv (in_argv inp)) ch E model H8 (a : word),
YA02.TOP sp <= bv_unsigned a -> w_H (W1 sp rdraw inp Hsp Hva ch E model H8) a = false.
Proof.
intros sp rdraw inp Hsp Hva ch E model H8 a Ha. cbn [w_H W1]. unfold AD2i.H1. cbv beta.
destruct (YA02.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp) E a) eqn:Hg.
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
Hypothesis FPU : fprintf_s_site_tfa B est 0x158ea (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
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
(* LPS 727298f3: main over the hand-off state of the run's own CONFIG_RSEQ flag, with the stack invariant abstract
   (SINV, its entry-sp fact SP0) and the launch's fifth valid_entry conjunct given (A/AD1q.v drv_mainX_stmt). *)
Theorem tfib_drv_main : forall (sp : word) (rdraw : EntryDraw) (brk mbase : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
(FULL : word -> option byte) (model : Model) (SINV : env -> (word -> option byte) -> Prop),
valid_sp sp -> valid_brk TSEGS brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
HS_tfib_r (rseq_z (kb_rseq (in_kernel inp))) h = Some ch ->
(forall E' M, SINV E' M -> uE E' e_sp0 = YA02.TOP sp + 8388608) ->
cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp) SINV (YA02.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)) (in_fs inp) E ch R FULL model ->
(forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 sp rdraw brk (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)) n) ->
(forall a, YA02.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp) E a = true ->
FULL a = wrap_mem inp mbase TPH (Z_to_bv 64 (Z.of_N Asan.M.init_pc)) sp rdraw a) ->
srealizes TSEGS (cfg_of TSEGS R (pc ch) FULL model) (CLOSEDX inp).
Proof.
intros sp rdraw brk mbase inp h ch E R FULL model SINV Hsp Hbrk Hfit Hinp Hlau Hceil Hch SP0 HC HE HM.
pose proof Hinp as (Hva & Hve & Hvfs & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hvl & _).
(* The section lemmas of A/AD1g.v, A/AD2i.v and A/CmdWorldH8.v that the driver's main reads, with their section
   arguments given by name in their declaration order (each one only if the lemma takes it): the idiom of A/AD1d.v's
   [inst].  [inst_drv] is local to the proof (here and in [HTK]'s proof below): a top-level [Ltac] resolves each name
   it uses where it is defined, and these names exist only after the proof's [intros]. *)
let inst_drv H := (try specialize (H sp); try specialize (H rdraw); try specialize (H brk); try specialize (H mbase);
  try specialize (H inp); try specialize (H Hsp); try specialize (H Hva); try specialize (H Hve); try specialize (H Hfit);
  try specialize (H Hvl); try specialize (H Hlau); try specialize (H Hinp); try specialize (H h); try specialize (H ch);
  try specialize (H E); try specialize (H R); try specialize (H FULL); try specialize (H model); try specialize (H Hch);
  try specialize (H SINV); try specialize (H SP0); try specialize (H HC); try specialize (H HE); try specialize (H HM);
  try specialize (H rc); try specialize (H Hceil)) in
(pose (SLA := ltac:(let X := fresh in pose proof AD1g.sliver_allowed as X; inst_drv X; exact X));
 pose (H8 := ltac:(let X := fresh in pose proof CmdWorldH8.H1_H8 as X; inst_drv X; exact X));
 pose proof tfib_main_entry as TME; inst_drv TME; specialize (TME SLA H8)).
destruct TME as (Hpc & HST & HAI & Hfs & Hfds & _).
(* The hand-off model's channel reader, which [fdchan] asks for at LPS 727298f3 beside the
   descriptor: [cs_ok]'s [co_rdr], proved at the launch.  The arms carry it to their sites. *)
assert (Hcr : m_channel_reader model = true) by (eapply co_rdr; exact HC).
set (ly := AD1g.ly0 ch E model).
assert (HAR : AR TSEGS B ly init_state (W1 sp rdraw inp Hsp Hva ch E model H8) FULL model) by (eapply tfib_AR; eassumption).
assert (HTOP : AD1v.top_ok (bv_unsigned sp) ly) by (eapply tfib_top_ok; eassumption).
assert (HFI : FINV ly (w_H (W1 sp rdraw inp Hsp Hva ch E model H8)) FULL) by (eapply tfib_finv_handoff; eassumption).
rewrite Hpc. change (cfg_of TSEGS R TFIB_MAIN FULL model) with (mkCfg (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom tfibsegs)) model).
change TSEGS with tfibsegs in HST, HAI, HAR |- *. unfold CLOSEDX.
(* the stack from the entry sp to the driver's stack top is present: argc, argv[0], argv[1] from the entry state's R_hdr;
   above them every byte is an argH0 byte (the hand-off pins it to wrap_mem, which maps the whole entry stack up to
   the stack VMA's end), an auxv byte or an AT_RANDOM byte (the hand-off state's knowledge covers both,
   A/StartStkAuxG.v) *)
assert (HTK : two_ok inp true -> stk_top (bv_unsigned sp) (mrestrict (w_H (W1 sp rdraw inp Hsp Hva ch E model H8)) FULL)).
{ intros Htwo. destruct (HST true Htwo) as [HS _].
pose proof (st_ok_mem_ok tfibsegs _ _ _ HS) as HMEM. cbn [restrict ms_mem ss_main ss_mem] in HMEM.
pose proof Hsp as (Ulo & Uhi & _).
pose proof (length_entry_stack_image_launch Sv48 inp mbase TPH (Z_to_bv 64 (Z.of_N Asan.M.init_pc)) sp brk rdraw Hlau) as HLEN.
let inst_drv H := (try specialize (H sp); try specialize (H rdraw); try specialize (H brk); try specialize (H mbase);
  try specialize (H inp); try specialize (H Hsp); try specialize (H Hva); try specialize (H Hve); try specialize (H Hfit);
  try specialize (H Hvl); try specialize (H Hlau); try specialize (H Hinp); try specialize (H h); try specialize (H ch);
  try specialize (H E); try specialize (H R); try specialize (H FULL); try specialize (H model); try specialize (H Hch);
  try specialize (H SINV); try specialize (H SP0); try specialize (H HC); try specialize (H HE); try specialize (H HM);
  try specialize (H rc); try specialize (H Hceil)) in
(pose proof AD2i.u_auxb as UA; inst_drv UA; rewrite snd_auxb in UA; pose proof AD2i.u_atrb as UR; inst_drv UR).
pose proof Hlau as ((Htal & _) & _). unfold page_size in Htal.
pose proof (TOPF_le_top (bv_unsigned sp) (bv_unsigned (ed_top rdraw)) ltac:(pose proof (Nat2Z.is_nonneg (length (entry_stack_image inp mbase TPH (Z_to_bv 64 (Z.of_N Asan.M.init_pc)) sp rdraw))); lia) Htal) as HPT.
pose proof (stk_aux_chk_of (kb_rseq (in_kernel inp)) h ch Hch) as Hchk.
intros a Ha Ha2. destruct (Z.lt_ge_cases a (bv_unsigned sp + 24)) as [Hl|Hl].
- apply (hdr_stk_present _ _ (smem_main true) (bv_unsigned sp) HMEM);
[unfold smem_main; right; left; reflexivity | reflexivity | exact Ulo | unfold sp_window_hi in Uhi; lia | lia].
- unfold mrestrict. rewrite W1_high_visible by (rewrite YK00.u64_lit by (unfold sp_window_lo in Ulo; lia); unfold YA02.TOP; lia).
destruct (YA02.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp) E (Z_to_bv 64 a)) eqn:Hg.
* rewrite (HM (Z_to_bv 64 a) Hg). apply wrap_mem_present; lia.
* assert (HFC : (bv_unsigned sp + 8 * Z.of_nat (length (in_argv inp)) + 8 * Z.of_nat (length (in_envp inp)) + 24 <= bv_unsigned (Z_to_bv 64 a)
< bv_unsigned sp + 8 * Z.of_nat (length (in_argv inp)) + 8 * Z.of_nat (length (in_envp inp)) + 456 + 32 * rseq_z (kb_rseq (in_kernel inp)))
\/ (bv_unsigned sp + Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)) - 16 <= bv_unsigned (Z_to_bv 64 a)
< bv_unsigned sp + Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)))).
{ (* [YA02.argH0_false_cases]'s own proof at this input: the lemma's exported binder list leads with section
     variables this file does not hold (plugin-hostd/fuzz_reply's copy of this call failed with "sp" given where a
     segment list is expected), so the cases are read off argH0 here. *)
unfold YA02.argH0, YA02.argH0_core in Hg. cbv zeta in Hg.
cbn [in_kernel YA02.inp recorded_kernel kb_rseq] in Hg.
rewrite YK00.u64_lit in Hg |- * by (unfold sp_window_lo in Ulo; lia).
repeat rewrite orb_false_iff in Hg.
destruct Hg as ((((H1 & H2) & Ht) & Hg5) & Hp).
apply andb_false_iff in H1, H2, Ht, Hg5, Hp.
destruct H1 as [H1|H1], H2 as [H2|H2], Ht as [Ht|Ht], Hg5 as [Hg5|Hg5], Hp as [Hp|Hp];
  rewrite ?Z.leb_gt, ?Z.ltb_ge in H1; rewrite ?Z.leb_gt, ?Z.ltb_ge in H2; rewrite ?Z.leb_gt, ?Z.ltb_ge in Ht;
  rewrite ?Z.leb_gt, ?Z.ltb_ge in Hg5; rewrite ?Z.leb_gt, ?Z.ltb_ge in Hp; lia. }
rewrite YK00.u64_lit in HFC by (unfold sp_window_lo in Ulo; lia).
destruct HFC as [HFC|HFC].
+ apply (stk_auxv_present (YA02.TOP sp) SINV _ (in_fs inp) E ch R FULL model (rseq_z (kb_rseq (in_kernel inp))) HC Hchk);
[unfold AUXSZ; lia | unfold sp_window_lo in Ulo; lia].
+ apply (stk_atr_present (YA02.TOP sp) SINV _ (in_fs inp) E ch R FULL model (rseq_z (kb_rseq (in_kernel inp))) HC Hchk);
[lia | unfold sp_window_lo in Ulo; lia]. }
destruct (Nat.eq_dec (length (in_argv inp)) 2) as [Hlen|Hlen].
- assert (Hargv : exists a0 p, in_argv inp = [a0; p]).
{ clear -Hlen. destruct (in_argv inp) as [|a0 [|p [|x r]]]; try (cbn in Hlen; lia). exists a0, p. reflexivity. }
destruct Hargv as (a0 & p & Hargv).
assert (Htwo : two_ok inp true) by (unfold two_ok; rewrite Hargv; cbn; lia).
destruct (HST true Htwo) as [HS HR].
pose proof (HTK Htwo) as HTk.
replace (CLOSEDX_args (in_argv inp) (in_fs inp)) with (CLOSEDX_args [a0; p] (in_fs inp)) by (rewrite Hargv; reflexivity).
eapply (tfib_arm_argv2 B HB ARL HCO HFILE HDIR); try eassumption.
unfold AD1v.frm0; vm_compute; reflexivity.
- destruct (HST false I) as [HS HR].
replace (CLOSEDX_args (in_argv inp) (in_fs inp)) with (diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
2:{ clear -Hlen. unfold CLOSEDX_args. destruct (in_argv inp) as [|x [|y [|z r]]]; try reflexivity. cbn in Hlen. lia. }
eapply (tfib_usage B HB ARL xst est XFR ESTF FPU (EXS _)); eassumption.
Qed.
End c.
End b.
