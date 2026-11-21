(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1p.v, with its module paths changed, names TfibSyms -> CmdBSyms and its addresses moved to plugin-hostd/fuzz_command's ASan build; the program contract is taken at every call index j with fuzz_command's GI_cmdA (lib/A/Prog/CmdGlob.v) and at every float state, since a call may return in another one (C3's pass 5b), so the sites the loop reaches after a call (the contract, printf, free, exit) are hypotheses for all float states; main's entry gives the arms frm0 (fx0's fcsr is 0) and stk_top (AD1v.v): [sp, sp + 24) from argc/argv in the entry state, and [sp + 24, stack top) from the hand-off's argH0 equation with wrap_mem_present (the kernel maps the entry stack to the page boundary above its image) where argH0 holds, from StartStkAuxG.stk_aux_present (the hole states' auxv and AT_RANDOM words) where it does not; the start-up certificate's hole states come from class StartData (A/CmdStartCert.v) and its checks from classes TfibHolesChk, TfibHolesIf, EntryCheckAll, TfibHolesChkB, TfibHolesImgsh, FinvCheckAll, TfibHolesStkAux and TfibAvis8 (A/CmdWorldH8.v), Section hypotheses until plugin-hostd/fuzz_command's certificate is generated; the entry world W1 takes A/CmdWorldH8.v's H1_H8 for the world field w_H8. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AD1p.v (donor image sha256 c0661b96b5bd), with its module paths changed, names CmdBSyms -> SegBSyms and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/AD1p.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel-reader conjunct of fdchan; the auxv layout over the CONFIG_RSEQ flag; the start-up hand-off states computed per CONFIG_RSEQ flag; the launch's ProcInput; the image and mmap-base arguments of YA02's start-up lemmas); internal commit ids in comments replaced by public commits or removed. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_segconf.images Require Import AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02 YA00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB12 YB1h YB01r StartStkAuxG StartStkAux.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YF0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP09 YP0l YP08 YP03 YN3q YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YA0p.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YD1h.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YD1d YD1g YD1f YD2i YD1t CmdWorldH8.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YD1v YD1w YD2a YD26 YD22 YD1z YD2g YD2c YD2d YD29 YD2e YD1r YD1x YD27 YD1i YD1n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YCfn YCeg YE2k YD1u YD1m YD2k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
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
(* Every byte of the kernel's entry stack, from the entry sp up to the stack VMA's end [ed_top], is mapped in the
   exec state: at 727298f3 the image is Linux's block, sp .. [ed_top] exactly
   (PropExec.length_entry_stack_image_launch, PropExec.wrap_above_sp, StackLayout.stack_to_mem). *)
Lemma wrap_mem_present : forall inp mbase ph entry (sp brk : word) rnd a,
entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
bv_unsigned sp <= a < bv_unsigned (ed_top rnd) ->
wrap_mem inp mbase ph entry sp rnd (Z_to_bv 64 a) <> None.
Proof.
intros inp mbase ph entry sp brk rnd a Hlau Ha.
pose proof (length_entry_stack_image_launch Sv48 inp mbase ph entry sp brk rnd Hlau) as HL.
pose proof (u64_range (ed_top rnd)) as HT. pose proof (u64_range sp) as HS.
rewrite (wrap_above_sp inp mbase ph entry sp rnd (Z_to_bv 64 a)) by (rewrite YK00.u64_lit by lia; lia).
unfold stack_to_mem. cbv zeta. rewrite YK00.u64_lit by lia.
destruct (Z.leb_spec (bv_unsigned sp) a) as [_|Hgt]; [| lia].
destruct (Z.ltb_spec (a - bv_unsigned sp) (Z.of_nat (length (entry_stack_image inp mbase ph entry sp rnd)))) as [_|Hge]; [| lia].
apply (proj2 (nth_error_Some _ _)). lia.
Qed.
(* The driver's stack top (YD1v.TOPF, the page boundary ly_top of YD1g.ly0) is at or below any page boundary at
   or above usp - 160: the stack VMA's end [ed_top] is one (Run.valid_stack_top_va). *)
Lemma TOPF_le_top : forall usp t, usp - 160 <= t -> t mod 4096 = 0 -> YD1v.TOPF usp <= t.
Proof.
intros usp t H Hm. unfold YD1v.TOPF.
pose proof (Z.div_mod (usp - 160 + 4095) 4096 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (usp - 160 + 4095) 4096 ltac:(lia)) as M.
pose proof (Z.div_mod t 4096 ltac:(lia)) as Dt. rewrite Hm in Dt.
lia.
Qed.
(* The driver world's hidden set YD2i.H1 (HID && not argH && not sliver) is false where HID is false whenever
   argH is: above TOP (YA0j.ho_hid_high). *)
Lemma H1_high_false : forall (hd ah sl : word -> bool) (x : word), (ah x = false -> hd x = false) ->
(hd x && negb (ah x) && negb (sl x))%bool = false.
Proof.
intros hd ah sl x H. destruct (ah x) eqn:Ha.
- rewrite andb_false_r. reflexivity.
- rewrite (H eq_refl). reflexivity.
Qed.
#[local] Notation AH inp sp rdraw := (YA02.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp)
  (in_uid inp) (in_gid inp) (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp)
  (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)).
#[local] Existing Instance YK11.fx0.
Section b. Context {rc : YM05.RunCeil} {LS : lib_shape}.
Section c.
Variable B : asyms.
Hypothesis HB : SegBSyms B.
Let ARL : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let ML : model_laws (as_universe B) := model_laws_ok (as_universe B) (ts_universe B HB).
Hypothesis AMALLOC : amalloc_realizes tfibsegs B.
Hypothesis AFREE : forall (fy : YK11.FPState), afree_realizes (fx := fy) tfibsegs B.
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : aread_check_stmt B.
Variables (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z).
Hypothesis MT_FREE : forall S m, mo_ok MT S m.
Hypothesis RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a.
Hypothesis LIBC : forall (fy : YK11.FPState) (j : nat), tfib_lib_contract_x (fx := fy) B MT XM_LIB XN_LIB RLO RHI GI_segA j.
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
Hypothesis FPO : fprintf_s_site_tfa B est 0x1d8d2 (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est 0x1d8e7 (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est 0x15977 (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
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
(* LPS 727298f3: the driver's main over the hand-off state of the run's own CONFIG_RSEQ flag
   ([AB01r.HS_tfib_r]), with the stack invariant abstract and the launch's [entry_launch_ok_va],
   the statement [AD1q.drv_mainX_stmt] reads (as libreac/fuzz_boxreg's A/AD1q.v).  The section
   lemmas of AD1g/AD1f/AD2i/AD2k are taken at this lemma's arguments, whatever subset each one
   abstracts ([inst]), as AU/YD1d.v does. *)
Theorem tfib_drv_main : forall (sp : word) (rdraw : EntryDraw) (brk mbase : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
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
Proof.
intros sp rdraw brk mbase inp h ch E R FULL model SINV Hsp Hbrk Hfit Hvi Hlau Hceil Hch SINV_sp0 HC HE HM.
pose proof Hvi as (Hva & Hve & Hvfs & _).
assert (Hvl : valid_launch inp) by (unfold valid_input in Hvi; tauto).
pose proof YD1g.sliver_allowed as SLA.
pose proof CmdWorldH8.H1_H8 as H8.
pose proof YD2i.tfib_main_entry as ME.
pose proof tfib_AR as HAR.
pose proof tfib_top_ok as HTOP.
pose proof tfib_finv_handoff as HFI.
(* The section lemmas at this proof's names, whatever subset of their section arguments each one abstracts.
   The tactic is local to this proof: a top-level [Ltac] resolves each name it uses where it is defined,
   and these names exist only after the [intros] above (OSSV-648's fuzz_pcap). *)
let inst H := (try specialize (H B); try specialize (H HB); try specialize (H sp); try specialize (H rdraw); try specialize (H brk); try specialize (H mbase); try specialize (H inp); try specialize (H Hsp); try specialize (H Hva); try specialize (H Hve); try specialize (H Hfit); try specialize (H Hvl); try specialize (H Hlau); try specialize (H Hvi); try specialize (H h); try specialize (H ch); try specialize (H E); try specialize (H R); try specialize (H FULL); try specialize (H model); try specialize (H Hch); try specialize (H SINV); try specialize (H SINV_sp0); try specialize (H HC); try specialize (H HE); try specialize (H HM); try specialize (H SLA); try specialize (H rc); try specialize (H Hceil); try specialize (H H8)) in
(inst SLA; inst H8; inst ME; inst HAR; inst HTOP; inst HFI).
destruct ME as (Hpc & HST & HAI & Hfs & Hfds & _).
(* LPS 727298f3: [fdchan]'s third conjunct.  [cs_ok]'s last field [co_rdr] (YA0e.v:250)
   carries the launch's channel-reader flag, which [YA02.init_cs_ok] proves by
   computation; [eapply] leaves the projection's other arguments to [HC]. *)
assert (Hcr : m_channel_reader model = true) by (eapply co_rdr; exact HC).
rewrite Hpc. change (cfg_of TSEGS R TFIB_MAIN FULL model) with (mkCfg (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom tfibsegs)) model).
change TSEGS with tfibsegs in HST, HAI, HAR |- *. unfold CLOSEDX.
destruct (Nat.eq_dec (length (in_argv inp)) 2) as [Hlen|Hlen].
- assert (Hargv : exists a0 p, in_argv inp = [a0; p]).
{ clear -Hlen. destruct (in_argv inp) as [|a0 [|p [|x r]]]; try (cbn in Hlen; lia). exists a0, p. reflexivity. }
destruct Hargv as (a0 & p & Hargv).
destruct (HST true ltac:(unfold two_ok; rewrite Hargv; cbn; lia)) as [HS HR].
(* the stack from the entry sp to the stack top is present: argc, argv[0], argv[1] from the entry state's R_hdr;
   above them every byte is either an argH0 byte (the hand-off pins it to wrap_mem, which maps the whole entry
   block up to the stack VMA's end) or one of the auxv / AT_RANDOM bytes the hand-off knowledge covers *)
assert (HFRM : YD1v.frm0) by (unfold YD1v.frm0; vm_compute; reflexivity).
pose proof Hsp as (Ulo & Uhi & _).
pose proof Ulo as Ulo'. unfold sp_window_lo in Ulo'.
assert (HFC0 : forall x : word, bv_unsigned sp + 24 <= bv_unsigned x < bv_unsigned (ed_top rdraw) -> AH inp sp rdraw E x = false ->
  (uE E (fst e_auxb) + snd e_auxb <= bv_unsigned x < uE E (fst e_auxb) + snd e_auxb + AUXSZ (rseq_z (kb_rseq (in_kernel inp))))
  \/ (uE E (fst (e_atrb (rseq_z (kb_rseq (in_kernel inp))))) + snd (e_atrb (rseq_z (kb_rseq (in_kernel inp)))) <= bv_unsigned x
      < uE E (fst (e_atrb (rseq_z (kb_rseq (in_kernel inp))))) + snd (e_atrb (rseq_z (kb_rseq (in_kernel inp)))) + 16)).
{ intros x Hx Hgx.
  (* 727298f3: [YA02.argH0_false_den] abstracts the image ([segs A ph]) and [mbase] before and after [sp rdraw brk]
     (Reusable/YA02.v Section c's order; R22 measured [segs] first).  Each Section variable is given by type, in that
     order, and skipped where the lemma does not abstract it; the premises are closed from this proof's facts. *)
  pose proof YA02.argH0_false_den as D.
  try specialize (D TSEGS); try specialize (D TFIB); try specialize (D TPH);
  try specialize (D sp); try specialize (D rdraw); try specialize (D brk); try specialize (D mbase);
  try specialize (D (in_argv inp)); try specialize (D (in_envp inp)); try specialize (D (in_image_fs inp));
  try specialize (D (in_stdin inp)); try specialize (D (in_uid inp)); try specialize (D (in_gid inp));
  try specialize (D (in_hwcap inp)); try specialize (D (in_groups inp)); try specialize (D (in_net inp));
  try specialize (D (in_nofile inp)); try specialize (D (in_sigmask inp)); try specialize (D (in_urandom inp));
  try specialize (D (in_tmp inp)); try specialize (D (in_kernel inp)); try specialize (D (in_execfn inp));
  try specialize (D (in_sigpipe_default inp)); try specialize (D AsanUbsan.M.init_pc).
  unshelve eapply D;
  first [ exact tfib_img_facts | exact Hsp | exact Hbrk | exact Hva | exact Hve | exact Hfit | exact Hvl | exact Hlau
        | exact HE | exact Hx | exact Hgx | reflexivity | idtac ]. }
assert (HTU : YD1v.TOPF (bv_unsigned sp) <= bv_unsigned (ed_top rdraw)).
{ pose proof (length_entry_stack_image_launch Sv48 inp mbase TPH (Z_to_bv 64 (Z.of_N AsanUbsan.M.init_pc)) sp brk rdraw Hlau) as HL.
  pose proof Hlau as (HTV & _ & _). destruct HTV as (Hal & _ & _). unfold page_size in Hal.
  apply TOPF_le_top; [| exact Hal].
  pose proof (Nat2Z.is_nonneg (length (entry_stack_image inp mbase TPH (Z_to_bv 64 (Z.of_N AsanUbsan.M.init_pc)) sp rdraw))). lia. }
lazymatch type of HS with context [w_H ?W] =>
assert (HTK : stk_top (bv_unsigned sp) (mrestrict (w_H W) FULL)) end.
{ pose proof (st_ok_mem_ok tfibsegs _ _ _ HS) as HMEM. cbn [restrict ms_mem ss_main ss_mem] in HMEM.
intros a Ha Ha2. destruct (Z.lt_ge_cases a (bv_unsigned sp + 24)) as [Hl|Hl].
- apply (hdr_stk_present _ _ (smem_main true) (bv_unsigned sp) HMEM);
[unfold smem_main; right; left; reflexivity | reflexivity | exact Ulo | unfold sp_window_hi in Uhi; lia | lia].
- unfold mrestrict.
  match goal with |- context [w_H ?W (Z_to_bv 64 a)] => assert (Hw : w_H W (Z_to_bv 64 a) = false) end.
  { cbn [w_H W1]. unfold YD2i.H1. cbv beta. apply H1_high_false. intros Hg0.
    rewrite YA0j.ho_hid_high; [reflexivity | rewrite YK00.u64_lit by lia; unfold YA02.TOP; lia | exact Hg0]. }
  rewrite Hw. cbv iota.
  destruct (AH inp sp rdraw E (Z_to_bv 64 a)) eqn:Hg.
  * rewrite (HM (Z_to_bv 64 a) Hg).
    apply (wrap_mem_present inp mbase TPH (Z_to_bv 64 (Z.of_N AsanUbsan.M.init_pc)) sp brk rdraw a Hlau). lia.
  * pose proof (HFC0 (Z_to_bv 64 a) ltac:(rewrite YK00.u64_lit by lia; lia) Hg) as HFC.
    rewrite YK00.u64_lit in HFC by lia.
    pose proof (stkaux_of (kb_rseq (in_kernel inp)) h ch Hch) as Hchk.
    exact (stk_aux_present YA02.LIMIT (YA02.TOP sp) SINV _ (in_fs inp) ch E R FULL model _ HC Hchk a HFC ltac:(lia)). }
replace (CLOSEDX_args (in_argv inp) (in_fs inp)) with (CLOSEDX_args [a0; p] (in_fs inp)) by (rewrite Hargv; reflexivity).
eapply (tfib_arm_argv2 B HB ARL HCO HFILE HDIR sp brk mbase inp rdraw); eassumption.
- destruct (HST false I) as [HS HR].
replace (CLOSEDX_args (in_argv inp) (in_fs inp)) with (diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
2:{ clear -Hlen. unfold CLOSEDX_args. destruct (in_argv inp) as [|x [|y [|z r]]]; try reflexivity. cbn in Hlen. lia. }
eapply (tfib_usage B HB ARL xst est XFR ESTF FPU (EXS _) sp brk mbase inp rdraw); eassumption.
Qed.
End c.
End b.
