From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1p.v (origin/ossv/recipes c8557374ad2e), with its module paths changed, names TfibSyms -> PcapSyms and its addresses moved to libreac/fuzz_pcap's ASan build. ADAPTED to pcap's program contract (the porter, 2026-10-28: "the program contract is tfib_lib_contract_x_all {rc} (SK : YI16.sink_head) stk G B MT XM_LIB XN_LIB RLO RHI KS, SK EXPLICIT, never inferred"): the donor's LIBC (cgif lib/A/ACfn.v tfib_lib_contract_x, AD1p.v:49) is lib/A/Prog/PcapEntry.v's at the ASan image (SK explicit, G_HARNESS, pcap_KS; RLO / RHI fixed to PcapRelro.v's PCAP_RLO / PCAP_RHI, which lib/A/ACeg.v's in_ro_tfa names, so the donor's RO_IN goes); the output shape is fixed to AgreePcap.ag_out_shape (the one PcapEntry.v states LIBK at; = PcapAsanTop.pcap_shape) instead of the donor's generic {LS}; the sink head is the Section's SK with pcap_head (lib/A/AD1u.v). The proof of tfib_drv_main is the donor's. rule 24: no function proved anew. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_pcap.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02 YA00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB12 AB1h AB01 AB1n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0f YG00 YG01 YG0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AF0m.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP09 YP0l YP08 YP03 YN3q YK04 YA0i YA0n YA0o YA0p.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YD1h.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AD1g AD1f AD2i AD1t.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AD1v AD1w AD2a AD26 AD22 AD1z AD2g AD2c AD2d AD29 AD2e AD1r AD1x AD27 AD1i AD1n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG05 YG0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import ACeg AD1u AD1m AD2k.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require AgreePcap.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSourceK.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapRelro PcapEntry PcapEntryA.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
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
(* The output shape pcap's program contract states LIBK at (PcapEntry.v:51; = PcapAsanTop.pcap_shape). *)
#[local] Existing Instance AgreePcap.ag_out_shape.
Section b. Context {rc : YM05.RunCeil}.
(* Fully qualified: AgreePcap loads lib/U's twin of YI16, so the short qualifier `YI16` is ambiguous here. *)
Context {SK : OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI16.sink_head} {PH : pcap_head}.
Section c.
Variable B : asyms.
Hypothesis HB : PcapSyms B.
Let ARL : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let ML : model_laws (as_universe B) := model_laws_ok (as_universe B) (ts_universe B HB).
Hypothesis AMALLOC : amalloc_realizes tfibsegs B.
Hypothesis AFREE : afree_realizes tfibsegs B.
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : aread_check_stmt B.
Variables (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z).
Hypothesis MT_FREE : forall S m, mo_ok MT S m.
(* donor AD1p.v:49 LIBC, at pcap's program contract (lib/A/Prog/PcapEntry.v, SK explicit; RLO / RHI are
   PCAP_RLO / PCAP_RHI, which in_ro_tfa already names, so the donor's RO_IN is not needed). *)
Hypothesis LIBC : tfib_lib_contract_x SK tfibsegs PCAP_RLO PCAP_RHI A_LLVMF RA_LLVMF A_EMPTY LLVMF_STK G_HARNESS B MT XM_LIB XN_LIB pcap_KS.
Let MSITE : malloc_site_tfa B := tfib_malloc_site B ML AMALLOC.
Let RCHK : read_check_tfa B := tfib_read_check B ARDCHK.
Let MCPY : memcpy_site_tfa B := tfib_memcpy_site B AICPY.
Let FREE : free_site_tfa B := tfib_free_site B ML AFREE.
Let FREEN : free_null_site_tfa B := tfib_free_null_site B ML AFREE.
Let LIB : lib_site_x B := tfib_lib_site_x B MT XM_LIB XN_LIB MT_FREE LIBC.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis PF1 : printf_first_tfa B xst.
Hypothesis PFN : printf_next_tfa B xst.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis ESTI : est_img_tfa est.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis FWS : fwrite_site_tfa B est.
Hypothesis RFS : refused_site_tfa B est.
Hypothesis FPO : fprintf_s_site_tfa B est (symaddr (Symbols.Asan.Sec.s_rodata + 0xd351)%Z) (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est (symaddr (Symbols.Asan.Sec.s_rodata + 0xd366)%Z) (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est (symaddr (Symbols.Asan.Sec.s_rodata + 0x553c)%Z) (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS : exit_site_tfa B est xst.
Let RDERR : rderr_leaf_tfa B := tfib_rderr_leaf B HB ARL xst est XFR ESTF FPR EXS.
Let REFUSED : refused_leaf_tfa B := tfib_refused_leaf B HB ARL xst est XFR ESTF RFS EXS.
Let SHORT : short_leaf_tfa B := tfib_short_leaf B HB ARL ML xst est XFR ESTF FWS EXS FREE.
Let OVERRUN : overrun_leaf_tfa B := tfib_overrun_leaf B HB ARL ML xst est XFR ESTF FWS EXS FREE.
Let EXITL : exit_leaf_tfa B xst := tfib_exit_leaf B HB ARL xst est XFR ESTI ESTF EXS.
Let HCO : cannot_open_tfa B := tfib_cannot_open B HB ARL xst est XFR ESTF FPO EXS.
Let LOOPL : loop_L_x B xst := tfib_loop_L B HB ARL ML xst LIB PF1 PFN FREE FREEN EXITL XFR.
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
pose proof (tfib_main_entry sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC HE HM (sliver_allowed sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC Hceil)    ) as (Hpc & HST & HAI & Hfs & Hfds & _).
set (ly := AD1g.ly0 ch E model).
assert (HAR : AR TSEGS B ly init_state (W1 sp rdraw inp Hsp Hva ch E model) FULL model) by (eapply (tfib_AR B HB); eassumption).
assert (HTOP : AD1v.top_ok (bv_unsigned sp) ly) by (eapply tfib_top_ok; eassumption).
assert (HFI : FINV ly (w_H (W1 sp rdraw inp Hsp Hva ch E model)) FULL) by exact (tfib_finv_handoff sp rdraw brk inp Hsp Hva h ch E R FULL model Hch HC).
rewrite Hpc. change (cfg_of TSEGS R TFIB_MAIN FULL model) with (mkCfg (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom tfibsegs)) model).
change TSEGS with tfibsegs in HST, HAI, HAR |- *. unfold CLOSEDX.
destruct (Nat.eq_dec (length (in_argv inp)) 2) as [Hlen|Hlen].
- assert (Hargv : exists a0 p, in_argv inp = [a0; p]).
{ clear -Hlen. destruct (in_argv inp) as [|a0 [|p [|x r]]]; try (cbn in Hlen; lia). exists a0, p. reflexivity. }
destruct Hargv as (a0 & p & Hargv).
destruct (HST true ltac:(unfold two_ok; rewrite Hargv; cbn; lia)) as [HS HR].
replace (CLOSEDX_args (in_argv inp) (in_fs inp)) with (CLOSEDX_args [a0; p] (in_fs inp)) by (rewrite Hargv; reflexivity).
exact (tfib_arm_argv2 B HB ARL HCO HFILE HDIR sp inp (xwE E R) (xdE inp)
(W1 sp rdraw inp Hsp Hva ch E model) (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom tfibsegs)) model ly a0 p
Hargv Hsp Hva Hve Hfit Hvfs HS HR HAI HAR HTOP HFI Hfs Hfds).
- destruct (HST false I) as [HS HR].
replace (CLOSEDX_args (in_argv inp) (in_fs inp)) with (diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
2:{ clear -Hlen. unfold CLOSEDX_args. destruct (in_argv inp) as [|x [|y [|z r]]]; try reflexivity. cbn in Hlen. lia. }
exact (tfib_usage B HB ARL xst est XFR ESTF FPU EXS sp inp (xwE E R) (xdE inp) (W1 sp rdraw inp Hsp Hva ch E model) (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom tfibsegs))
model ly Hsp Hva Hve Hfit Hlen HS HR HAI HAR HTOP Hfs Hfds).
Qed.
End c.
End b.
