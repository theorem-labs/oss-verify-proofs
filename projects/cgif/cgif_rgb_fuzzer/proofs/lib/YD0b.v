(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK15 YK18 YK0d YK0f YK0a YA0c YA0e YA01 YA02 YA00 YB06 YB0l YB00
YB0r YG0h YG00 YG01 YG0u YF90 YQ0j YQ0b YQ0i YQ0a YQ04 YO3p YK05 YA0i YA0l YA0m YA0n
YB0z YD04 YD03 YD02 YD14 YD0f YG0d YD0g YD0h YD0v YD0r YD0n YD0k YD12
YD0y YD0z YD0u YD10 YD0c YD0i YD0s YCce YD05 YD09 YG05 YG0w
YK0p YCcx YCcd YD0x YD0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP07 YP01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
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
Lemma CLOSED_has_nil : forall inp, CLOSED inp [].
Proof.
intros inp. unfold CLOSED, CLOSED_args.
destruct (in_argv inp) as [|a0 [|p [|x r]]]; try apply diag_has_nil.
destruct (classify_open p (in_fs inp)); [apply diag_has_nil | |]; apply t_alt2_has_nil_l; apply diag_has_nil.
Qed.
#[local] Existing Instance YK11.fx0.
Section b. Context {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis HB : TraSyms B.
Let ARL : AR_laws trasegs B := AR_laws_ok trasegs B.
Let ML : model_laws (as_universe B) := model_laws_ok (as_universe B) (ts_universe B HB).
Hypothesis AMALLOC : amalloc_realizes trasegs B.
Hypothesis AFREE_A : forall fx : YK11.FPState, @afree_realizes fx rc trasegs B.
Let AFREE : afree_realizes trasegs B := AFREE_A _.
Hypothesis AICPY : aintrin_realizes trasegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : aread_check_stmt B.
Hypothesis LIBC : tra_rlibV_contract_all B.
Let MSITE : malloc_site_tfa B := tra_malloc_site B ML AMALLOC.
Let RCHK : read_check_tfa B := tra_read_check B ARDCHK.
Let MCPY : memcpy_site_tfa B := tra_memcpy_site B AICPY.
Let FREE : free_site_tfa B := tra_free_site B ML AFREE.
Let FREEN : free_null_site_tfa B := tra_free_null_site B ML AFREE.
Let FREE_A : forall fx : YK11.FPState, @free_site_tfa fx rc B := fun fx => tra_free_site B ML (AFREE_A fx).
Let FREEN_A : forall fx : YK11.FPState, @free_null_site_tfa fx rc B := fun fx => tra_free_null_site B ML (AFREE_A fx).
Let LIB_A : forall fx : YK11.FPState, @lib_site_rgb fx rc B := tra_rlib_site B LIBC.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis PF1_A : forall fx : YK11.FPState, @printf_first_tfa fx rc B xst.
Hypothesis PFN_A : forall fx : YK11.FPState, @printf_next_tfa fx rc B xst.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis ESTI : est_img_tfa est.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis FWS : fwrite_site_tfa B est.
Hypothesis RFS : refused_site_tfa B est.
Hypothesis FPO : fprintf_s_site_tfa B est 0x1d7cd (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est 0x1d7e2 (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est 0x158ff (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS_A : forall fx : YK11.FPState, @exit_site_tfa fx rc B est xst.
Let EXS : exit_site_tfa B est xst := EXS_A _.
Let OOM : oom_leaf_tfa B := tra_oom_leaf B HB ARL xst est XFR ESTF FWS EXS.
Let RDERR : rderr_leaf_tfa B := tra_rderr_leaf B HB ARL xst est XFR ESTF FPR EXS.
Let REFUSED : refused_leaf_tfa B := tra_refused_leaf B HB ARL xst est XFR ESTF RFS EXS.
Let SHORT : short_leaf_tfa B := tra_short_leaf B HB ARL ML xst est XFR ESTF FWS EXS FREE.
Let OVERRUN : overrun_leaf_tfa B := tra_overrun_leaf B HB ARL ML xst est XFR ESTF FWS EXS FREE.
Let EXITL : exit_leaf_tfa B xst := tra_exit_leaf B HB ARL xst est XFR ESTI ESTF EXS.
Let HCO : cannot_open_tfa B := tra_cannot_open B HB ARL xst est XFR ESTF FPO EXS.
Let EXITL_A : forall fx : YK11.FPState, @exit_leaf_tfa fx rc B xst := fun fx => tra_exit_leaf B HB ARL xst est XFR ESTI ESTF (EXS_A fx).
Let LOOPL : loop_L_tfa B xst := tra_loop_L B HB ARL ML xst LIB_A PF1_A PFN_A FREE_A FREEN_A EXITL_A XFR fp_frm_zero_fx0.
Let RUNQM : run_QM_tfa B := tra_run_QM B HB ARL ML MSITE MCPY FREE xst EXITL XFR LOOPL.
Let RUNQ : run_Q_tfa B := tra_run_Q B HB ARL xst LOOPL RUNQM.
Let POSTP : post_P_tfa B := tra_post_P B HB ARL RUNQ.
Let HDR : hdr_tfa B := tra_hdr B HB ARL SHORT OVERRUN POSTP.
Let RDD : rd0_dir_tfa B := tra_rd0_dir B HB ARL RDERR.
Let RDF : rd0_file_tfa B := tra_rd0_file B HB ARL ML MSITE OOM RCHK MCPY FREE REFUSED HDR.
Let HFILE : file_arm_tfa B := tra_file_arm B HB ARL ML MSITE OOM RDF.
Let HDIR : dir_arm_tfa B := tra_dir_arm B HB ARL ML MSITE OOM RDD.
Theorem tra_drv_main : forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
(FULL : word -> option byte) (model : Model),
valid_sp sp -> valid_brk TSEGS brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YN05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
(forall a0 p data, in_argv inp = [a0; p] -> fs_lookup (in_fs inp) p = Some data -> rrfc_universe B (payload_len data)) ->
HS_tra h = Some ch ->
cs_ok TSEGS TRA YA02.LIMIT (YA02.TOP sp)
(YA02.SINV0 TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
(forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) n) ->
(forall a, YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E a = true ->
FULL a = wrap_mem TPH sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw a) ->
srealizes TSEGS (cfg_of TSEGS R (pc ch) FULL model) (CLOSED inp).
Proof.
intros sp rdraw brk inp h ch E R FULL model Hsp Hbrk Hfit (Hva & Hve & Hvfs & _) Hceil HRUA Hch HC HE HM.
pose proof (tra_main_entry sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC HE HM (sliver_allowed sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC Hceil)    ) as (Hpc & HST & HAI & Hfs & Hfds & _).
destruct (tra_AR_init B HB sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC HE HM Hceil) as (ly & HAR & HTOP).
rewrite Hpc. change (cfg_of TSEGS R TRA_MAIN FULL model) with (mkCfg (mkst R (Z_to_bv 64 TRA_MAIN) FULL (seg_rom trasegs)) model).
change TSEGS with trasegs in HST, HAI, HAR |- *. unfold CLOSED.
destruct (Nat.eq_dec (length (in_argv inp)) 2) as [Hlen|Hlen].
- assert (Hargv : exists a0 p, in_argv inp = [a0; p]).
{ clear -Hlen. destruct (in_argv inp) as [|a0 [|p [|x r]]]; try (cbn in Hlen; lia). exists a0, p. reflexivity. }
destruct Hargv as (a0 & p & Hargv).
destruct (HST true ltac:(unfold two_ok; rewrite Hargv; cbn; lia)) as [HS HR].
replace (CLOSED_args (in_argv inp) (in_fs inp)) with (CLOSED_args [a0; p] (in_fs inp)) by (rewrite Hargv; reflexivity).
exact (tra_arm_argv2 B HB ARL HCO HFILE HDIR sp inp (xwE E R) (xdE inp)
(W1 sp rdraw inp Hsp Hva ch E model) (mkst R (Z_to_bv 64 TRA_MAIN) FULL (seg_rom trasegs)) model ly a0 p
Hargv Hsp Hva Hve Hfit Hvfs (fun data => HRUA a0 p data Hargv) HS HR HAI HAR HTOP Hfs Hfds).
- destruct (HST false I) as [HS HR].
replace (CLOSED_args (in_argv inp) (in_fs inp)) with (diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
2:{ clear -Hlen. unfold CLOSED_args. destruct (in_argv inp) as [|x [|y [|z r]]]; try reflexivity. cbn in Hlen. lia. }
exact (tra_usage B HB ARL xst est XFR ESTF FPU EXS sp inp (xwE E R) (xdE inp) (W1 sp rdraw inp Hsp Hva ch E model) (mkst R (Z_to_bv 64 TRA_MAIN) FULL (seg_rom trasegs))
model ly Hsp Hva Hve Hfit Hlen HS HR HAI HAR HTOP Hfs Hfds).
Qed.
Theorem tra_srealizes : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YN05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
(forall a0 p data, in_argv inp = [a0; p] -> fs_lookup (in_fs inp) p = Some data -> rrfc_universe B (payload_len data)) ->
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw YA02.LIMIT inp) (CLOSED inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil HRUA.
pose proof Hinp as (Hva & Hve & Hvfs & _ & [Huid Hgid] & Hnof & Hsig & Hhw & Hab & Hmmu & _).
destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw ab mmu urnd tmp]. cbn in *. subst ab mmu.
change (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp)
with (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp) in *.
apply (tra_startup_T1 sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp Hsp Hbrk Hva Hve Hfit Huid Hhw
(CLOSED (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)) (CLOSED_has_nil _)).
intros h c Hok.
destruct (HS_ok_open h sp rdraw brk argv envp uid hw (fs_seed_tmp fs tmp) c Hok) as (ch & E & R & FULL & model & Hch & -> & HC & HE & HM & _).
exact (tra_drv_main sp rdraw brk (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp) h ch E R FULL model
Hsp Hbrk Hfit Hinp Hceil HRUA Hch HC HE HM).
Qed.
End d.
End b.
