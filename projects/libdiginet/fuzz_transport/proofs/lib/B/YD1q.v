(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *) (* Modified by Theorem Labs, 2026-10: the unit's own library shape (lib/A/DecodeShape.v, decode_shape = ag_shape kept_shape, which states no image value) replaces the donor's YI0a / YI17 instance ff_lib_shape, which --no-stage never stages *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YD1q.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_decode's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the closed walk is proved with the float-state invariant P of the slot (tfib_srealizesXP); tfib_srealizesXF is it at cgif's exists-fx' slot (lib/A/YCfn.v tfib_lib_contract_xf_all, a zero rounding mode), and tfib_srealizesX, at the slot that keeps the float state (tfib_lib_contract_x_all), is its corollary at P = (fun fx => fx = YK11.fx0). *)
(* Modified by Theorem Labs, 2026-10: cgif_file's ff_lib_shape is replaced by this unit's decode_shape (patches/B_YD1q.v.patch), so its lemmas ff_unl_has_nil and ff_libk_has_nil are dropped, as pg-core dropped them from grant's A/AD1q.v; nothing else uses them. *)
(* Modified by Theorem Labs, 2026-10: YC5d and YCbq are Required from lib/Reusable: the lib/B copies were the Reusable files' text under lib.B (so lib/B had a second ameter_ops type beside the statement's), and they are deleted. *)
(* Modified by Theorem Labs, 2026-10: LIBX in each section is the slot at the harness's globals G := G_HARNESS_B (lib/B/TransportGB.v; lib/B/YCfn.v takes G, libreac/fuzz_pcap's G form, origin/ossv/recipes 198234fa4d3). *)
(* Relocated from proofs/libreac/fuzz_decode/lib/YD1q.v at 88154566652a by port_core 83f5203d2a2f onto libdiginet/fuzz_transport (asan-ubsan). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libdiginet.fuzz_transport.images Require Import AsanUbsan.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YG0f YG00 YG01 YG0n YG0d YK04 YA0i YA0n YI16. From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK09 YA0c YA0e YA01 YA02. From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB12 YB1h YB01 YB1n. From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YCbq YC5d. From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YCbp. From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YCfn.


From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YI16. From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import TransportShape.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0f YG0d. From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YF0m YCeg YD1v YD1w YD1x YD1i. From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YC5d. From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YCfn YD1p.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import TransportGB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance transport_shape.
Section b. Context {rc : YM05.RunCeil}.
Definition drv_mainX_stmt : Prop :=
forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
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
(* The start-up part of the closed walk, at YK11.fx0: from the start state to the driver's main. *)
Lemma tfib_srealizesX_of_main : drv_mainX_stmt -> forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw YA02.LIMIT inp) (SPECX inp).
Proof.
intros DRV_MAINX sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
pose proof Hinp as (Hva & Hve & Hvfs & _ & [Huid Hgid] & Hnof & Hsig & Hhw & Hab & Hmmu & _).
destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw ab mmu urnd tmp].
cbn in Hsp, Hbrk, Hmb, Hfit, Hinp, Hceil, Hva, Hve, Hvfs, Huid, Hgid, Hnof, Hsig, Hhw, Hab, Hmmu |- *. subst ab mmu.
change (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp)
with (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp) in *.
apply (srz_conseq TSEGS _ (CLOSEDX (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)));
[| apply t_eq_sym; apply specx_closedx_eq].
apply (tfib_startup_T1 sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp Hsp Hbrk Hva Hve Hfit Huid Hhw
(CLOSEDX (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)) (CLOSEDX_has_nil _)).
intros h c Hok.
destruct (HS_ok_open h sp rdraw brk argv envp uid hw (fs_seed_tmp fs tmp) c Hok) as (ch & E & R & FULL & model & Hch & -> & HC & HE & HM & _).
exact (DRV_MAINX sp rdraw brk (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp) h ch E R FULL model
Hsp Hbrk Hfit Hinp Hceil Hch HC HE HM).
Qed.
(* The closed walk with the float-state invariant P: the walk starts at YK11.fx0 (P0), each call of
   LLVMFuzzerTestOneInput returns at some float state with P (LIBX, lib/A/YCfn.v tfib_lib_contract_xP), and the driver
   goes on at that state; so the hypotheses the driver uses after a call (AFREE, PF1, PFN, EXS) are asked at every
   float state with P. *)
Section dP.
Variable P : YK11.FPState -> Prop.
Hypothesis P0 : P YK11.fx0.
Variable B : asyms.
Hypothesis HB : TransportSyms B.
Hypothesis AMALLOC : amalloc_realizes tfibsegs B.
Hypothesis AFREE : forall fx : YK11.FPState, P fx -> afree_realizes (fx := fx) tfibsegs B.
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : aread_check_stmt B.
Variables (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z).
Hypothesis MT_FREE : forall S m, mo_ok MT S m.
Hypothesis RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a.
Hypothesis LIBX : forall fx : YK11.FPState, P fx -> tfib_lib_contract_xP (fx := fx) G_HARNESS_B B MT XM_LIB XN_LIB RLO RHI P.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis PF1 : forall fx : YK11.FPState, P fx -> printf_first_tfa (fx := fx) B xst.
Hypothesis PFN : forall fx : YK11.FPState, P fx -> printf_next_tfa (fx := fx) B xst.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis ESTI : est_img_tfa est.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis FWS : fwrite_site_tfa B est.
Hypothesis RFS : refused_site_tfa B est.
Hypothesis FPO : fprintf_s_site_tfa B est 0x1d83f (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est 0x1d854 (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est 0x15860 (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS : forall fx : YK11.FPState, P fx -> exit_site_tfa (fx := fx) B est xst.
Theorem tfib_srealizesXP : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw YA02.LIMIT inp) (SPECX inp).
Proof.
exact (tfib_srealizesX_of_main (tfib_drv_main P P0 B HB AMALLOC AFREE AICPY ARDCHK MT XM_LIB XN_LIB RLO RHI MT_FREE RO_IN LIBX
xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS)).
Qed.
End dP.
(* The closed walk at cgif's exists-fx' slot (lib/A/YCfn.v tfib_lib_contract_xf_all): the entry function may return
   with changed float registers, at a zero rounding mode; P is a zero rounding mode, which holds at YK11.fx0. *)
Section dF.
Variable B : asyms.
Hypothesis HB : TransportSyms B.
Hypothesis AMALLOC : amalloc_realizes tfibsegs B.
Hypothesis AFREE : forall fx : YK11.FPState, frm_zero (@fp_csr fx) -> afree_realizes (fx := fx) tfibsegs B.
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : aread_check_stmt B.
Variables (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z).
Hypothesis MT_FREE : forall S m, mo_ok MT S m.
Hypothesis RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a.
Hypothesis LIBX : tfib_lib_contract_xf_all G_HARNESS_B B MT XM_LIB XN_LIB RLO RHI.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis PF1 : forall fx : YK11.FPState, frm_zero (@fp_csr fx) -> printf_first_tfa (fx := fx) B xst.
Hypothesis PFN : forall fx : YK11.FPState, frm_zero (@fp_csr fx) -> printf_next_tfa (fx := fx) B xst.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis ESTI : est_img_tfa est.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis FWS : fwrite_site_tfa B est.
Hypothesis RFS : refused_site_tfa B est.
Hypothesis FPO : fprintf_s_site_tfa B est 0x1d83f (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est 0x1d854 (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est 0x15860 (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS : forall fx : YK11.FPState, frm_zero (@fp_csr fx) -> exit_site_tfa (fx := fx) B est xst.
Theorem tfib_srealizesXF : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw YA02.LIMIT inp) (SPECX inp).
Proof.
exact (tfib_srealizesXP (fun fx : YK11.FPState => frm_zero (@fp_csr fx)) fp_frm_zero_fx0 B HB AMALLOC AFREE AICPY ARDCHK
MT XM_LIB XN_LIB RLO RHI MT_FREE RO_IN (fun fx Hz => tfib_lib_contract_xP_of_xf (fx := fx) G_HARNESS_B B MT XM_LIB XN_LIB RLO RHI Hz (LIBX fx))
xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS).
Qed.
End dF.
(* The closed walk at the slot that keeps the float state (lib/A/YCfn.v tfib_lib_contract_x_all): the corollary of
   tfib_srealizesXP at P = (fun fx => fx = YK11.fx0), whose slot is tfib_lib_contract_xP_pinned at YK11.fx0. *)
Section d.
Variable B : asyms.
Hypothesis HB : TransportSyms B.
Hypothesis AMALLOC : amalloc_realizes tfibsegs B.
Hypothesis AFREE : afree_realizes tfibsegs B.
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : aread_check_stmt B.
Variables (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z).
Hypothesis MT_FREE : forall S m, mo_ok MT S m.
Hypothesis RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a.
Hypothesis LIBX : tfib_lib_contract_x_all G_HARNESS_B B MT XM_LIB XN_LIB RLO RHI.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis PF1 : printf_first_tfa B xst.
Hypothesis PFN : printf_next_tfa B xst.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis ESTI : est_img_tfa est.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis FWS : fwrite_site_tfa B est.
Hypothesis RFS : refused_site_tfa B est.
Hypothesis FPO : fprintf_s_site_tfa B est 0x1d83f (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est 0x1d854 (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est 0x15860 (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS : exit_site_tfa B est xst.
Theorem tfib_srealizesX : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw YA02.LIMIT inp) (SPECX inp).
Proof.
refine (tfib_srealizesXP (fun fx : YK11.FPState => fx = YK11.fx0) eq_refl B HB AMALLOC _ AICPY ARDCHK MT XM_LIB XN_LIB RLO RHI
MT_FREE RO_IN _ xst XFR _ _ est ESTI ESTF FWS RFS FPO FPR FPU _);
intros fx Hfx; cbv beta in Hfx; subst fx;
first [exact AFREE | exact PF1 | exact PFN | exact EXS
| exact (tfib_lib_contract_xP_pinned (fx := YK11.fx0) G_HARNESS_B B MT XM_LIB XN_LIB RLO RHI (fun fx : YK11.FPState => fx = YK11.fx0) eq_refl
(LIBX YK11.fx0))].
Qed.
End d.
End b.
