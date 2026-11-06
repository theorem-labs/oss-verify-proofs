(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/APgLib.v of this library, for fuzz_knock's ASan-UBSan
   image (fuzz_knock.asan-ubsan, sha256 f834165f5002e65398e68d514ab2a5a5b10e53144f0b41b93ebbc6f895290e82), made the way
   proofs/cgif/cgif_file_fuzzer/lib/YCfn.v / YCfj.v / YCfh.v / YCfi.v are made from lib/A/ACfn.v / ACfj.v / ACfh.v /
   ACfi.v at c8557374ad2e (the sources of lib/A/APgLib.v: ACfn.v:22-72 the contract, ACfj.v:180-255 its proof,
   ACfh.v:29-50 and 153-164 the journal facts, ACfi.v:56-140 the links and the closed form), with their module paths
   changed. rule 24: no function proved.
   - The imports move to the lib/AU twins (AWalkFw0 YCef YF0l YCej YCeh YCem YCep AWalkFw1 AWalkFw2 YCfm APgRt APgMain0
     YE2k YF0m YD2l YF0s APgImg APgImgLink); the constants are lib/AU/YCfm.v's (A_EMPTY 0x5d0be0); the read-only pair is the asan-ubsan
     .data.rel.ro start .. .got end, RO_LO 0x960b8 .. RO_HI 0x97310 (lib/AU/YCeh.v in_ro_tfa); tfib_K and
     tfib_sink_head are lib/AU/YE2k.v's (ofl_head 0x5f1c08), passed by name at every SK use, with the same sink-head
     guard as the A file.
   - S0 is lib/AU/APgMain0.knock_lib_A_seg, S1 .. S7 lib/AU/APgMain2.rt_H; rt_H's callee contracts TKINIT / TKHEARD
     / TKSTEP (asan-ubsan entries 0x7f480 / 0x7f520 / 0x7f5b0) are discharged in the closed form by a Theorem Labs lane's
     lib/AU/APgInit.v / APgHeard.v / APgStep.v at PI_knock_asanubsan through lib/AU/APgImgLink.v.
   - The closed form knock_lib_x_all is at TfibB (lib/AU/YD2l.v), ameter_triv, XL0 and RO_LO / RO_HI; ASM1 is
     lib/AU/YF0s.v's stack_malloc1_contract, TL and LAWS are a Theorem Labs lane's lib/AU/APgImgLink.v tfibX_lib / tfibX_LAWS;
     AIL is discharged by the core's lib/AU/YD1u.v tfib_AIL at TfibB (TfibB_syms, lib/AU/YD2l.v), the twin of the A
     file's lib/A/AD1u.v tfib_AIL, so the closed form's one hypothesis left is LEAF (LIBK pl fs K = K (LL 0 fs [])). *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00 YI04.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG05 YG0q YG0t.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import APgCSpec.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import APgBase.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep AWalkFw1 AWalkFw2 YCfm APgRt.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import APgMain0.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import YE2k YF0m YD2l YF0s APgImg APgImgLink.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require YD1u.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import APgLoop0 APgMainL APgMain1 APgMain2 APgInit APgHeard APgStep.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YP0b YC4a YC1f YI0w YI0y.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YI5b.
(* SINK-HEAD GUARD (a Theorem Labs lane's Theorem Labs guard, the form of omx-clap-core fuzz_state lib/A/FSH_Gen.v:49 and
   FSH_Harness.v:32): this file's load closure has the plain build's `#[global] Instance src0_sink_head` (Reusable/YI5b.v:12,
   ofl_head src0_D_ofl_head). It is removed, #[global], so no {SK : YI16.sink_head} is inferred in this file or in a
   file that loads it. lib/AU/YE2k.v's tfib_sink_head (knock asan-ubsan, 0x5f1c08) is a plain Definition, not an
   instance (the twin of the core's lib/A/AE2k.v), so every SK below is passed by name (tfib_sink_head). *)
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
(* The PLAIN sink_syms / sink_laws instances (YI5c.src0_sink, src0_sink_laws) are NOT in this file's closure:
   `Remove Hints YI5c.src0_sink` here fails with "reference not found". knock's asan-ubsan symbols are
   YE2k.tfib_K, passed by name everywhere. *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* knock asan-ubsan .data.rel.ro start .. .got end (section headers), the second disjunct of AU/YCeh.v in_ro_tfa *)
Definition RO_LO : Z := 0x960b8.
Definition RO_HI : Z := 0x97310.

(* ============================== the contract [A/ACfn.v:22-72] ============================== *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Local Notation segs := tfibsegs.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Definition knock_lib_pre_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (pl : list byte) (M : Z) : Prop :=
afn_pre segs B LLVMF_STK ly S W regs mem md [] /\
raZ regs = RA_LLVMF /\
getr regs 10 = w64 p /\ getr regs 11 = w64 n /\
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
n = Z.of_nat (length pl) /\ garr8 segs (rd W mem) p (map (fun b : byte => bv_unsigned b) pl) /\
frames S = [] /\ st_nev S + EV_LIB <= EV_MAX /\ blocks_bytes S + LIVE_LIB <= LIVE_MAX /\
arodata_okS segs B RLO RHI (aview segs (w_H W) mem) /\
asink_none segs tfib_K (rd W mem) md /\
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
Fs.fs_sorted (m_fs md) = true /\
ameta_inv segs tfib_K ly (rd W mem) M /\
mo_ok MT S (XM_LIB n).
Definition knock_lib_post_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (M : Z) (l : lleaf)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
ajournal (SK := tfib_sink_head) segs B LLVMF_STK (spZ regs) [sink_token] ly S W mem md [] ly' S' W' mem' md' k /\ k <= EV_LIB /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\
(forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
asink_none segs tfib_K (rd W' mem') md' /\
ameta_inv segs tfib_K ly' (rd W' mem') M /\
mo_le MT S S' (XN_LIB n) /\
(forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)).
Definition knock_lib_contract_x : Prop :=
forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet),
AI segs (w_H W) (w_A W) md ->
knock_lib_pre_x regs ly S W mem md p n pl M ->
(forall (l : lleaf) (W' : world segs) (c' : config),
wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(exists ly' S' regs' mem' md' k,
c' = cfg_at segs RA_LLVMF regs' mem' md' /\
knock_lib_post_x regs ly S W mem md p n M l ly' S' W' regs' mem' md' k) ->
srealizes segs c' (K l)) ->
srealizes segs (cfg_at segs A_LLVMF regs mem md) (LIBK pl (m_fs md) K).
End a.
Definition knock_lib_contract_x_all {rc : YM05.RunCeil} {LS : lib_shape} (B : asyms) (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) : Prop :=
forall fx : YK11.FPState, @knock_lib_contract_x fx rc LS B MT XM_LIB XN_LIB RLO RHI.

(* ============================== journal facts [A/ACfh.v:29-50, 153-164] ============================== *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Section e.
Variable segs : list Segment.
Variable B : asyms.
Lemma ajournal_fp_nil : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal (SK := SK) segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
ajournal (SK := SK) segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_mono; [|exact Hio]; intros Ho; exfalso; exact (sink_closed_nil Ho)|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|].
split; [intros p n i H1 H2 Hi _; apply (F2 p n i H1 H2 Hi); apply inFP_nil|].
split; [intros a Hi Hns He _; apply (F3 a Hi Hns He); apply (fp_spares_closed (SK := SK)); intros Ho; exact (sink_closed_nil Ho)|].
split; [intros cid pos a H1 H2 _; apply (F4 cid pos a H1 H2); apply inFP_nil|].
split; [intros p n i H1 H2 Hi; exfalso; exact (inFP_nil _ (Hgone p n i H1 H2 Hi))|].
split; [exact Hpres|]. split; [exact Hstatic|]. split; [exact F5 | exact HQT].
Qed.
Lemma ajournal_closed_io : forall STK sp0 FP ly S (W : world segs) mem md own ly' S' W' mem' md' k,
~ YI16.sink_open_fp FP ->
ajournal (SK := SK) segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k Hcl HJ. pose proof HJ as (_ & _ & _ & _ & Hos & _).
destruct (aos_step_closed FP md md' Hcl Hos) as (Efd & Efsys & _ & _).
unfold m_fds, m_fs. rewrite Efd, Efsys. split; reflexivity.
Qed.
Lemma ajournal_nil_io : forall STK sp0 ly S (W : world segs) mem md own ly' S' W' mem' md' k,
ajournal (SK := SK) segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof. intros until 0. intros HJ. exact (ajournal_closed_io _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sink_closed_nil HJ). Qed.
End e.
Section f.
Variable segs : list Segment.
Lemma srz_enter : forall (W : world segs) (c : config) (T : TSet),
AI segs (w_H W) (w_A W) (cfg_model c) ->
SRr segs W c (fun W' c' => AI segs (w_H W') (w_A W') (cfg_model c') -> srealizes segs c' T) -> srealizes segs c T.
Proof. intros W c T HAI HS. apply (HS HAI T). intros W' c' _ HAI' HK. exact (HK HAI'). Qed.
End f.
End d.

(* ============================== the proof [A/ACfj.v:180-255] ============================== *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM1 : astack_malloc_realizes tfibsegs B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis AIL : asink_img_laws (SK := tfib_sink_head) tfibsegs B tfib_K.
(* the three callee contracts at their asan-ubsan addresses: lib/AU/APgMain2.rt_H's TKINIT / TKHEARD / TKSTEP *)
Hypothesis TKINIT : tknock_init_specX (SK := tfib_sink_head) tfibsegs B MT A_reac_knock_init.
Hypothesis TKHEARD : tknock_heard_specX (SK := tfib_sink_head) tfibsegs B MT A_reac_knock_heard.
Hypothesis TKSTEP : tknock_step_specX (SK := tfib_sink_head) tfibsegs B MT A_reac_knock_step.
Variable XL : Z -> Z.
Hypothesis HXL : forall n, 0 <= XL n.
Hypothesis LEAF : forall pl fs (K : lleaf -> TSet), LIBK pl fs K = K (LL 0 fs []).
(* the asan-ubsan harness walk S1 .. S7 from ss_H (lib/AU/APgMain2.rt_H, cgif's lx_RA2, YCfj.v) *)
Let RH : rt_from (SK := tfib_sink_head) B MT [] (rt_post (SK := tfib_sink_head) B MT []) ss_H (INV_0 B MT 0) :=
rt_H (SK := tfib_sink_head) B MT [] MTL TL LAWS ML ASF FFL MTF eq_refl TKINIT TKHEARD TKSTEP.
Theorem knock_lib_x_body :
forall ly S (W : world tfibsegs) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet),
AI tfibsegs (w_H W) (w_A W) md ->
knock_lib_pre_x B MT XL RO_LO RO_HI regs ly S W mem md p n pl M ->
(forall (l : lleaf) (W' : world tfibsegs) (c' : config),
wle W W' -> AI tfibsegs (w_H W') (w_A W') (cfg_model c') ->
(exists ly' S' regs' mem' md' k,
c' = cfg_at tfibsegs RA_LLVMF regs' mem' md' /\
knock_lib_post_x B MT XL regs ly S W mem md p n M l ly' S' W' regs' mem' md' k) ->
srealizes tfibsegs c' (K l)) ->
srealizes tfibsegs (cfg_at tfibsegs A_LLVMF regs mem md) (LIBK pl (m_fs md) K).
Proof.
intros ly S W regs mem md p n pl M K HAI HPRE HK.
rewrite LEAF.
destruct HPRE as (HPRE0 & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr0 & Hev & Hlive & HROS & HSNK & HFD & HSORT & HAM & HMOK).
assert (HROD : arodata_ok B (aview tfibsegs (w_H W) mem)) by (intros a Ha; apply (HROS a); exact Ha).
apply (srz_enter tfibsegs W (cfg_at tfibsegs A_LLVMF regs mem md) _ HAI).
eapply SRr_mono.
{ exact (knock_lib_A_seg (SK := tfib_sink_head) B MT MTL TL LAWS ML ASM1 SMP FFL MTF
[] (rt_post (SK := tfib_sink_head) B MT []) RH
ly S W regs mem md p n (XL n) HPRE0 Hra Hp Hn Hpn Hfr0 Hev Hlive HROD HMOK (HXL n)). }
intros W' c' Hwle (fpos & sp1 & E0 & HPOST) HAI'.
unfold rt_post, rt_postP in HPOST.
destruct HPOST as (ly' & S' & regs' & mem' & md' & k' & -> & HJ & Hk & HPR & Ha0 & HPerm & HMLE & _).
cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_fpos c_sp1 c_E0 c_T] in HJ, HPR, HPerm, HMLE.
destruct (ajournal_nil_io tfib_sink_head tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Efds Efs].
apply (HK (LL 0 (m_fs md) []) W' _ Hwle HAI').
exists ly', S', regs', mem', md', k'. split; [reflexivity|].
unfold knock_lib_post_x. cbn [ll_fs ll_ret ll_out].
assert (HSNK' : asink_none tfibsegs tfib_K (mrestrict (w_H W') mem') md').
{ eapply (asink_none_kept (SK := tfib_sink_head) tfibsegs B tfib_K AIL); [exact HJ | intros Ho; exact (sink_closed_nil Ho) | exact HSNK]. }
split; [apply (ajournal_fp_nil tfib_sink_head); exact HJ|]. split; [exact Hk|]. split; [exact HPR|]. split; [exact Ha0|].
split; [exact HPerm|].
split; [intros fd; rewrite Efds; reflexivity|].
split; [exact Efs|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HSORT|].
split; [exact HSNK'|].
split; [exact (ameta_inv_kept (SK := tfib_sink_head) tfibsegs B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HAM)|].
split; [exact HMLE|].
intros i Hi. destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; clear - Hi Hn0; lia|].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 p n i Hpin).
- eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. exact Hpin.
- unfold req_size. destruct (Z.eqb_spec n 0) as [Heq0|Hne0]; [exfalso; clear - Hnpos Heq0; lia | exact Hi].
- apply inFP_nil.
Qed.
Theorem knock_lib_x : knock_lib_contract_x B MT XL XL RO_LO RO_HI.
Proof. exact knock_lib_x_body. Qed.
End h.
End g.

(* ============================== the links and the closed form [A/ACfi.v:39-140] ============================== *)
Definition XL0 : Z -> Z := fun _ => 0.
Lemma XL0_HXL : forall n, 0 <= XL0 n.
Proof. intros n. unfold XL0. lia. Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Lemma link_ML : model_laws (as_universe B).
Proof. exact (model_laws_ok (as_universe B) (ts_universe B HB)). Qed.
Lemma link_SMP : stack_malloc_progressP B.
Proof. intros s cid W Hc Hn. exact (stack_malloc_progress (as_universe B) s cid W Hc Hn). Qed.
Lemma link_FFL : frame_flag_lawP tfibsegs B.
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (tfib_img_cover ly S md L) as [C1 C2].
unfold TFIB_IMG_LO, TFIB_IMG_END, YImgTop.IMG_LO, YImgTop.IMG_TOP in C1, C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil].
unfold zone2, off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma link_ASF : astack_free_law tfibsegs B.
Proof. exact (astack_free_law_ok tfibsegs B). Qed.
(* knock's harness frame is class 1 (`li a0,128` at 0x7ef40, `jal __asan_stack_malloc_1` at 0x7ef44) *)
Lemma link_ASM1 : astack_malloc_realizes tfibsegs B 1.
Proof. exact (stack_malloc1_contract B LAWS HB). Qed.
End c.
End b.
Section f. Context {rc : YM05.RunCeil} {LS : lib_shape}.
Hypothesis LEAF : forall pl fs (K : lleaf -> TSet), LIBK pl fs K = K (LL 0 fs []).
(* the callee contracts: a Theorem Labs lane's walks pb_knock_initX / pb_knock_heardX / pb_knock_stepX (lib/AU/APgInit.v,
   APgHeard.v, APgStep.v) at PI_knock_asanubsan, through a Theorem Labs lane's bridge lib/AU/APgImgLink.v (tfibX_init0 / heard0 /
   step0, tfibX_LAWS, tfibX_PALib0, tfibX_AMEMSET) *)
Lemma knock_TKINIT : forall fx : YK11.FPState,
tknock_init_specX (fx := fx) (SK := tfib_sink_head) tfibsegs TfibB ameter_triv A_reac_knock_init.
Proof.
intros fx. unfold A_reac_knock_init. rewrite <- tfibX_init0.
eapply (pb_knock_initX (SK := tfib_sink_head) (PI := PI_knock_asanubsan));
first [exact tfibX_LAWS | exact tfibX_PALib0 | exact ameter_triv_laws | exact tfibX_AMEMSET].
Qed.
Lemma knock_TKHEARD : forall fx : YK11.FPState,
tknock_heard_specX (fx := fx) (SK := tfib_sink_head) tfibsegs TfibB ameter_triv A_reac_knock_heard.
Proof.
intros fx. unfold A_reac_knock_heard. rewrite <- tfibX_heard0.
eapply (pb_knock_heardX (SK := tfib_sink_head) (PI := PI_knock_asanubsan));
first [exact tfibX_LAWS | exact tfibX_PALib0 | exact ameter_triv_laws].
Qed.
Lemma knock_TKSTEP : forall fx : YK11.FPState,
tknock_step_specX (fx := fx) (SK := tfib_sink_head) tfibsegs TfibB ameter_triv A_reac_knock_step.
Proof.
intros fx. unfold A_reac_knock_step. rewrite <- tfibX_step0.
eapply (pb_knock_stepX (SK := tfib_sink_head) (PI := PI_knock_asanubsan));
first [exact tfibX_LAWS | exact tfibX_PALib0 | exact ameter_triv_laws].
Qed.
Theorem knock_lib_x_all : knock_lib_contract_x_all TfibB ameter_triv XL0 XL0 RO_LO RO_HI.
Proof.
intros fx.
exact (knock_lib_x (fx := fx) (LS := LS) TfibB ameter_triv ameter_triv_laws tfibX_lib tfibX_LAWS
(link_ML TfibB TfibB_syms) (link_ASM1 TfibB TfibB_syms) (link_SMP TfibB) (link_ASF TfibB) (link_FFL TfibB)
(* AIL: the core's tfib_AIL (lib/AU/YD1u.v) at knock's symbols TfibB, with TfibSyms TfibB from lib/AU/YD2l.v *)
ameter_triv_fs_laws (YD1u.tfib_AIL TfibB TfibB_syms) (knock_TKINIT fx) (knock_TKHEARD fx) (knock_TKSTEP fx) XL0 XL0_HXL LEAF).
Qed.
End f.

(* ============================== the bridge to the core's contract [AU/YCfn.v:43-82] ============================== *)
(* The asan-ubsan twin of the bridge at the end of lib/A/APgLib.v. The AU core (lib/AU/YD1m.v) takes the relocated
   donor contract YCfn.tfib_lib_contract_x_all; this file proves knock_lib_contract_x_all. The two texts are the same, with YCfn's
   constants for YCfm's: A_LLVMF 0x7eed0, RA_LLVMF 0x7edcc, A_EMPTY 0x5d0be0, LIVE_LIB 2 ^ 33 and LLVMF_STK 32768 are
   equal in both (tfib_knock_consts), and EV_LIB is 2000 in YCfn and 0 in YCfm (tfib_knock_ev). So YCfn's pre gives
   knock's pre (st_nev S + 2000 <= EV_MAX gives st_nev S + 0 <= EV_MAX), knock's post gives YCfn's post (k <= 0 gives
   k <= 2000), and knock's contract gives YCfn's at the same B MT XM_LIB XN_LIB RLO RHI. YCfn is Required, not
   Imported, so its names keep the YCfn prefix and the names above stay YCfm's. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require YCfn.
Lemma tfib_knock_consts :
  YCfn.A_LLVMF = A_LLVMF /\ YCfn.RA_LLVMF = RA_LLVMF /\ YCfn.A_EMPTY = A_EMPTY /\
  YCfn.LIVE_LIB = LIVE_LIB /\ YCfn.LLVMF_STK = LLVMF_STK.
Proof. repeat split; reflexivity. Qed.
Lemma tfib_knock_ev : EV_LIB <= YCfn.EV_LIB.
Proof. unfold EV_LIB, YCfn.EV_LIB. lia. Qed.
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Lemma knock_lib_pre_x_of_tfib : forall regs ly S (W : world tfibsegs) mem md p n pl M,
  YCfn.tfib_lib_pre_x B MT XM_LIB RLO RHI regs ly S W mem md p n pl M ->
  knock_lib_pre_x B MT XM_LIB RLO RHI regs ly S W mem md p n pl M.
Proof.
intros regs ly S W mem md p n pl M H. unfold YCfn.tfib_lib_pre_x in H. unfold knock_lib_pre_x.
destruct tfib_knock_consts as (_ & HRA & HE & HLIVE & HSTK). rewrite HRA, HE, HLIVE, HSTK in H.
destruct H as (HPRE & HRA' & H10 & H11 & HPN & HLEN & HARR & HFR & HEV & HREST).
refine (conj HPRE (conj HRA' (conj H10 (conj H11 (conj HPN (conj HLEN (conj HARR (conj HFR (conj _ HREST))))))))).
pose proof tfib_knock_ev as Hle. lia.
Qed.
Lemma knock_lib_post_x_tfib : forall regs ly S (W : world tfibsegs) mem md p n M l ly' S' W' regs' mem' md' k,
  knock_lib_post_x B MT XN_LIB regs ly S W mem md p n M l ly' S' W' regs' mem' md' k ->
  YCfn.tfib_lib_post_x B MT XN_LIB regs ly S W mem md p n M l ly' S' W' regs' mem' md' k.
Proof.
intros regs ly S W mem md p n M l ly' S' W' regs' mem' md' k H. unfold knock_lib_post_x in H. unfold YCfn.tfib_lib_post_x.
destruct tfib_knock_consts as (_ & _ & _ & _ & HSTK). rewrite HSTK.
destruct H as (HJ & Hk & HREST).
refine (conj HJ (conj _ HREST)).
pose proof tfib_knock_ev as Hle. lia.
Qed.
Lemma knock_lib_contract_x_tfib :
  knock_lib_contract_x B MT XM_LIB XN_LIB RLO RHI -> YCfn.tfib_lib_contract_x B MT XM_LIB XN_LIB RLO RHI.
Proof.
unfold knock_lib_contract_x, YCfn.tfib_lib_contract_x.
destruct tfib_knock_consts as (HA & HRA & _ & _ & _). rewrite HA, HRA.
intros HX ly S W regs mem md p n pl M K HAI HPRE HK.
apply (HX ly S W regs mem md p n pl M K HAI (knock_lib_pre_x_of_tfib regs ly S W mem md p n pl M HPRE)).
intros l W' c' Hle HAI' (ly' & S' & regs' & mem' & md' & k & Hc & HPOST).
apply (HK l W' c' Hle HAI').
exists ly', S', regs', mem', md', k. split; [exact Hc|].
exact (knock_lib_post_x_tfib regs ly S W mem md p n M l ly' S' W' regs' mem' md' k HPOST).
Qed.
End k.
Lemma knock_lib_contract_x_all_tfib {rc : YM05.RunCeil} {LS : lib_shape} (B : asyms) (MT : ameter_ops)
  (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) :
  knock_lib_contract_x_all B MT XM_LIB XN_LIB RLO RHI -> YCfn.tfib_lib_contract_x_all B MT XM_LIB XN_LIB RLO RHI.
Proof. intros HX fx. exact (knock_lib_contract_x_tfib (fx := fx) B MT XM_LIB XN_LIB RLO RHI (HX fx)). Qed.
