(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: relocated to libreac/fuzz_disco (the walk and the composition of libreac/fuzz_grant's lib/A/Prog/CtrlParse.v on a working branch, split at n = 50 as fuzz_disco's contract is: the short path n < 50 is CtrlParseShort.v). *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin, for fuzz_disco.asan-ubsan (lib_both3_0_listing, entry 0x874a4): lib/A/Prog/CtrlParseWalk.v (a working branch a6498221fa6) over lib/Y/Prog/CtrlParseCut.v, with the walk to cut A as fuzz_grant image B's lib/B/Prog/CtrlParse.v (a working branch edc3e948664) walks the same code; the image regions are fuzz_disco.asan-ubsan's objects 1 (atom 242, the side-stack flag's GOT word), 0 (atom 241, the shadow-base cell's GOT word) and 12 (atom 253, the shadow-base cell) and the flag cell atom 34 (as_uar_cell B). *)
(* reac_ctrl_parse (0x874a4) of fuzz_disco's asan-ubsan build: its contract treac_ctrl_parse_spec (CtrlParse.v),
   proved from the walk's segments. For n < 50 the whole path is CtrlParseShort.v (pz_segShort). For
   50 <= n: pz_segA here walks from the entry to cut A (the side-stack frame of class 1 seated);
   CtrlParseMid.v from cut A to cut M; CtrlParseNone.v (header rejected) to cut J, CtrlParseAcc.v (header
   accepted) to cut B; CtrlParseTail1..5.v (CtrlParseTail4a..c.v for class 4) from cut B to cut J;
   CtrlParseEpi.v from cut J to the return. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0s YM05 YI16 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1g YC1h YC81 YC4b YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo YCkd YCjr YCj1 YCja YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import CtrlParse CtrlParseLib KindOfLink1.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import CtrlParseCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import CtrlParseMid CtrlParseNone CtrlParseAcc CtrlParseEpi CtrlParseShort.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
CtrlParseTail1 CtrlParseTail2 CtrlParseTail3 CtrlParseTail4a CtrlParseTail4b CtrlParseTail4c CtrlParseTail5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[local] Ltac Zify.zify_pre_hook ::= try unfold YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
Section b. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
Context {RO : ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
(* ---- The walk from the entry to cut A for 50 <= n: the prologue, sp realigned to 32 bytes, the side-stack
   frame of class 1 (__asan_stack_malloc_1, called at +0x70) and its two regions. ---- *)
Lemma pz_segA : forall B G, pz_rt B G ->
  (forall c, pz_ok B c -> pz_cutA_spec B c) ->
  forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) ch (f n o : Z) (fr : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 f -> getr regs 11 = w64 n -> getr regs 12 = w64 o ->
  achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_CTRL_PARSE_STK -> spZ regs <= sp0 ->
  spZ regs + 32 <= ly_top lyc ->
  Z.of_nat (length (frames Sc)) <= REAC_CTRL_PARSE_DEPTH ->
  50 <= n < 2 ^ 64 -> length fr = 50%nat ->
  pz_fok B lyc Sc W memc (spZ regs) f o fr ->
  pz_ook B STK sp0 FP ly S lyc Sc own W memc (spZ regs) o ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_ctrl_parse) regs memc mdc)
    (treac_ctrl_parse_post B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs o n fr).
Proof.
intros B G RT HAc fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch f n o fr
HJ HROD Hra Hra4 Hgp Htp H10 H11 H12 Hch Hal16 Hwin Hsp0 Htop32 Hroom Hn Hflen HFOK HOOK.
pose proof RT as RT0. pz_open_rt RT0.
pose proof HJ as HJe.
assert (Hn64 : 0 <= n < 2 ^ 64) by lia.
pose proof HFOK as (Hf0 & Hf47 & Hfam & Hfimg & Hfsh & Hfwin & Hfpres & Hfloc & HRf & HHf & HGf & Hdfo).
pose proof HOOK as (Ho32 & Ho4096 & Ho47 & Hoam & Hoimg & Hosh & Hoce & HRo & HHo & HOW).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_CTRL_PARSE_STK = 8336) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres &
(Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
assert (Hownf : forall cid pos, In (cid, pos) own -> In (cid, pos) (frames Sc)).
{ intros cid pos Hin. pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. apply in_or_app. left. exact Hin. }
assert (Hstk : alloc_ceiling <= sp0 - STK) by lia.
destruct (pz_entry B LAWS TL TLF fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs f n o fr
HJ H10 H11 H12 Hn64 Hal16 Hwin Hsp0 Hflen HFOK HOOK) as [HS SHOK].
destruct (pz_env (as_uar_cell B) regs fr f n o H10 H11 H12) as (EE & E10 & E11 & E12 & E32 & E33 & E34 & EFB & EOB).
set (E := Eimg (Ereg regs (pz_extra (as_uar_cell B) (spZ regs) fr))) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (B10 : bv_unsigned (ew E 10) = f) by (rewrite E10; apply unsigned_lit_small; lia).
assert (B12 : bv_unsigned (ew E 12) = o) by (rewrite E12; apply unsigned_lit_small; lia).
assert (B241 : bv_unsigned (ew E 241) = VAL (A_OBJ 0))
by (change 241%nat with (A_OBJ 0); rewrite (EOB 0%nat ltac:(lia)); apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 0)); lia).
assert (B242 : bv_unsigned (ew E 242) = VAL (A_OBJ 1))
by (change 242%nat with (A_OBJ 1); rewrite (EOB 1%nat ltac:(lia)); apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 1)); lia).
assert (B253 : bv_unsigned (ew E 253) = VAL (A_OBJ 12))
by (change 253%nat with (A_OBJ 12); rewrite (EOB 12%nat ltac:(lia)); apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 12)); lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0.
pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_uar_img B TLF) as Hobu. pose proof (palf_uar_al B TLF) as Huar4.
assert (B34 : bv_unsigned (ew E 34) = as_uar_cell B)
by (rewrite E34; apply unsigned_lit_small; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hobu; lia).
set (sp := spZ regs) in *. set (sp1 := pz_sp1 sp) in *.
destruct (sp1_facts (sp - 128) ltac:(lia) ltac:(rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
change (32 * ((sp - 128) / 32)) with sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (B33 : bv_unsigned (ew E 33) = sp1) by (rewrite E33; apply unsigned_lit_small; lia).
(* The walk's stack window lies above the allocation ceiling. *)
assert (Hce : alloc_ceiling <= sp - REAC_CTRL_PARSE_STK) by lia.
assert (Hshi64 : sp <= 2 ^ 64) by lia.
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (pz_kept_refl B lyc Sc W memc (sp - REAC_CTRL_PARSE_STK) sp o ltac:(intros a Ha; apply Hpres; lia)) as KP.
unfold cfg_at. change (w64 (BASE + AF_both3_reac_ctrl_parse)) with (Z_to_bv 64 (BASE + AF_both3_reac_ctrl_parse)).
(* 1. The saved registers, to the instruction after the realignment of sp (+0x40). *)
paj_run_to_tok RUNTO HS HJ SHOK PZspan (AF_both3_reac_ctrl_parse + 0x40).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own') end.
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0)); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
do 5 (apply awr_ok_cons_ro; [cbn; lia|]).
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 12%nat o); [reflexivity | exact B12 | | apply awr_ok_nil].
intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. exact (proj1 (HOW a ltac:(lia))). }
lazymatch type of HFr with frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (Hw1 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
(fun a => (sp - 144 <= a < sp) \/ (o <= a < o + 36)) a) by (pz_win_tac ltac:(fun H => rewrite ?Usp, ?B12 in H));
pose proof (pz_kept_run B LAWS lyc Sc W memc mdc mA mB (sp - REAC_CTRL_PARSE_STK) sp o (fun _ => False)
(fun a => (sp - 144 <= a < sp) \/ (o <= a < o + 36)) HAR Hce Hshi64 Hoimg
ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction)
ltac:(intros a Ha; cbv beta in Ha; destruct Ha; [left | right; left]; lia) KP
(kept_of_frame _ _ _ _ _ _ HFr Hw1)
(fun a Ha => apresent_grows _ _ _ a HG Ha)) as KP' end.
clear KP Hw1 HF HFr HG; rename KP' into KP.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
(* 2. sp is realigned to 32 bytes: atom 33 names it; the stack region keeps the saved registers and a
   new region holds sp1 + [0, 32). *)
assert (E2' : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
pose proof (st_ok_pi_restrict_reg (w_H W) E _ _ 2%bv HS) as R2.
lazymatch type of R2 with _ = sv_denot _ (sr_get (ss_regs ?ssx) _) =>
let e := eval vm_compute in (sr_get (ss_regs ssx) 2%bv) in change (sr_get (ss_regs ssx) 2%bv) with e in R2 end.
rewrite (denot_and_m32 E 2 sp (-128) E2') in R2 by lia.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp E ssx msx 2%bv (SOff 33 0) HS eq_refl
ltac:(cbn [ms_regs restrict]; rewrite R2; cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS' end.
clear HS R2; rename HS' into HS; pz_norm HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
pose proof (st_ok_pi_add_fact E ssx msx 33%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E33, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS' end.
clear HS; rename HS' into HS; pz_norm HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
let rs' := eval vm_compute in (pz_trim (ss_mem ssx)) in
pose proof (st_ok_pi_submem E ssx msx rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS' end.
clear HS; rename HS' into HS; pz_norm HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
pose proof (st_ok_pi_add_region E ssx msx (YP09.mkRegion (Some 33%nat) 0 32 0 32 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
rewrite E33, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|constructor];
intros o0 Ho0; apply (apresent_writable SEGS); apply Hpres1; lia)
ltac:(cbn [ss_mem]; cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite ?Usp, ?B10, ?B12, ?B241, ?B242, ?B253, ?B34, E33, unsigned_lit_small by lia;
repeat split; lia)) as HS' end.
clear HS; rename HS' into HS; pz_norm HS.
(* 3. To the side-stack frame's allocation (+0x70): the use-after-return flag cell holds 1. *)
paj_run_tok RUN HS HJ SHOK PZspan.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own') end.
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 33%nat (sp1 - sp0)); [reflexivity | rewrite B33; lia | cbn; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (sp - sp0)); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
do 5 (apply awr_ok_cons_ro; [cbn; lia|]).
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 12%nat o); [reflexivity | exact B12 | | apply awr_ok_nil].
intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. exact (proj1 (HOW a ltac:(lia))). }
lazymatch type of HFr with frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (Hw2 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
(fun a => (sp1 <= a < sp) \/ (o <= a < o + 36)) a) by (pz_win_tac ltac:(fun H => rewrite ?Usp, ?B12, ?B33 in H));
pose proof (pz_kept_run B LAWS lyc Sc W memc mdc mA mB (sp - REAC_CTRL_PARSE_STK) sp o (fun _ => False)
(fun a => (sp1 <= a < sp) \/ (o <= a < o + 36)) HAR Hce Hshi64 Hoimg
ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction)
ltac:(intros a Ha; cbv beta in Ha; destruct Ha; [left | right; left]; lia) KP
(kept_of_frame _ _ _ _ _ _ HFr Hw2)
(fun a Ha => apresent_grows _ _ _ a HG Ha)) as KP' end.
clear KP Hw2 HF HFr HG; rename KP' into KP.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
rewrite E33 in R2. rewrite (EE 3%nat 3%bv eq_refl) in R3. rewrite (EE 4%nat 4%bv eq_refl) in R4.
pmkst HS. rewrite (palf_sm1 B TLF).
pose proof (count_cid_le_length 1 (frames Sc)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs (pal_env B TL) ML SMP 1 (ASM1 fq) ltac:(lia) W (ms_regs msX) (ms_mem msX)
STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (sp1 - sp0) _ HJ) end.
- unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
- rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
- lia. - rewrite Hes; lia.
- rewrite R3. exact Hgp. - rewrite R4. exact Htp.
- exact R1. - apply ret_ok_codeptr_v; [lia | reflexivity].
- change (fs_frames 1) with 8192. unfold REAC_CTRL_PARSE_DEPTH in Hroom. lia. }
cbv beta. clear R1 R2 R3 R4 SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJin & (fS2 & ES2)).
pose proof HJin as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hstklo & _) & _).
pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6).
pose proof (pz_kept_trans B lyc Sc W memc _ mem2 (sp - REAC_CTRL_PARSE_STK) sp _ _ o _ Hce Hshi64 KP HK
  ltac:(rewrite Hes; lia) ltac:(lia) ltac:(intros ? [])) as KP'.
clear KP; rename KP' into KP.
(* 4. After the allocation: the registers it clobbers are havocked from atom 512 on, the regions kept. *)
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kc0 & Ku0 & Kg0 & Kgu0).
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kc2 & Ku2 & Kg2 & Kgu2).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kg0, Kg2. rewrite (pal_cell B TL) in Kc0, Kc2.
rewrite (palf_got_uar B TLF) in Kgu0, Kgu2.
pose proof (proj1 HJ2) as HAR2.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
assert (HfinS2 : forall c p, In (c, p) (frames Sc) -> In (c, p) (frames S2)) by (intros c p Hcp; rewrite Hfrs2; right; exact Hcp).
(* Each byte of the out struct lies in a caller block or a caller frame (mid_out_loc, CtrlParseMid.v). *)
assert (Loc_o : forall x, o <= x < o + 36 ->
(exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= x < b + req_size m) \/
(exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid))
by (intros x Hx; exact (mid_out_loc B LAWS STK sp0 FP ly S lyc Sc own W memc mdc o x HAR Hownf Hstk Hoce Hosh Hx (proj1 (HOW x Hx)))).
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5; 6; 7]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q); [| specialize (HS2 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
- apply (pz_region_kept E _ _ _ 33 sp1); [exact B33 | intros a Ha; apply K1; [lia | intros [? ?]; lia] | intros a Ha; apply Hpres2; lia].
- apply (pz_region_kept E _ _ _ 2 sp); [exact Usp | intros a Ha; apply K1; [lia | intros [? ?]; lia] | intros a Ha; apply Hpres2; lia].
- apply (region_kept_val_at E _ _ 242 (VAL (A_OBJ 1)) 8 (as_uar_cell B)); [exact B242 | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu0) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu2) | lia].
- apply (region_kept_val_at E _ _ 34 (as_uar_cell B) 4 1); [exact B34 | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku0) | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku2) | lia].
- apply (region_kept_val_at E _ _ 241 (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12))); [exact B241 | exact (val_mem_of_rdword SEGS _ _ _ _ Kg0) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg2) | lia].
- apply (region_kept_val_at E _ _ 253 (VAL (A_OBJ 12)) 8 SHADOW_OFF); [exact B253 | exact (val_mem_of_rdword SEGS _ _ _ _ Kc0) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc2) | lia].
- (* the frame f: its place (pz_loc) is a caller frame, a caller block or the machine stack below the call's window *)
  apply (pz_region_kept E _ _ _ 10 f); [exact B10 | | intros a Ha; lia].
  intros a Ha. destruct Hfloc as [(cid & pos & Hin & Hlo & Hhi)|[(b & m & Hb & Hlo & Hhi)|(Hlo & Hhi)]].
  + apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | intros []].
  + replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hb); [lia | intros []].
  + apply K1; [lia | intros [? ?]; lia].
- (* the out struct: each byte in a caller block or a caller frame *)
  apply (pz_region_kept E _ _ _ 12 o); [exact B12 | |].
  + intros a Ha. destruct (Loc_o a ltac:(lia)) as [(b & m & Hb & Hr)|(cid & pos & Hin & Hr)].
    * replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hb); [lia | intros []].
    * apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | intros []].
  + intros a Ha. refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ2 _)).
    rewrite Eab. exact (pz_awr_cons _ _ _ _ _ _ _ _ a (proj1 (HOW a ltac:(lia)))). }
rewrite <- restrict_mkst_fx in HS2. clear HS; rename HS2 into HS.
(* 4b. The frame (1, fpos): atom 516 is its address, 528 its flag, 529 its shadow; a region for the
   frame and one for its 16 shadow bytes. *)
assert (AGX0 : forall n0, (n0 < 512)%nat -> ew E n0 = ew E n0) by reflexivity.
pz_rebase HS AGX0. rename AGX0 into AGX.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & _).
destruct (FFL _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFLpres & HFLown & (HFLapp & HFLimg) & (HFL4096 & _ & HFLce)).
pose proof (frm_off_imgP B _ _ _ _ _ 1 fpos HAR2 Hfin2) as HFimg.
change (fs_frame_bytes 1) with 128 in HFapp, HFceil, HFpres, HFSpres, Hz, Hflag, HFimg.
change (128 / 8) with 16 in HFSpres.
set (F := frame_addr lyc 1 fpos) in *. set (FL := flag_addr lyc 1 fpos) in *.
assert (EF : F = frame_addr lyc 1 fpos) by reflexivity. assert (EFL : FL = flag_addr lyc 1 fpos) by reflexivity.
destruct (pz_nf_sep B LAWS lyc Sc S2 W mem2 md2 fpos F FL HAR2 Hfrs2 Eab EF EFL FFL) as (N1 & N2 & N3 & N4).
(* The frame is apart from f (its place, pz_loc_nf) and from the out struct (awr_byte, pz_awr_nf). *)
assert (HsepF : f + 50 <= F \/ F + 128 <= f).
{ apply (mid_sep F FL f 50); [lia|]. intros a Ha.
  exact (pz_loc_nf B lyc Sc W memc mdc f 50 a F FL HAR Hfloc N1 N3 N4 Hstklo Ha). }
assert (HsepO : o + 36 <= F \/ F + 128 <= o).
{ apply (mid_sep F FL o 36); [lia|]. intros a Ha.
  exact (pz_awr_nf B STK sp0 FP ly S lyc Sc own W memc mdc a F FL HAR Hownf N1 N3 N4 Hstk (proj1 (HOW a Ha))). }
prreg HS (10%bv : bv 5) RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 + 16 <= 17592184995840).
{ assert (Hd : (F + 16 * 8) / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; lia).
rewrite Z.div_add in Hd by lia. change (140737479966720 / 8) with 17592184995840 in Hd. lia. }
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
add_atom HS 528%nat (Z_to_bv 64 FL) E528. pz_rebase HS AGX.
add_atom HS 529%nat (Z_to_bv 64 (SB + F / 8)) E529. pz_rebase HS AGX.
pose proof E32 as E32'.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 516%nat (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia; change (2 ^ 5) with 32;
split; [lia|]; split; [rewrite HFq, Z.mul_comm; apply Z_mod_mult | lia])) as HS' end.
clear HS; rename HS' into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 528%nat (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E528, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS' end.
clear HS; rename HS' into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 529%nat (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E529, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS' end.
clear HS; rename HS' into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_alias Ev ssx msx _ _ HS (shadow_decl_ok Ev 516 32 529 F SB RF ltac:(lia) E32' E529)) as HS' end.
clear HS; rename HS' into HS. pz_norm HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
assert (ROK : region_ok SEGS Ev (ms_mem msx) (fframe_region 516 528 1 []));
[| assert (RDJ : all_disjoint Ev (fframe_region 516 528 1 []) (ss_mem ssx))] end.
{ unfold region_ok, fframe_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val app ms_mem restrict mkst].
change (fs_frame_bytes 1) with 128. rewrite RF, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
- intros o0 Ho0. apply (apresent_writable SEGS). apply (proj1 (HFpres (F + o0) ltac:(lia))).
- apply Forall_cons; [|apply Forall_nil].
change (128 - 8) with 120.
eapply (chunk_ok_val SEGS _ _ F 120 8 _ FL).
+ cbn [sv_denot]. rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
+ pz_vside.
+ pz_vside.
+ replace (F + 120) with (F + 128 - 8) by lia. exact (val_mem_of_rdword SEGS _ _ _ _ Hflag). }
{ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
cbn [all_disjoint]. unfold extent_disjoint, fframe_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
change (fs_frame_bytes 1) with 128. pz_bases.
revert Hslo Hshi H47 Hceil Hwin Hstk0 WS C1 Hsp1r Hob0 Hob1 Hob12 Hobu Hf0 Hf47 Ho4096 Ho47 Hoce HF4096 HFceil HFapp HFimg HsepF HsepO Hsp0.
unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. clear. intros. repeat split; first [lia | match goal with |- ?g => idtac "DISJ516" g; fail end]. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_region Ev ssx msx (fframe_region 516 528 1 []) HS eq_refl ROK RDJ) as HS' end.
clear HS ROK RDJ; rename HS' into HS. pz_norm HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
assert (ROK : region_ok SEGS Ev (ms_mem msx) (fshadow_region 529 1 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]));
[| assert (RDJ : all_disjoint Ev (fshadow_region 529 1 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]) (ss_mem ssx))] end.
{ unfold region_ok, fshadow_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
change (fs_frame_bytes 1 / 8) with 16. rewrite E529, unsigned_lit_small by (unfold SB; lia).
split; [unfold SB; lia|]. split; [unfold SB; lia|]. split.
- intros o0 Ho0. apply (apresent_writable SEGS). unfold shadow_addr in HFSpres. rewrite <- SB_SHADOW_OFF in HFSpres.
apply (proj1 (HFSpres o0 ltac:(lia))).
- unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
+ eapply (chunk_ok_val SEGS _ _ (SB + F / 8) 0 8 _ 0); [reflexivity | pz_vside | pz_vside |].
apply val_mem_zero8. intros ii Hii. replace (SB + F / 8 + 0 + ii) with (SB + F / 8 + ii) by lia. apply Hz. change (128 / 8) with 16. lia.
+ eapply (chunk_ok_val SEGS _ _ (SB + F / 8) 8 8 _ 0); [reflexivity | pz_vside | pz_vside |].
apply val_mem_zero8. intros ii Hii. replace (SB + F / 8 + 8 + ii) with (SB + F / 8 + (8 + ii)) by lia. apply Hz. change (128 / 8) with 16. lia. }
{ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
cbn [all_disjoint]. unfold extent_disjoint, fshadow_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
change (fs_frame_bytes 1 / 8) with 16. change (fs_frame_bytes 1) with 128. pz_bases.
revert Hslo Hshi H47 Hceil Hwin Hstk0 WS C1 Hsp1r Hob0 Hob1 Hob12 Hobu Hf0 Hf47 Hfsh Ho4096 Ho47 Hosh Hoce HF4096 HFceil HFapp HFimg Hsp0 HF8lo HF8hi.
unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB. clear. intros. repeat split; first [lia | match goal with |- ?g => idtac "DISJ529" g; fail end]. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_region Ev ssx msx (fshadow_region 529 1 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]) HS eq_refl ROK RDJ) as HS' end.
clear HS ROK RDJ; rename HS' into HS. pz_norm HS.
(* Cut A: the rest of the walk is the cut A chain. *)
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => change ssx with ss_cutA in HS end.
set (c := mkPZ fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch f n o fr S2 fpos).
assert (Hok : pz_ok B c).
{ unfold pz_ok, c. cbn [cx_fq cx_STK cx_sp0 cx_FP cx_ly cx_S cx_W0 cx_mem0 cx_md0 cx_own cx_lyc cx_Sc cx_W cx_memc
cx_mdc cx_k cx_regs cx_ch cx_f cx_n cx_o cx_fr cx_S2 cx_fpos].
exact (conj HJe (conj HROD (conj Hra (conj Hra4 (conj Hgp (conj Htp (conj H10 (conj H11 (conj H12 (conj Hn64
(conj Hch (conj Hal16 (conj Hwin (conj Hsp0 (conj Htop32 (conj Hroom (conj Hflen (conj (fun _ => HFOK) (conj HOOK
(conj Hfrs2 (conj Eab (conj Hnin (ex_intro _ fS2 ES2))))))))))))))))))))))). }
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msv) =>
assert (Hcur : pz_cur B c Ev msv md2);
[ unfold pz_cur, pz_E0, c; cbn [cx_fq cx_STK cx_sp0 cx_FP cx_ly cx_S cx_W0 cx_mem0 cx_md0 cx_own cx_lyc cx_Sc cx_W cx_memc
cx_mdc cx_k cx_regs cx_ch cx_f cx_n cx_o cx_fr cx_S2 cx_fpos ms_mem];
split; [assumption|]; split; [exact AGX|]; split; [exact RF|]; split; [exact E528|]; split; [exact E529|];
split; [exact HJ2 | exact KP]
| exact (HAc c Hok (proj1 Hn) Ev msv md2 Hcur HS) ] end.
Qed.
(* ---- The contract. ---- *)
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA AS___asan_memset).
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Hypothesis ASM1 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis KIND : tkind_of_link1_spec B.
(* The bcmp wrapper compares the frame with "\xff\xff\xff\xff\xff\xff" (.str.4, a registered global of 7 bytes). *)
Variable G : list (Z * Z).
Hypothesis HGM : globs_marked SEGS B G.
Hypothesis HG15 : In (VAL (A_OBJ OBJ_BCAST), 7) G.
Hypothesis HIMGSH : img_shadow_vis SEGS B.
Hypothesis HBC_RNG : IMG_LO + 64 <= VAL (A_OBJ OBJ_BCAST) /\ VAL (A_OBJ OBJ_BCAST) + 6 + 64 <= IMG_TOP.
Hypothesis HBC_VAL : forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
forall i, 0 <= i < 6 -> aview SEGS H mem (VAL (A_OBJ OBJ_BCAST) + i) = Some 255.
Theorem pb_reac_ctrl_parse : treac_ctrl_parse_spec B.
Proof.
unfold treac_ctrl_parse_spec.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch f n o fr
HJ HROD Hra Hra4 Hgp Htp H10 H11 H12 Hch Hal16 Hwin Hsp0 Htop32 Hroom Hn Hflen HFOK
Ho32 Ho4096 Ho47 Hoam Hoimg Hosh Hoce HRo HHo HOW.
(* kind_of_link1 is called through its symbol, which the listing's call table puts at its entry. *)
assert (HKL1 : SIGMA AS_kind_of_link1 = BASE + AF_both3_kind_of_link1) by exact pa_sigma_kind_of_link1.
pose proof (conj LAWS (conj TL (conj TLF (conj ML (conj AMEMSET (conj AMEMCPY (conj ABCMP (conj ASM1 (conj SMP
(conj ASF (conj FFL (conj KIND (conj HGM (conj HG15 (conj HIMGSH (conj HBC_RNG (conj HBC_VAL HKL1)))))))))))))))) : pz_rt B G) as RT.
pose proof (conj Ho32 (conj Ho4096 (conj Ho47 (conj Hoam (conj Hoimg (conj Hosh (conj Hoce (conj HRo (conj HHo HOW))))))))
  : pz_ook B STK sp0 FP ly S lyc Sc own W memc (spZ regs) o) as HOOK.
(* Cut J onwards is CtrlParseEpi.v; cut A onwards chains Mid, None / Acc, Tail1..5 and Epi. *)
assert (HJc : forall c, pz_ok B c -> pz_cutJ_spec B c) by exact (fun c Hok => pz_segD B G RT c Hok).
assert (HAc : forall c, pz_ok B c -> pz_cutA_spec B c).
{ intros c Hok. pose proof (HJc c Hok) as HJ1.
  assert (HBc : pz_cutB_spec B c).
  { intros Hbig E ms md Hcur HS SHOK Hhdr Hbc.
    destruct (pz_cases (cx_fr c)) as [P|[P|[P|[P|P]]]].
    - exact (pz_tail1 B G RT c Hok HJ1 Hbig E ms md Hcur HS SHOK Hhdr Hbc P).
    - exact (pz_tail2 B G RT c Hok HJ1 Hbig E ms md Hcur HS SHOK Hhdr Hbc P).
    - exact (pz_tail3 B G RT c Hok HJc Hbig E ms md Hcur HS SHOK Hhdr Hbc P).
    - destruct (pz_cases4 (cx_fr c) P) as [Q|[Q|Q]].
      + exact (pz_tail4a B G RT c Hok HJ1 Hbig E ms md Hcur HS SHOK Hhdr Hbc Q).
      + exact (pz_tail4b B G RT c Hok HJ1 Hbig E ms md Hcur HS SHOK Hhdr Hbc Q).
      + exact (pz_tail4c B G RT c Hok HJ1 Hbig E ms md Hcur HS SHOK Hhdr Hbc Q).
    - exact (pz_tail5 B G RT c Hok HJ1 Hbig E ms md Hcur HS SHOK Hhdr Hbc P). }
  apply (pz_segB B G RT c Hok). intros Hbig E ms md Hcur HS SHOK _.
  destruct (cp_hdr (cx_n c) (cx_fr c)) eqn:Hh.
  - exact (pz_segAcc B G RT c Hok HBc Hbig E ms md Hcur HS SHOK Hh).
  - exact (pz_segN B G RT c Hok HJ1 Hbig E ms md Hcur HS SHOK Hh). }
destruct (Z_lt_ge_dec n 50) as [Hlt | Hge].
- exact (pz_segShort B G RT HJc fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch f n o fr
    HJ HROD Hra Hra4 Hgp Htp H10 H11 H12 Hch Hal16 Hwin Hsp0 Htop32 Hroom ltac:(lia) Hflen HOOK).
- exact (pz_segA B G RT HAc fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch f n o fr
    HJ HROD Hra Hra4 Hgp Htp H10 H11 H12 Hch Hal16 Hwin Hsp0 Htop32 Hroom ltac:(lia) Hflen (HFOK ltac:(lia)) HOOK).
Qed.
End d.
End b.
