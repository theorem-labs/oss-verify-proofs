(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: relocated to libreac/fuzz_disco (the prologue of CtrlParse.v, CtrlParseMid.v and the short path of CtrlParseNone.v of libreac/fuzz_grant's walk on a working branch, restated on fuzz_disco's contract, whose entry state has no region for the frame f when n < 50). *)
(* reac_ctrl_parse (0x6464) of fuzz_disco's ASan build, the whole short path n < 50: from the entry
   (pz_entry0: no region and no atom fact for the frame f, which the contract does not describe there)
   through the prologue, the side-stack frame of class 1 (__asan_stack_malloc_1, called at +0x70), the
   memset of the out struct (+0x13c) and the length test (+0x144) to cut J (+0x3a8), where pz_cutJ_spec
   takes over. The path reads the frame f nowhere and reaches no __asan_report_* call: the function's
   first shadow check (+0x158) is on the other side of the length test. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase YC81 YC4b YC1g YC1h YC45 YC85 DiscoFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import CtrlParse CtrlParseLib KindOfLink1 DiscoRo ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import CtrlParseCut.
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
Context {PI : PAImg disco_listing}.
Context {RO : ro_below_ofl (@pa_segs _ disco_listing PI) (@pa_relro_lo _ disco_listing PI) (@pa_relro_hi _ disco_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
(* The windows of a run of the short path lie in the stack below the entry sp, the out struct or the
   function's own side-stack frame. *)
Local Ltac pzS_win :=
let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Ha := fresh "Ha" in let Hq := fresh "Hq" in
intros b wlo whi a Hin Ha;
lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In (b, wlo, whi) l') in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Ha; revert Ha; pz_bases; intro Ha; cbv beta;
unfold pz_nf, SHADOW_OFF, SB in *; lia |]); destruct Hin.
(* The walk of the short path: it takes the contract's premises (without the ones about the frame f,
   which the contract gives only under 50 <= n) and ends at cut J, where the cut's hypothesis takes
   over. *)
Lemma pz_segShort : forall B G, pz_rt B G ->
(forall c, pz_ok B c -> pz_cutJ_spec B c) ->
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
0 <= n < 50 -> length fr = 50%nat ->
pz_ook B STK sp0 FP ly S lyc Sc own W memc (spZ regs) o ->
SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_ctrl_parse) regs memc mdc)
  (treac_ctrl_parse_post B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs o n fr).
Proof.
intros B G RT HJcut fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch f n o fr
HJ HROD Hra Hra4 Hgp Htp H10 H11 H12 Hch Hal16 Hwin Hsp0 Htop32 Hroom Hn Hflen HOOK.
pz_open_rt RT.
pose proof HJ as HJe.
assert (Hn64 : 0 <= n < 2 ^ 64) by lia.
assert (Hh : cp_hdr n fr = false)
by (unfold cp_hdr; replace (50 <=? n) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
pose proof HOOK as (Ho32 & Ho4096 & Ho47 & Hoam & Hoimg & Hosh & Hoce & HRo & HHo & HOW).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_CTRL_PARSE_STK = 8336) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres &
(Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
destruct (pz_entry0 B LAWS TL TLF fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs f n o fr
HJ H10 H11 H12 Hn64 Hal16 Hwin Hsp0 HOOK) as [HS SHOK].
destruct (pz_env regs fr f n o H10 H11 H12) as (EE & E10 & E11 & E12 & E32 & E33 & EFB & EOB).
set (E := Eimg (Ereg regs (pz_extra (spZ regs) fr))) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
(* The contract says nothing about f on this path, so atom 10 is the entry register's value only. *)
assert (B10 : bv_unsigned (ew E 10) = bv_unsigned (getr regs 10)) by (rewrite (EE 10%nat 10%bv eq_refl); reflexivity).
assert (B12 : bv_unsigned (ew E 12) = o) by (rewrite E12; apply unsigned_lit_small; lia).
assert (B241 : bv_unsigned (ew E 241) = VAL (A_OBJ 0))
by (change 241%nat with (A_OBJ 0); rewrite (EOB 0%nat ltac:(lia)); apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 0)); lia).
assert (B242 : bv_unsigned (ew E 242) = VAL (A_OBJ 1))
by (change 242%nat with (A_OBJ 1); rewrite (EOB 1%nat ltac:(lia)); apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 1)); lia).
assert (B307 : bv_unsigned (ew E 307) = VAL (A_OBJ 66))
by (change 307%nat with (A_OBJ 66); rewrite (EOB 66%nat ltac:(lia)); apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 66)); lia).
assert (B308 : bv_unsigned (ew E 308) = VAL (A_OBJ 67))
by (change 308%nat with (A_OBJ 67); rewrite (EOB 67%nat ltac:(lia)); apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 67)); lia).
pose proof (pa_obj_img 0 ltac:(unfold disco_nobj; lia)) as Hob0.
pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as Hob1.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as Hob66.
pose proof (pa_obj_img 67 ltac:(unfold disco_nobj; lia)) as Hob67.
set (sp := spZ regs) in *. set (sp1 := pz_sp1 sp) in *.
destruct (sp1_facts (sp - 128) ltac:(lia) ltac:(rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
change (32 * ((sp - 128) / 32)) with sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (B33 : bv_unsigned (ew E 33) = sp1) by (rewrite E33; apply unsigned_lit_small; lia).
(* The walk's stack window lies above the allocation ceiling, and the out struct below it. *)
assert (Hce : alloc_ceiling <= sp - REAC_CTRL_PARSE_STK) by lia.
assert (Hshi64 : sp <= 2 ^ 64) by lia.
(* A shadow byte of the out struct is not a byte of the out struct. *)
assert (Hsh_o : forall x, o <= x < o + 36 -> ~ (o <= shadow_addr x < o + 36)).
{ intros x Hx [HA HB]. unfold shadow_addr, SHADOW_OFF in *.
  assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  assert (0 <= x / 8) by (apply Z.div_pos; lia).
  unfold kLowShadowBeg, kHighMemBeg in Hosh. lia. }
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
pose proof (pz_kept_refl B lyc Sc W memc (sp - REAC_CTRL_PARSE_STK) sp o
ltac:(intros a Ha; apply Hpres; lia)) as KP.
unfold cfg_at. change (w64 (BASE + AF_reac_ctrl_parse)) with (Z_to_bv 64 (BASE + AF_reac_ctrl_parse)).
(* 1. The saved registers, to the instruction after the realignment of sp (+0x40). *)
paj_run_to_tok RUNTO HS HJ SHOK PZspan (AF_reac_ctrl_parse + 0x40).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own') end.
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0)); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
do 4 (apply awr_ok_cons_ro; [cbn; lia|]).
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 12%nat o); [reflexivity | exact B12 | | apply awr_ok_nil].
intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. exact (proj1 (HOW a ltac:(lia))). }
lazymatch type of HFr with frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (Hw1 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
(fun a => (sp - 144 <= a < sp) \/ (o <= a < o + 36)) a) by (pz_win_tac ltac:(fun H => rewrite ?Usp, ?B12 in H));
pose proof (pz_kept_run B LAWS lyc Sc W memc mdc mA mB (sp - REAC_CTRL_PARSE_STK) sp o (fun _ => False)
(fun a => (sp - 144 <= a < sp) \/ (o <= a < o + 36)) HAR Hce Hshi64 Hoimg
ltac:(intros ? ? ? ? ? []) ltac:(intros ? []) ltac:(intros ? ? ? ? ? []) ltac:(intros ? [])
ltac:(intros a [Ha|Ha]; [left; lia | right; left; exact Ha]) KP
(kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => (sp - 144 <= a < sp) \/ (o <= a < o + 36)) HFr Hw1)
(fun a Ha => apresent_grows (w_H W) _ _ a HG Ha)) as KP' end.
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
rewrite ?Usp, ?B12, ?B241, ?B242, ?B307, ?B308, E33, unsigned_lit_small by lia;
repeat split; lia)) as HS' end.
clear HS; rename HS' into HS; pz_norm HS.
(* 3. To the side-stack frame's allocation (+0x70): the use-after-return flag cell holds 1. *)
paj_run_tok RUN HS HJ SHOK PZspan.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own') end.
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 33%nat (sp1 - sp0)); [reflexivity | rewrite B33; lia | cbn; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (sp - sp0)); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
do 4 (apply awr_ok_cons_ro; [cbn; lia|]).
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 12%nat o); [reflexivity | exact B12 | | apply awr_ok_nil].
intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. exact (proj1 (HOW a ltac:(lia))). }
lazymatch type of HFr with frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (Hw2 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
(fun a => (sp1 <= a < sp) \/ (o <= a < o + 36)) a) by (pz_win_tac ltac:(fun H => rewrite ?Usp, ?B12, ?B33 in H));
pose proof (pz_kept_run B LAWS lyc Sc W memc mdc mA mB (sp - REAC_CTRL_PARSE_STK) sp o (fun _ => False)
(fun a => (sp1 <= a < sp) \/ (o <= a < o + 36)) HAR Hce Hshi64 Hoimg
ltac:(intros ? ? ? ? ? []) ltac:(intros ? []) ltac:(intros ? ? ? ? ? []) ltac:(intros ? [])
ltac:(intros a [Ha|Ha]; [left; lia | right; left; exact Ha]) KP
(kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => (sp1 <= a < sp) \/ (o <= a < o + 36)) HFr Hw2)
(fun a Ha => apresent_grows (w_H W) _ _ a HG Ha)) as KP' end.
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
- unfold REAC_CTRL_PARSE_DEPTH in Hroom. change (fs_frames 1) with 8192. lia. }
cbv beta. clear R1 R2 R3 R4 SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJin & (fS2 & ES2)).
pose proof (pz_kept_trans B lyc Sc W memc _ mem2 (sp - REAC_CTRL_PARSE_STK) sp
(sp0 + (sp1 - sp0) - ESTACK) (sp0 + (sp1 - sp0)) o
(fun _ => False) Hce Hshi64 KP HK ltac:(rewrite Hes; lia) ltac:(lia) ltac:(intros ? [])) as KP'.
clear KP; rename KP' into KP.
(* 4. After the allocation: the registers it clobbers are havocked from atom 512 on, the regions kept. *)
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kc0 & Ku0 & Kg0 & Kgu0).
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kc2 & Ku2 & Kg2 & Kgu2).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kg0, Kg2. rewrite (pal_cell B TL) in Kc0, Kc2.
rewrite (pal_got_uar B TL), (pal_uar_cell B TL) in Kgu0, Kgu2. rewrite (pal_uar_cell B TL) in Ku0, Ku2.
pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6).
pose proof (proj1 HJ2) as HAR2.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
assert (HfinS2 : forall c p, In (c, p) (frames Sc) -> In (c, p) (frames S2)) by (intros c p Hcp; rewrite Hfrs2; right; exact Hcp).
assert (Hownf : forall cid pos, In (cid, pos) own -> In (cid, pos) (frames Sc)).
{ intros cid pos Hin. pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. apply in_or_app. left. exact Hin. }
assert (HOpres : forall memX mdX S2x, AR SEGS B lyc S2x W memX mdX ->
ablocks B lyc S2x = ablocks B lyc Sc ->
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((1, fpos) :: own) lyc S2x W memX mdX k ->
forall a, o <= a < o + 36 -> apresent (w_H W) memX a).
{ intros memX mdX S2x HARx EabX HJx a Ha.
assert (Hpx : apresent (w_H W) memX a /\ ~ aowned B lyc S2x a)
by (eapply awr_byte_present; [exact LAWS | exact HJx
| rewrite EabX; apply pz_awr_cons; exact (proj1 (HOW a Ha))]).
exact (proj1 Hpx). }
lazymatch type of HK with acall_kept _ _ _ _ _ ?mX _ _ _ _ _ =>
assert (HOkept : forall a, o <= a < o + 36 -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mX a) end.
{ intros a Ha.
destruct (proj1 (HOW a Ha)) as [Hstk | [(HFP & b & m & Hb & Hab) | [(b & m & Hb & _ & Hab) | (cid & pos & Hin & Hr)]]].
- exfalso. lia.
- replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hb ltac:(lia)). intros [].
- replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hb ltac:(lia)). intros [].
- destruct Hr as [Hr | Hr].
+ apply (K4 cid pos a (Hownf cid pos Hin) (or_introl Hr)). intros [].
+ exfalso. destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR (Hownf cid pos Hin)) as (HG4096 & HGce & _).
pose proof (fs_frame_bytes_nonneg cid) as Hgs.
unfold in_zr, shadow_addr, SHADOW_OFF in Hr; cbn [fst snd] in Hr.
unfold kLowShadowBeg, kHighMemBeg in Hosh. lia. }
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5; 6; 7]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q); [| specialize (HS2 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
- apply (pz_region_kept E _ _ _ 33 sp1); [exact B33 | intros a Ha; apply K1; [lia | intros [? ?]; lia] | intros a Ha; apply Hpres2; lia].
- apply (pz_region_kept E _ _ _ 2 sp); [exact Usp | intros a Ha; apply K1; [lia | intros [? ?]; lia] | intros a Ha; apply Hpres2; lia].
- apply (region_kept_val_at E _ _ 241 (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 67))); [exact B241 | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu0) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu2) | lia].
- apply (region_kept_val_at E _ _ 308 (VAL (A_OBJ 67)) 4 1); [exact B308 | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku0) | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku2) | lia].
- apply (region_kept_val_at E _ _ 242 (VAL (A_OBJ 1)) 8 (VAL (A_OBJ 66))); [exact B242 | exact (val_mem_of_rdword SEGS _ _ _ _ Kg0) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg2) | lia].
- apply (region_kept_val_at E _ _ 307 (VAL (A_OBJ 66)) 8 SHADOW_OFF); [exact B307 | exact (val_mem_of_rdword SEGS _ _ _ _ Kc0) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc2) | lia].
- apply (pz_region_kept E _ _ _ 12 o); [exact B12 | intros a Ha; exact (HOkept a ltac:(lia))
  | intros a Ha; exact (HOpres mem2 md2 S2 HAR2 Eab HJ2 a ltac:(lia))]. }
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
assert (HFo : forall a, o <= a < o + 36 -> ~ pz_nf F FL a).
{ intros a Ha Hnf.
destruct (proj1 (HOW a Ha)) as [Hstk | [(HFP & b & m & Hb & Hab) | [(b & m & Hb & _ & Hab) | (cid & pos & Hin & Hr)]]].
- pose proof (N4 a Hnf). lia.
- exact (N1 b m (a - b) Hb ltac:(lia) ltac:(replace (b + (a - b)) with a by lia; exact Hnf)).
- exact (N1 b m (a - b) Hb ltac:(lia) ltac:(replace (b + (a - b)) with a by lia; exact Hnf)).
- exact (N3 cid pos a (Hownf cid pos Hin) Hr Hnf). }
assert (HFo2 : o + 36 <= F \/ F + 128 <= o).
{ destruct (Z_le_gt_dec (o + 36) F) as [HA|HA]; [left; lia|].
destruct (Z_le_gt_dec (F + 128) o) as [HB|HB]; [right; lia|].
exfalso. apply (HFo (Z.max o F) ltac:(lia)). left. lia. }
assert (HFLo : ~ (o <= FL < o + 36)) by (intros HX; apply (HFo FL HX); right; right; reflexivity).
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
revert Hslo Hshi H47 Hceil Hwin Hstk0 WS C1 Hsp1r Hob0 Hob1 Hob66 Hob67 Ho4096 Ho47 Hoce Hosh HFo2 HFLo HF4096 HFceil HFapp HFimg Hsp0.
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
revert Hslo Hshi H47 Hceil Hwin Hstk0 WS C1 Hsp1r Hob0 Hob1 Hob66 Hob67 Ho4096 Ho47 Hoce Hosh HFo2 HFLo HF4096 HFceil HFapp HFimg Hsp0 HF8lo HF8hi.
unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB. clear. intros. repeat split; first [lia | match goal with |- ?g => idtac "DISJ529" g; fail end]. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_region Ev ssx msx (fshadow_region 529 1 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]) HS eq_refl ROK RDJ) as HS' end.
clear HS ROK RDJ; rename HS' into HS. pz_norm HS.
(* The out struct's shadow at any state the walk reaches, byte by byte: the contract places each byte
   of it (awr_byte) in a caller block (the shadow of which the current state gives) or in a caller
   frame (the shadow of which the walk keeps); the machine-stack case is dead, because the out struct
   lies below the allocation ceiling. range_addressable is a byte-wise property; the hull of the 36
   bytes is the union of the 1-byte hulls, because each shadow byte of the hull is the shadow byte of
   one of the 36 addresses. *)
assert (HSHO : forall memX mdX S2x, AR SEGS B lyc S2x W memX mdX ->
(forall c p, In (c, p) (frames Sc) -> In (c, p) (frames S2x)) ->
ablocks B lyc S2x = ablocks B lyc Sc ->
pz_kept B lyc Sc W memc memX (sp - REAC_CTRL_PARSE_STK) sp o ->
range_addressable (aview SEGS (w_H W) memX) SHADOW_OFF o 36 /\ shadow_hull_vis (aview SEGS (w_H W) memX) o 36).
{ intros memX mdX S2x HARx HfinX EabX KPX.
assert (HB1 : forall x, o <= x < o + 36 ->
range_addressable (aview SEGS (w_H W) memX) SHADOW_OFF x 1 /\ shadow_hull_vis (aview SEGS (w_H W) memX) x 1).
{ intros x Hx.
destruct (proj1 (HOW x Hx)) as [Hstk | [(HFP & b & m & Hb & Hab) | [(b & m & Hb & _ & Hab) | (cid & pos & Hin & Hr)]]].
- exfalso. lia.
- assert (HbX : In (b, m) (ablocks B lyc S2x)) by (rewrite EabX; exact Hb). split.
+ exact (range_addressable_of_block SEGS B LAWS lyc S2x W memX mdX b m x 1 HARx HbX ltac:(lia) ltac:(lia)).
+ exact (shadow_hull_vis_of_block SEGS B LAWS lyc S2x W memX mdX b m x 1 HARx HbX ltac:(lia) ltac:(lia) ltac:(lia)).
- assert (HbX : In (b, m) (ablocks B lyc S2x)) by (rewrite EabX; exact Hb). split.
+ exact (range_addressable_of_block SEGS B LAWS lyc S2x W memX mdX b m x 1 HARx HbX ltac:(lia) ltac:(lia)).
+ exact (shadow_hull_vis_of_block SEGS B LAWS lyc S2x W memX mdX b m x 1 HARx HbX ltac:(lia) ltac:(lia) ltac:(lia)).
- pose proof (Hownf cid pos Hin) as HinSc.
destruct (frames_bounds SEGS B LAWS lyc S2x W memX mdX cid pos HARx (HfinX _ _ HinSc)) as (HG4096 & HGce & _).
pose proof (fs_frame_bytes_nonneg cid) as Hgs.
destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng, shadow_addr in Hr; cbn [fst snd] in Hr.
+ split.
* refine (pz_kept_ra B LAWS lyc Sc W memc mdc memX (sp - REAC_CTRL_PARSE_STK) sp o cid pos x 1 HAR KPX HinSc
ltac:(lia) ltac:(lia) ltac:(intros y Hy; apply Hsh_o; lia) _).
exact (range_addressable_sub (aview SEGS (w_H W) memc) SHADOW_OFF o 36 x 1 HRo ltac:(lia) ltac:(lia)).
* exact (shadow_hull_vis_of_frame SEGS B LAWS lyc S2x W memX mdX cid pos x 1 HARx (HfinX _ _ HinSc) ltac:(lia) ltac:(lia) ltac:(lia)).
+ exfalso. unfold SHADOW_OFF in Hr. unfold kLowShadowBeg, kHighMemBeg in Hosh. lia. }
split.
- intros x Hx. exact (proj1 (HB1 x Hx) x ltac:(lia)).
- intros s Hs. unfold shadow_addr in Hs.
assert (Hq : o <= Z.max o (64 * (s / 8) - 8 * SHADOW_OFF) < o + 36) by (unfold SHADOW_OFF in *; lia).
apply (proj2 (HB1 _ Hq)). unfold shadow_addr. unfold SHADOW_OFF in *. lia. }
(* 5. The frame's header and its shadow, to the memset of the out struct (+0x13c). *)
assert (HFp : forall m md', AR SEGS B lyc S2 W m md' -> forall a, F <= a < F + 128 -> apresent (w_H W) m a).
{ intros m md' HA a Ha. destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HA Hfin2) as (_ & _ & Hp & _).
rewrite <- EF in Hp. change (fs_frame_bytes 1) with 128 in Hp. exact (proj1 (Hp a Ha)). }
assert (HFSp : forall m md', AR SEGS B lyc S2 W m md' -> forall a, SB + F / 8 <= a < SB + F / 8 + 16 -> apresent (w_H W) m a).
{ intros m md' HA a Ha. destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HA Hfin2) as (_ & _ & _ & Hp).
rewrite <- EF in Hp. unfold shadow_addr in Hp. change (fs_frame_bytes 1 / 8) with 16 in Hp.
replace a with (SHADOW_OFF + F / 8 + (a - (SB + F / 8))) by (unfold SHADOW_OFF, SB; lia).
assert (Hi : 0 <= a - (SB + F / 8) < 16) by (unfold SB in *; lia).
apply (proj1 (Hp (a - (SB + F / 8)) Hi)). }
assert (AG : forall n0, (n0 < 33)%nat -> ew E n0 = ew E n0) by reflexivity.
pose proof (SRr_run_pi_AJ_call B LAWS) as RUNC.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => assert (HEIc : img_env VAL A_LIM Ex) by assumption end.
lazymatch type of RUNC with forall W n E ss ss' s ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wx) ?msx) =>
let r := eval vm_compute in (sym_runN_pi tpi FUEL ssx) in
lazymatch r with (?ss', PRS_call ?sym) =>
assert (Hrun : sym_runN_pi tpi FUEL ssx = (ss', PRS_call sym)) by (vm_compute; reflexivity);
eapply (RUNC Wx FUEL Ex ssx ss' sym msx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEIc HS Hrun HJ2);
[ clear Hrun | clear Hrun HS HJ2; intros ms1 mat1 HS HJ2 HF HFr HG ] end end end.
{ awrFL_with ltac:(idtac; pz_awr_hd) AG fpos F I. }
lazymatch type of HFr with frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (Hw3 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
(fun a => (sp1 <= a < sp) \/ (o <= a < o + 36) \/ pz_nf F FL a) a) by pzS_win;
pose proof (pz_kept_own B LAWS lyc Sc S2 W memc mdc mem2 md2 mA mB (sp - REAC_CTRL_PARSE_STK) sp o fpos F FL
(fun a => (sp1 <= a < sp) \/ (o <= a < o + 36) \/ pz_nf F FL a) HAR HAR2 Hfrs2 Eab EF EFL FFL Hce Hshi64 Hoimg
ltac:(intros a [Ha|[Ha|Ha]]; [left; lia | right; left; exact Ha | right; right; exact Ha]) KP
(kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => (sp1 <= a < sp) \/ (o <= a < o + 36) \/ pz_nf F FL a) HFr Hw3)
(fun a Ha => apresent_grows (w_H W) _ _ a HG Ha)) as KP' end.
clear KP Hw3 HF HFr HG; rename KP' into KP.
(* 6. memset(out, 0, 36). *)
pose proof (proj1 HJ2) as HAR2b.
destruct (HSHO _ _ S2 HAR2b HfinS2 Eab KP) as [HRAo HHVo].
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
(* pz_rebase carried E12 and E33 to the current valuation. *)
rewrite E12 in Ra0. rewrite E33 in R2.
rewrite AGX, (EE 3%nat 3%bv eq_refl) in R3 by lia. rewrite AGX, (EE 4%nat 4%bv eq_refl) in R4 by lia.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA DS___asan_memset) (AMEMSET fq) W rT mT
STK sp0 FP ly S W0 mem0 md0 _ lyc S2 dT k o 0 36 (sp1 - sp0) _ HJ2) end.
- rewrite Ra0. reflexivity.
- rewrite Ra1. reflexivity.
- rewrite Ra2. reflexivity.
- lia. - lia. - unfold ASAN_CEIL in *; lia.
- unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
- rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
- lia. - rewrite Hes; lia.
- rewrite R3. exact Hgp. - rewrite R4. exact Htp.
- exact R1. - apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split; [rewrite Eab; apply pz_awr_cons; exact (proj1 (HOW a ltac:(lia))) | unfold ASAN_CEIL in *; lia].
- exact Hoam.
- exact HRAo.
- intros _. exact HHVo.
- exact I. }
cbv beta. clear R1 R2 R3 R4 Ra0 Ra1 Ra2.
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff3 & Hfr3 & Hpres3).
pose proof (proj1 HJ3) as HAR3.
lazymatch type of KP with pz_kept _ _ _ _ _ ?mA _ _ _ =>
pose proof (pz_kept_own B LAWS lyc Sc S2 W memc mdc mem2 md2 mA mem3 (sp - REAC_CTRL_PARSE_STK) sp o fpos F FL
(fun a => (sp1 - ESTACK <= a < sp1) \/ (o <= a < o + 36)) HAR HAR2 Hfrs2 Eab EF EFL FFL Hce Hshi64 Hoimg
ltac:(intros a [Ha|Ha]; [left; rewrite Hes in Ha; lia | right; left; exact Ha]) KP
ltac:(intros a Ha Hna; apply Hfr3; [exact Ha | intros Hx; apply Hna; right; exact Hx | intros Hx; apply Hna; left; lia]) Hpres3) as KP' end.
clear KP; rename KP' into KP.
(* 7. The out struct is zero (memset); the frame and its shadow are read-only while the shadow is checked. *)
jafter_call_keep_hi HS 544%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1; 2; 3; 4; 5; 6; 7]%nat HS3.
match type of HS3 with ?Q -> _ => assert (HQ : Q); [| specialize (HS3 HQ); clear HQ] end.
{ pose proof Hoimg as Hoimg'. unfold off_img in Hoimg'. pose proof Hosh as Hosh'. unfold kLowShadowBeg, kHighMemBeg in Hosh'.
cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
(eapply pz_region_kept; [pz_bases; reflexivity
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr3;
  [ unfold SB, SHADOW_OFF in *; lia | unfold SB, SHADOW_OFF in *; lia | unfold ESTACK, SB in *; lia ]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
  first [ exfalso; lia | apply (HFp _ _ HAR3); lia | apply (HFSp _ _ HAR3); lia
  | apply (proj2 (proj2 (proj2 (proj2 (proj2 KP))))); lia ] ]). }
rewrite <- restrict_mkst_fx in HS3. clear HS; rename HS3 into HS.
pz_rebase HS AGX.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
assert (ROK : region_ok SEGS Ev (ms_mem msx) (YP09.mkRegion (Some 12%nat) 0 36 0 36 [YP09.mkChunk 0 (CZero 36)]));
[| assert (RDJ : all_disjoint Ev (YP09.mkRegion (Some 12%nat) 0 36 0 36 [YP09.mkChunk 0 (CZero 36)]) (ss_mem ssx))] end.
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
pz_bases. split; [lia|]. split; [unfold ASAN_CEIL in *; lia|]. split.
- intros o0 Ho0. apply (apresent_writable SEGS). exact (HOpres mem3 md3 S2 HAR3 Eab HJ3 (o + o0) ltac:(lia)).
- apply Forall_cons; [|apply Forall_nil]. apply pz_chunk_zero. intros i Hi.
replace (o + 0 + i) with (o + i) by lia. rewrite (Heff3 i Hi). reflexivity. }
{ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
cbn [all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
pz_bases.
revert Hslo Hshi H47 Hceil Hwin Hstk0 WS C1 Hsp1r Hob0 Hob1 Hob66 Hob67 Ho4096 Ho47 Hoce Hosh Hoimg HFo2 HFLo HF4096 HFceil HFapp HFimg Hsp0 HF8lo HF8hi.
unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB. clear. intros. repeat split; first [lia | match goal with |- ?g => idtac "DISJ12" g; fail end]. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_region Ev ssx msx (YP09.mkRegion (Some 12%nat) 0 36 0 36 [YP09.mkChunk 0 (CZero 36)]) HS eq_refl ROK RDJ) as HS' end.
clear HS ROK RDJ; rename HS' into HS. pz_norm HS.
(* The frame's shadow (529) and the frame (516) become read-only: the shadow-checked runs need every
   writable window apart from the shadow span (as at cut M of the walk proper). *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o0 Ho0; lia))) as HS' end.
clear HS; rename HS' into HS. pz_norm HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 516%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o0 Ho0; lia))) as HS' end.
clear HS; rename HS' into HS. pz_norm HS.
(* 8. The shadow entry of the out struct at the memory the memset left, then the length test (+0x144). *)
destruct (HSHO _ _ S2 HAR3 HfinS2 Eab KP) as [HRA3 HHV3].
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msv) =>
assert (SHOK : sh_ok SEGS PZx PZ_SH0 Ev (mrestrict (w_H W) (ms_mem msv)));
[ unfold sh_ok, PZ_SH0; constructor; [|constructor];
  apply (shent_ok_of_range SEGS (w_H W) (ms_mem msv) Ev PZx 12 o 36 o 0 36 HRA3);
  [ unfold U, PZx; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by (unfold SB; lia); reflexivity
  | unfold U; cbn [sv_denot]; rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity
  | lia | lia
  | intros x Hx; cbn [Z.min Z.max] in Hx; unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia ]
| ] end.
paj_run_to_tok RUNTO HS HJ3 SHOK PZspan AF_JOIN.
{ awrFL_with ltac:(idtac; pz_awr_hd) AG fpos F I. }
lazymatch type of HFr with frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (Hw4 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
(fun a => (sp1 <= a < sp) \/ (o <= a < o + 36) \/ pz_nf F FL a) a) by pzS_win;
pose proof (pz_kept_own B LAWS lyc Sc S2 W memc mdc mem2 md2 mA mB (sp - REAC_CTRL_PARSE_STK) sp o fpos F FL
(fun a => (sp1 <= a < sp) \/ (o <= a < o + 36) \/ pz_nf F FL a) HAR HAR2 Hfrs2 Eab EF EFL FFL Hce Hshi64 Hoimg
ltac:(intros a [Ha|[Ha|Ha]]; [left; lia | right; left; exact Ha | right; right; exact Ha]) KP
(kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => (sp1 <= a < sp) \/ (o <= a < o + 36) \/ pz_nf F FL a) HFr Hw4)
(fun a Ha => apresent_grows (w_H W) _ _ a HG Ha)) as KP' end.
clear KP Hw4 HF HFr HG; rename KP' into KP.
psrr_branch_tok RUN BR HS SHOK PZspan.
2: { (* 50 <= n contradicts the premise of the short walk. *)
exfalso. rewrite branch_ltu_U in Hc.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rewrite (U_atom Ev 11 n E11 ltac:(lia)), U_lit in Hc by lia end.
apply Z.ltb_ge in Hc. lia. }
clear Hc.
(* 9. 0x6464 + 0x3a4 li a0,0, to cut J. *)
paj_run_to_tok RUNTO HS HJ3 SHOK PZspan AF_JOIN.
{ awrFL_with ltac:(idtac; pz_awr_hd) AG fpos F I. }
lazymatch type of HFr with frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (Hw5 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
(fun a => (sp1 <= a < sp) \/ (o <= a < o + 36) \/ pz_nf F FL a) a) by pzS_win;
pose proof (pz_kept_own B LAWS lyc Sc S2 W memc mdc mem2 md2 mA mB (sp - REAC_CTRL_PARSE_STK) sp o fpos F FL
(fun a => (sp1 <= a < sp) \/ (o <= a < o + 36) \/ pz_nf F FL a) HAR HAR2 Hfrs2 Eab EF EFL FFL Hce Hshi64 Hoimg
ltac:(intros a [Ha|[Ha|Ha]]; [left; lia | right; left; exact Ha | right; right; exact Ha]) KP
(kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => (sp1 <= a < sp) \/ (o <= a < o + 36) \/ pz_nf F FL a) HFr Hw5)
(fun a Ha => apresent_grows (w_H W) _ _ a HG Ha)) as KP' end.
clear KP Hw5 HF HFr HG; rename KP' into KP.
(* 10. Cut J: the out struct holds the model's 36 zero bytes and a0 is 0. *)
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wx) ?msv) |- _ =>
let rs := eval vm_compute in (ss_mem ssx) in
let ix := idx_of_base rs 12%nat in let ix := eval vm_compute in ix in
let r := eval vm_compute in (nth ix rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wx) msv) ix r HS ltac:(vm_compute; reflexivity)) as R12;
cbn [ms_mem restrict] in R12;
assert (HZ : forall j, (j < 36)%nat -> aview SEGS (w_H W) (ms_mem msv) (o + Z.of_nat j) = Some (bv_unsigned cp_z));
[ intros j Hj;
  assert (Hb : pz_chunk_at Ex (base_val Ex (Some 12%nat)) [YP09.mkChunk 0 (CZero 36)] (Z.of_nat j) = Some (Z_to_bv 8 0))
  by (cbn [pz_chunk_at YP09.c_off YP09.c_len YP09.cv_len YP09.c_val];
      replace ((0 <=? Z.of_nat j) && (Z.of_nat j <? 0 + 36)) with true
      by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia);
      reflexivity);
  pose proof (pz_region_byte Ex (w_H W) (ms_mem msv) _ (Z.of_nat j) _ R12 Hb) as Hv;
  revert Hv; cbn [YP09.r_base base_val]; pz_bases; intros Hv; exact Hv
| clear R12 ] end.
(* The frame (516) and its shadow (529) become writable again, as cut J has them. *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let ix := idx_of_base rs 529%nat in let ix := eval vm_compute in ix in
let r := eval vm_compute in (nth ix rs got_regionP) in
pose proof (ast_ok_pi_set_region Ex ssx msx ix r (set_window r 0 16) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 16 (st_ok_pi_region_nth Ex ssx msx ix r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite E529, unsigned_lit_small by (unfold SB; lia);
intros o0 Ho0; apply (apresent_writable _); apply (HFSp _ _ (proj1 HJ3)); lia))) as HS' end.
clear HS; rename HS' into HS; pz_norm HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let ix := idx_of_base rs 516%nat in let ix := eval vm_compute in ix in
let r := eval vm_compute in (nth ix rs got_regionP) in
pose proof (ast_ok_pi_set_region Ex ssx msx ix r (set_window r 0 128) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 128 (st_ok_pi_region_nth Ex ssx msx ix r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite RF, unsigned_lit_small by lia;
intros o0 Ho0; apply (apresent_writable _); apply (HFp _ _ (proj1 HJ3)); lia))) as HS' end.
clear HS; rename HS' into HS; pz_norm HS.
prreg HS (10%bv : bv 5) R0.
ra_join HS ss_cutJ 700%nat pz_deadJ ltac:(idtac).
ra_join_val HS 700%nat 0%nat R0 E700.
pz_rebase HS AGX.
(* 11. The cut's context and its hypothesis. *)
set (c := mkPZ fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch f n o fr S2 fpos).
assert (Hok : pz_ok B c).
{ unfold pz_ok, c. cbn [cx_fq cx_STK cx_sp0 cx_FP cx_ly cx_S cx_W0 cx_mem0 cx_md0 cx_own cx_lyc cx_Sc cx_W cx_memc
cx_mdc cx_k cx_regs cx_ch cx_f cx_n cx_o cx_fr cx_S2 cx_fpos].
split; [exact HJe|]. split; [exact HROD|]. split; [exact Hra|]. split; [exact Hra4|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact H10|]. split; [exact H11|]. split; [exact H12|].
split; [exact Hn64|]. split; [exact Hch|]. split; [exact Hal16|]. split; [exact Hwin|]. split; [exact Hsp0|].
split; [exact Htop32|]. split; [exact Hroom|]. split; [exact Hflen|].
split; [intros Hbig; exfalso; lia|]. split; [exact HOOK|].
split; [exact Hfrs2|]. split; [exact Eab|]. split; [exact Hnin|]. exists fS2. exact ES2. }
pose proof (HJcut c Hok) as HJc.
unfold pz_cutJ_spec, pz_cur, pz_post, pz_E0, c in HJc.
cbn [cx_fq cx_STK cx_sp0 cx_FP cx_ly cx_S cx_W0 cx_mem0 cx_md0 cx_own cx_lyc cx_Sc cx_W cx_memc
cx_mdc cx_k cx_regs cx_ch cx_f cx_n cx_o cx_fr cx_S2 cx_fpos ms_mem] in HJc.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msv) =>
eapply (HJc Ev msv);
[ split; [assumption|]; split; [exact AGX|]; split; [exact RF|]; split; [exact E528|]; split; [exact E529|];
  split; [exact HJ3 | exact KP]
| exact HS
| unfold ctrlparse; rewrite Hh; cbn [fst]; exact E700
| intros j Hj; rewrite (ctrlparse_bytes_none n fr Hh), nth_repeat; exact (HZ j Hj) ] end.
Qed.
End d.
End b.
