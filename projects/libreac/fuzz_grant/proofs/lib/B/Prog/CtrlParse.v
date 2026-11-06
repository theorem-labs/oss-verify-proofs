(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: adapted from cgif's lib/A/ACgq.v and lib/A/ACk8.v (file header, walk tactic forms) for reac_ctrl_parse of libreac's fuzz_grant. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) walk of reac_ctrl_parse 0x82774, in the shape of lib/A/Prog/CtrlParse.v at a working branch 603e40683a4 (image A 0x82000), with image B's addresses, objects and the B-only UBSan branches; B's function is 2692 bytes / 673 instructions against A's 2464 / 616. Source blob de33ee0576e4 (lib/A/Prog/CtrlParse.v at a working branch 603e40683a4; the same blob at 7e98c198edd). *)
(* reac_ctrl_parse (0x82774) of image B (fuzz_grant.asan-ubsan): its contract, in the caller-journal form
   (it writes the caller's `struct reac_ctrl_parsed`), and its walk on the position-abstract listing.
   The function takes a side-stack frame of class 1, calls __asan_memset once, __asan_memcpy twice,
   the bcmp wrapper (through the 4-byte jump __interceptor_trampoline_bcmp) once and kind_of_link1 once;
   the return code and the 36 bytes it writes are Pau's model `ctrlparse` (lib/Prog/RcParse.v). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantSyms GrantList GrantPa GrantPaLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC1g YC1h YC45 YC85 GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC88.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import CtrlParseLib KindOfLink1 GrantRo ACj1 GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Export CtrlParseCut.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import CtrlParseMid CtrlParseNone CtrlParseAcc CtrlParseTail CtrlParseEpi.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantTop.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require GrantBContracts.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
Section m.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA GS___asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA GS___asan_memcpy).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA GS___interceptor_trampoline_bcmp).
Hypothesis ASM1 : astack_malloc_realizes SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis KIND : tkind_of_link1_spec B.
(* The bcmp wrapper compares the frame with "\xff\xff\xff\xff\xff\xff" (.str.4, a registered global of 7 bytes). *)
Variable G : list (Z * Z).
Hypothesis HGM : globs_marked SEGS B G.
Hypothesis HG15 : In (VAL (A_OBJ OBJ_BCAST), 7) G.
Hypothesis HIMGSH : img_shadow_vis SEGS B.
Hypothesis HBC_RNG : IMG_LO + 64 <= VAL (A_OBJ OBJ_BCAST) /\ VAL (A_OBJ OBJ_BCAST) + 6 + 64 <= IMG_HI.
Hypothesis HBC_VAL : forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
forall i, 0 <= i < 6 -> aview SEGS H mem (VAL (A_OBJ OBJ_BCAST) + i) = Some 255.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI). Let RET := paj_ret_at (PL := PL_grant) (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Theorem pb_ctrl_parse : tctrl_parse_spec B.
Proof.
unfold tctrl_parse_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch f n o fr
HJ HROD Hra Hra4 Hgp Htp H10 H11 H12 Hn Hch Hal16 Hwin Hsp0 Hroom Hof Hoo Hdfo HOW Hflen Hfr.
pose proof HJ as HJe.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pz_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (WS : TPARSE_STK = 8336) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
destruct (pz_entry B LAWS TL TLF STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs f n o fr HJ H10 H11 H12 Hn Hal16 Hwin Hsp0 Hof Hoo Hdfo Hfr) as [HS SHOK].
destruct (pz_env regs fr f n o H10 H11 H12) as (EE & E10 & E11 & E12 & E32 & E33 & EFB & EOB).
set (E := Eimg (Ereg regs (pz_extra (spZ regs) fr))) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
pose proof Hof as ((cf & pf & Hfin & Hcf0 & Hfal & Hflo & Hfhi) & Hf8 & HRf).
pose proof Hoo as ((co & po & Hoin & Hco0 & Hoal & Holo & Hohi) & Ho8 & HRo).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cf pf HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc co po HAR Hoin) as (Ho4096 & Hoceil & Hoapp).
assert (B241 : bv_unsigned (ew E 241) = VAL (A_OBJ 0)) by (change 241%nat with (A_OBJ 0); rewrite (EOB 0%nat ltac:(lia)); apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 0)); lia).
assert (B242 : bv_unsigned (ew E 242) = VAL (A_OBJ 1)) by (change 242%nat with (A_OBJ 1); rewrite (EOB 1%nat ltac:(lia)); apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 1)); lia).
assert (B276 : bv_unsigned (ew E 276) = VAL (A_OBJ 35)) by (change 276%nat with (A_OBJ 35); rewrite (EOB 35%nat ltac:(lia)); apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 35)); lia).
assert (B277 : bv_unsigned (ew E 277) = VAL (A_OBJ 36)) by (change 277%nat with (A_OBJ 36); rewrite (EOB 36%nat ltac:(lia)); apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 36)); lia).
assert (B10 : bv_unsigned (ew E 10) = f) by (rewrite E10; apply unsigned_lit_small; lia).
assert (B12 : bv_unsigned (ew E 12) = o) by (rewrite E12; apply unsigned_lit_small; lia).
pose proof (pz_obj_img 0 ltac:(lia)) as Hob0. pose proof (pz_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pz_obj_img 35 ltac:(lia)) as Hob32. pose proof (pz_obj_img 36 ltac:(lia)) as Hob33.
set (sp := spZ regs) in *. set (sp1 := pz_sp1 sp) in *.
pose proof (pz_kept_refl B lyc Sc W memc (sp - TPARSE_STK) sp (fun a => o <= a < o + 36) ltac:(intros a Ha; apply Hpres; lia)) as KP.
unfold cfg_at, A_ctrl_parseP. change (w64 (BASE + AF_reac_ctrl_parse)) with (Z_to_bv 64 (BASE + AF_reac_ctrl_parse)).
(* 1. To the instruction after the realignment of sp. *)
paj_run_to_tok RUNTO HS HJ SHOK PZspan (AF_reac_ctrl_parse + 0x40).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own' => let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own') end.
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0)); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
do 5 (apply awr_ok_cons_ro; [cbn; lia|]).
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 12%nat o); [reflexivity | rewrite E12; apply unsigned_lit_small; lia | | apply awr_ok_nil].
intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply HOW. lia. }
lazymatch type of HFr with frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (Hw1 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
(fun a => (sp - 144 <= a < sp) \/ (o <= a < o + 36)) a) by (pz_win_tac ltac:(fun H => rewrite ?Usp, ?B12 in H));
pose proof (pz_kept_run B LAWS lyc Sc W memc mdc mA mB (sp - TPARSE_STK) sp o (fun _ => False)
(fun a => (sp - 144 <= a < sp) \/ (o <= a < o + 36)) co po HAR ltac:(lia) ltac:(lia) Hoin Holo Hohi
ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction)
ltac:(intros a Ha; cbv beta in Ha; lia) KP
(kept_of_frame _ _ _ _ _ _ HFr Hw1)
(fun a Ha => apresent_grows _ _ _ a HG Ha)) as KP' end.
clear KP Hw1 HF HFr HG; rename KP' into KP.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
(* 2. sp is realigned to 32 bytes: atom 33 names it; the stack region keeps the saved registers and a new
   region holds sp + [0, 32). *)
assert (E2' : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
destruct (sp1_facts (sp - 128) ltac:(lia) ltac:(rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
change (32 * ((sp - 128) / 32)) with sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (B33 : bv_unsigned (ew E 33) = sp1) by (rewrite E33; apply unsigned_lit_small; lia).
pose proof (st_ok_pi_restrict_reg (w_H W) E _ _ 2%bv HS) as R2.
lazymatch type of R2 with _ = sv_denot _ (sr_get (ss_regs ?ssx) _) => let e := eval vm_compute in (sr_get (ss_regs ssx) 2%bv) in change (sr_get (ss_regs ssx) 2%bv) with e in R2 end.
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
rewrite ?Usp, ?B10, ?B12, ?B241, ?B242, ?B276, ?B277, E33, unsigned_lit_small by lia;
repeat split; lia)) as HS' end.
clear HS; rename HS' into HS; pz_norm HS.
(* 3. To the side-stack frame's allocation: the use-after-return flag cell holds 1. *)
paj_run_tok RUN HS HJ SHOK PZspan.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own' => let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own') end.
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 33%nat (sp1 - sp0)); [reflexivity | rewrite E33, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (sp - sp0)); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
do 5 (apply awr_ok_cons_ro; [cbn; lia|]).
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 12%nat o); [reflexivity | exact B12 | | apply awr_ok_nil].
intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply HOW. lia. }
lazymatch type of HFr with frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (Hw1 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
(fun a => (sp1 <= a < sp) \/ (o <= a < o + 36)) a) by (pz_win_tac ltac:(fun H => rewrite ?Usp, ?B12, ?B33 in H));
pose proof (pz_kept_run B LAWS lyc Sc W memc mdc mA mB (sp - TPARSE_STK) sp o (fun _ => False)
(fun a => (sp1 <= a < sp) \/ (o <= a < o + 36)) co po HAR ltac:(lia) ltac:(lia) Hoin Holo Hohi
ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction)
ltac:(intros a Ha; cbv beta in Ha; lia) KP
(kept_of_frame _ _ _ _ _ _ HFr Hw1)
(fun a Ha => apresent_grows _ _ _ a HG Ha)) as KP' end.
clear KP Hw1 HF HFr HG; rename KP' into KP.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
rewrite E33 in R2. rewrite (EE 3%nat 3%bv eq_refl) in R3. rewrite (EE 4%nat 4%bv eq_refl) in R4.
pmkst HS. rewrite (palf_sm1 B TLF).
pose proof (count_cid_le_length 1 (frames Sc)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs (pal_env B TL) ML SMP 1 ASM1 ltac:(lia) W (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (sp1 - sp0) _ HJ) end.
- unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
- rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
- lia. - rewrite Hes; lia.
- rewrite R3. exact Hgp. - rewrite R4. exact Htp.
- exact R1. - apply ret_ok_codeptr_v; [lia | reflexivity].
- change (fs_frames 1) with 8192. lia. }
cbv beta. clear R1 R2 R3 R4 SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJin & (fS2 & ES2)).
pose proof (pz_kept_trans B lyc Sc W memc _ mem2 (sp - TPARSE_STK) sp _ _ _ _ ltac:(lia) ltac:(lia) KP HK ltac:(lia) ltac:(lia) ltac:(intros; contradiction)) as KP'.
clear KP; rename KP' into KP.
(* 4. After the allocation: the registers it clobbers are havocked from atom 512 on and the regions are kept. *)
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kc0 & Ku0 & Kg0 & Kgu0).
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kc2 & Ku2 & Kg2 & Kgu2).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kg0, Kg2. rewrite (pal_cell B TL) in Kc0, Kc2.
rewrite (pal_got_uar B TL), (pal_uar_cell B TL) in Kgu0, Kgu2. rewrite (pal_uar_cell B TL) in Ku0, Ku2.
pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6).
pose proof (proj1 HJ2) as HAR2.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
assert (HfinS2 : forall c p, In (c, p) (frames Sc) -> In (c, p) (frames S2)) by (intros c p Hcp; rewrite Hfrs2; right; exact Hcp).
destruct (al_frames _ _ LAWS _ _ _ _ _ co po HAR2 (HfinS2 _ _ Hoin)) as (_ & _ & Hopres2 & _).
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5; 6; 7]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q); [| specialize (HS2 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
- apply (pz_region_kept E _ _ _ 33 sp1); [exact B33 | intros a Ha; apply K1; [lia | intros [? ?]; lia] | intros a Ha; apply Hpres2; lia].
- apply (pz_region_kept E _ _ _ 2 sp); [exact Usp | intros a Ha; apply K1; [lia | intros [? ?]; lia] | intros a Ha; apply Hpres2; lia].
- apply (region_kept_val_at E _ _ 241 (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 36))); [exact B241 | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu0) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu2) | lia].
- apply (region_kept_val_at E _ _ 277 (VAL (A_OBJ 36)) 4 1); [exact B277 | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku0) | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku2) | lia].
- apply (region_kept_val_at E _ _ 242 (VAL (A_OBJ 1)) 8 (VAL (A_OBJ 35))); [exact B242 | exact (val_mem_of_rdword SEGS _ _ _ _ Kg0) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg2) | lia].
- apply (region_kept_val_at E _ _ 276 (VAL (A_OBJ 35)) 8 SHADOW_OFF); [exact B276 | exact (val_mem_of_rdword SEGS _ _ _ _ Kc0) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc2) | lia].
- apply (pz_region_kept E _ _ _ 10 f); [exact B10 | intros a Ha; apply (K4 cf pf a Hfin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | intros []] | intros a Ha; lia].
- apply (pz_region_kept E _ _ _ 12 o); [exact B12 | intros a Ha; apply (K4 co po a Hoin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | intros []] | intros a Ha; apply (proj1 (Hopres2 a ltac:(lia)))]. }
rewrite <- restrict_mkst_fx in HS2. clear HS; rename HS2 into HS.
(* 4b. The frame (1, fpos) the allocation returned: atom 516 is its address (a0), 528 its flag, 529 its
   shadow; a region for each of the frame and its 16 shadow bytes. *)
assert (AGX0 : forall n0, (n0 < 512)%nat -> ew E n0 = ew E n0) by reflexivity.
pz_rebase HS AGX0. rename AGX0 into AGX.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & _).
destruct (FFL _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFLpres & HFLown & (HFLapp & HFLimg) & (HFL4096 & _ & HFLce)).
pose proof (pz_frm_off B _ _ _ _ _ 1 fpos HAR2 Hfin2) as HFimg.
pose proof (pz_own_sep B LAWS _ _ _ _ _ 1 fpos Sc cf pf HAR2 Hfrs2 Hfin) as HsepF.
pose proof (pz_own_sep B LAWS _ _ _ _ _ 1 fpos Sc co po HAR2 Hfrs2 Hoin) as HsepO.
unfold zdisjoint, frame_rng in HsepF, HsepO. cbn [fst snd] in HsepF, HsepO.
change (fs_frame_bytes 1) with 128 in HsepF, HsepO.
change (fs_frame_bytes 1) with 128 in HFapp, HFceil, HFpres, HFSpres, Hz, Hflag, HFimg.
change (128 / 8) with 16 in HFSpres.
set (F := frame_addr lyc 1 fpos) in *. set (FL := flag_addr lyc 1 fpos) in *.
assert (EF : F = frame_addr lyc 1 fpos) by reflexivity. assert (EFL : FL = flag_addr lyc 1 fpos) by reflexivity.
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
revert Hslo Hshi H47 Hceil Hwin Hstk0 WS C1 Hsp1r Hob0 Hob1 Hob32 Hob33 Hflo Hfhi Holo Hohi Hfceil Hoceil Hf4096 Ho4096 HF4096 HFceil HFapp HFimg HsepF HsepO Hfapp Hoapp Hsp0.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. clear. intros. repeat split; first [lia | match goal with |- ?g => idtac "DISJ516" g; fail end]. }
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
revert Hslo Hshi H47 Hceil Hwin Hstk0 WS C1 Hsp1r Hob0 Hob1 Hob32 Hob33 Hflo Hfhi Holo Hohi Hfceil Hoceil Hf4096 Ho4096 HF4096 HFceil HFapp HFimg HsepF HsepO Hfapp Hoapp Hsp0 HF8lo HF8hi.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB. clear. intros. repeat split; first [lia | match goal with |- ?g => idtac "DISJ529" g; fail end]. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_region Ev ssx msx (fshadow_region 529 1 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]) HS eq_refl ROK RDJ) as HS' end.
clear HS ROK RDJ; rename HS' into HS. pz_norm HS.
(* Cut A. The rest of the walk is in CtrlParseMid.v (to cut M), CtrlParseNone.v and CtrlParseAcc.v (cut M to
   cut J / cut B), CtrlParseTail.v (cut B to cut J) and CtrlParseEpi.v (cut J to the return). *)
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => change ssx with ss_cutA in HS end.
pose proof (conj LAWS (conj TL (conj TLF (conj ML (conj AMEMSET (conj AMEMCPY (conj ABCMP (conj ASM1 (conj SMP
(conj ASF (conj FFL (conj KIND (conj HGM (conj HG15 (conj HIMGSH (conj HBC_RNG HBC_VAL))))))))))))))) : pz_rt B G) as RT.
set (c := mkPZ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch f n o fr S2 fpos cf pf co po).
assert (Hok : pz_ok B c).
{ unfold pz_ok, c. cbn [cx_STK cx_sp0 cx_FP cx_ly cx_S cx_W0 cx_mem0 cx_md0 cx_own cx_lyc cx_Sc cx_W cx_memc
cx_mdc cx_k cx_regs cx_ch cx_f cx_n cx_o cx_fr cx_S2 cx_fpos cx_cf cx_pf cx_co cx_po].
split; [exact HJe|].
repeat match goal with |- _ /\ _ => split; [assumption|] end. exists fS2. exact ES2. }
assert (HJc : pz_cutJ_spec B c) by exact (pz_segD B G RT c Hok).
assert (HBc : pz_cutB_spec B c) by exact (pz_segC B G RT c Hok HJc).
assert (HMc : pz_cutM_case B c True).
{ intros E' ms' md' Hc' HS' SH' _. destruct (cp_hdr n fr) eqn:Hh.
- exact (pz_segAcc B G RT c Hok HBc E' ms' md' Hc' HS' SH' Hh).
- exact (pz_segN B G RT c Hok HJc E' ms' md' Hc' HS' SH' Hh). }
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msv) =>
assert (Hcur : pz_cur B c Ev msv md2);
[ unfold pz_cur, pz_E0, c; cbn [cx_STK cx_sp0 cx_FP cx_ly cx_S cx_W0 cx_mem0 cx_md0 cx_own cx_lyc cx_Sc cx_W cx_memc
cx_mdc cx_k cx_regs cx_ch cx_f cx_n cx_o cx_fr cx_S2 cx_fpos cx_cf cx_pf cx_co cx_po ms_mem];
split; [assumption|]; split; [exact AGX|]; split; [exact RF|]; split; [exact E528|]; split; [exact E529|];
split; [exact HJ2 | exact KP]
| exact (pz_segB B G RT c Hok HMc Ev msv md2 Hcur HS) ] end.
Qed.
End m.
End d.
End b.
(* The image-B contract (GrantBContracts.v walk_reac_ctrl_parse): hyps_reac_ctrl_parse and kind_of_link1's contract
   give pb_ctrl_parse's section hypotheses (G := GRANT_GLOBS_B; RT_TP_FS and IMG_RO_BELOW are not used, and neither
   is tb_live_frames_client); the contract's twr_ok gives awr_byte over [o, o + 36), and the walk's acall_kept over
   the window [sp - 144 - 2 * ESTACK, sp) gives tcj_kept with STK_reac_ctrl_parse = TPARSE_STK. *)
Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg grant_listing}.
Variable B : asyms.
Lemma pz_tcj : forall lyc Sc (W : world (@pa_segs _ grant_listing PI)) memc W2 mem2 sp (Eo : Z -> Prop),
acall_kept (@pa_segs _ grant_listing PI) B lyc Sc W memc W2 mem2 (sp - TPARSE_STK) sp Eo ->
GrantBContracts.tcj_kept B GrantBContracts.STK_reac_ctrl_parse lyc Sc W memc W2 mem2 sp Eo.
Proof.
intros lyc Sc W memc W2 mem2 sp Eo (K1 & K2 & K3 & K4 & K5 & K6).
unfold GrantBContracts.tcj_kept. change GrantBContracts.STK_reac_ctrl_parse with TPARSE_STK.
split; [intros a Ha Hw _; exact (K1 a Ha Hw)|].
split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K5 | exact K6].
Qed.
Theorem pb_reac_ctrl_parse : GrantBContracts.walk_reac_ctrl_parse B.
Proof.
unfold GrantBContracts.walk_reac_ctrl_parse, GrantBContracts.hyps_reac_ctrl_parse, GrantBContracts.tb_reac_ctrl_parse_spec,
GrantBContracts.IMG_reac_ctrl_parse, GrantBContracts.tb_kind_of_link1_spec.
intros (LAWS & TL & TLF & ML & AMS & AMC & ABC & ASM1 & SMP & ASF & FFL & _ & HIMGSH & HGM & _ & HG15 & HRNG1 & HRNG2 & HVAL) KIND.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch f n o fr
HJ HROD Hra Hra4 Hgp Htp H10 H11 H12 Hn Hch Hal16 Hwin Hsp0 Hroom _ Hof Hoo Hdfo HOW Hflen Hfr.
eapply SRr_mono.
{ exact (pb_ctrl_parse B LAWS TL TLF ML AMS AMC ABC ASM1 SMP ASF FFL KIND GRANT_GLOBS_B HGM HG15 HIMGSH (conj HRNG1 HRNG2) HVAL
  STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch f n o fr HJ HROD Hra Hra4 Hgp Htp H10 H11 H12 Hn Hch Hal16
  Hwin Hsp0 Hroom Hof Hoo Hdfo (fun a Ha => proj1 (HOW a Ha)) Hflen Hfr). }
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ2 & HP & Hfr2 & Eab & Hff & Hr & Hb & KP).
exists ly2, S2, regs2, mem2, md2.
split; [exact Hc|]. split; [exact HJ2|]. split; [exact HP|]. split; [exact Hfr2|]. split; [exact Eab|].
split; [exact Hff|]. split; [exact Hr|]. split; [exact Hb|].
exact (pz_tcj lyc Sc W memc W2 mem2 (spZ regs) (fun a => o <= a < o + 36) KP).
Qed.
End W.
